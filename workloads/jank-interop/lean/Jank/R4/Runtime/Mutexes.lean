import Determinismo
import Std.Data.HashMap
import Jank.R3.Runtime.Common
import Jank.R3.Runtime.Folly

/-!
# Round 4, Runtime: the recursive mutexes round 3 left out, and lazy compilation's locks

Round 3 replicated jank's SharedMutex/std::mutex/loader lock sequences (`Jank.R3.Runtime.Locks`)
but left out the JIT's and the multimethods' recursive mutexes, saying no callbacks run under
them. Re-read at 7135b7708 (upstream-main/compiler+runtime):

- **multimethods**, runtime/obj/multi_function.cpp: one `std::recursive_mutex mutex`
  (multi_function.hpp 99), taken by `reset` 129-135, `reset_cache` 137-143, `add_method`
  145-153, `remove_method` 155-161, `prefer_method` 163-184 and `find_and_cache_best_method`
  262-307. `add_method` holds it across `method_table->assoc(dispatch_val, method)`, which hashes
  the dispatch value: a lazy seq is realized there, its body (user code) running under the
  mutex. `get_method` 248-260 calls `reset_cache` whenever `cached_hierarchy !=
  hierarchy.deref()`; `reset_cache` stores `cached_hierarchy = hierarchy`, the hierarchy *var*
  (defmulti's default `#'global-hierarchy`, core.jank 4118), so the comparison (a var against
  its map, object_ref identity, oref.hpp 1324-1346) never holds and **every call takes the
  mutex**. Methods and the dispatch fn run unlocked. Clojure 1.12 (MultiFn.java): a
  `ReentrantReadWriteLock`; `addMethod`/`preferMethod`/`removeMethod` take the write lock (also
  hashing under it); `getMethod` reads `methodCache` with no lock when `cachedHierarchy ==
  hierarchy.deref()` (it caches the deref'd map), so a dispatch value that is a method-table key
  (the cache starts as the table) is found lock-free; `findAndCacheBestMethod` takes the read
  lock, then the write lock.
- **the JIT**, jit/processor.hpp 100-102: `folly::Synchronized<…, std::recursive_mutex>
  interpreter`, held by `eval_string` 590-605 across `ParseAndExecute` (cpp/raw's code runs
  there: evaluate.cpp eval(cpp_raw) 633-637, and its global initializers can call into jank),
  `load_object`, `load_ir_module` (runs module initializers), `find_symbol`, `remove_symbol`,
  `load_dynamic_library` (dlopen runs the library's constructors). jank compiles under it.
- **lazy compilation**, deferred_cpp_function.cpp `realize` 46-73 (see `Deferred`): the
  per-object `std::recursive_mutex compilation_mutex`, then the JIT lock (`eval_string` of the
  declaration), then `var->bind_root` (the owner var's `write_mutex`, folly::SharedMutex,
  exclusive). var.cpp `alter_root` 106-112 holds that write_mutex across the user fn.
- lazy seqs, runtime/obj/lazy_sequence.cpp: a recursive mutex around realization, as Clojure's
  synchronized `sval` (round 1).

The world: one var `f` whose root is a never-called `defn` (a deferred fn owning `f`), one lazy seq
`L`, one multimethod `mm` with a method for `:a`, a future `F` started at the beginning when a
program derefs it. Operations below; callback bodies (alter fn, `f`'s body, `L`'s body, `F`'s body,
a cpp/raw initializer) are drawn from the same alphabet, at a depth budget.
-/

namespace Jank.R4.Runtime.Mutexes

open Determinismo Jank.R3.Runtime

inductive Mode | jank | clojure
  deriving BEq, Hashable, Repr, Inhabited

inductive Op where
  | alterF | defF | callF | derefF | realizeL | mmDefL | mmCallA | mmCallL | cppRaw | evalFn
  deriving BEq, Hashable, Repr, Inhabited, DecidableEq

def Op.clj : Op → String
  | .alterF => "(alter-var-root #'f g)" | .defF => "(def f 1)" | .callF => "(f)"
  | .derefF => "@F" | .realizeL => "(seq L)" | .mmDefL => "(defmethod mm L …)"
  | .mmCallA => "(mm :a)" | .mmCallL => "(mm L)"
  | .cppRaw => "(cpp/raw \"…initializer calling jank…\")" | .evalFn => "(eval '(fn [] 1))"

def alphabet : List Op := [.alterF, .defF, .callF, .derefF, .realizeL, .mmDefL, .mmCallA, .mmCallL, .cppRaw, .evalFn]

inductive Slot | alterFn | fBody | lBody | futBody | rawBody
  deriving BEq, Hashable, Repr, Inhabited, DecidableEq

def Slot.idx : Slot → Nat
  | .alterFn => 0 | .fBody => 1 | .lBody => 2 | .futBody => 3 | .rawBody => 4

def Slot.name : Slot → String
  | .alterFn => "alter-var-root fn g" | .fBody => "f's body" | .lBody => "L's body"
  | .futBody => "F's body" | .rawBody => "the cpp/raw initializer"

/-- Recursive locks. -/
def rComp : Nat := 0   -- deferred fn's compilation_mutex (jank)
def rJit : Nat := 1    -- the JIT interpreter (jank)
def rMM : Nat := 2     -- the multimethod's recursive mutex (jank)
def rL : Nat := 3      -- L's realization lock (both)
def rVar : Nat := 4    -- Clojure: the var's monitor
def numR : Nat := 5

def rName : Nat → String
  | 0 => "deferred fn compilation_mutex" | 1 => "JIT interpreter recursive_mutex"
  | 2 => "multimethod recursive_mutex" | 3 => "lazy seq L's lock" | 4 => "var f's monitor" | _ => "?"

inductive I where
  | op (o : Op) (d : Nat)
  | call (s : Slot) (d : Nat)
  | rAcq (x : Nat) | rRel (x : Nat)
  /-- f's write_mutex (folly::SharedMutex, exclusive: two halves as round 3's coarse lock) -/
  | wmSet | wmDrain | wmRel
  /-- Clojure ReentrantReadWriteLock of mm -/
  | rwR | rwRRel | rwW | rwWRel
  | dCheck (d : Nat)
  | dSet
  | lCheck (d : Nat)
  | lSet
  | lKey
  | fWait
  | fDone
  deriving BEq, Hashable, Repr, Inhabited

structure Mem where
  mode : Mode
  bodies : Array (List Op)
  wm : Folly.CSM := {}
  rl : Array (Option (Nat × Nat))
  rwReaders : List Nat := []
  rwWriter : Option (Nat × Nat) := none
  dCompiled : Bool := false
  lRealized : Bool := false
  lIsKey : Bool := false
  fDone : Bool := false
  deriving BEq, Hashable, Repr, Inhabited

structure Loc where
  instrs : List I
  deriving BEq, Hashable, Repr, Inhabited

abbrev PM := ProcessM Mem Loc

def mem : PM Mem := do pure (← get).memory
def setMem (m : Mem) : PM Unit := modify fun p => { p with memory := m }

def body (me : Mem) (s : Slot) (d : Nat) : List I :=
  if d == 0 then [] else (me.bodies[s.idx]!).map fun o => I.op o (d - 1)

def realizeL (d : Nat) : List I := [.rAcq rL, .lCheck d, .rRel rL]

def expandJ (o : Op) (d : Nat) : List I :=
  match o with
  | .alterF => [.wmSet, .wmDrain, .call .alterFn d, .wmRel]
  | .defF => [.wmSet, .wmDrain, .wmRel]
  | .callF => [.rAcq rComp, .dCheck d, .rRel rComp, .call .fBody d]
  | .derefF => [.fWait]
  | .realizeL => realizeL d
  -- add_method: lock; assoc hashes L (realizes it); reset_cache (re-entrant); unlock
  | .mmDefL => [.rAcq rMM] ++ realizeL d ++ [.lKey, .rAcq rMM, .rRel rMM, .rRel rMM]
  -- get_method: reset_cache always (the var vs its map); :a is in the table
  | .mmCallA => [.rAcq rMM, .rRel rMM]
  -- (mm L): the dispatch value hashed by method_cache->get (unlocked), reset_cache, then
  -- find_and_cache_best_method unless L is a key
  | .mmCallL => realizeL d ++ [.rAcq rMM, .rRel rMM, .rAcq rMM, .rRel rMM]
  | .cppRaw => [.rAcq rJit, .call .rawBody d, .rRel rJit]
  | .evalFn => [.rAcq rJit, .rRel rJit]

def expandC (o : Op) (d : Nat) : List I :=
  match o with
  | .alterF => [.rAcq rVar, .call .alterFn d, .rRel rVar]
  | .defF => [.rAcq rVar, .rRel rVar]
  | .callF => [.call .fBody d]
  | .derefF => [.fWait]
  | .realizeL => realizeL d
  | .mmDefL => [.rwW] ++ realizeL d ++ [.lKey, .rwWRel]
  -- the cache holds the method table's keys: no lock
  | .mmCallA => []
  | .mmCallL => realizeL d ++ [.rwR, .rwRRel, .rwW, .rwWRel]
  -- no counterpart: the initializer's body, no lock
  | .cppRaw => [.call .rawBody d]
  | .evalFn => []

def step (t : Nat) (l : Loc) : PM (StepResult Loc) := do
  match l.instrs with
  | [] => pure .done
  | i :: rest =>
    let me ← mem
    let next : PM (StepResult Loc) := pure (.ran { instrs := rest })
    let push (is : List I) : PM (StepResult Loc) := pure (.ran { instrs := is ++ rest })
    match i with
    | .op o d =>
      Process.note s!"thread {t}: {o.clj}"
      push (if me.mode == .jank then expandJ o d else expandC o d)
    | .call s d => push (body me s d)
    | .rAcq x =>
      match me.rl[x]! with
      | none => setMem { me with rl := me.rl.set! x (some (t, 1)) }; Process.note s!"thread {t}: {rName x} lock"; next
      | some (o, n) => if o == t then setMem { me with rl := me.rl.set! x (some (t, n + 1)) }; next else pure .blocked
    | .rRel x =>
      match me.rl[x]! with
      | some (o, n) => setMem { me with rl := me.rl.set! x (if n ≤ 1 then none else some (o, n - 1)) }; next
      | none => next
    | .wmSet =>
      match me.wm.lockSet t with
      | some c => setMem { me with wm := c }; Process.note s!"thread {t}: f's write_mutex sets kHasE"; next
      | none => pure .blocked
    | .wmDrain =>
      match me.wm.lockDrain t with
      | some c => setMem { me with wm := c }; next
      | none => pure .blocked
    | .wmRel => setMem { me with wm := me.wm.unlock }; next
    | .rwR =>
      match me.rwWriter with
      | some (w, _) => if w == t then setMem { me with rwReaders := t :: me.rwReaders }; next else pure .blocked
      | none => setMem { me with rwReaders := t :: me.rwReaders }; next
    | .rwRRel => setMem { me with rwReaders := me.rwReaders.erase t }; next
    | .rwW =>
      match me.rwWriter with
      | some (w, n) => if w == t then setMem { me with rwWriter := some (t, n + 1) }; next else pure .blocked
      | none =>
        if me.rwReaders.isEmpty then
          setMem { me with rwWriter := some (t, 1) }; Process.note s!"thread {t}: mm write lock"; next
        else pure .blocked
    | .rwWRel =>
      match me.rwWriter with
      | some (w, n) => setMem { me with rwWriter := if n ≤ 1 then none else some (w, n - 1) }; next
      | none => next
    | .dCheck _ =>
      -- realize: compile under the JIT lock, then var->bind_root (the write_mutex)
      if me.dCompiled then next
      else push [.rAcq rJit, .rRel rJit, .dSet, .wmSet, .wmDrain, .wmRel]
    | .dSet => setMem { me with dCompiled := true }; next
    | .lCheck d => if me.lRealized then next else push (body me .lBody d ++ [.lSet])
    | .lSet => setMem { me with lRealized := true }; next
    | .lKey => setMem { me with lIsKey := true }; next
    | .fWait => if me.fDone then next else pure .blocked
    | .fDone => setMem { me with fDone := true }; next

def prog : Program Mem Loc := { step := step }

structure Prog where
  threads : List (List Op)
  bodies : Array (List Op)
  usesFuture : Bool
  depth : Nat
  deriving Repr, Inhabited

def start (pg : Prog) (mode : Mode) : Process Mem Loc :=
  let tops : List (Option Loc) := pg.threads.map fun ops => some { instrs := ops.map fun o => I.op o pg.depth }
  let fut : List (Option Loc) := if pg.usesFuture then [some { instrs := [.call .futBody pg.depth, .fDone] }] else []
  { memory := { mode, bodies := pg.bodies, rl := Array.replicate numR none, fDone := !pg.usesFuture },
    threads := (tops ++ fut).toArray }

def waitsFor (p : Process Mem Loc) (t : Nat) : String :=
  match p.threads[t]! with
  | none => "done"
  | some l => match l.instrs.head? with
    | some (.rAcq x) => rName x
    | some .wmSet => "f's write_mutex (kHasE)"
    | some .wmDrain => "f's write_mutex (readers)"
    | some .rwR => "mm read lock"
    | some .rwW => "mm write lock"
    | some .fWait => "the future F"
    | some i => reprStr i
    | none => "?"

def holds (p : Process Mem Loc) (t : Nat) : List String :=
  let me := p.memory
  let rs := (List.range numR).filterMap fun x => match me.rl[x]! with
    | some (o, _) => if o == t then some (rName x) else none
    | none => none
  let wm := if me.wm.e == some t || me.wm.pend == some t then ["f's write_mutex"] else []
  let rw := (if me.rwReaders.contains t then ["mm read lock"] else []) ++
            (match me.rwWriter with | some (w, _) => if w == t then ["mm write lock"] else [] | none => [])
  rs ++ wm ++ rw

def deadlockClass (p : Process Mem Loc) : String :=
  let ths := (List.range p.threads.size).filterMap fun t =>
    (p.threads[t]!).map fun _ => s!"waits {waitsFor p t} holding [{String.intercalate ", " (holds p t)}]"
  String.intercalate " | " ((ths.mergeSort (· ≤ ·)).eraseDups)

/-! ## Generator -/

structure Gen where
  bodies : Array (Option (List Op)) := Array.replicate 5 none
  decisions : Decisions := {}
  deriving Inhabited

instance : Chaotic Gen where
  decisions g := g.decisions
  setDecisions g d := { g with decisions := d }

abbrev GM := EStateM Stop Gen

def slotsOf : Op → List Slot
  | .alterF => [.alterFn] | .callF => [.fBody] | .derefF => [.futBody]
  | .realizeL | .mmDefL | .mmCallL => [.lBody] | .cppRaw => [.rawBody] | _ => []

partial def chooseSlots (len depth : Nat) (o : Op) : GM Unit := do
  for s in slotsOf o do
    if ((← get).bodies[s.idx]!).isNone then
      let n ← decide (σ := Gen) s!"prog.{s.name}.len" (len + 1)
      let mut ops : List Op := []
      for _ in [0:n] do
        let k ← decide (σ := Gen) s!"prog.{s.name}.op" alphabet.length
        ops := ops ++ [alphabet.getD k .evalFn]
      modify fun g => { g with bodies := g.bodies.set! s.idx (some ops) }
      if depth > 0 then
        for o' in ops do chooseSlots len (depth - 1) o'

def genProgram (threads ops len depth : Nat) : GM Prog := do
  let nt ← decide (σ := Gen) "prog.threads" threads
  let mut ths : List (List Op) := []
  for _ in [0:nt + 1] do
    let no ← decide (σ := Gen) "prog.ops" ops
    let mut th : List Op := []
    for _ in [0:no + 1] do
      let k ← decide (σ := Gen) "prog.op" alphabet.length
      let o := alphabet.getD k .evalFn
      th := th ++ [o]
      chooseSlots len depth o
    ths := ths ++ [th]
  let g ← get
  let b (s : Slot) := (g.bodies[s.idx]!).getD []
  let all := ths.flatten ++ (g.bodies.toList.filterMap id).flatten
  return { threads := ths, bodies := #[b .alterFn, b .fBody, b .lBody, b .futBody, b .rawBody],
           usesFuture := all.contains .derefF, depth := depth + 1 }

def Prog.describe (pg : Prog) : String :=
  let slots : List Slot := [.alterFn, .fBody, .lBody, .futBody, .rawBody]
  let bs := slots.filterMap fun s =>
    let b := pg.bodies[s.idx]!
    if b.isEmpty then none else some s!"{s.name} = {String.intercalate " " (b.map (·.clj))}"
  let ths := (List.range pg.threads.length).map fun i =>
    s!"thread {i}: {String.intercalate " " ((pg.threads.getD i []).map (·.clj))}"
  String.intercalate "; " (bs ++ ths)

def usesRaw (pg : Prog) : Bool :=
  (pg.threads.flatten ++ pg.bodies.toList.flatten).contains .cppRaw

def judge (pg : Prog) (maxStates : Nat) : Option (String × String) :=
  let j := stateSearch prog (start pg .jank) (onDeadlock := fun p => some (deadlockClass p)) (maxStates := maxStates)
  match j.violation with
  | some (_, "deadlock", cls) =>
    let c := stateSearch prog (start pg .clojure) (onDeadlock := fun p => some (deadlockClass p)) (maxStates := maxStates)
    match c.violation with
    | some (_, "deadlock", _) => none
    | _ =>
      let tag := if usesRaw pg then "(cpp/raw, no Clojure counterpart) " else ""
      if c.complete then some (tag ++ cls, pg.describe) else some ("(Clojure search stopped) " ++ cls, pg.describe)
  | some _ => none
  | none => if j.complete then none else some ("(search stopped)", pg.describe)

def runGen (threads ops len depth maxStates : Nat) (aside : List String) (source : Source) : Ended :=
  let g : Gen := { decisions := { source, limit := 100000 } }
  match (genProgram threads ops len depth).run g with
  | .ok pg g' =>
    match judge pg maxStates with
    | some (cls, d) =>
      if aside.any (fun e => (cls.splitOn e).length > 1) then { taken := g'.decisions.taken, violation := none }
      else { taken := g'.decisions.taken, violation := some (cls, d) }
    | none => { taken := g'.decisions.taken, violation := none }
  | .error _ g' => { taken := g'.decisions.taken, violation := none }

end Jank.R4.Runtime.Mutexes
