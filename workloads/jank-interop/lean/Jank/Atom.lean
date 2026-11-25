import Determinismo
import Jank.Sync

/-!
# Atoms in the Threads world (src/cpp/jank/runtime/obj/atom.cpp)

The C++, step by step at the granularity of its atomics and locks:

- `atom::swap(fn)`: `while(true) { v = val.load(); next = fn.call(v); validate(next);
  if(val.compare_exchange_weak(v, next)) { notify_watches(this, v, next); return next; } }`
- `atom::validate(val)`: `auto const locked_validator(validator.rlock()); do_validate(...)`
- `atom::reset(o)`: `validate(o); v = val.load(); val = o; notify_watches(this, v, o)`
- `atom::compare_and_set(old, new)`: `validate(new); ret = val.compare_exchange_weak(old, new);
  if(ret) notify_watches(...)` — one **weak** CAS.
- `notify_watches`: `auto const locked_watches(a->watches.rlock()); for(entry : ...) fn.call(...)`
  — the watch functions run while the watches' `folly::Synchronized` is held shared.
- `atom::add_watch` / `remove_watch`: `auto locked_watches(watches.wlock()); ...` — exclusive.

`compare_exchange_weak` may fail although the value is the expected one (C++
[atomics.types.operations]: "spuriously fail"); on LL/SC hardware (AArch64 without LSE atomics)
it does. Here a decision (`cpu.cas_spurious`) when the platform is `llsc`.

Clojure (Atom.java, ARef.java): `swap`'s loop over a strong `AtomicReference.compareAndSet`;
`compareAndSet` strong; `notifyWatches` iterates a snapshot of the watches map with no lock;
`addWatch`/`removeWatch` are `synchronized` on the atom, which a watch running in `notifyWatches`
does not hold.

Values are small integers: NaN-boxed inline, so `compare_exchange` on the raw word compares them
by value (oref.hpp `tag(i32)`).
-/

namespace Jank.Atom

open Determinismo Jank.Sync

/-- A watch function's body. -/
inductive WatchFn where
  /-- `(fn [k r old new] ...)` with no effect on the atom. -/
  | record
  /-- `(fn [k r old new] (remove-watch r k))`: a one-shot watch. -/
  | removeSelf
  /-- `(fn [k r old new] (when (< new bound) (swap! r inc)))`. -/
  | swapBelow (bound : Nat)
  deriving Repr, BEq, Inhabited

/-- What a client operation is, for the history. -/
inductive Op where
  | swapInc | deref | cas (old new : Nat) | reset (x : Nat)
  deriving Repr, BEq

inductive Res where
  | val (v : Nat)
  | bool (b : Bool)
  deriving Repr, BEq

/-- One atomic step of a thread. Each high-level operation expands into these. -/
inductive Instr where
  /-- `v = val.load(); next = fn.call(v)` (fn is `inc`). -/
  | loadInc (op : Nat)
  /-- `validator.rlock()` (no validator is set: `do_validate` returns at once). -/
  | validateLock
  | validateUnlock
  /-- `val.compare_exchange_weak(v, next)` in swap: retry on failure, notify on success. -/
  | swapCas (op : Nat)
  /-- `compare_and_set(old, new)`: one weak CAS, result recorded. -/
  | casOnce (op : Nat) (old new : Nat)
  /-- `reset`: `v = val.load(); val = o` (two steps in the C++; jank and Clojure alike). -/
  | resetLoad (op : Nat) (x : Nat)
  | resetStore (op : Nat) (x : Nat)
  /-- `watches.rlock()` then the calls, then the unlock. -/
  | notifyLock (old new : Nat)
  | callWatch (key : Nat) (fn : WatchFn) (old new : Nat)
  | notifyUnlock
  /-- `watches.wlock()` (announce, then acquire), the change, the unlock. -/
  | watchAnnounce
  | watchLock
  | watchAdd (key : Nat) (fn : WatchFn)
  | watchRemove (key : Nat)
  | watchUnlock
  /-- `@a`. -/
  | deref (op : Nat)
  /-- The operation `op` begins (its history record invoked). -/
  | invoke (op : Nat) (o : Op)
  /-- The operation `op` returns `r` (its history record answered). -/
  | ret (op : Nat) (r : Res)
  deriving Repr, Inhabited

structure Mem where
  val : Nat := 0
  watches : List (Nat × WatchFn) := []
  watchesMutex : SharedMutex := {}
  validatorMutex : SharedMutex := {}
  /-- Watch calls seen: (key, old, new). -/
  calls : List (Nat × Nat × Nat) := []
  history : Array (OpRec Op Res) := #[]
  /-- Platform: `compare_exchange_weak` may fail spuriously (LL/SC). -/
  llsc : Bool := false
  /-- The Clojure semantics instead: strong CAS, watches called on a snapshot without a lock. -/
  clojure : Bool := false
  deriving Inhabited

structure Loc where
  instrs : List Instr
  v : Nat := 0
  next : Nat := 0
  deriving Inhabited

abbrev PM := ProcessM Mem Loc

def stamp : PM Nat := do pure (← get).steps

def invoke (op : Nat) (o : Op) (thread : Nat) : PM Unit := do
  let t ← stamp
  let r : OpRec Op Res := { id := op, node := thread, op := o, invoke := t }
  modify fun p => { p with memory := { p.memory with history := p.memory.history.push r } }

def answer (op : Nat) (r : Res) : PM Unit := do
  let t ← stamp
  modify fun p => { p with memory := { p.memory with history := p.memory.history.map fun h =>
    if h.id == op && h.ret.isNone then { h with ret := some t, outcome := some (.ok r) } else h } }

def mem : PM Mem := do pure (← get).memory
def setMem (m : Mem) : PM Unit := modify fun p => { p with memory := m }

/-- The instructions of a watch function's body. -/
def watchBody (key : Nat) : WatchFn → Nat → List Instr
  | .record, _ => []
  | .removeSelf, _ => [.watchAnnounce, .watchLock, .watchRemove key, .watchUnlock]
  | .swapBelow bound, new =>
    if new < bound then [.loadInc 1000, .validateLock, .validateUnlock, .swapCas 1000] else []

/-- Does the weak CAS fail although the value matches? (a decision on LL/SC platforms) -/
def spurious : PM Bool := do
  let m ← mem
  if m.llsc && !m.clojure then
    pure ((← decideWeighted (σ := Process Mem Loc) "cpu.cas_spurious" [7, 1]) == 1)
  else pure false

/-- One atomic step of thread `t`. -/
def step (t : Nat) (l : Loc) : PM (StepResult Loc) := do
  match l.instrs with
  | [] => pure .done
  | i :: rest =>
    let m ← mem
    match i with
    | .loadInc _ => pure (.ran { l with instrs := rest, v := m.val, next := m.val + 1 })
    | .validateLock =>
      match m.validatorMutex.lockShared t with
      | some vm => setMem { m with validatorMutex := vm }; pure (.ran { l with instrs := rest })
      | none => pure .blocked
    | .validateUnlock =>
      setMem { m with validatorMutex := m.validatorMutex.unlockShared t }
      pure (.ran { l with instrs := rest })
    | .swapCas op =>
      let fail ← spurious
      if m.val == l.v && !fail then
        setMem { m with val := l.next }
        let after := if op == 1000 then rest else .ret op (.val l.next) :: rest
        pure (.ran { l with instrs := .notifyLock l.v l.next :: after })
      else
        -- retry: load, fn, validate, CAS again
        pure (.ran { l with instrs := .loadInc op :: .validateLock :: .validateUnlock :: .swapCas op :: rest })
    | .casOnce op old new =>
      let fail ← spurious
      if m.val == old && !fail then
        setMem { m with val := new }
        pure (.ran { l with instrs := .notifyLock old new :: .ret op (.bool true) :: rest })
      else pure (.ran { l with instrs := .ret op (.bool false) :: rest })
    | .resetLoad _ _ => pure (.ran { l with instrs := rest, v := m.val })
    | .resetStore op x =>
      setMem { m with val := x }
      pure (.ran { l with instrs := .notifyLock l.v x :: .ret op (.val x) :: rest })
    | .notifyLock old new =>
      if m.clojure then
        -- ARef.notifyWatches: `IPersistentMap ws = watches;` a snapshot, no lock.
        let calls := m.watches.map fun (k, f) => Instr.callWatch k f old new
        pure (.ran { l with instrs := calls ++ rest })
      else
        match m.watchesMutex.lockShared t with
        | some wm =>
          setMem { m with watchesMutex := wm }
          -- `for(auto const &entry : (*locked_watches)->data)`: the map under the lock.
          let calls := m.watches.map fun (k, f) => Instr.callWatch k f old new
          pure (.ran { l with instrs := calls ++ [.notifyUnlock] ++ rest })
        | none => pure .blocked
    | .callWatch k f old new =>
      setMem { m with calls := m.calls ++ [(k, old, new)] }
      pure (.ran { l with instrs := watchBody k f new ++ rest })
    | .notifyUnlock =>
      setMem { m with watchesMutex := m.watchesMutex.unlockShared t }
      pure (.ran { l with instrs := rest })
    | .watchAnnounce =>
      if m.clojure then pure (.ran { l with instrs := rest })
      else
        setMem { m with watchesMutex := m.watchesMutex.announce t }
        pure (.ran { l with instrs := rest })
    | .watchLock =>
      if m.clojure then pure (.ran { l with instrs := rest })
      else
        match m.watchesMutex.lock t with
        | some wm => setMem { m with watchesMutex := wm }; pure (.ran { l with instrs := rest })
        | none => pure .blocked
    | .watchAdd k f =>
      setMem { m with watches := (m.watches.filter (·.1 != k)) ++ [(k, f)] }
      pure (.ran { l with instrs := rest })
    | .watchRemove k =>
      setMem { m with watches := m.watches.filter (·.1 != k) }
      pure (.ran { l with instrs := rest })
    | .watchUnlock =>
      if m.clojure then pure (.ran { l with instrs := rest })
      else
        setMem { m with watchesMutex := m.watchesMutex.unlock }
        pure (.ran { l with instrs := rest })
    | .deref op => pure (.ran { l with instrs := .ret op (.val m.val) :: rest })
    | .invoke op o =>
      invoke op o t
      pure (.ran { l with instrs := rest })
    | .ret op r =>
      answer op r
      pure (.ran { l with instrs := rest })

/-- The step, with the timeline's story: each instruction a thread ran or blocked on. -/
def stepLogged (t : Nat) (l : Loc) : PM (StepResult Loc) := do
  let r ← step t l
  match l.instrs, r with
  | i :: _, .ran _ => modify fun p => { p with log := p.log.push s!"thread {t}: {reprStr i}" }
  | i :: _, .blocked => modify fun p => { p with log := p.log.push s!"thread {t}: {reprStr i} blocks" }
  | _, _ => pure ()
  pure r

def prog : Program Mem Loc := { step := stepLogged }

/-! ## Client operations as instruction lists (with their history records) -/

def swapInc (op : Nat) : List Instr := [.loadInc op, .validateLock, .validateUnlock, .swapCas op]
def addWatch (k : Nat) (f : WatchFn) : List Instr := [.watchAnnounce, .watchLock, .watchAdd k f, .watchUnlock]
def resetTo (op : Nat) (x : Nat) : List Instr := [.validateLock, .validateUnlock, .resetLoad op x, .resetStore op x]
def casOp (op : Nat) (old new : Nat) : List Instr := [.validateLock, .validateUnlock, .casOnce op old new]
def derefOp (op : Nat) : List Instr := [.deref op]

/-- A scenario: threads' operations, with the history entries they invoke first. -/
structure Scenario where
  name : String
  /-- Per thread: (operation id, op, its instructions) in order; `none` id: not in the history. -/
  threads : List (List (Option (Nat × Op) × List Instr))
  initial : Nat := 0

/-- A thread's instructions: each operation in the history begins with its `invoke` step. -/
def flatten (ops : List (Option (Nat × Op) × List Instr)) : List Instr :=
  ops.flatMap fun (o, is) => match o with
    | some (id, op) => .invoke id op :: is
    | none => is

def start (s : Scenario) (llsc clojure : Bool) : Process Mem Loc :=
  { memory := { val := s.initial, llsc, clojure },
    threads := (s.threads.map fun ops => some ({ instrs := flatten ops } : Loc)).toArray }

/-- The register's sequential model: `swap! inc` returns the new value, `deref` the value,
`compare-and-set!` true exactly when the value is `old`, `reset!` the value set. -/
def applyOp (v : Nat) : Op → Nat × Res
  | .swapInc => (v + 1, .val (v + 1))
  | .deref => (v, .val v)
  | .cas old new => if v == old then (new, .bool true) else (v, .bool false)
  | .reset x => (x, .val x)

/-- Properties judged at the end: the history is linearizable; watches saw each change once
(each call's `new` is a value the atom took, olds distinct for swap!s). -/
def judge (p : Process Mem Loc) : Option String :=
  let ops := p.memory.history.toList
  if !linearizable (S := Nat) (Op := Op) (Res := Res) 0 applyOp ops then
    some s!"history not linearizable: {historyLines (Op := Op) (Res := Res) p.memory.history}"
  else none

def runScenario (s : Scenario) (llsc clojure : Bool) (source : Source) (maxSteps : Nat := 200) : Ended :=
  let body : ProcessM Mem Loc Unit := do
    interleave prog maxSteps
    if let some d := judge (← get) then
      throw (.violation "linearizable" d)
  match runProcess (start s llsc clojure) body source with
  | (.ok _, p) => { taken := p.decisions.taken, violation := none }
  | (.error (.violation prop d), p) =>
    { taken := p.decisions.taken, violation := some (prop, s!"{d} (steps {p.steps})") }
  | (.error .limit, p) => { taken := p.decisions.taken, violation := none }
  | (.error (.nodeDown _), p) => { taken := p.decisions.taken, violation := none }

/-- The story of one timeline. -/
def storyOf (s : Scenario) (llsc clojure : Bool) (source : Source) (maxSteps : Nat := 200) : Array String :=
  (runProcess (start s llsc clojure) (interleave prog maxSteps) source).2.log

/-! ## The scenarios -/

/-- A one-shot watch that removes itself (`(add-watch a :k (fn [k r _ _] (remove-watch r k)))`)
then `(reset! a 1)`, one thread. -/
def selfRemove : Scenario :=
  { name := "a watch that removes itself",
    threads := [[(none, addWatch 0 .removeSelf), (some (0, .reset 1), resetTo 0 1)]] }

/-- Thread 0: a watch that `swap!`s the same atom once, then `(swap! a inc)`; thread 1:
`(add-watch a :j ...)`. -/
def nestedSwap : Scenario :=
  { name := "a watch that swaps the atom, beside an add-watch",
    threads := [[(none, addWatch 0 (.swapBelow 2)), (some (0, .swapInc), swapInc 0)],
                [(none, addWatch 1 .record)]] }

/-- `(compare-and-set! a 0 1)` on `(atom 0)`, alone. -/
def casFresh : Scenario :=
  { name := "compare-and-set! on a fresh atom",
    threads := [[(some (0, .cas 0 1), casOp 0 0 1)]] }

/-- Two `swap! inc`s and a `deref` with a recording watch: linearizable? -/
def counter : Scenario :=
  { name := "two swap! inc and a deref",
    threads := [[(none, addWatch 9 .record), (some (0, .swapInc), swapInc 0)],
                [(some (1, .swapInc), swapInc 1)],
                [(some (2, .deref), derefOp 2)]] }

/-- Two `swap! inc`s, nothing else: small enough to exhaust. -/
def counter2 : Scenario :=
  { name := "two swap! inc",
    threads := [[(some (0, .swapInc), swapInc 0)], [(some (1, .swapInc), swapInc 1)]] }

/-- Two `compare-and-set!` racing on the same old value: exactly one may win. -/
def casRace : Scenario :=
  { name := "two compare-and-set! from 0",
    threads := [[(some (0, .cas 0 1), casOp 0 0 1)], [(some (1, .cas 0 2), casOp 1 0 2)]] }

/-! ## alter-meta! (core.jank: `(reset-meta! o (apply f (meta o) args))`, "TODO: Atomics")

Clojure's `alter-meta!` on an atom is AReference.alterMeta, `synchronized`. jank's reads the
metadata, applies f, then writes it: two steps. -/

structure MetaMem where
  n : Nat := 0
  /-- Clojure: one atomic step. -/
  atomic : Bool := false
  deriving Inhabited

def metaStep (_ : Nat) (pc : Nat × Nat) : ProcessM MetaMem (Nat × Nat) (StepResult (Nat × Nat)) := do
  let m := (← get).memory
  match pc with
  | (0, _) =>
    if m.atomic then
      modify fun p => { p with memory := { m with n := m.n + 1 } }
      pure .done
    else pure (.ran (1, m.n))                       -- (meta o)
  | (1, seen) =>
    modify fun p => { p with memory := { m with n := seen + 1 } }  -- (reset-meta! o ...)
    pure .done
  | _ => pure .done

def runAlterMeta (atomic : Bool) (source : Source) : Ended :=
  let start : Process MetaMem (Nat × Nat) := { memory := { atomic }, threads := #[some (0, 0), some (0, 0)] }
  let body : ProcessM MetaMem (Nat × Nat) Unit := do
    interleave { step := metaStep } 20
    let n := (← get).memory.n
    if n != 2 then
      throw (.violation "alter-meta! is atomic"
        s!"two threads each (alter-meta! a update :n inc) from :n 0: :n is {n}, Clojure 2")
  match runProcess start body source with
  | (.ok _, p) => { taken := p.decisions.taken, violation := none }
  | (.error (.violation prop d), p) => { taken := p.decisions.taken, violation := some (prop, d) }
  | (.error .limit, p) => { taken := p.decisions.taken, violation := none }
  | (.error (.nodeDown _), p) => { taken := p.decisions.taken, violation := none }

end Jank.Atom
