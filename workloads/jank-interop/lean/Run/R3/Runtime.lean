import Jank.R3.Runtime.Common
import Jank.R3.Runtime.Folly
import Jank.R3.Runtime.Locks
import Jank.R3.Runtime.Gc
import Jank.R3.Runtime.Containers

/-! Round 3 driver: Runtime (folly SharedMutex/Synchronized/fbvector, bdwgc as jank uses them).
`jank3-runtime <search>`; each search prints its world, bounds, states/timelines and result. -/

open Determinismo Jank.R3.Runtime

namespace Run.R3.Runtime

def say (s : String) : IO Unit := IO.println s

/-! ## folly::SharedMutex: the replica against the coarse lock -/

def foldDeadlock (threads : List (List Folly.Act)) (coarse : Bool) (maxSlots : Nat) (maxStates : Nat) (useLib : Bool := false) : SearchResult :=
  let p := Folly.start threads 2 maxSlots coarse useLib
  stateSearch (Folly.prog coarse useLib) p (invariant := Folly.invariant)
    (onDeadlock := fun p => some (Folly.stuckDetail p)) (maxStates := maxStates)

/-- Every 2-thread program of `shapes` (and 3-thread single acquisitions): does the fine replica
deadlock exactly when the coarse lock does, and do its acquisitions refine the coarse lock? -/
def refinement (maxSlots : Nat) (maxStates : Nat := 400000) : IO Unit := do
  let singles := Folly.kinds.map fun k => Folly.bracket k none
  let progs2 := Folly.shapes.flatMap fun a => Folly.shapes.map fun b => [a, b]
  let progs3 := singles.flatMap fun a => singles.flatMap fun b => singles.map fun c => [a, b, c]
  let progs := progs2 ++ progs3
  let mut mismatch := 0
  let mut fineDead := 0
  let mut coarseDead := 0
  let mut other := 0
  let mut incomplete := 0
  let mut maxSt := 0
  let mut total := 0
  let mut firstMismatch : Option String := none
  for pr in progs do
    let f := foldDeadlock pr false maxSlots maxStates
    let c := foldDeadlock pr true maxSlots maxStates
    total := total + f.states
    maxSt := max maxSt f.states
    if !f.complete then incomplete := incomplete + 1
    let fd := match f.violation with | some (_, "deadlock", _) => true | _ => false
    let cd := match c.violation with | some (_, "deadlock", _) => true | _ => false
    if fd then fineDead := fineDead + 1
    if cd then coarseDead := coarseDead + 1
    match f.violation with
    | some (moves, prop, d) =>
      if prop != "deadlock" then
        other := other + 1
        if firstMismatch.isNone then
          firstMismatch := some s!"{prop} in {reprStr pr}: {d}\n{pathTape moves}"
    | none => pure ()
    if fd != cd then
      mismatch := mismatch + 1
      if firstMismatch.isNone then
        firstMismatch := some s!"fine deadlock {fd}, coarse {cd} for {reprStr pr}"
  say s!"SharedMutex refinement, getMaxDeferredReaders = {maxSlots}: {progs.length} programs ({progs2.length} two-thread over {Folly.shapes.length} shapes, {progs3.length} three-thread), {total} fine states in all (largest {maxSt}), incomplete {incomplete}"
  say s!"  fine deadlocks {fineDead}, coarse deadlocks {coarseDead}, mismatches {mismatch}, other violations {other}"
  if let some m := firstMismatch then say s!"  first: {m}"
  -- round 1's lock (= Determinismo.RwLock with writer priority) on the S/E programs
  let noU (pr : List (List Folly.Act)) := pr.all fun th => th.all fun a => match a with
    | .lockU _ | .unlockU _ | .upgrade _ => false | _ => true
  let se := progs.filter noU
  let mut libMis := 0
  let mut libFirst : Option String := none
  for pr in se do
    let f := foldDeadlock pr false maxSlots maxStates
    let l := foldDeadlock pr true maxSlots maxStates (useLib := true)
    let fd := match f.violation with | some (_, "deadlock", _) => true | _ => false
    let ld := match l.violation with | some (_, "deadlock", _) => true | _ => false
    if fd != ld then
      libMis := libMis + 1
      if libFirst.isNone then libFirst := some s!"folly deadlock {fd}, round-1/library lock {ld}: {reprStr pr}"
  say s!"  round 1's SharedMutex (Determinismo.RwLock, writer priority) on the {se.length} programs without upgrade: {libMis} disagree with the replica"
  if let some m := libFirst then say s!"  first: {m}"

/-! ## jank's lock graph -/

section
open Locks

def mkProg (threads : List (List JOp)) (bodies : List (Slot × List JOp)) (validator watch pending : Bool := false) (depth : Nat := 3) : Program' :=
  let b (s : Slot) := ((bodies.find? (·.1 == s)).map (·.2)).getD []
  let all := threads.flatten ++ (bodies.map (·.2)).flatten
  { threads, bodies := #[b .validator, b .watch, b .alterFn, b .metaSrc, b .delayBody, b .futureBody, b .moduleBody],
    hasValidator := validator, hasWatch := watch, metaPending := pending,
    usesFuture := all.any usesFutureOp, depth }

/-- One program, both modes, coarse and fine locks: deadlock reachability, states, shortest path,
tape and story of the jank deadlock. -/
def scenario (name : String) (pg : Program') : IO Unit := do
  say s!"* {name}"
  say s!"  program: {pg.describe}"
  for fine in [false, true] do
    let j := stateSearch prog (start pg .jank fine) (onDeadlock := fun p => some (stuck p)) (maxStates := 500000)
    let c := stateSearch prog (start pg .clojure false) (onDeadlock := fun p => some (stuck p)) (maxStates := 500000)
    let lock := if fine then "fine SharedMutex replica" else "coarse SharedMutex"
    let cres := match c.violation with
      | some (_, "deadlock", _) => "deadlocks"
      | some (_, prop, d) => s!"{prop}: {d}"
      | none => if c.complete then "always completes" else "stopped"
    say s!"  Clojure: {cres} ({c.states} states)"
    match j.violation with
    | some (moves, "deadlock", d) =>
      say s!"  jank ({lock}): DEADLOCK after {moves.length} steps, {j.states} states searched"
      say s!"    {d}"
      if !fine then
        say s!"    tape:\n{pathTape moves}"
        let story := pathStory prog (start pg .jank fine) moves
        say s!"    story:"
        for line in story do say s!"      {line}"
    | some (_, prop, d) => say s!"  jank ({lock}): {prop}: {d}"
    | none => say s!"  jank ({lock}): {if j.complete then "always completes" else "stopped"} ({j.states} states)"

def scenarios : IO Unit := do
  scenario "a validator that calls set-validator! on its atom"
    (mkProg [[.swap]] [(.validator, [.setValidator])] (validator := true))
  scenario "a validator that calls get-validator, while another thread calls set-validator!"
    (mkProg [[.swap], [.setValidator]] [(.validator, [.getValidator])] (validator := true))
  scenario "a validator that swap!s its atom, while another thread calls set-validator!"
    (mkProg [[.swap], [.setValidator]] [(.validator, [.swap])] (validator := true) (depth := 2))
  scenario "a watch calls set-validator! while a validator calls add-watch (two threads, lock order)"
    (mkProg [[.swap], [.swap]] [(.validator, [.addWatch]), (.watch, [.setValidator])] (validator := true) (watch := true) (depth := 2))
  scenario "the future cancels itself while another thread derefs it"
    (mkProg [[.derefFuture]] [(.futureBody, [.cancelFuture])])
  scenario "a delay's body derefs a future that asks (realized? d)"
    (mkProg [[.derefDelay]] [(.delayBody, [.derefFuture]), (.futureBody, [.realizedDelay])])
  scenario "(meta #'v) whose lazy meta source derefs a future that calls reset-meta! on v"
    (mkProg [[.metaRead]] [(.metaSrc, [.derefFuture]), (.futureBody, [.resetMeta])] (pending := true))
  scenario "a watch that removes itself (round 1 D16)"
    (mkProg [[.swap]] [(.watch, [.removeWatch])] (watch := true))
  scenario "a watch that swap!s, beside an add-watch (round 1 D16)"
    (mkProg [[.swap], [.addWatch]] [(.watch, [.swap])] (watch := true))
  scenario "alter-var-root whose fn defs the same var"
    (mkProg [[.alterVarRoot]] [(.alterFn, [.defVar])])
  scenario "alter-var-root whose fn calls alter-var-root on the same var"
    (mkProg [[.alterVarRoot]] [(.alterFn, [.alterVarRoot])])
  scenario "a delay whose body asks (realized? d)"
    (mkProg [[.derefDelay]] [(.delayBody, [.realizedDelay])])
  scenario "a delay whose body derefs itself"
    (mkProg [[.derefDelay]] [(.delayBody, [.derefDelay])])
  scenario "future-cancel while another thread derefs the future"
    (mkProg [[.derefFuture], [.cancelFuture]] [])
  scenario "future-cancelled? while another thread derefs the future"
    (mkProg [[.derefFuture], [.cancelledFuture]] [])
  scenario "two threads deref the same future"
    (mkProg [[.derefFuture], [.derefFuture]] [])
  scenario "(meta #'v) whose lazy meta source reads (meta #'v)"
    (mkProg [[.metaRead]] [(.metaSrc, [.metaRead])] (pending := true))
  scenario "a module with a managed load fn (AOT) whose top level derefs a future that requires another module"
    (mkProg [[.requireMod]] [(.moduleBody, [.derefFuture]), (.futureBody, [.requireOther])])

/-- The census over generated programs: every jank deadlock that Clojure does not have, per class
(IO, with progress lines). -/
def lockCensus (threads ops len depth maxRuns : Nat) (exclude : List String := []) (pfx : Array Nat := #[]) (alpha : List JOp := alphabet) : IO Unit := do
  say s!"lock census: ≤{threads} threads × ≤{ops} ops, callback bodies ≤{len} ops chosen to depth {depth}, alphabet {alpha.length} ops; excluded classes {exclude}; partition (decision prefix) {pfx}"
  let run := runGen alpha threads ops len depth 20000 exclude
  let mut path : Array Nat := pfx
  let mut classes : Array (String × Nat × String × Nat) := #[]
  let mut runs := 0
  let mut complete := false
  let out ← IO.getStdout
  for i in [0:maxRuns] do
    let o := run (Source.path path)
    runs := i + 1
    if let some (cls, d) := o.violation then
      -- the smallest program of each class (fewest operations named)
      let size := (d.splitOn "(").length + (d.splitOn "@").length
      match classes.findIdx? (·.1 == cls) with
      | some k => classes := classes.modify k fun (c, n, dd, sz) => if size < sz then (c, n + 1, d, size) else (c, n + 1, dd, sz)
      | none =>
        classes := classes.push (cls, 1, d, size)
        say s!"  [{i + 1}] new class: {cls}"
    if (i + 1) % 20000 == 0 then
      say s!"  ... {i + 1} programs, {classes.size} classes"
      out.flush
    -- stay inside the partition: the next path must keep the prefix
    match nextPath o.taken with
    | none => complete := true; break
    | some p =>
      if p.size < pfx.size || p.extract 0 pfx.size != pfx then complete := true; break
      path := p
  say s!"  {if complete then "complete" else "stopped"} after {runs} programs; {classes.size} classes of jank deadlocks that Clojure does not have"
  for (cls, n, d, _) in classes do
    say s!"  - {n}× {cls}\n      smallest: {d}"

end

/-! ## bdwgc -/

def gcSearch (name : String) (body : Gc.GM Unit) (jvmRoots : List String) (maxRuns : Nat := 100000)
    (cljBody : Option (Gc.GM Unit) := none) (counterfactual : Bool := false) : IO Unit := do
  let runJ := fun src => (Gc.run body false jvmRoots src).1
  let runC := fun src => (Gc.run (cljBody.getD body) true jvmRoots src).1
  let ej := exhaust runJ maxRuns
  let ec := exhaust runC maxRuns
  let showE (e : Exhausted) : String := match e with
    | .found c => s!"found after {c.runs}: {c.detail}"
    | .complete n => s!"complete, {n} timelines, nothing"
    | .stopped n => s!"stopped at {n}"
  say s!"* {name}"
  say s!"  jank: {showE ej}"
  if !counterfactual then say s!"  Clojure (the JVM's roots{if jvmRoots.isEmpty then "" else s!", also {jvmRoots}"}): {showE ec}"
  if let .found c := ej then
    let c' := shrink runJ c
    say s!"  shrunk tape:\n{tape c'.taken}"
    say "  story:"
    for line in (Gc.run body false jvmRoots (Source.path c'.values)).2 do say s!"    {line}"

def gc : IO Unit := do
  say s!"persistent_string typed descriptor: bitmap {Gc.psBitmap} → GC_make_descriptor = {Gc.psDescriptor} (0x{String.ofList (Nat.toDigits 16 Gc.psDescriptor.toNat)}); scanned words {Gc.scannedWords Gc.psDescriptor Gc.psWords}; store.large.data is word {Gc.psDataWord}"
  for (fa, ot) in [(1, 0), (2, 0), (3, 0), (0, 1), (0, 2)] do
    gcSearch s!"a fresh ex-info thrown through a finally ({fa} allocations in the finally, {ot} by another thread during the unwind)"
      (Gc.exceptionInFlight fa ot) ["C++ exception object (malloc)"]
  gcSearch "control: the thrown value is also held by a var" (Gc.exceptionFromVar 3) ["C++ exception object (malloc)"]
  gcSearch "(def x) (def u @#'x) (ns-unmap *ns* 'x), 2 allocations, (str u)" (Gc.unboundRoot 2 true) []
    (cljBody := some (Gc.unboundRoot 2 true .normal))
  gcSearch "control: the same without ns-unmap" (Gc.unboundRoot 2 false) [] (cljBody := some (Gc.unboundRoot 2 false .normal))
  for (size, off, shared) in [(0, 0, false), (23, 0, false), (24, 0, false), (100, 0, false), (100, 37, true), (600, 513, true)] do
    gcSearch s!"persistent_string of {size} bytes{if shared then s!", sharing at offset {off}" else ""}, jank's descriptor"
      (Gc.persistentString size off shared Gc.psDescriptor 2) []
  gcSearch "counterfactual: persistent_string with descriptor 0 (allocated before jank_init_base; jank never does)"
    (Gc.persistentString 100 0 false 0 2) [] (counterfactual := true)
  gcSearch "future thread registered (Linux path, core.cpp 1111-1115)" (Gc.futureStack true 2) []
  gcSearch "counterfactual: an unregistered thread running jank code" (Gc.futureStack false 2) [] (counterfactual := true)
  gcSearch "module lifted constants laid out in declaration order" (Gc.liftedRoots [0, 1, 2] 2) []
  gcSearch "counterfactual: lifted constants laid out in reverse order" (Gc.liftedRoots [2, 1, 0] 2) [] (counterfactual := true)

/-! ## fbvector and immutable_string -/

def containers (vlen slen : Nat) (maxRuns : Nat) : IO Unit := do
  let showE (e : Exhausted) : String := match e with
    | .found c => s!"found after {c.runs}: {c.property}: {c.detail}"
    | .complete n => s!"complete, {n} timelines, nothing"
    | .stopped n => s!"stopped at {n}"
  let cv := census (Containers.runVec vlen) maxRuns
  say s!"fbvector<object_ref, gc_allocator> against std::vector, every sequence of {vlen} operations: {if cv.complete then "complete" else "stopped"} after {cv.runs}"
  for (cls, n, tk, d) in cv.classes do
    say s!"  - {n}× {cls}: first {d}\n    tape {tk.size} decisions"
  let cv2 := census (Containers.runVec vlen (emplaceAlias := false)) maxRuns
  say s!"  residual (emplace's argument never an element): {if cv2.complete then "complete" else "stopped"} after {cv2.runs}, {cv2.classes.length} classes"
  for (cls, n, _, d) in cv2.classes do
    say s!"  - {n}× {cls}: first {d}"
  let cs := census (Containers.runStr slen) maxRuns
  say s!"immutable_string ownership, every sequence of {slen} operations on 2 strings: {if cs.complete then "complete" else "stopped"} after {cs.runs}"
  for (cls, n, _, d) in cs.classes do
    say s!"  - {n}× {cls}: first {d}"
  let cs2 := census (Containers.runStr slen (selfCStr := false)) maxRuns
  say s!"  residual (no `s = s.c_str()`): {if cs2.complete then "complete" else "stopped"} after {cs2.runs}, {cs2.classes.length} classes"
  for (cls, n, _, d) in cs2.classes do
    say s!"  - {n}× {cls}: first {d}"
  let _ := showE

/-- The deadlock mechanisms found (class components); the residual census sets them aside. -/
def baseMechanisms : List String :=
  ["atom watches exclusive (readers to drain) ⟂ atom watches shared",
   "atom watches shared ⟂ atom watches kHasE",
   "atom validator exclusive (readers to drain) ⟂ atom validator shared",
   "atom validator shared ⟂ atom validator kHasE",
   "var write_mutex exclusive (kHasE) ⟂ var write_mutex exclusive",
   "var lazy_meta exclusive (kHasE) ⟂ var lazy_meta exclusive",
   "delay std::mutex ⟂ delay std::mutex held",
   "future thread exclusive (kHasE) ⟂ future thread exclusive",
   "future state",
   "loader recursive_mutex ⟂ loader recursive_mutex held"]

def main (args : List String) : IO UInt32 := do
  match args with
  | ["residual"] =>
    say "residual lock census: the one-thread census with every found mechanism set aside"
    lockCensus 1 1 1 1 10000000 (exclude := baseMechanisms)
  | ["all"] =>
    say "jank3-runtime: round 3, Runtime (folly SharedMutex/Synchronized/fbvector, bdwgc), jank 7135b7708"
    say "\n## 1. folly::SharedMutex replica against the coarse lock and round 1's lock (state search, every reachable state)"
    refinement 2; refinement 4
    say "\n## 2. jank's locks: scenarios (state search, jank with the coarse lock and with the fine replica; Clojure)"
    scenarios
    say "\n## 3. bdwgc reachability (exhaust over gc.collect decisions; Clojure = the JVM's roots)"
    gc
    say "\n## 4. fbvector and immutable_string"
    containers 5 3 3000000
    say "\n## 5. lock census, one top-level thread (plus the future's thread)"
    lockCensus 1 1 1 1 10000000
  | ["gc"] => gc
  | ["containers", v, s, n] => containers v.toNat! s.toNat! n.toNat!
  | ["scenarios"] => scenarios
  | ["census", t, o, l, d, n] => lockCensus t.toNat! o.toNat! l.toNat! d.toNat! n.toNat!
  | "census2" :: t :: o :: l :: d :: n :: pfx =>
    lockCensus t.toNat! o.toNat! l.toNat! d.toNat! n.toNat! (pfx := (pfx.map String.toNat!).toArray) (alpha := Locks.alphabet2)
  | ["count2", t, o, l, d] =>
    let c := census (fun src =>
      let g : Locks.Gen := { decisions := { source := src, limit := 100000 } }
      match (Locks.genProgram Locks.alphabet2 t.toNat! o.toNat! l.toNat! d.toNat!).run g with
      | .ok _ g' => { taken := g'.decisions.taken, violation := none }
      | .error _ g' => { taken := g'.decisions.taken, violation := none }) 100000000
    say s!"programs: {c.runs} (complete {c.complete})"
  | "census" :: t :: o :: l :: d :: n :: pfx =>
    lockCensus t.toNat! o.toNat! l.toNat! d.toNat! n.toNat! (pfx := (pfx.map String.toNat!).toArray)
  | ["count", t, o, l, d] =>
    let c := census (fun src =>
      let g : Locks.Gen := { decisions := { source := src, limit := 100000 } }
      match (Locks.genProgram Locks.alphabet t.toNat! o.toNat! l.toNat! d.toNat!).run g with
      | .ok _ g' => { taken := g'.decisions.taken, violation := none }
      | .error _ g' => { taken := g'.decisions.taken, violation := none }) 100000000
    say s!"programs: {c.runs} (complete {c.complete})"
  | ["refine"] => refinement 2; refinement 4
  | ["refine", n] => refinement n.toNat!
  | _ => say "usage: jank3-runtime refine [slots]"
  return 0

end Run.R3.Runtime

def main (args : List String) : IO UInt32 := Run.R3.Runtime.main args
