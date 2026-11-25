import Jank.R3.Runtime.Common
import Jank.R3.Runtime.Locks
import Jank.R4.Runtime.Census2
import Jank.R4.Runtime.Gc4
import Jank.R4.Runtime.Deferred
import Jank.R4.Runtime.Bindings4
import Jank.R4.Runtime.Mutexes
import Jank.R4.Runtime.Proofs4

/-! Round 4 driver: Runtime. `jank4-runtime <command>`; each command prints its world, bounds and
result. -/

open Determinismo Jank.R3.Runtime Jank.R4.Runtime

namespace Run.R4.Runtime

def say (s : String) : IO Unit := IO.println s

/-- Round 3's two-thread census partition `pfx`, every program round 3 left undecided escalated
through `budgets`. -/
def census2 (pfx : Array Nat) (budgets : List Nat) : IO Unit := do
  say s!"two-thread lock census (round 3's world: 2 threads × 1 op, alphabet2, bodies ≤1 op, depth 0), partition {pfx}, budgets {budgets}"
  let out ← IO.getStdout
  let (rows, runs, complete) ← Census2.walk 2 1 1 0 budgets pfx 10000000
    (progress := fun i n => do say s!"  [{i}] undecided at {budgets.headD 0}: {n} so far"; out.flush)
  say s!"  {if complete then "complete" else "stopped"} after {runs} programs; {rows.size} exceeded {budgets.headD 0} states"
  let mut decided := 0
  for r in rows do
    if r.decided then decided := decided + 1
    say s!"  - #{r.idx}: {r.verdict} (budget {r.budget}{if r.decided then ", decided" else ", still stopped"})\n      {r.program}"
  say s!"  decided {decided} of {rows.size}"

/-! ## bdwgc with conservative stacks (S69, S70 feedback) -/

def showE (e : Exhausted) : String := match e with
  | .found c => s!"found after {c.runs}: {c.detail}"
  | .complete n => s!"complete, {n} timelines, nothing"
  | .stopped n => s!"stopped at {n}"

def gcSearch4 (name : String) (body : Jank.R3.Runtime.Gc.GM Unit) (jvmRoots : List String)
    (cljBody : Option (Jank.R3.Runtime.Gc.GM Unit) := none) (maxRuns : Nat := 2000000) : IO Unit := do
  let runJ := fun src => (Jank.R3.Runtime.Gc.run body false jvmRoots src).1
  let runS := fun src => (Jank.R3.Runtime.Gc.run (Gc4.survives body) false jvmRoots src).1
  let runC := fun src => (Jank.R3.Runtime.Gc.run (cljBody.getD body) true jvmRoots src).1
  let ej := exhaust runJ maxRuns
  let es := exhaust runS maxRuns
  let ec := exhaust runC maxRuns
  say s!"* {name}"
  say s!"  jank, a freed read: {showE ej}"
  say s!"  jank, the value survives: {showE es}"
  say s!"  Clojure (the JVM's roots): {showE ec}"
  if let .found c := ej then
    let c' := shrink runJ c
    say s!"  shortest freed-read tape ({c'.taken.size} decisions):\n{tape c'.taken}"
    say "  story:"
    for line in (Jank.R3.Runtime.Gc.run body false jvmRoots (Source.path c'.values)).2 do say s!"    {line}"

def gc4 : IO Unit := do
  say "S69 (prompted): the thrown ex-info, a collection in the finally"
  for (shape, sname) in [(Gc4.Shape.sameFn, "throw in the fn that runs the finally (round 3's test)"), (Gc4.Shape.separateFn, "throw from a separate fn boom (round 3's report)")] do
    for opt in [0, 1] do
      for fa in [1, 2, 3] do
        gcSearch4 s!"{sname}, -O{opt}, {fa} allocation(s) in the finally" (Gc4.exceptionInFlight shape opt fa) ["C++ exception object (malloc)"]
  say "\nS70 (prompted): (def x) (def u @#'x) at load; in the test fn (ns-unmap *ns* 'x), allocations, (str u)"
  for n in [1, 2, 3] do
    gcSearch4 s!"{n} allocation(s) after ns-unmap" (Gc4.unboundRoot n true) [] (cljBody := some (Gc4.unboundRoot n true .normal))
  gcSearch4 "control: no ns-unmap, 2 allocations" (Gc4.unboundRoot 2 false) [] (cljBody := some (Gc4.unboundRoot 2 false .normal))
  say s!"\nprinted form of an unbound root: jank {Gc4.jankUnboundStr "7f062d022660" "#'user/x"}; Clojure {Gc4.cljUnboundStr "#'user/x"}"

/-! ## Lazily compiled fns -/

def deferredCensus (n : Nat) (mode : Deferred.Mode) (aside : List String) (maxRuns : Nat) : IO Unit := do
  let c := census (Deferred.runOne n mode aside) maxRuns
  say s!"deferred fns ({reprStr mode} vs Clojure), every program of 1..{n} forms over {Deferred.ops.length} forms, classes set aside {aside}: {if c.complete then "complete" else "stopped"} after {c.runs}"
  for (cls, k, _, d) in c.classes do
    say s!"  - {k}× {cls}\n      first: {d}"

def deferredAll (n : Nat) : IO Unit := do
  deferredCensus n .jankLazy [] 100000000
  deferredCensus n .jankLazy ["rebound the var", "with-meta", "hangs", "meta of a called"] 100000000
  deferredCensus n .jankEager [] 100000000
  deferredCensus n .jankEager ["meta of a called"] 100000000

/-! ## Thread bindings -/

def bindingsCensus (n : Nat) (aside : List String) : IO Unit := do
  let c := census (Bindings4.runOne n aside) 100000000
  say s!"thread bindings (main thread or a future's), every program of 1..{n} ops over {Bindings4.ops.length}, classes set aside {aside}: {if c.complete then "complete" else "stopped"} after {c.runs}"
  for (cls, k, _, d) in c.classes do
    say s!"  - {k}× {cls}\n      first: {d}"

/-! ## Recursive mutexes, lazy compilation's locks -/

def mutexCensus (threads ops len depth maxStates maxRuns : Nat) (aside : List String) : IO Unit := do
  say s!"mutex census: ≤{threads} threads × ≤{ops} ops, bodies ≤{len} ops to depth {depth}, alphabet {Mutexes.alphabet.length}, ≤{maxStates} states per search, classes set aside {aside}"
  let out ← IO.getStdout
  let run := Mutexes.runGen threads ops len depth maxStates aside
  let mut path : Array Nat := #[]
  let mut classes : Array (String × Nat × String × Nat) := #[]
  let mut runs := 0
  let mut complete := false
  for i in [0:maxRuns] do
    let o := run (Source.path path)
    runs := i + 1
    if let some (cls, d) := o.violation then
      let size := d.length
      match classes.findIdx? (·.1 == cls) with
      | some k => classes := classes.modify k fun (c, n, dd, sz) => if size < sz then (c, n + 1, d, size) else (c, n + 1, dd, sz)
      | none =>
        classes := classes.push (cls, 1, d, size)
        say s!"  [{i + 1}] new class: {cls}"; out.flush
    if (i + 1) % 20000 == 0 then say s!"  ... {i + 1} programs, {classes.size} classes"; out.flush
    match nextPath o.taken with
    | none => complete := true; break
    | some p => path := p
  say s!"  {if complete then "complete" else "stopped"} after {runs} programs; {classes.size} classes"
  for (cls, n, d, _) in classes do
    say s!"  - {n}× {cls}\n      smallest: {d}"

def mutexScenario (name : String) (pg : Mutexes.Prog) : IO Unit := do
  say s!"* {name}\n  program: {pg.describe}"
  let j := stateSearch Mutexes.prog (Mutexes.start pg .jank) (onDeadlock := fun p => some (Mutexes.deadlockClass p)) (maxStates := 500000)
  let c := stateSearch Mutexes.prog (Mutexes.start pg .clojure) (onDeadlock := fun p => some (Mutexes.deadlockClass p)) (maxStates := 500000)
  let showR (r : SearchResult) : String := match r.violation with
    | some (moves, "deadlock", d) => s!"DEADLOCK after {moves.length} steps ({r.states} states): {d}"
    | some (_, p, d) => s!"{p}: {d}"
    | none => s!"{if r.complete then "always completes" else "stopped"} ({r.states} states)"
  say s!"  jank: {showR j}"
  say s!"  Clojure: {showR c}"
  if let some (moves, "deadlock", _) := j.violation then
    say s!"  tape:\n{pathTape moves}"
    say "  story:"
    for line in pathStory Mutexes.prog (Mutexes.start pg .jank) moves do say s!"    {line}"

def mutexScenarios : IO Unit := do
  let mk (ths : List (List Mutexes.Op)) (bs : List (Mutexes.Slot × List Mutexes.Op)) (depth : Nat := 2) : Mutexes.Prog :=
    let b (s : Mutexes.Slot) := ((bs.find? (·.1 == s)).map (·.2)).getD []
    let all := ths.flatten ++ (bs.map (·.2)).flatten
    { threads := ths, bodies := #[b .alterFn, b .fBody, b .lBody, b .futBody, b .rawBody],
      usesFuture := all.contains .derefF, depth }
  mutexScenario "alter-var-root on a defn'd var whose fn calls the var's fn (never called before)"
    (mk [[.alterF]] [(.alterFn, [.callF])])
  mutexScenario "alter-var-root whose fn derefs a future that calls the var's fn for the first time"
    (mk [[.alterF]] [(.alterFn, [.derefF]), (.futBody, [.callF])])
  mutexScenario "defmethod with a lazy-seq dispatch value whose realization waits on a thread that calls the multimethod"
    (mk [[.mmDefL]] [(.lBody, [.derefF]), (.futBody, [.mmCallA])])
  mutexScenario "a multimethod call while another thread's defmethod realizes its lazy dispatch value"
    (mk [[.mmDefL], [.mmCallA]] [(.lBody, [.evalFn])])
  mutexScenario "a cpp/raw initializer that derefs a future that JIT-compiles (no Clojure counterpart)"
    (mk [[.cppRaw]] [(.rawBody, [.derefF]), (.futBody, [.evalFn])])
  mutexScenario "a deferred fn's first call while another thread's alter-var-root waits on it"
    (mk [[.alterF], [.callF]] [(.alterFn, [.derefF]), (.futBody, [.callF])])

/-! ## Round 3's one stopped fine-replica scenario, with a larger budget -/

def fineValidator (budget : Nat) : IO Unit := do
  let ths : List (List Locks.JOp) := [ [Locks.JOp.swap], [Locks.JOp.setValidator] ]
  let bs : Array (List Locks.JOp) := #[ [Locks.JOp.swap], [], [], [], [], [], [] ]
  let pg : Locks.Program' :=
    { threads := ths, bodies := bs, hasValidator := true, hasWatch := false, metaPending := false,
      usesFuture := false, depth := 2 }
  say s!"a validator that swap!s its atom, while another thread calls set-validator! (round 3: fine replica stopped at 500,001 states); budget {budget}"
  say s!"  program: {pg.describe}"
  let j := stateSearch Locks.prog (Locks.start pg .jank true) (onDeadlock := fun p => some (Locks.stuck p)) (maxStates := budget)
  match j.violation with
  | some (moves, "deadlock", d) => say s!"  jank (fine SharedMutex replica): DEADLOCK after {moves.length} steps, {j.states} states\n    {d}"
  | some (_, p, d) => say s!"  jank (fine): {p}: {d}"
  | none => say s!"  jank (fine): {if j.complete then "always completes" else "stopped"} ({j.states} states)"
  let c := stateSearch Locks.prog (Locks.start pg .clojure false) (onDeadlock := fun p => some (Locks.stuck p)) (maxStates := budget)
  say s!"  Clojure: {match c.violation with | some _ => "deadlocks" | none => if c.complete then "always completes" else "stopped"} ({c.states} states)"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["fine-validator", b] => fineValidator b.toNat!
  | ["all-quick"] => gc4; deferredAll 4; bindingsCensus 4 []
  | ["bindings", n] =>
    bindingsCensus n.toNat! []
    bindingsCensus n.toNat! ["push-thread-bindings rejects an array map", "pop-thread-bindings without a matching push", "get-thread-bindings holds var_thread_binding boxes, not values"]
  | ["mutex-scenarios"] => mutexScenarios
  | ["mutexes", t, o, l, d, ms] => mutexCensus t.toNat! o.toNat! l.toNat! d.toNat! ms.toNat! 100000000 []
  | "mutexes-aside" :: t :: o :: l :: d :: ms :: aside => mutexCensus t.toNat! o.toNat! l.toNat! d.toNat! ms.toNat! 100000000 aside
  | ["gc"] => gc4
  | ["deferred", n] => deferredAll n.toNat!
  | "census2" :: rest =>
    -- census2 <budget,budget,...> <prefix...>
    match rest with
    | bs :: pfx =>
      let budgets := (bs.splitOn ",").map String.toNat!
      census2 ((pfx.map String.toNat!).toArray) budgets
    | [] => say "usage: census2 20000,500000,3000000 1 <k>"
  | _ => say "usage: jank4-runtime census2 | ..."
  return 0

end Run.R4.Runtime

def main (args : List String) : IO UInt32 := Run.R4.Runtime.main args
