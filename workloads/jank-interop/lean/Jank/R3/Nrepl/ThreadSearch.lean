import Jank.R3.Nrepl.Threads
import Jank.Nrepl.Search

/-!
# Round 3, nREPL: searches of World T, and round 2's controls run to completion

## Library gap: preemption-bounded interleaving

`Determinismo.interleave` decides the next thread at every step, so the interleavings of two
connections (~200 steps) cannot be enumerated: round 2's controls stopped at 20,000 timelines.
`interleavePB` searches every schedule that differs from the round-robin one by at most `budget`
preemptions (CHESS-style preemption bounding): at each step where the running thread could go on and
another thread is ready, a decision `thread.preempt` keeps it (0) or switches to another ready
thread (1..n), spending one unit of budget; when the running thread blocks or ends, the next ready
thread in round-robin order runs (no decision). An `exhaust` over these decisions is complete for
that bound.
-/

namespace Jank.R3.Nrepl

open Determinismo Jank.Analyzer

def interleavePB {M L : Type} (prog : Program M L) (maxSteps budget : Nat)
    (stuck : Process M L → Option String := fun _ => some "every live thread blocked") :
    ProcessM M L Unit := do
  let mut blocked : List Nat := []
  let mut cur : Option Nat := none
  let mut left := budget
  for _ in List.range maxSteps do
    let p ← get
    let live := (List.range p.threads.size).filter fun i => (p.threads.getD i none).isSome
    if live.isEmpty then return
    let ready := live.filter (!blocked.contains ·)
    if ready.isEmpty then
      if let some detail := stuck p then throw (.violation "deadlock" detail)
      return
    let t ← match cur with
      | some c =>
        if ready.contains c then
          let others := ready.filter (· != c)
          if left > 0 && !others.isEmpty then do
            let k ← decide (σ := Process M L) "thread.preempt" (others.length + 1)
            if k == 0 then pure c else do
              left := left - 1
              pure (others.getD (k - 1) c)
          else pure c
        else
          -- round robin: the next ready thread after `c`
          pure ((ready.find? (· > c)).getD (ready.headD 0))
      | none => pure (ready.headD 0)
    let some locals := p.threads.getD t none | return
    match ← prog.step t locals with
    | .ran locals' =>
      modify fun p => { p with threads := p.threads.set! t (some locals'), steps := p.steps + 1 }
      blocked := []
      cur := some t
    | .blocked =>
      blocked := t :: blocked
      cur := some t
    | .done =>
      modify fun p => { p with threads := p.threads.set! t none, steps := p.steps + 1 }
      blocked := []
      cur := some t

/-! ## World T runs with either scheduler -/

def runTWith (sched : Option Nat) (cfg : TConfig) (aside : Aside) (scripts : List (List TReq)) (source : Source) :
    Ended × Process TMem TTh :=
  let body : TM Unit := do
    match sched with
    | some b => interleavePB tProg cfg.maxSteps b tStuck
    | none => interleave tProg cfg.maxSteps tStuck
    let p ← get
    let live := p.threads.toList.any Option.isSome
    if !live then
      if let some (prop, d) := tJudge aside scripts p.memory then throw (.violation prop d)
      match p.memory.fd 1 with
      | some .terminal => pure ()
      | d => throw (.violation "stdout is restored after every eval" s!"fd 1 is left on {reprStr d}")
    else
      throw (.violation "the timeline ends within the step bound (model bound)" s!"{(p.threads.toList.filter Option.isSome).length} threads live after {cfg.maxSteps} rounds")
  match runProcess (tInitial cfg scripts) body source 100000 with
  | (.ok _, p) => ({ taken := p.decisions.taken, violation := none }, p)
  | (.error (.violation "deadlock" d), p) => ({ taken := p.decisions.taken, violation := some ("every request gets a done reply (no hang)", d) }, p)
  | (.error (.violation prop d), p) => ({ taken := p.decisions.taken, violation := some (prop, d) }, p)
  | (.error .limit, p) => ({ taken := p.decisions.taken, violation := none }, p)
  | (.error (.nodeDown _), p) => ({ taken := p.decisions.taken, violation := none }, p)

structure TScenario where
  name : String
  cfg : TConfig := {}
  aside : Aside := {}
  scripts : List (List TReq)
  seeds : Nat := 2000
  /-- Preemption budget of the complete search. -/
  budget : Nat := 2
  maxRuns : Nat := 3000000
  deriving Inhabited

def allVariant : Variant := { noTopDoSplit := true, inNsNil := true, nsPrintName := true, printOutLost := true }

def allAside : Aside :=
  { blankOut := true, sessions := true, lookupKnown := true, lookupFallback := true, loadNs := true, variant := allVariant }

def tScenarios : List TScenario := [
  { name := "T1 R125: two connections printing (real code), random schedules"
    cfg := { partialReads := false }
    scripts := [[.clone, .eval "(println \"a\")"], [.clone, .eval "(print \"b\")"]] },
  { name := "T2 R125 set aside (capture under a lock): the same"
    cfg := { partialReads := false, fixCapture := true }
    scripts := [[.clone, .eval "(println \"a\")"], [.clone, .eval "(print \"b\")"]] },
  { name := "T3 two connections, disjoint names, evals that define, print, fail, read back; capture locked"
    cfg := { partialReads := false, fixCapture := true }
    aside := allAside
    scripts := [[.clone, .eval "(def a 1) (defn f [x] (+ x a))", .eval "(f 1) (print \"r\")", .eval "(throw (ex-info \"e\" {})) 9", .eval "(nil? *e)"],
                [.clone, .eval "(ns bar) (def b 2)", .eval "b" (some "bar"), .eval "*1 (println b)" (some "bar"), .completions "bar" "b"]] },
  { name := "T4 R1 through nREPL: a NUL in one connection's code, the other printing"
    cfg := { partialReads := false }
    scripts := [[.clone, .eval "\"a\u0000\""], [.clone, .eval "(println \"x\")"]] },
  { name := "T5 R126: a value that throws while printed, then more evals on the connection; capture locked"
    cfg := { partialReads := false, fixCapture := true }
    scripts := [[.clone, .eval "(map (fn [_] (throw (ex-info \"p\" {}))) [1])", .eval "(nil? *e)", .eval "*1"],
                [.clone, .eval "(def c 3)"]] },
  { name := "T6 macros defined on one connection used by the other (shared namespace); capture locked"
    cfg := { partialReads := false, fixCapture := true }
    aside := allAside
    scripts := [[.clone, .eval "(defmacro m [x] (list 'inc x))", .eval "(m 1)"], [.clone, .eval "(defn g [] 5)", .eval "(g)"]] },
  { name := "T7 control: partial reads, one client, every op"
    cfg := { partialReads := true }
    aside := allAside
    scripts := [[.clone, .eval "(do (print \"a\") 3)", .lookup "user" "map", .completions "user" "ma", .describe, .close]] },
  { name := "T8 control: EINTR on a blocked read_some (R139)"
    cfg := { partialReads := false, eintr := true }
    aside := allAside
    scripts := [[.clone, .eval "(do (print \"a\") 3)", .lookup "user" "map", .close]] },
  { name := "T9 two connections, disjoint names, two evals each (define, print, read back); capture locked"
    cfg := { partialReads := false, fixCapture := true }
    aside := allAside
    scripts := [[.clone, .eval "(def a 1) (defn f [x] (+ x a))", .eval "(f 1) (print \"r\")"],
                [.clone, .eval "(ns bar) (def b 2)", .eval "*1 (println b)" (some "bar")]] },
  { name := "T10 N6 across connections: a lazy value printed after its capture, the other connection capturing; capture locked"
    cfg := { partialReads := false, fixCapture := true }
    scripts := [[.clone, .eval "(map println [1 2])"], [.clone, .eval "(print \"b\")"]] } ]

/-! ## Round 2's controls, on round 2's model, preemption-bounded -/

open Jank.NreplServer in
def runR2PB (s : Scenario) (budget : Nat) (source : Source) : Ended :=
  let body : Jank.NreplServer.SM Unit := do
    interleavePB prog s.cfg.maxSteps budget stuckDetail
    let p ← get
    let live := p.threads.toList.any Option.isSome
    if !live then
      if let some (prop, d) := judge p.memory then throw (.violation prop d)
    else if s.cfg.requireFinish then
      throw (.violation "the timeline ends within the step bound (model bound)"
        s!"{(p.threads.toList.filter Option.isSome).length} threads still live after {s.cfg.maxSteps} scheduler rounds")
  match runProcess (initial s.cfg s.scripts s.sequential) body source 100000 with
  | (.ok _, p) => { taken := p.decisions.taken, violation := none }
  | (.error (.violation "deadlock" d), p) => { taken := p.decisions.taken, violation := some ("every request gets a done reply (no hang)", d) }
  | (.error (.violation prop d), p) => { taken := p.decisions.taken, violation := some (prop, d) }
  | (.error .limit, p) => { taken := p.decisions.taken, violation := none }
  | (.error (.nodeDown _), p) => { taken := p.decisions.taken, violation := none }

/-- Round 2's scenarios whose exhaustive search stopped at 20,000 timelines (the controls and
N12). -/
def r2Controls : List Jank.NreplServer.Scenario :=
  Jank.NreplServer.scenarios.filter fun s => (s.name.splitOn "(control").length > 1 || (s.name.splitOn "N12").length > 1

/-- A census of any world: every timeline under the prefix `pre` (depth first), violations counted
by property, the first example's decisions kept. -/
def censusRun (run : Source → Ended) (maxRuns : Nat) (pre : Array Nat := #[]) : Census := Id.run do
  let mut path : Array Nat := pre
  let mut c : Census := {}
  for i in List.range maxRuns do
    let o := run (Source.path path)
    c := { c with runs := i + 1 }
    if let some (p, d) := o.violation then
      let counts := match c.counts.lookup p with
        | some n => (p, n + 1) :: c.counts.filter (·.1 != p)
        | none => (p, 1) :: c.counts
      let examples := if (c.examples.lookup p).isSome then c.examples else c.examples ++ [(p, d)]
      let tapes := if (c.tapes.lookup p).isSome then c.tapes else c.tapes ++ [(p, o.taken.map (·.value))]
      c := { c with counts, examples, tapes }
    match nextPath o.taken with
    | none => return { c with complete := true }
    | some q =>
      if q.size < pre.size || (q.extract 0 pre.size) != pre then return { c with complete := true }
      path := q
  return c

end Jank.R3.Nrepl
