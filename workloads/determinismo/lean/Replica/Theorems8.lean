import Replica.Theorems7

/-!
# Round 8's theorems

As before: general ones for every input, and "(by computation)" ones that evaluate a minimal case
with `native_decide` (trusting Lean's compiler, as the searches do). The models c4f246e changed
default to it since round 8 (Serve3, Explain7, Tape6, Tree, TreeRun, Resume5, Request6); round 7's
theorems about df8f08b's code of them are pinned to `.vdf8f08b` (Theorems7).

First the recheck of round 7's counterexamples (CE45, CE56 to CE60) on c4f246e's code: closed,
or what the change leaves. Then round 8's counterexamples.
-/

namespace Replica.Theorems8

open Determinismo
open Replica.Theorems2 (code)

/-! ## CE45: closed on its three paths (report.zig:553-568; main.zig:2131-2137, 2316-2323, 2361-2364) -/

def declares : Verdicts.Timeline := Theorems7.declares
def passes : Verdicts.Timeline := Theorems7.passes
def reaches : Verdicts.Timeline := { scenario := 0, events := [.declare .reachable "r", .eval .reachable "r" true] }

/-- (by computation) Round 7's three paths at c4f246e: a complete run resumed again (3, as
before); a stop after the last timeline's line and before the run's end (no catalog line: the
explorer's way, the declarations judged: 3); a session's timeline holding one of the run's
numbers (3); a run stopped after its first timeline, the rest not declaring "r" (3). The run's
own verdict is 3 in each. -/
theorem ce45_paths_closed :
    code (Resume5.resumedExit .vc4f246e [declares, declares] 2 1000) = some 3 ∧
    code (Resume5.resumedExit .vc4f246e [declares, declares] 2 1000 (ended := false)) = some 3 ∧
    code (Resume5.resumedExitWithSession .vc4f246e [declares, declares] 2 1000 true) = some 3 ∧
    code (Resume5.resumedExit .vc4f246e [declares, passes] 1 1000) = some 3 ∧
    code (Verdicts.explorerExit [[declares, passes]] 1) = some 3 := by
  native_decide

/-! ## CE61: a drained run's catalog line taken for the run's -/

/-- (by computation) Three timelines: two declare reachable "r", the third reaches it. Drained
after two (its end's catalog line: "r" unreached, 1 failing), resumed, interrupted after the
third's line and before its end, resumed again: complete, its catalog line the drain's: 3. The
run's verdict: 0 ("r" reached). df8f08b reads the same line: 3. -/
theorem ce61_drained_catalog_line :
    code (Verdicts.explorerExit [[declares, declares, reaches]] 1) = some 0 ∧
    code (Resume5.resumedExitAfterDrain .vc4f246e [declares, declares, reaches] 2) = some 3 ∧
    code (Resume5.resumedExitAfterDrain .vdf8f08b [declares, declares, reaches] 2) = some 3 := by
  native_decide

/-! ## CE63: a run of two scenarios resumed as one -/

/-- (by computation) Two scenarios, each one timeline declaring reachable "r", never reaching
it: the run fails for its catalog (3). Interrupted in the second scenario before its timeline's
line, that scenario's run resumed (its request names it alone): its catalog judged over one
scenario, nothing fails: 0. Interrupted in the first: the second never explored, 0. -/
theorem ce63_scenario_resumed_alone :
    code (Verdicts.explorerExit [[declares], [declares]] 2) = some 3 ∧
    code (Resume5.resumedExitScenarios .vc4f246e [declares] [declares] 1 0) = some 0 ∧
    code (Resume5.resumedExitScenarios .vc4f246e [declares] [declares] 0 0) = some 0 := by
  native_decide

/-! ## CE56: closed (serve.zig:766-770) -/

/-- (by computation) Round 7's draws on an instrumented run from a snapshot at c4f246e: never
stopped, never labeled. What the exemption leaves (a note: the gate cannot tell): the same run of
an uninstrumented system is never said to run blind, though the exemption's comment (783-787)
says such a run is "judged at its end". -/
theorem ce56_closed_and_its_note :
    ((Serve3.judgeGate 2 { label := "", instrumented := some true, fromSnapshot := some true }
        (Source.path #[0, 0, 1, 3, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1])).violation.isSome) = false ∧
    ((Serve3.judgeGate 2 { label := "", instrumented := some true, fromSnapshot := some true, ver := .vdf8f08b }
        (Source.path #[0, 0, 1, 3, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1])).violation.isSome) = true ∧
    ((Serve3.judgeGate 3 { label := "", instrumented := some false, fromSnapshot := some true }
        (Source.path #[0, 0, 1, 3, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1])).violation.isSome) = true := by
  native_decide

/-! ## CE57: closed where the control's pull still varies the history; CE62 is what it leaves -/

/-- How many histories (distinct tapes) one explanation replays. -/
def histories (set : Option Nat) (ver : Ver) (live : Bool) : Nat :=
  match (Explain7.explain 6 set 6 ver live).run { decisions := { source := Source.path #[] } } with
  | .ok _ s => s.outcomes.length
  | .error _ _ => 0

/-- (by computation) A value set, 6 variants beside the control's 6: df8f08b replays 7 histories
(the value's one tape 6 times); c4f246e 12 (each variant its control's draw varied beside it).
With the value's history leaving the control's pull to a draw that decides nothing (CE62): 7. -/
theorem ce57_closed_ce62_left :
    histories (some 0) .vdf8f08b true = 7 ∧
    histories (some 0) .vc4f246e true = 12 ∧
    histories (some 0) .vc4f246e false = 7 := by
  native_decide

/-- (by computation) CE62: the control's 6 histories fail 5 times; the value set, its pull's
history not failing, its 6 variants one history: "needed" at c4f246e. -/
theorem ce62_one_history_needed :
    ((Explain7.judge 6 (some 0) (Source.path #[1, 1, 1, 1, 1, 0, 0]) .vc4f246e false).violation.isSome) = true := by
  native_decide

/-! ## CE58: closed for the archive, the frontier, an extension and this generation's strategy -/

/-- (by computation) Round 7's draws at c4f246e: the parent cut at its horizon (its archive's
places, `open_to_end`), and a strategy's return to one of the generation's timelines
(`returns_end`): the moment is drawn before the marker; no violation. A strategy's return to a
timeline of an earlier generation (main.zig:7753-7762: checked against nothing) still lands past
it (a remainder: its node needs a holder there, see the report). -/
theorem ce58_closed_but_earlier_generations :
    ((Tape6.judgeFull (Tape6.fullWorlds[3]!) (Source.path #[0, 1, 1, 3, 0])).violation.isSome) = false ∧
    ((Tape6.judgeFull (Tape6.fullWorlds[4]!) (Source.path #[0, 1, 1, 3, 0])).violation.isSome) = false ∧
    ((Tape6.judgeFull { Tape6.fullWorlds[4]! with earlier := true } (Source.path #[0, 1, 1, 3, 0])).violation.isSome) = true := by
  native_decide

/-! ## CE59: closed (main.zig:7262-7290) -/

/-- (by computation) The census world's seed 20 at c4f246e: the moved return's landing is taken,
it stays; the generation's moments are distinct. -/
theorem ce59_closed :
    ((Tree.judgeT Tree.distinctMoments (Tree.tworlds[0]!) (Source.seeded 20)).violation.isSome) = false ∧
    ((Tree.judgeT Tree.distinctMoments { Tree.tworlds[0]! with ver := .vdf8f08b } (Source.seeded 20)).violation.isSome) = true := by
  native_decide

/-! ## CE60: closed, for every command-line run (runs.zig:227-262 `injectors_keep`) -/

/-- For every command-line run, c4f246e's analyses boot the inputs its tapes were recorded with:
each injector kept under its own name. -/
theorem ce60_closed (a : Request6.Asked) :
    Request6.inputs (Request6.analysisOfCommandLine .vc4f246e a) = Request6.inputs a := by
  cases a
  simp [Request6.analysisOfCommandLine, Request6.inputs, Ver.sinceC4, Request6.basename, Function.comp_def]

end Replica.Theorems8
