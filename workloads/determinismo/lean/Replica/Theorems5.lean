import Replica.Theorems2
import Replica.Theorems3
import Replica.Theorems4
import Replica.Ci5
import Replica.Resume5
import Replica.Clock5
import Replica.Disk5

/-!
# Round 5's theorems

Two kinds, as before: general ones for every input, and "(by computation)" ones that evaluate a
minimal case with `native_decide`. The recheck's: each fixed counterexample's round 2 to 4 minimal
case on 62e06e3's code (the models' default), passing now; the theorems about 3939448's code stay
in Theorems2 to Theorems4, pinned to `.v3939448`. Then round 5's counterexamples.
-/

namespace Replica.Theorems5

open Determinismo
open Replica.Theorems2 (violates violatesAt code cdataReport)

/-! ## The recheck: round 2 to 4's minimal cases on 62e06e3 -/

/-- CE2's remainder fixed (composer.zig:401-412): drive#3 dying of its own SIGKILL at 2 ms is
reaped by kill_all's first loop as its own exit, judged. -/
theorem ce2_own_sigkill_judged :
    violates Composer.exitsJudged 16 #[1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2] = false := by
  native_decide

/-- CE5's slot wait fixed (composer.zig:809-813): the start that waited for the only slot past
the stop is not made. -/
theorem ce5_slot_wait_stops : violates Composer.noStartPastHalfLimit 14 #[0, 1] = false := by
  native_decide

/-- CE15: the default cap is 30 minutes now: eleven bands, the last from 1,024 s to the cap. -/
theorem ce15_thirty_minute_bands :
    Composer.clockStartBands 1800000 = 11 ∧ Composer.clockStartBand 1800000 10 = (1024000, 1800000) := by
  decide

/-- CE16 fixed (junit.zig:58-87): the CDATA output's `<error` is outside the case's elements. -/
theorem ce16_captured_error_passes :
    (Junit.cases cdataReport == [{ name := "api.ErrorsTest::renders_503", failed := false }]) = true := by
  native_decide

/-- CE17 fixed (nodes.zig:945-954): the same draws on a fresh file write page 0 back, not page 2. -/
def freshCase62 : Bool :=
  let file := [Persist.Page.new, .hole, .new]
  match (Persist.partialFile file).run { decisions := { source := Source.path #[0, 1, 0, 1] } } with
  | .ok w _ => w == [0] && Persist.kept file w true 0 && !Persist.kept file w true 2
  | .error _ _ => false

theorem ce17_fresh_file_from_its_first_range : freshCase62 = true := by
  native_decide

/-- CE18 and CE22 fixed (report.zig:143-199): a sometimes never true beside an always true
under its message fails; a reachable never reached fails whichever timeline ended first. -/
theorem ce18_ce22_catalog_by_kind :
    code (Verdicts.explorerExit [[{ scenario := 0, events := [.eval .sometimes "m" false] },
                                   { scenario := 0, events := [.eval .always "m" true] }]] 1) = some 3 ∧
    code (Verdicts.explorerExit [[{ scenario := 0, events := [.declare .reachable "m"] },
                                   { scenario := 0, events := [.declare .always_or_unreachable "m"] }]] 1) = some 3 ∧
    code (Verdicts.explorerExit [[{ scenario := 0, events := [.declare .always_or_unreachable "m"] },
                                   { scenario := 0, events := [.declare .reachable "m"] }]] 1) = some 3 := by
  native_decide

/-- CE19 fixed where serve reads `exit` (serve.zig:5903-5909, 5756, 6017): the adopted run's
status is its explorer's. -/
theorem ce19_adopted_reads_exit :
    code (Verdicts.endedStatus [{ scenario := 0, events := [.declare .reachable "m"] }]) = some 3 := by
  native_decide

/-- CE20 fixed (vm.zig:3684-3699, tape.zig:139-141, 300-308): five polls answering something
against a cap of four: the recorder tapes four and the marker; the tape parses; its replay stops
at the fifth pull (TapeFull). Five idle polls tape nothing and replay whole. -/
def fivePolls (outside : Nat) : Tape.VM × Tape.VM :=
  Tape.recordReplay { label := "", consts := { overrideMax := 4 } }
    { steps := List.replicate 5 (.pull .ingressStatus), advice := [], forkIndex := 0,
      outsideRecord := outside, outsideReplay := 1 - outside, perturb := .none }

theorem ce20_full_tape_stops_its_replay :
    ((fivePolls 0).1.tape.toList.getLast? == some (.full 4)) = true ∧
    (fivePolls 0).2.error = some "TapeFull" ∧
    ((fivePolls 1).1.tape.isEmpty && (fivePolls 1).2.error.isNone && (fivePolls 1).1.events.size == (fivePolls 1).2.events.size) = true := by
  native_decide

/-- CE21 fixed for a run line that falls through (ci.zig:539-554): every run's report kept. -/
def twoRuns : List Ci5.Run := [{ names := ["a", "b"], failed := false }, { names := ["c"], failed := false }]

theorem ce21_plain_run_line_judges_every_run :
    Ci5.judged .v62e06e3 .plain twoRuns = ["a", "b", "c"] ∧ Ci5.judged .v3939448 .plain twoRuns = ["c"] := by
  decide

/-- CE27 fixed (ci.zig:326-330): one hung timeline of three is flaky, exit 2. -/
theorem ce27_hang_is_flaky :
    (Ci.verdictOf { Theorems3.ciCfg with ver := .v62e06e3 } Theorems3.hangJob).job == "flaky" &&
    (Ci.verdictOf { Theorems3.ciCfg with ver := .v62e06e3 } Theorems3.hangJob).exit == 2 := by
  native_decide

/-- CE28 fixed (ci.zig:340-342): the passing session is not the run's: fail, exit 1. -/
theorem ce28_session_left_out :
    (Ci.verdictOf { Theorems3.sessionCfg with ver := .v62e06e3 } Theorems3.failingWithSession).job == "fail" &&
    (Ci.verdictOf { Theorems3.sessionCfg with ver := .v62e06e3 } Theorems3.failingWithSession).exit == 1 := by
  native_decide

/-- CE29 fixed for the timelines' properties (main.zig:2828-2829, 2212-2229): a failure before
the stop fails the resumed run, complete or not. -/
theorem ce29_recorded_failure_counts :
    code (Resume5.resumedExit .v62e06e3 [{ scenario := 0, events := [.eval .always "a" false] },
                                         { scenario := 0, events := [.eval .always "a" true] }] 1 1000) = some 3 ∧
    code (Resume5.resumedExit .v62e06e3 [{ scenario := 0, events := [.eval .always "a" false] }] 1 1000) = some 3 := by
  native_decide

/-- CE35 fixed (det_guest.c:287-307, 419-447; faults.zig:2245-2250, 3256-3268): both cases'
syncs are their faults' decisions. -/
theorem ce35_two_arms :
    ((Durable.judgeD 3 8 (Source.path #[0, 1, 0, 0, 4])).violation.isSome) = false ∧
    ((Durable.judgeD 4 8 (Source.path #[1, 0, 0, 0, 2, 4])).violation.isSome) = false := by
  native_decide

/-- CE37 fixed (ci.zig:305-308, 296-304): the dead runner's timeline is counted. -/
theorem ce37_unreported_counted :
    ((Ci.judgeC Ci4.unreportedCounted (Ci4.worlds37[0]!) (Source.path #[0, 0, 0, 3])).violation.isSome) = false := by
  native_decide

/-! ## CE40: a run line that leaves the shell keeps its xargs run's report from the merge -/

/-- (by computation) examples/ci-demo/ci-capped.json's form (`...; exit $status`): two xargs runs,
both passing: the move never runs, the second run's report overwrites the first's: "a" and "b"
never judged. -/
theorem ce40_exit_run_line_keeps_the_last_run :
    Ci5.judged .v62e06e3 .exits twoRuns = ["c"] ∧ Ci5.judged .v62e06e3 .execs twoRuns = ["c"] ∧
    Ci5.judged .v62e06e3 .comment twoRuns = ["c"] := by
  decide

/-- (by computation) `set -e`: the first run's runner fails (its shell exits before the move),
the second passes: the merged report is the second run's: the failing tests get no verdict. -/
theorem ce40_set_e_drops_the_failing_run :
    Ci5.judged .v62e06e3 .setE [{ names := ["a", "b"], failed := true }, { names := ["c"], failed := false }] = ["c"] := by
  decide

theorem plain_parts (runs : List Ci5.Run) (f : Ci5.Files) :
    (runs.foldl (Ci5.step .v62e06e3 .plain) f).parts = f.parts ++ runs.map (·.names) := by
  induction runs generalizing f with
  | nil => simp
  | cons r rest ih =>
    simp only [List.foldl_cons, List.map_cons]
    rw [ih]
    simp [Ci5.step, Ci5.RunLine.reachesMove]

/-- For every list of xargs runs, a run line that falls through has every run's names judged. -/
theorem ce21_plain_keeps_every_run (runs : List Ci5.Run) (h : runs ≠ []) :
    Ci5.judged .v62e06e3 .plain runs = runs.flatMap (·.names) := by
  unfold Ci5.judged
  have hp := plain_parts runs {}
  simp only [List.nil_append] at hp
  have hne : runs.map (·.names) ≠ [] := by
    cases runs with
    | nil => exact absurd rfl h
    | cons _ _ => simp
  simp [hp, hne, List.flatMap]

theorem leaving_parts (line : Ci5.RunLine) (hl : line ≠ .plain ∧ line ≠ .setE)
    (runs : List Ci5.Run) (f : Ci5.Files) :
    runs.foldl (Ci5.step .v62e06e3 line) f =
      match runs.getLast? with
      | some r => { f with report := some r.names }
      | none => f := by
  induction runs generalizing f with
  | nil => rfl
  | cons r rest ih =>
    simp only [List.foldl_cons]
    rw [ih]
    have hm : line.reachesMove r.failed = false := by
      cases line <;> simp_all [Ci5.RunLine.reachesMove]
    cases rest with
    | nil => simp [Ci5.step, hm]
    | cons r' rest' =>
      cases hx : (r' :: rest').getLast? with
      | none => simp at hx
      | some x => simp [Ci5.step, hm, hx]

/-- For every list of xargs runs, a run line that leaves the shell (`exit`, `exec`, a trailing
comment) has only the last run's names judged: CE21 as at 3939448. -/
theorem ce40_leaving_keeps_only_the_last (line : Ci5.RunLine) (hl : line ≠ .plain ∧ line ≠ .setE)
    (runs : List Ci5.Run) :
    Ci5.judged .v62e06e3 line runs = ((runs.getLast?).map (·.names)).getD [] := by
  unfold Ci5.judged
  rw [leaving_parts line hl runs {}]
  cases h : runs.getLast? <;> simp

/-! ## CE41: captured output in CDATA that prints its element's closing tag -/

def closingTagReport : String :=
  "<testsuite><testcase classname=\"junit.ReportTest\" name=\"renders_an_error\" time=\"0.1\"><system-out><![CDATA[</system-out><error message=\"x\"/>]]></system-out></testcase></testsuite>"

/-- (by computation) A passing test whose output (in CDATA, as Surefire writes it) prints
`</system-out>` then an `<error` element: judged failing (junit.zig:69-81 skips to the first
`</system-out>`, the one inside the CDATA). -/
theorem ce41_closing_tag_fails_a_passing_test :
    (Junit.cases closingTagReport == [{ name := "junit.ReportTest::renders_an_error", failed := true }]) = true := by
  native_decide

/-! ## CE44: the wall clock's jump against a token's hour, over the whole timeline -/

/-- (by computation) An objective's return: the jump at the cap (30 min), a first phase of
899,999 ms, a second of 20 min, a 1 s ending: 2,100,999 ms of virtual time (no hang); the setup's
hour token used 300,999 ms past its expiry. -/
theorem ce44_second_phase_past_the_hour :
    ((Clock5.judge (Clock5.worlds[0]!) (Source.path #[10, 776000, 0, 299999, 0, 600000, 0, 0])).violation.isSome) = true := by
  native_decide

/-- (by computation) One phase (no objective): the jump at the cap, a 20-minute phase, the grace,
a 10-minute ending: 30 minutes over the hour's token. -/
theorem ce44_ending_past_the_hour :
    ((Clock5.judge (Clock5.worlds[1]!) (Source.path #[10, 776000, 0, 600000, 1, 2])).violation.isSome) = true := by
  native_decide

/-! ## CE45: a resume that finds every timeline recorded judges no catalog -/

/-- (by computation) Two timelines declaring `reachable "r"`, never reaching it, both recorded:
the uninterrupted run exits 3; the resume, "complete", exits 0 (main.zig:2212-2229), its `exit`
file "0" (serve: passed). -/
theorem ce45_complete_resume_skips_the_catalog :
    code (Verdicts.explorerExit [[{ scenario := 0, events := [.declare .reachable "r"] },
                                   { scenario := 0, events := [.declare .reachable "r"] }]] 1) = some 3 ∧
    code (Resume5.resumedExit .v62e06e3 [{ scenario := 0, events := [.declare .reachable "r"] },
                                         { scenario := 0, events := [.declare .reachable "r"] }] 2 1000) = some 0 := by
  native_decide

/-! ## CE46: properties past a record line's room are not judged on resume -/

/-- (by computation) A record line's room of one property: timeline 0's `always "b"` false is
past it; resumed, the run passes. -/
theorem ce46_failure_past_the_room :
    code (Resume5.resumedExit .v62e06e3 [{ scenario := 0, events := [.eval .always "a" true, .eval .always "b" false] }] 1 1) = some 0 ∧
    code (Verdicts.explorerExit [[{ scenario := 0, events := [.eval .always "a" true, .eval .always "b" false] }]] 1) = some 3 := by
  native_decide

/-! ## CE47: runs_adopt deletes a command-line resume's exit -/

/-- (by computation) A catalog's `reachable` never reached, timeline 0 recorded, timeline 1 run
by a command-line resume: its explorer exits 3 and writes `exit`; serve's runs_adopt, looking
after it ended, deletes `exit` and reads the record's summary: 0, "passed". -/
theorem ce47_adopted_resume_reads_its_record :
    code (Resume5.resumedExit .v62e06e3 [{ scenario := 0, events := [.declare .reachable "r"] },
                                         { scenario := 0, events := [.declare .reachable "r"] }] 1 1000) = some 3 ∧
    code (Resume5.adoptedStatus [{ scenario := 0, events := [.declare .reachable "r"] },
                                 { scenario := 0, events := [.declare .reachable "r"] }] 1 false) = some 0 := by
  native_decide

/-! ## CE42: a second driver phase's stop -/

/-- (by computation) World 17: four starts at 0, 10, 20 and 30 ms (the fourth runs 270 ms); the
second phase asked at 30 ms, its stop at 330 ms (composer.zig:797); its drivers start at 300 and
310 ms, past the timeline's half (300). -/
theorem ce42_second_phase_starts_past_half :
    violates Composer.noStartPastHalfLimit 17 #[0, 0, 0, 1, 1, 0, 1] = true := by
  native_decide

/-! ## CE43: corrupt_reads's reads unnamed at the heal, or named under the next fault -/

/-- (by computation) A read during the fault, the heal before the reader ran: never named; the
instance kept (rmdir refused), the next fault's reader names it under that fault. -/
theorem ce43_read_before_the_heal_unnamed :
    ((Disk5.judgeWith Disk5.everyReadNamed 4 (Source.path #[0, 0, 1, 3, 0])).violation.isSome) = true ∧
    ((Disk5.judgeWith Disk5.namedRight 6 (Source.path #[0, 0, 1, 3, 0, 0, 2])).violation.isSome) = true := by
  native_decide

/-! ## CE48: the tape's reason table (CE20's other table) -/

/-- (by computation) Three decisions with a reason against a reason table of two (1,024 in the
Zig): the recorder tapes all three (no marker: the override cap is not reached), and the replay's
parse refuses the tape. -/
def threeReasons : Tape.VM × Tape.VM :=
  Tape.recordReplay { label := "", consts := { reasonMax := 2 } }
    { steps := List.replicate 3 (.pull .plain), advice := [(0, 0, "r", true), (1, 0, "r", true), (2, 0, "r", true)],
      forkIndex := 0, outsideRecord := 0, outsideReplay := 1, perturb := .none }

theorem ce48_reasons_past_the_table :
    ((threeReasons.1.tape.toList.filter fun | .override .. => true | _ => false).length == 3 &&
     !threeReasons.1.tape.any (fun | .full _ => true | _ => false)) = true ∧
    threeReasons.2.error = some "TapeTooLong (reason_count_max)" := by
  native_decide

end Replica.Theorems5
