import Replica.Theorems6
import Replica.Explain7
import Replica.Disk7
import Replica.ComposerSearch

/-!
# Round 7's theorems

As before: general ones for every input, and "(by computation)" ones that evaluate a minimal case
with `native_decide` (trusting Lean's compiler, as the searches do). The models default to
df8f08b since round 7; round 6's theorems about a7fe05d's code are pinned to `.va7fe05d`
(Theorems6, Theorems4, Theorems3). Round 8: the models c4f246e changed default to it, and this
file's theorems about df8f08b's code of them are pinned to `.vdf8f08b`.

First the recheck: each counterexample round 6 found, on df8f08b's code (closed, or what the
change leaves). Then the earlier ones df8f08b's commits touched (CE25, CE26, CE32 to CE34, the
composer's stop). Then round 7's counterexamples.
-/

namespace Replica.Theorems7

open Determinismo
open Replica.Theorems2 (violates violatesAt code)

/-! ## CE49: closed (junit.zig:14, 21, 62-83 `case_index`, 115-131 `captured_end`) -/

/-- (by computation) Round 6's two reports at df8f08b: the printed cases make no test of their
own, and the failure after printed `</testcase>` is seen. -/
theorem ce49_closed :
    (Junit.cases Theorems6.printedReport == [{ name := "junit.WriterTest::writes_a_report", failed := false }]) = true ∧
    (Junit.cases Theorems6.cutReport == [{ name := "junit.WriterTest::closes_a_case", failed := true }]) = true := by
  native_decide

/-- A passing case whose body holds a comment that mentions a failure element. -/
def commentReport : String :=
  "<testsuite><testcase classname=\"c\" name=\"retried\"><!-- <failure message=\"first attempt\"/> --></testcase></testsuite>"

/-- (by computation) What the fix leaves: `case_index` and `captured_end` skip comments,
`element_index` (junit.zig:85-112) does not: a comment in a case's body that mentions `<failure`
fails the case. -/
theorem df_comment_in_a_body_fails_its_case :
    (Junit.cases commentReport == [{ name := "c::retried", failed := true }]) = true ∧
    (Junit.cases commentReport .va7fe05d == [{ name := "c::retried", failed := true }]) = true := by
  native_decide

/-! ## CE52: closed (tape.zig:501-609; vm.zig:2214-2221, 2258-2263; main.zig:3846-3852) -/

/-- (by computation) Round 6's steps at df8f08b: a 131,072-byte `det:ask`, a 42,236-byte one,
a step of 70,000 bytes with 61,072 escapes: each line written whole and read back. The table's
caps: the recorder refuses the step past them (room kept for det:over), so what it wrote reads
back. -/
theorem ce52_closed :
    ((Tape6.parse {} (Tape6.record {} [.step 131072 0, .step 7 0])).toOption == some [.step 131072 0, .step 7 0]) = true ∧
    ((Tape6.parse {} (Tape6.record {} [.step 42236 0, .step 7 0])).toOption == some [.step 42236 0, .step 7 0]) = true ∧
    ((Tape6.parse {} (Tape6.record {} [.step 70000 61072])).toOption == some [.step 70000 61072]) = true ∧
    (Tape6.accepted { stepsMax := 2 } [.step 4 0, .step 4 0, .step 4 0] == [.step 4 0]) = true ∧
    ((Tape6.parse { stepsMax := 2 } (Tape6.record { stepsMax := 2 } [.step 4 0, .step 4 0, .step 4 0])).toOption == some [.step 4 0]) = true := by
  native_decide

/-! ## CE53: closed for the frontier and an uncut timeline's archive; CE58 is what it leaves -/

/-- A replay to a moment at or before the marker's pull never reaches it: for every marker and
moment. df8f08b's returns land before `tape_full_ns` (main.zig:4083, 6556-6558). -/
theorem replay_before_the_marker (at_ m : Nat) (h : m ≤ at_) : Tape6.replayTo (some at_) m = .ok () := by
  simp [Tape6.replayTo, Nat.not_lt.mpr h]

/-- (by computation) Round 6's draws at df8f08b: the judgment's moment is drawn before the
marker (pull 2); the child replays. -/
theorem ce53_closed :
    ((Tape6.judgeFull { Tape6.fullWorlds[0]! with ver := .vdf8f08b } (Source.path #[0, 1, 1, 3, 0])).violation.isSome) = false ∧
    ((Tape6.judgeFull { Tape6.fullWorlds[0]! with ver := .vdf8f08b } (Source.path #[0, 1, 1, 2, 0])).violation.isSome) = false := by
  native_decide

/-! ## CE54: closed (nodes.zig:2269-2285, 2293-2318 `read_corrupted_parts`) -/

/-- For every aimed table and read, df8f08b's reader names exactly the blocks whose byte dm
changed (in blocks, `corrupt_byte` 1). -/
theorem ce54_closed (aimed : List (Nat × Nat)) (start count : Nat) :
    Aimed6.namedAt .vdf8f08b aimed start count = Aimed6.changed aimed start count := by
  simp [Aimed6.namedAt, Ver.sinceDf, Aimed6.namedDf, Aimed6.changed]

/-- The same in sectors with any `corrupt_byte`: `read_corrupted_parts`'s bytes are dm-flakey's
(byte `cb` of each clone over an extent, none in a clone shorter than it), for every input. -/
theorem ce54_parts_are_the_changed_bytes (aimed : List (Nat × Nat)) (start count cb : Nat) :
    Aimed6.readCorruptedParts aimed start count cb = Aimed6.changedB aimed start count cb := by
  unfold Aimed6.readCorruptedParts Aimed6.changedB
  congr 1
  funext e
  obtain ⟨s, c⟩ := e
  dsimp only
  generalize max start s = ps
  generalize min (start + count) (s + c) = pe
  by_cases h1 : ps < pe
  · have h1' : ¬ pe ≤ ps := Nat.not_le.mpr h1
    by_cases h2 : cb ≤ (pe - ps) * 512
    · have h2' : ¬ (pe - ps) * 512 < cb := Nat.not_lt.mpr h2
      simp [h1, h1', h2, h2']
    · have h2' : (pe - ps) * 512 < cb := Nat.lt_of_not_le h2
      simp [h1, h1', h2, h2']
  · have h1' : pe ≤ ps := Nat.le_of_not_lt h1
    simp [h1, h1']

/-- (by computation) Round 6's minimal cases at df8f08b: both bytes named, the right ones. -/
theorem ce54_minimal_cases_named :
    Aimed6.namedAt .vdf8f08b [(1, 1)] 0 2 = [1] ∧
    Aimed6.namedAt .vdf8f08b [(0, 1), (2, 1)] 0 3 = [0, 2] := by
  decide

/-! ## CE55: closed (ci.zig:543-555) -/

theorem subshell_parts_df (line : Ci5.RunLine) (runs : List Ci5.Run) (f : Ci5.Files) :
    (runs.foldl (Ci5.step .vdf8f08b line) f).parts = f.parts ++ runs.map (·.names) := by
  induction runs generalizing f with
  | nil => simp
  | cons r rest ih =>
    simp only [List.foldl_cons, List.map_cons]
    rw [ih]
    simp [Ci5.step, Ver.sinceA7]

/-- For every run line's form and every non-empty list of xargs runs, runners exiting 255
among them: df8f08b passes a 255 on as 254, xargs runs every batch, and every name is judged. -/
theorem ce55_closed (line : Ci5.RunLine) (runs : List Ci5.Run) (h : runs ≠ []) :
    Ci5.judged .vdf8f08b line (Ci5.xargsRunsV .vdf8f08b runs) = runs.flatMap (·.names) := by
  have hx : Ci5.xargsRunsV .vdf8f08b runs = runs := by simp [Ci5.xargsRunsV, Ver.sinceDf]
  rw [hx]
  unfold Ci5.judged
  have hp := subshell_parts_df line runs {}
  simp only [List.nil_append] at hp
  have hne : runs.map (·.names) ≠ [] := by
    cases runs with
    | nil => exact absurd rfl h
    | cons _ _ => simp
  simp [hp, hne, List.flatMap]

/-! ## CE45: closed for a complete run resumed again; the session's path stays -/

def declares : Verdicts.Timeline := { scenario := 0, events := [.declare .reachable "r"] }

/-- (by computation) Two timelines declaring `reachable "r"`, never reaching it: the run fails
(3). df8f08b's complete resume reads the record's catalog line: 3 (main.zig:1170-1175, 2297,
2147-2154). What it leaves: a stop after the last timeline's line and before the run's end (no
catalog line yet): 0; a session's timeline holding one of the run's numbers (never complete,
the explorer's way, the catalog judged from nothing): 0. -/
theorem ce45_closed_for_a_complete_run :
    code (Verdicts.explorerExit [[declares, declares]] 1) = some 3 ∧
    code (Resume5.resumedExit .vdf8f08b [declares, declares] 2 1000) = some 3 ∧
    code (Resume5.resumedExit .vdf8f08b [declares, declares] 2 1000 (ended := false)) = some 0 ∧
    code (Resume5.resumedExitWithSession .vdf8f08b [declares, declares] 2 1000 true) = some 0 := by
  native_decide

def passes : Verdicts.Timeline := { scenario := 0, events := [.eval .always "a" true] }

/-- (by computation) CE45's other path at df8f08b (found by `runs7/resume.txt`): a run stopped
after its first timeline's line, that timeline declaring `reachable "r"` (its record line keeps
no declaration: report.zig keeps evaluated properties), the rest run again without declaring it:
the resumed run's catalog has no "r": 0, the run's 3. -/
theorem ce45_interrupted_run_loses_declarations :
    code (Verdicts.explorerExit [[declares, passes]] 1) = some 3 ∧
    code (Resume5.resumedExit .vdf8f08b [declares, passes] 1 1000) = some 0 := by
  native_decide

/-! ## CE50: closed for the stop; CE56 is what it leaves -/

/-- (by computation) Round 3's draws on a run from a snapshot, at df8f08b (serve.zig:779-783):
never stopped. Its four timelines run to the run's end, none reporting coverage (all the
setup's): the end's `uncovered` file says its system runs without its language's
instrumentation (762-772): CE56. -/
theorem ce50_closed_ce56_said :
    (match (Serve3.drawGate { label := "", instrumented := some true, fromSnapshot := some true, ver := .vdf8f08b }).run
        { decisions := { source := Source.path #[0, 0, 1, 3, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1] } } with
     | .ok g _ => g.stoppedAt.isNone && g.labeled && g.rows.all (·.2 == 0)
     | .error _ _ => false) = true := by
  native_decide

/-! ## CE51: closed for the six flags (main.zig:1441-1453, 1519-1522; serve.zig:5595-5602) -/

/-- For every command-line run without an injector of its own, df8f08b's analyses boot the inputs
its tapes were recorded with. -/
theorem ce51_closed (a : Request6.Asked) (h : a.injectors = []) :
    Request6.inputs (Request6.analysisOfCommandLine .vdf8f08b a) = Request6.inputs a := by
  cases a
  simp_all [Request6.analysisOfCommandLine, Ver.sinceDf, Ver.sinceC4]

/-- (by computation) CE60: with `--injector ./chaos`, the request holds the kept copy
(`<hash>-chaos`): the analysis's system disk has another injector name, its inputs differ. -/
theorem ce60_injector_by_another_name :
    Request6.inputs (Request6.analysisOfCommandLine .vdf8f08b { injectors := [["chaos"]] }) ≠ Request6.inputs { injectors := [["chaos"]] } := by
  native_decide

/-! ## The composer's stop (composer.zig:820-827, df8f08b) -/

/-- (by computation) World 14 (a 400 ms driver holding the only slot, a 600 ms limit): three
starts, the fourth's wait for the slot reaches the stop at 300 ms. a7fe05d: the phase ends with
no `drivers_stopped`; df8f08b says it. -/
theorem drivers_stop_said :
    violatesAt .va7fe05d Composer.stopSaid 14 #[1, 1, 0] = true ∧
    violates Composer.stopSaid 14 #[1, 1, 0] = false ∧
    violates Composer.noStartPastHalfLimit 14 #[1, 1, 0] = false := by
  native_decide

/-! ## CE32 to CE34: closed by the `planned` lines (main.zig:2117-2127, 4752-4775, 6491-6545) -/

/-- (by computation) Round 4's minimal cases at df8f08b: every recorded timeline keeps its plan,
none starts from the setup inside another's path, and the fillers come first. -/
theorem ce32_ce33_ce34_closed :
    ((Resume4.judgeR Resume4.keepsRecorded (Resume4.rworlds[0]!) (Source.path #[0, 0, 0, 0, 1, 0])).violation.isSome) = false ∧
    ((Resume4.judgeR Resume4.keepsRecorded (Resume4.rworlds[2]!) (Source.path #[0, 0, 1, 1, 1, 0])).violation.isSome) = false ∧
    ((Resume4.judgeR Resume4.startsWhereItsPathSays (Resume4.rworlds[2]!) (Source.path #[0, 0, 1, 1, 1, 0])).violation.isSome) = false ∧
    ((Resume4.judgeR Resume4.neverCut (Resume4.rworlds[3]!) (Source.path #[0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0])).violation.isSome) = false ∧
    ((Resume4.judgeR Resume4.keepsRecorded (Resume4.rworlds[3]!) (Source.path #[0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0])).violation.isSome) = false := by
  native_decide

/-! ## CE25, CE26: closed (main.zig:7308-7314 `archive_add_judged`, 7482-7486) -/

/-- (by computation) The twin timelines: the repeat is planned and no cell's place. The
frontier's return and the archive's cell at one moment: one return. -/
theorem ce25_ce26_closed :
    let st := Tree.archiveAdd (Tree.archiveAdd {} Theorems3.twinPlan (Theorems3.twin 0)) Theorems3.twinPlan (Theorems3.twin 1) true
    ((st.cells.map fun c => c.places.toList.map (·.branch)) == #[[0]]) = true ∧
    (match (Tree.archiveReturns Theorems3.oneCell 16 4 Theorems3.frontierAtIt).run { decisions := { source := Source.path #[] } } with
     | .ok (_, rs) _ => (rs.filter fun r => r.branch == 0 && r.vtime == 1000001).length == 1
     | .error _ _ => false) = true := by
  native_decide

/-! ## CE56: the gate's end says an instrumented run from a snapshot is uninstrumented -/

/-- (by computation) The same draws as `ce50_closed_ce56_said`, read as the property: an
instrumented system, said to run without its instrumentation. -/
theorem ce56_snapshot_run_said_uninstrumented :
    ((Serve3.judgeGate 2 { label := "", instrumented := some true, fromSnapshot := some true, ver := .vdf8f08b }
        (Source.path #[0, 0, 1, 3, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1])).violation.isSome) = true := by
  native_decide

/-! ## CE57: explain's set values, one history counted m times -/

/-- (by computation) The Zig's verdict (explain.zig:109-119, Wilson's 90% intervals): 0 of 6
against the control's 5 of 6 is "needed"; 0 of 1 (one history) would be "unclear". -/
theorem ce57_verdicts :
    Explain7.verdict 0 6 5 6 = .needed ∧ Explain7.verdict 0 1 5 6 = .unclear := by
  native_decide

/-- (by computation) A timeline whose every history fails with probability 5/6 whatever the
named draw's value: the control's 6 histories, 5 failing; the value set to 0, one history (its
tape replayed 6 times), not failing: "needed". -/
theorem ce57_one_history_needed :
    ((Explain7.judge 6 (some 0) (Source.path #[1, 1, 1, 1, 1, 0, 0]) .vdf8f08b).violation.isSome) = true := by
  native_decide

/-! ## CE59: two returns at one moment through returns_earlier (CE26's remainder) -/

/-- (by computation) The tree's census world, seed 20 (`runs7/tree-dup.txt`): judgment 1's
archive returns #0@23 and #0@8 are distinct; returns_earlier moves the first 15 µs earlier: both
at #0@8. -/
theorem ce59_offsets_meet :
    ((Tree.judgeT Tree.distinctMoments { Tree.tworlds[0]! with ver := .vdf8f08b } (Source.seeded 20)).violation.isSome) = true := by
  native_decide

/-- (by computation) What two returns at one moment do to a resume at df8f08b: two `planned`
lines under one key; `plan_note`'s `put` keeps the last; both makings get its numbers, the
first's are passed over (`planned_indices`) and never planned again. Round 4's CE26 world (two
returns to #0 at 10 µs, one branch each): a recorded timeline is planned under the other making. -/
theorem ce59_one_key_two_plans_on_resume :
    ((Resume4.judgeR Resume4.keepsRecorded (Resume4.rworlds[5]!) (Source.path #[0, 0, 1, 0, 1, 0])).violation.isSome) = true := by
  native_decide

/-! ## CE58: a return past a full tape's marker, from a cut timeline's archive or a strategy -/

/-- (by computation) The parent cut at its horizon: the archive takes its moments to its end
(main.zig:7374 `open = summary.cut or ...`); a strategy's moment is bounded by the timeline's
start and end alone (main.zig:7625-7631). Either returns to moment 3, past the marker at pull 2:
the child's chain stops there. -/
theorem ce58_cut_or_strategy_past_the_marker :
    ((Tape6.judgeFull { Tape6.fullWorlds[3]! with ver := .vdf8f08b } (Source.path #[0, 1, 1, 3, 0])).violation.isSome) = true ∧
    ((Tape6.judgeFull { Tape6.fullWorlds[4]! with ver := .vdf8f08b } (Source.path #[0, 1, 1, 3, 0])).violation.isSome) = true := by
  native_decide

/-! ## corrupt_reads: a reader that dies during its fault (round 6's list) -/

/-- (by computation) A fault, a read, the reader's death (the OOM killer), the heal: pidfd_open
fails (ESRCH), nothing is said, the read is never named. With the reader's pid reused by another
process: "drain" said, and the heal SIGKILLs that process. -/
theorem dead_reader_unsaid_or_stranger_killed :
    ((Disk5.judgeWith Disk5.everyReadNamedOrSaid 4 (Source.path #[0, 1, 4, 3, 0]) .vdf8f08b false true).violation.isSome) = true ∧
    ((Disk5.judgeWith Disk5.everyReadNamedOrSaid 4 (Source.path #[0, 1, 4, 3, 1]) .vdf8f08b false true).violation.isSome) = false ∧
    ((Disk5.judgeWith Disk5.killsOnlyItsReader 4 (Source.path #[0, 1, 4, 3, 1]) .vdf8f08b false true).violation.isSome) = true := by
  native_decide

end Replica.Theorems7
