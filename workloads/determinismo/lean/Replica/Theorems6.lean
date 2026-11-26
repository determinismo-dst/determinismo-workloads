import Replica.Theorems5
import Replica.Request6
import Replica.Tape6
import Replica.Aimed6
import Replica.Steer4
import Replica.Ci4

/-!
# Round 6's theorems

As before: general ones for every input, and "(by computation)" ones that evaluate a minimal case
with `native_decide` (trusting Lean's compiler, as the searches do). The recheck's: each round 2
to 5 finding's minimal case on a7fe05d's code (the models' default since round 6); round 5's
theorems about 62e06e3's code stay in Theorems5, pinned to `.v62e06e3`. Then round 6's
counterexamples.
-/

namespace Replica.Theorems6

open Determinismo
open Replica.Theorems2 (violates violatesAt code cdataReport)

/-! ## The recheck: round 5's findings on a7fe05d -/

/-- CE40 fixed (ci.zig:537-552): the run line in a subshell; `exit`, `exec` and a trailing
comment leave only the subshell: every run's report moved aside, every name judged. -/
theorem ce40_exit_run_line_judges_every_run :
    Ci5.judged .va7fe05d .exits Theorems5.twoRuns = ["a", "b", "c"] ∧
    Ci5.judged .va7fe05d .execs Theorems5.twoRuns = ["a", "b", "c"] ∧
    Ci5.judged .va7fe05d .comment Theorems5.twoRuns = ["a", "b", "c"] := by
  decide

/-- CE40 fixed for `set -e`: the failing first run's report is moved aside too. -/
theorem ce40_set_e_judges_the_failing_run :
    Ci5.judged .va7fe05d .setE [{ names := ["a", "b"], failed := true }, { names := ["c"], failed := false }] = ["a", "b", "c"] := by
  decide

theorem subshell_parts (line : Ci5.RunLine) (runs : List Ci5.Run) (f : Ci5.Files) :
    (runs.foldl (Ci5.step .va7fe05d line) f).parts = f.parts ++ runs.map (·.names) := by
  induction runs generalizing f with
  | nil => simp
  | cons r rest ih =>
    simp only [List.foldl_cons, List.map_cons]
    rw [ih]
    simp [Ci5.step, Ver.sinceA7]

/-- For every run line's form and every list of xargs runs (none stopping xargs), a7fe05d judges
every name: CE40's property, for all inputs. -/
theorem ce40_subshell_keeps_every_run (line : Ci5.RunLine) (runs : List Ci5.Run) (h : runs ≠ []) :
    Ci5.judged .va7fe05d line runs = runs.flatMap (·.names) := by
  unfold Ci5.judged
  have hp := subshell_parts line runs {}
  simp only [List.nil_append] at hp
  have hne : runs.map (·.names) ≠ [] := by
    cases runs with
    | nil => exact absurd rfl h
    | cons _ _ => simp
  simp [hp, hne, List.flatMap]

/-- CE41 fixed (junit.zig:77, 92-103): the closing tag inside the CDATA is the output's. -/
theorem ce41_closing_tag_in_cdata_passes :
    (Junit.cases Theorems5.closingTagReport == [{ name := "junit.ReportTest::renders_an_error", failed := false }]) = true := by
  native_decide

/-- CE42 fixed (composer.zig:801-804): world 17's decisions; the second phase's stop is half the
limit since the drivers began: no start past it. -/
theorem ce42_second_phase_stops_at_half : violates Composer.noStartPastHalfLimit 17 #[0, 0, 0, 1, 1, 0, 1] = false := by
  native_decide

/-- CE43 fixed (nodes.zig:2340-2356): the read queued before the heal; the heal waits for the
reader, which names it up to the end marker and exits; the instance removed. -/
theorem ce43_drained_at_the_heal :
    ((Disk5.judgeWith Disk5.everyReadNamed 4 (Source.path #[0, 0, 1, 3, 1])).violation.isSome) = false := by
  native_decide

/-- CE43's drain cut (the reader not scheduled within 2 s): the read unnamed, but the fault says
so ("drain"); the next fault clears what was left (2199-2205): nothing named under it. -/
theorem ce43_starved_reader_said :
    ((Disk5.judgeWith Disk5.everyReadNamed 4 (Source.path #[0, 0, 1, 3, 0, 1])).violation.isSome) = true ∧
    ((Disk5.judgeWith Disk5.everyReadNamedOrSaid 4 (Source.path #[0, 0, 1, 3, 0, 1])).violation.isSome) = false ∧
    ((Disk5.judgeWith Disk5.namedRight 6 (Source.path #[0, 0, 1, 3, 0, 0, 0, 2])).violation.isSome) = false := by
  native_decide

/-- CE44 still there (only composer.zig:916-923's comment changed): an objective's return, the
jump at the 30-minute cap: the setup's hour token used 300,999 ms past its expiry. -/
theorem ce44_still_past_the_hour :
    ((Clock5.judge (Clock5.worlds[0]!) (Source.path #[10, 776000, 0, 299999, 0, 600000, 0, 0])).violation.isSome) = true := by
  native_decide

/-- CE45 still there (main.zig:2241-2257 unchanged): the complete resume judges no catalog, and
(round 6) neither does a resume whose missing number is a session's (2196-2199, 2865). -/
theorem ce45_complete_resume_still_skips_the_catalog :
    code (Verdicts.explorerExit [[{ scenario := 0, events := [.declare .reachable "r"] },
                                   { scenario := 0, events := [.declare .reachable "r"] }]] 1) = some 3 ∧
    code (Resume5.resumedExit .va7fe05d [{ scenario := 0, events := [.declare .reachable "r"] },
                                         { scenario := 0, events := [.declare .reachable "r"] }] 2 1000) = some 0 ∧
    code (Resume5.resumedExitWithSession .va7fe05d [{ scenario := 0, events := [.declare .reachable "r"] },
                                                    { scenario := 0, events := [.declare .reachable "r"] }] 2 1000 true) = some 0 := by
  native_decide

/-- CE46 fixed (report.zig:51-78, 551-588): no room: `always "b"` false is in the line, the
resumed run fails as the run does. -/
theorem ce46_every_property_recorded :
    code (Resume5.resumedExit .va7fe05d [{ scenario := 0, events := [.eval .always "a" true, .eval .always "b" false] }] 1 1) = some 3 := by
  native_decide

/-- CE47 fixed (main.zig:1293-1297; serve.zig:5836-5851): serve keeps the resume's own exit, 3. -/
theorem ce47_adopted_resume_keeps_its_exit :
    code (Resume5.adoptedStatus [{ scenario := 0, events := [.declare .reachable "r"] },
                                 { scenario := 0, events := [.declare .reachable "r"] }] 1 false .va7fe05d) = some 3 := by
  native_decide

/-- CE48 fixed (tape.zig:146-149, 186-198, 605, 651): three reasons, the table sized from the
tape: the replay reads it. -/
def threeReasonsA7 : Tape.VM × Tape.VM :=
  Tape.recordReplay { label := "", consts := { reasonMax := 2 } }
    { steps := List.replicate 3 (.pull .plain), advice := [(0, 0, "r", true), (1, 0, "r", true), (2, 0, "r", true)],
      forkIndex := 0, outsideRecord := 0, outsideReplay := 1, perturb := .none }

theorem ce48_reasons_sized_from_the_tape : threeReasonsA7.2.error = none := by
  native_decide

/-! ## The recheck: earlier findings whose code a7fe05d changed -/

/-- CE23 fixed (main.zig:6399-6410, 6490 `plan_adopt_ran`): with same_seed.py, the returned
timeline's tape replays its own prefix, and the node replayed from the parent's start is its
state. -/
theorem ce23_strategy_seed_adopted :
    (match (Tree.runOf { Theorems3.sameSeedWorld with ver := .va7fe05d } (Source.seeded 1)).1 with
     | .ok s => (Tree.replaysFromTape.check { Theorems3.sameSeedWorld with ver := .va7fe05d } s).isSome
     | .error _ => true) = false ∧
    (match (Tree.runOf { Theorems3.sameSeedWorld with ver := .va7fe05d } (Source.seeded 0)).1 with
     | .ok s => (Tree.nodeIsParentsState.check { Theorems3.sameSeedWorld with ver := .va7fe05d } s).isSome
     | .error _ => true) = false := by
  native_decide

/-- CE30 fixed for a run whose setup ran in it (serve.zig:703-727, 750): round 3's draws, the
setup's coverage in its events/setup.jsonl: not stopped. -/
theorem ce30_setup_covered_not_stopped :
    (match (Serve3.drawGate { label := "", instrumented := some true }).run
        { decisions := { source := Source.path #[0, 0, 1, 3, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1] } } with
     | .ok g _ => g.stoppedAt.isNone
     | .error _ _ => false) = true := by
  native_decide

/-- CE38 fixed (serve.zig:765-769): docs/CI.md's Jest job, its first four timelines ended one
look each: never stopped, every shard passes, exit 0. -/
theorem ce38_ci_job_runs_uncovered :
    ((Ci4.judgeG { label := "", shards := 8, timelines := 3, runners := [.jest] } (Source.path #[0, 0, 0, 0])).violation.isSome) = false := by
  native_decide

/-- CE39 fixed (main.zig:4462-4464, 6426-6445): the timeline no judgment took is counted. -/
theorem ce39_last_timeline_counted :
    ((Steer4.judgeS (Steer4.sworlds[0]!) (Source.path #[0, 0, 1])).violation.isSome) = false := by
  native_decide

/-- CE21, CE27, CE28, CE29 stay fixed on a7fe05d (round 5's minimal cases). -/
theorem ce21_ce27_ce28_ce29_still_fixed :
    Ci5.judged .va7fe05d .plain Theorems5.twoRuns = ["a", "b", "c"] ∧
    (Ci.verdictOf { Theorems3.ciCfg with ver := .va7fe05d } Theorems3.hangJob).job = "flaky" ∧
    (Ci.verdictOf { Theorems3.sessionCfg with ver := .va7fe05d } Theorems3.failingWithSession).job = "fail" ∧
    code (Resume5.resumedExit .va7fe05d [{ scenario := 0, events := [.eval .always "a" false] },
                                         { scenario := 0, events := [.eval .always "a" true] }] 1 1000) = some 3 := by
  native_decide

/-! ## CE49: captured output that prints test cases -/

/-- A JUnit writer's test that prints a report (two cases, the second failing) in its
`<system-out>`'s CDATA, and passes. -/
def printedReport : String :=
  "<testsuite><testcase classname=\"junit.WriterTest\" name=\"writes_a_report\" time=\"0.1\"><system-out><![CDATA[<testsuite><testcase classname=\"printed\" name=\"ok\"></testcase><testcase classname=\"printed\" name=\"bad\"><failure message=\"x\"/></testcase></testsuite>]]></system-out></testcase></testsuite>"

/-- A failing test whose output (before its failure element) printed `</testcase>`. -/
def cutReport : String :=
  "<testsuite><testcase classname=\"junit.WriterTest\" name=\"closes_a_case\" time=\"0.1\"><system-out><![CDATA[</testcase>]]></system-out><failure message=\"expected 2 cases\"/></testcase></testsuite>"

/-- (by computation) `cases` (junit.zig:14-20) ends a case's body at the first `</testcase>`,
the one in the CDATA, and goes on from there: the printed `printed::bad` is judged failing (in
every timeline: the job fails); and a test's real failure after such output is never seen. -/
theorem ce49_printed_cases_judged :
    (Junit.cases printedReport .va7fe05d == [{ name := "junit.WriterTest::writes_a_report", failed := false },
                                    { name := "printed::bad", failed := true }]) = true ∧
    (Junit.cases cutReport .va7fe05d == [{ name := "junit.WriterTest::closes_a_case", failed := false }]) = true := by
  native_decide

/-! ## CE50: the coverage gate on a run from a snapshot -/

/-- (by computation) Round 3's draws on a run from a snapshot (its setup another run's: its
events/setup.jsonl empty): stopped as uninstrumented. -/
theorem ce50_snapshot_run_stopped :
    (match (Serve3.drawGate { label := "", instrumented := some true, fromSnapshot := some true, ver := .va7fe05d }).run
        { decisions := { source := Source.path #[0, 0, 1, 3, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1] } } with
     | .ok g _ => g.instrumented && g.stoppedAt.isSome && g.rows.all (·.2 == 0)
     | .error _ _ => false) = true := by
  native_decide

/-! ## CE51: a command-line run's request -/

/-- (by computation) a7fe05d's fix: `--clock-start-max 0` is booted again; `--timeline-limit
30s`, `--no-swarm`, `--epoch`, `--timer-slack-us`, `--timer-landing-permille` and `--injector`
are not: every tape refused. A run recorded by 62e06e3's explorer with `--clock-start-max 0`
stays refused by a7fe05d's serve. -/
theorem ce51_analysis_boots_other_inputs :
    Request6.inputs (Request6.analysisOfCommandLine .va7fe05d { clockStartMaxMs := some 0 }) = Request6.inputs { clockStartMaxMs := some 0 } ∧
    Request6.inputs (Request6.analysisOfCommandLine .va7fe05d { timelineLimitMs := 30000 }) ≠ Request6.inputs { timelineLimitMs := 30000 } ∧
    Request6.inputs (Request6.analysisOfCommandLine .va7fe05d { swarm := false }) ≠ Request6.inputs { swarm := false } ∧
    Request6.inputs (Request6.analysisOfCommandLine .va7fe05d { epoch := some 1893456000 }) ≠ Request6.inputs { epoch := some 1893456000 } ∧
    Request6.inputs (Request6.analysisOfCommandLine .va7fe05d { timerSlackUs := 50 }) ≠ Request6.inputs { timerSlackUs := 50 } ∧
    Request6.inputs (Request6.analysisOfCommandLine .va7fe05d { injectors := ["./chaos"] }) ≠ Request6.inputs { injectors := ["./chaos"] } ∧
    Request6.inputs (Request6.analysisOfCommandLine .v62e06e3 { clockStartMaxMs := some 0 }) ≠ Request6.inputs { clockStartMaxMs := some 0 } := by
  native_decide

/-- For every run serve started, its analyses boot its inputs (the posted request and serve's
machine): the property holds there, for all inputs. -/
theorem serve_run_boots_its_inputs (a : Request6.Asked) :
    Request6.inputs (Request6.analysisOfServeRun a) = Request6.inputs a := rfl

/-- The Zig's sizes at a7fe05d (round 7: the model's default is df8f08b's). -/
def a7 : Tape6.SC := { ver := .va7fe05d }

/-! ## CE52: a session's steps on its tape -/

/-- (by computation) The Zig's sizes. The parse: a `det:ask` step of 42,236 bytes (a 31 KiB REPL
message in base64) does not fit the line parse's 64 KiB scratch (OutOfMemory); 42,235 bytes do.
The recorder: one of 131,072 bytes (a 96 KiB message) has its head taped unfinished, the next
line running on from it (a parse with any scratch fails). And past steps_max: TapeTooLong. -/
theorem ce52_long_step_unreadable :
    (Tape6.parse a7 (Tape6.record a7 [.step 42236 0, .step 7 0])).toOption.isNone = true ∧
    (Tape6.parse a7 (Tape6.record a7 [.step 42235 0, .step 7 0])).toOption.isSome = true ∧
    (Tape6.parse { a7 with scratchMax := 1000000 } (Tape6.record a7 [.step 131072 0, .step 7 0])).toOption.isNone = true ∧
    (Tape6.parse { a7 with scratchMax := 1000000 } (Tape6.record a7 [.step 131068 0, .step 7 0])).toOption.isSome = true ∧
    (Tape6.parse { a7 with stepsMax := 2 } (Tape6.record a7 [.step 4 0, .step 4 0, .step 4 0])).toOption.isNone = true := by
  native_decide

/-! ## CE53: a return past a full tape's marker -/

/-- (by computation) A cap of one override; the parent's pulls: a draw, two overrides: its tape
full at pull 2. A return to its moment 3 from a holder: the child runs; its chain stops at
TapeFull. -/
theorem ce53_child_of_a_full_tape_never_replays :
    ((Tape6.judgeFull (Tape6.fullWorlds[2]!) (Source.path #[0, 1, 1, 3, 0])).violation.isSome) = true := by
  native_decide

/-! ## CE54: the byte an aimed corrupt_reads names -/

/-- (by computation) The aimed extent is block 1; the hole before it written at ext4's goal
(block 0); a read of both: dm changes block 1's byte, the event names block 0's. Over two aimed
extents with the hole between them filled: two bytes changed, one named. -/
theorem ce54_named_byte_not_the_changed_one :
    Aimed6.goal [none, some 1] 0 = some 0 ∧
    Aimed6.changed [(1, 1)] 0 2 = [1] ∧ Aimed6.named [(1, 1)] 0 2 = some 0 ∧
    Aimed6.goal [some 0, none, some 2] 1 = some 1 ∧
    Aimed6.changed [(0, 1), (2, 1)] 0 3 = [0, 2] ∧ Aimed6.named [(0, 1), (2, 1)] 0 3 = some 0 := by
  decide

/-- For every read inside one aimed extent, the byte named is the byte changed (the case the
fix of CE31 was for: a page read to merge a write). -/
theorem read_inside_an_extent_named_right (s c start count : Nat) (h1 : s ≤ start)
    (h2 : start + count ≤ s + c) (h3 : 0 < count) :
    Aimed6.changed [(s, c)] start count = [start] ∧ Aimed6.named [(s, c)] start count = some start := by
  have hov : start < s + c ∧ s < start + count := by omega
  have hmax : max start s = start := by omega
  constructor
  · simp only [Aimed6.changed, List.filterMap_cons, List.filterMap_nil]
    simp [hov, hmax]
  · simp [Aimed6.named, hov]

/-! ## CE55: a runner's 255 stops xargs -/

/-- (by computation) Two xargs batches; the first run's runner exits 255 (mocha with 255 failing
tests): xargs runs no more; "c" is never run, never judged, at every version. -/
theorem ce55_255_stops_the_shard :
    Ci5.judged .va7fe05d .plain (Ci5.xargsRuns [{ names := ["a", "b"], failed := true, stops := true },
                                               { names := ["c"], failed := false }]) = ["a", "b"] := by
  decide

end Replica.Theorems6
