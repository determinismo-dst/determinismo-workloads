import Replica.Composer
import Replica.ComposerSearch
import Replica.Verdicts
import Replica.Tape
import Replica.Clock
import Replica.Junit
import Replica.Persist

/-!
# Round 2's theorems

General ones for every input; "(by computation)" ones evaluate a counterexample's minimal case
with `native_decide` (trusting Lean's compiler, as the searches do).
-/

namespace Replica.Theorems2

open Determinismo

/-! ## CE15: the wall clock's start reaches its cap (composer.zig:929-937) -/

/-- The last band of every cap of a second or more ends at the cap itself: whatever the cap
(`--clock-start-max`), a timeline's jump can be the cap exactly. -/
theorem last_band_reaches_the_cap (m : Nat) (h : 1000 ≤ m) :
    (Composer.clockStartBand m (Composer.clockStartBands m - 1)).2 = m := by
  have hq : m / 1000 ≠ 0 := by
    intro h0
    have := (Nat.div_eq_zero_iff_lt (by decide : 0 < 1000)).mp h0
    omega
  have hb : Composer.clockStartBands m = Nat.log2 (m / 1000) + 1 := by
    unfold Composer.clockStartBands
    simp [Nat.not_lt.mpr h]
  rw [hb, Nat.add_sub_cancel]
  unfold Composer.clockStartBand
  simp only
  have hlt : m / 1000 < 2 ^ (Nat.log2 (m / 1000) + 1) := (Nat.log2_lt hq).mp (Nat.lt_succ_self _)
  have hmod : m < 1000 * (m / 1000 + 1) := by
    have := Nat.lt_mul_div_succ m (by decide : 0 < 1000)
    simpa [Nat.mul_comm] using this
  have hpow : 2 ^ (Nat.log2 (m / 1000) + 1) = 2 * 2 ^ Nat.log2 (m / 1000) := by
    rw [Nat.pow_succ]; omega
  have : m ≤ 2 * (1000 * 2 ^ Nat.log2 (m / 1000)) - 1 := by
    have h1 : m / 1000 + 1 ≤ 2 ^ (Nat.log2 (m / 1000) + 1) := hlt
    have h2 : 1000 * (m / 1000 + 1) ≤ 1000 * 2 ^ (Nat.log2 (m / 1000) + 1) := Nat.mul_le_mul_left _ h1
    rw [hpow] at h2
    omega
  exact Nat.min_eq_left this

/-- The default hour (by computation): twelve bands, the last from 2,048 s to 3,600 s. -/
theorem hour_bands :
    Composer.clockStartBands 3600000 = 12 ∧ Composer.clockStartBand 3600000 11 = (2048000, 3600000) := by
  decide

/-! ## CE16: captured output read as a failure (junit.zig:32) -/

def cdataReport : String :=
  "<testsuite>\n<testcase classname=\"api.ErrorsTest\" name=\"renders_503\" time=\"0.1\"><system-out><![CDATA[<error code=\"503\">unavailable</error>]]></system-out></testcase>\n</testsuite>"

theorem captured_error_fails_the_test :
    (Junit.cases cdataReport == [{ name := "api.ErrorsTest::renders_503", failed := true }]) = true := by
  native_decide

/-- The same output escaped (as pytest writes it) passes. -/
theorem escaped_output_passes :
    (Junit.cases "<testsuite><testcase classname=\"a\" name=\"b\"><system-out>&lt;error code=\"503\"/&gt;</system-out></testcase></testsuite>" ==
      [{ name := "a::b", failed := false }]) = true := by
  native_decide

/-! ## CE21: xargs's batches and the report each overwrites (ci.zig:226-233) -/

/-- 2,000 names of 80 bytes against GNU xargs's 131,072-byte buffer: two runs of the runner, the
first one's 1,617 tests never judged (by computation). -/
def names2000 : List String := (List.range 2000).map fun i => s!"tests/test_{i}" ++ String.ofList (List.replicate (80 - (s!"tests/test_{i}").length) 'x')

theorem xargs_loses_the_first_batch :
    (Junit.xargsBatches 131072 64 names2000).length = 2 ∧
    (Junit.testsJudged 131072 64 names2000).length = 2000 - 1617 := by
  native_decide

/-! ## CE17: a fresh file's later range kept, an earlier lost (nodes.zig:943-953) -/

/-- Pages: new, hole, new (a fresh sparse file); one page draw (a hole), then one new page from
range 1 (page 2): after the power loss with the journal committed, page 2 kept, page 0 zeros. -/
def freshCase : Bool :=
  let file := [Persist.Page.new, .hole, .new]
  match (Persist.partialFile file).run { decisions := { source := Source.path #[0, 1, 0, 1] } } with
  | .ok w _ => w == [2] && Persist.kept file w true 2 && !Persist.kept file w true 0
  | .error _ _ => false

theorem fresh_file_hole_before_kept : freshCase = true := by
  native_decide

/-! ## CE18, CE19, CE22: verdicts (by computation) -/

def code : Except String Nat → Option Nat
  | .ok n => some n
  | .error _ => none

/-- CE18: one scenario, a `sometimes` never true in one timeline and an `always` true under the
same message in another: the explorer passes; documented, the sometimes fails (serve says so). -/
theorem sometimes_hidden_by_another_kind :
    code (Verdicts.explorerExit [[{ scenario := 0, events := [.eval .sometimes "m" false] },
                                   { scenario := 0, events := [.eval .always "m" true] }]] 1) = some 0 ∧
    Verdicts.specFailing [{ scenario := 0, events := [.eval .sometimes "m" false] },
                          { scenario := 0, events := [.eval .always "m" true] }] true = [(.sometimes, "m")] := by
  native_decide

/-- CE22: a message declared `reachable` in one timeline and `always_or_unreachable` in another,
neither reached: the verdict is the catalog's first-noted kind's, so the order timelines end. -/
theorem catalog_kind_order :
    code (Verdicts.explorerExit [[{ scenario := 0, events := [.declare .reachable "m"] },
                                   { scenario := 0, events := [.declare .always_or_unreachable "m"] }]] 1) = some 3 ∧
    code (Verdicts.explorerExit [[{ scenario := 0, events := [.declare .always_or_unreachable "m"] },
                                   { scenario := 0, events := [.declare .reachable "m"] }]] 1) = some 0 := by
  native_decide

/-- CE19: a run whose only failure is a declared `reachable` never reached: reaped by serve, its
explorer's 3 (failed); adopted across a restart, its record's summary's 0 (passed). -/
theorem adopted_run_reads_passed :
    code (Verdicts.explorerExit [[{ scenario := 0, events := [.declare .reachable "m"] }]] 1) = some 3 ∧
    code (Verdicts.recordedStatus [{ scenario := 0, events := [.declare .reachable "m"] }]) = some 0 := by
  native_decide

/-! ## CE20: the replay's tables (tape.zig:8, 117, 554-567) -/

/-- Five ingress poll answers (each on the tape) against a table of four: the tape is refused at
the replay's parse, though it was recorded whole (by computation). -/
theorem polls_past_the_table :
    (Tape.parse { overrideMax := 4 } ((List.range 5).map fun p => .override p 1 Tape.ingressReason)).toBool = false ∧
    (Tape.parse { overrideMax := 5 } ((List.range 5).map fun p => .override p 1 Tape.ingressReason)).toBool = true := by
  native_decide

/-! ## CE5 and CE4 at 3939448: what remains (by computation) -/

def violates (p : Composer.Prop') (w : Nat) (path : Array Nat) : Bool :=
  let wd := Composer.worlds[w]!
  (Composer.judge p wd.scenario wd.cmdline wd.consts (Source.path path)).violation.isSome

/-- CE5's other path: parallelism 1, a 600 ms limit (stop at 300 ms): `holding` takes the slot
for 400 ms; the next start waits for the slot with no deadline (composer.zig:849-851, 868) and
starts `next` at 400 ms, past the stop, checked before the wait (795-803). -/
theorem slot_wait_past_half_the_limit : violates Composer.noStartPastHalfLimit 14 #[0, 1] = true := by
  native_decide

/-- CE2's remainder (world 16, the search's second case): min_drive 0, no swarm; drive#3 dies of
its own SIGKILL at 2 ms; nothing reaps before the eventually's kill_all at 3 ms, which reaps it
with killed = true, and SIGKILL is all `by_kill` asks (composer.zig:335-340): reported killed,
never judged. -/
theorem own_sigkill_reported_killed :
    violates Composer.exitsJudged 16 #[1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2] = true := by
  native_decide

/-- CE4's remainder: a singleton timeline of a scenario with `drive_ms_max` (60 ms, no
--timeline) runs its singleton 200 ms, past the longest drawn length and its grace: no length is
drawn for it (composer.zig:712-737). -/
theorem singleton_past_drive_max : violates Composer.driveMaxBound 15 #[0, 1] = true := by
  native_decide

end Replica.Theorems2

namespace Replica.Theorems2

/-- determinismo-ci's "timelines without their JUnit report" (ci.zig:446-470), by computation:
two shards of three timelines; shard 1's two tests reported in all three, shard 2's two tests in
two (its runner died before its report in the third). One timeline stated no test; the count
says none, so `tests_judge` does not say "error" (the shard's own property still fails it). -/
theorem missing_report_hidden_by_another_shard :
    Junit.unreportedTimelines 3 [3, 3, 2, 2] = 0 := by
  decide

end Replica.Theorems2
