import Replica.Resume4
import Replica.Durable
import Replica.Ci4
import Replica.Steer4
import Replica.Clock4
import Replica.Holders4

/-!
# Round 4's theorems

General ones for every input; "(by computation)" ones evaluate a counterexample's minimal case
with `native_decide` (trusting Lean's compiler, as the searches do).
-/

namespace Replica.Theorems4

open Determinismo

/-! ## Holders (holders.zig:1003-1011, 1275-1293) -/

/-- A known length's spacing is never below 10 ms. -/
theorem spacing_ge_min (l : Nat) : Holders4.spacingMin ≤ Holders4.spacing (some l) := by
  unfold Holders4.spacing; exact Nat.le_max_left _ _

/-- The periodic holders are 8 spacings apart. -/
theorem period_eight (sp : Nat) : Holders4.period sp = sp * 8 := by
  unfold Holders4.period Holders4.perTimelineMax; rfl

/-- (by computation) A behavior's holder is the one `drop` removes: the return just after it
replays 10,002 µs from the holder before (spacing 10,000). -/
theorem new_behavior_holder_dropped :
    Holders4.holdersOf 0 640000 [{ vtime := 1, new := true }, { vtime := 11001, new := true }] =
      #[1000, 91002, 171002, 251002, 331002, 411002, 491002, 571002] := by
  native_decide

/-! ## CE32 to CE34: a resumed tree -/

open Replica.Resume4 in
/-- (by computation) CE32: generation 0's returns to #0, #1 and #2 (one branch each); only #2's
child (timeline 6) recorded: `recorded_returns` gives #2 alone, the resumed tree numbers its
child 4, and timeline 6's record is judged as a fresh timeline. -/
theorem ce32_dropped_return :
    ((judgeR keepsRecorded ({ rworlds[0]! with ver := .va7fe05d }) (Source.path #[0, 0, 0, 0, 1, 0])).violation.isSome) = true := by
  native_decide

open Replica.Resume4 in
/-- (by computation) CE32: two returns to one moment (CE26) are one key: the second's child
(timeline 5) is judged as the third return's. -/
theorem ce32_merged_returns :
    ((judgeR keepsRecorded ({ rworlds[5]! with ver := .va7fe05d }) (Source.path #[0, 0, 1, 0, 1, 0])).violation.isSome) = true := by
  native_decide

open Replica.Resume4 in
/-- (by computation) CE33: #1's children all recorded (ready), #0's not: the resumed tree plans
#1's first (timelines 5, 6), #0's after (7, 8), its nodes made in the makings' order. -/
theorem ce33_ready_first :
    ((judgeR keepsRecorded ({ rworlds[2]! with ver := .va7fe05d }) (Source.path #[0, 0, 1, 1, 1, 0])).violation.isSome) = true ∧
    ((judgeR startsWhereItsPathSays ({ rworlds[2]! with ver := .va7fe05d }) (Source.path #[0, 0, 1, 1, 1, 0])).violation.isSome) = true := by
  native_decide

open Replica.Resume4 in
/-- (by computation) CE34: a filler (timeline 7) taken between #0's and #1's timelines: the resume
cuts the record and numbers the generation again. -/
theorem ce34_filler_cut :
    ((judgeR neverCut ({ rworlds[3]! with ver := .va7fe05d }) (Source.path #[0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0])).violation.isSome) = true ∧
    ((judgeR keepsRecorded ({ rworlds[3]! with ver := .va7fe05d }) (Source.path #[0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0])).violation.isSome) = true := by
  native_decide

/-! ## CE35: sync_stall and durable_crash share one arm -/

/-- (by computation) A sync_stall, then a durable_crash over it (the overlap drawn): the node's
syncs are crash decisions while the stall lasts. -/
theorem ce35_crash_replaces_stall :
    ((Durable.judgeD 3 8 (Source.path #[0, 1, 0, 0, 4]) .v3939448).violation.isSome) = true := by
  native_decide

/-- (by computation) A durable_crash, a sync_stall over it that ends first: the durable_crash
goes on with nothing armed. -/
theorem ce35_stall_end_disarms_crash :
    ((Durable.judgeD 4 8 (Source.path #[1, 0, 0, 0, 2, 4]) .v3939448).violation.isSome) = true := by
  native_decide

/-! ## CE36: lost writes read back stale before any crash -/

/-- (by computation) Two writes, the disk drops writes, the flusher writes back (dropped), the
page evicted: the node reads 0, no crash came. -/
theorem ce36_lost_write_read_back :
    ((Durable.judgeK Durable.lostUntilCrash { label := "", steps := 6, failures := [.lostWrites] }
        (Source.path #[0, 0, 3, 2, 8, 6])).violation.isSome) = true := by
  native_decide

/-! ## CE37: tests_judge's reports counted over the whole run -/

/-- The most timelines any test was hit in, over a list of (message, hit, failing). -/
def reportedOf (props : List (String × Nat × Nat)) : Nat := props.foldl (fun m p => max m p.2.1) 0

theorem foldl_max_ge (props : List (String × Nat × Nat)) (m : Nat) :
    m ≤ props.foldl (fun m p => max m p.2.1) m := by
  induction props generalizing m with
  | nil => exact Nat.le_refl _
  | cons p rest ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

theorem foldl_max_mem (props : List (String × Nat × Nat)) (m : Nat) (p : String × Nat × Nat)
    (h : p ∈ props) : p.2.1 ≤ props.foldl (fun m p => max m p.2.1) m := by
  induction props generalizing m with
  | nil => cases h
  | cons q rest ih =>
    simp only [List.foldl_cons]
    cases h with
    | head => exact Nat.le_trans (Nat.le_max_right _ _) (foldl_max_ge rest _)
    | tail _ h' => exact ih _ h'

/-- Any one test reported in a whole shard's timelines makes `unreported` 0 (ci.zig:458, 474):
whatever another shard's timelines did. -/
theorem unreported_zero_of_one_full (props : List (String × Nat × Nat)) (timelines : Nat)
    (p : String × Nat × Nat) (h : p ∈ props) (full : timelines ≤ p.2.1) :
    timelines - reportedOf props = 0 := by
  unfold reportedOf
  have := foldl_max_mem props 0 p h
  omega

/-- (by computation) Two shards of 2 timelines: shard 2's runner dies in one before its report;
tests_judge says 0 timelines without their report. -/
theorem ce37_unreported_missed :
    ((Ci.judgeC Ci4.unreportedCounted { Ci4.worlds37[0]! with ver := .v3939448 } (Source.path #[0, 0, 0, 3])).violation.isSome) = true := by
  native_decide

/-! ## CE38: the coverage gate on an uncovered CI job -/

/-- (by computation) docs/CI.md's own Jest config (8 shards of 3): its timelines' first four ended
one look each, serve stops the run, every shard "error", exit 1. -/
theorem ce38_jest_job_errors :
    ((Ci4.judgeG { label := "", shards := 8, timelines := 3, runners := [.jest], ver := .v62e06e3 } (Source.path #[0, 0, 0, 0])).violation.isSome) = true := by
  native_decide

/-- (by computation) The same job when all 24 timelines end before the gate's first look: pass. -/
theorem ce38_same_job_passes_on_a_bigger_host :
    ((Ci4.judgeG { label := "", shards := 8, timelines := 3, runners := [.jest] } (Source.path #[23])).violation.isSome) = false := by
  native_decide

/-! ## CE39: a targeted run's report -/

/-- (by computation) Generations of 2, 3 timelines: the third ran the hunk and is never judged:
"NEVER RAN". -/
theorem ce39_never_ran :
    ((Steer4.judgeS { Steer4.sworlds[0]! with ver := .v3939448 } (Source.path #[0, 0, 1])).violation.isSome) = true := by
  native_decide

end Replica.Theorems4
