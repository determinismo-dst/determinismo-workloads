import Replica.TreeProps
import Replica.Ci
import Replica.Serve3
import Replica.Disk
import Replica.Skew

/-!
# Round 3's theorems

General ones for every input; "(by computation)" ones evaluate a counterexample's minimal case
with `native_decide` (trusting Lean's compiler, as the searches do).
-/

namespace Replica.Theorems3

open Determinismo
open Replica.Tree

/-! ## The tree's shape (main.zig:3961-4004, 4614-4620) -/

/-- A generation is at least the base's 16 timelines, whatever the workers. -/
theorem generationFor_ge_base (w : Nat) : generationBase ≤ generationFor w := by
  unfold generationFor; exact Nat.le_max_left _ _

/-- A judgment never takes more timelines than completed. -/
theorem judgeCount_le (c s : Nat) : judgeCount c s ≤ c := by
  unfold judgeCount
  split
  · exact Nat.le_refl _
  · exact Nat.mul_div_le c s

/-- When the returns' branches fit, fresh starts and returned timelines make the generation. -/
theorem fits_shape (size b : Nat) (h : fits size b = true) : roots size + nodes size b * b = size := by
  unfold fits at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨hb, hmod⟩ := h
  unfold nodes
  have hr : roots size ≤ size := Nat.div_le_self size 4
  have := Nat.div_add_mod (size - roots size) b
  rw [hmod, Nat.add_zero] at this
  rw [Nat.mul_comm] at this
  omega

/-! ## CE24: the tree depends on the workers (main.zig:3973-3975, 8883) -/

/-- One worker plans generations of 16, 32 workers generations of 32. -/
theorem generation_for_workers : generationFor 1 = 16 ∧ generationFor 32 = 32 ∧ generationFor 40 = 32 := by
  decide

def zigJobs : Tree.Config :=
  { label := "the default generation (generation_for(jobs)), pipeline 3, 32 workers, 56 timelines",
    pipeline := 3, jobs := 32, total := 56, children := 4 }

/-- (by computation) The same seed, 32 workers against one: timeline 48 starts elsewhere. -/
theorem same_seed_other_tree :
    ((sameTimelines zigJobs generationFor (Source.seeded 0)).violation.isSome) = true := by
  native_decide

def timingJobs : Tree.Config := { label := "timing", pipeline := 2, jobs := 2, total := 12 }

/-- (by computation) A fixed generation of 4, two workers: the finishing order alone. -/
theorem finishing_order_other_tree :
    ((sameTimelines timingJobs (fun _ => 4) (Source.seeded 1)).violation.isSome) = true := by
  native_decide

/-! ## CE23: a strategy's seed lost to the tree's returns -/

def sameSeedWorld : Tree.Config :=
  { label := "same_seed.py", total := 12, strategy := some { seed := some 66 }, ver := .v3939448 }

/-- (by computation) With same_seed.py, a returned timeline's tape replays another timeline. -/
theorem strategy_seed_tape_replays_another :
    (match (runOf sameSeedWorld (Source.seeded 1)).1 with
     | .ok s => (replaysFromTape.check sameSeedWorld s).isSome
     | .error _ => false) = true := by
  native_decide

/-- (by computation) ... and a node replayed from the parent's start is not its state. -/
theorem strategy_seed_node_elsewhere :
    (match (runOf sameSeedWorld (Source.seeded 0)).1 with
     | .ok s => (nodeIsParentsState.check sameSeedWorld s).isSome
     | .error _ => false) = true := by
  native_decide

/-! ## CE25: the archive returns to a repeat (main.zig:6383, 6420, 7016-7026) -/

def twin (i : Nat) : Summary :=
  { index := i, startNs := 0, endNs := 65, behaviors := [{ hash := 7, vtime := 20, label := "line 1" }],
    traceHash := 99, lastPull := 50 }

def twinPlan : List Planned := [{ index := 0, seed := 1 }, { index := 1, seed := 2 }]

/-- (by computation) Timeline 1 is timeline 0 again (one trace); archive_add makes it the cell's
second place, the one its next return goes to. -/
theorem repeat_is_a_place :
    let st := archiveAdd (archiveAdd {} twinPlan (twin 0)) twinPlan (twin 1)
    (st.cells.map fun c => c.places.toList.map (·.branch)) == #[[0, 1]] &&
    ({ st.cells[0]! with visits := 1 }).place.branch == 1 := by
  native_decide

/-! ## CE26: two returns at one moment (main.zig:7081-7123, 7323-7339) -/

def oneCell : TreeState :=
  { cells := #[{ hash := 1000, places := #[{ branch := 0, vtime := 1000001 }], label := "sometimes \"leader elected\": true", sought := true }] }

def frontierAtIt : List TreeReturn :=
  [{ branch := 0, vtime := 1000001, why := "Returned to #0 just after it first reached it: its frontier.", earliest := some 1 }]

/-- (by computation) The Zig's default shape (16, 4 from each): the frontier's return and the
archive's return to the same moment. -/
theorem frontier_and_archive_one_moment :
    (match (archiveReturns { oneCell with ver := .va7fe05d } 16 4 frontierAtIt).run { decisions := { source := Source.path #[] } } with
     | .ok (_, rs) _ => rs.map (fun r => (r.branch, r.vtime)) == [(0, 1000001), (0, 1000001)]
     | .error _ _ => false) = true := by
  native_decide

/-! ## CE27, CE28: determinismo-ci (ci.zig:277-314) -/

open Replica.Ci in
def ciCfg : Cfg := { label := "", tests := ["t1", "t2"], timelines := 3, ver := .v3939448 }

open Replica.Ci in
def hangJob : Job :=
  { shardCount := 1, outcomes := [.passes, .passes, .hangs],
    stated := [statedOf ciCfg 1 0 .passes, statedOf ciCfg 1 1 .passes, statedOf ciCfg 1 2 .hangs] }

open Replica.Ci in
/-- (by computation) One timeline of three hangs: "error", "failing in 0 of 3", exit 1; the
docs: flaky, exit 2. -/
theorem hang_is_an_error :
    (verdictOf ciCfg hangJob).job == "error" && (verdictOf ciCfg hangJob).exit == 1 &&
    (verdictOf ciCfg hangJob).shards == [(1, "error", 0, 2)] && documented ciCfg hangJob == "flaky" := by
  native_decide

open Replica.Ci in
def sessionCfg : Cfg := { label := "", tests := ["t1"], timelines := 3, junit := false, flakyPasses := true, sessions := true, ver := .v3939448 }

open Replica.Ci in
def failingWithSession : Job :=
  { shardCount := 1, outcomes := [.fails [0], .fails [0], .fails [0]],
    stated := [statedOf sessionCfg 1 0 (.fails [0]), statedOf sessionCfg 1 1 (.fails [0]), statedOf sessionCfg 1 2 (.fails [0]),
               { statedOf sessionCfg 1 0 .passes with timeline := 3, session := true }] }

open Replica.Ci in
/-- (by computation) A shard failing in its 3 timelines, a session on it passing: "flaky",
exit 0 with --flaky-passes; its timelines alone: "fail", exit 1. -/
theorem session_turns_a_failing_job_green :
    (verdictOf sessionCfg failingWithSession).job == "flaky" && (verdictOf sessionCfg failingWithSession).exit == 0 &&
    (verdictOf sessionCfg { failingWithSession with stated := failingWithSession.stated.filter (!·.session) }).exit == 1 := by
  native_decide

/-! ## CE29: a resumed run's state (main.zig:2186-2192, 3460-3462) -/

open Replica.Serve3 in
/-- (by computation) Timeline 0 failed before the stop, timeline 1 runs after the resume and
passes: the explorer exits 0, serve says passed; the properties fail. -/
theorem resumed_reads_passed :
    let tls : List TL := [{ alwaysFalse := true }, {}]
    state (explorerExit (tls.drop 1)) == "passed" && runFailing tls := by
  native_decide

open Replica.Serve3 in
/-- (by computation) A sometimes made true only before the stop: the resumed run fails it. -/
theorem resumed_reads_failed :
    let tls : List TL := [{ sometimesHit := true, sometimesTrue := true }, { sometimesHit := true }]
    state (explorerExit (tls.drop 1)) == "failed" && !runFailing tls := by
  native_decide

/-! ## CE30: the coverage gate (serve.zig:703-752; sdk/zig/determinismo.zig:2122-2200) -/

open Replica.Serve3 in
/-- (by computation) An instrumented system whose setup ran edge 2 and whose first 4 timelines
run edge 2 again: none reports a coverage event, the gate stops it. -/
theorem instrumented_run_stopped :
    (match (drawGate { label := "", instrumented := some true, ver := .v3939448 }).run
        { decisions := { source := Source.path #[0, 0, 1, 3, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1] } } with
     | .ok g _ => g.instrumented && g.stoppedAt.isSome && g.rows.all (·.2 == 0)
     | .error _ _ => false) = true := by
  native_decide

/-! ## CE31: corrupt_reads stores a corrupted byte (nodes.zig:1979-1983) -/

open Replica.Disk in
def corruptWorld : DW := { label := "", pages := 1, bytes := 2, steps := 4, failure := some .corruptReads }

open Replica.Disk in
/-- (by computation) A write of byte 1 to a page not in the cache, during corrupt_reads (byte 1
reads 1): the page stored after the heal is [1, 0], byte 0 never written 1. -/
theorem corrupt_read_stored :
    (match (scenario corruptWorld).run { decisions := { source := Source.path #[0, 1, 2, 1, 0, 0, 0, 0, 0, 0] } } with
     | .ok _ s => s.device.toList == [[1, 0]] && (storedIntact.check corruptWorld s).isSome
     | .error _ _ => false) = true := by
  native_decide

open Replica.Disk in
/-- (by computation) writeback_s 5 s, its flusher drawn off and never switched: a power loss at
30 s loses 30 s of writes. -/
theorem writeback_off_loses_all :
    (match (writebackLoss 5 30).run { decisions := { source := Source.path #[1, 1, 1, 1, 1, 1, 1] } } with
     | .ok (age, _) _ => age == 30
     | .error _ _ => false) = true := by
  native_decide

/-! ## Clock skews (faults.zig:1728-1739) -/

open Replica.Skew in
/-- `skew_clamp`'s fold keeps its bounds: low at least each other's skew less the maximum, high
at most each other's plus it. -/
theorem clamp_fold (m : Int) (others : List Int) (l h : Int) :
    let r := others.foldl (fun (lh : Int × Int) o => (max lh.1 (o - m), min lh.2 (o + m))) (l, h)
    l ≤ r.1 ∧ r.2 ≤ h ∧ ∀ o ∈ others, o - m ≤ r.1 ∧ r.2 ≤ o + m := by
  induction others generalizing l h with
  | nil => simp
  | cons o os ih =>
    simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp]
    obtain ⟨h1, h2, h3⟩ := ih (max l (o - m)) (min h (o + m))
    refine ⟨by omega, by omega, ⟨by omega, by omega⟩, h3⟩

open Replica.Skew in
/-- A clamped skew is within the maximum, and within it of every other skew under way. -/
theorem skewClamp_within (offset m : Int) (others : List Int) (rem r : Int)
    (hr : skewClamp offset m others rem = some r) :
    -m ≤ r ∧ r ≤ m ∧ ∀ o ∈ others, o - m ≤ r ∧ r ≤ o + m := by
  unfold skewClamp at hr
  have hf := clamp_fold m others (max (-m) (rem - m)) m
  simp only at hf hr
  obtain ⟨hl, hh, ho⟩ := hf
  split at hr
  · cases hr
  · cases hr
    rename_i hlh
    refine ⟨by omega, by omega, ?_⟩
    intro o ho'
    obtain ⟨a, b⟩ := ho o ho'
    exact ⟨by omega, by omega⟩

end Replica.Theorems3
