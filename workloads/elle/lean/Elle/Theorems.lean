import Elle.ListAppend
import Elle.RwRegister
import Elle.Cases
import Elle.ClosedPredicate

/-!
# Theorems

General theorems are proved by hand. Facts about particular histories and about Elle's finite
lattice are proved by evaluation (`native_decide`: the compiled replica and specification
decide them; trusted as Lean's compiler is).
-/

namespace Elle.Theorems

open Elle Elle.ListAppend

/-! ## The incompatible-order check (list_append.clj:318)

Elle sorts a key's observed values by length and compares only neighbours: "If a total order
exists, we should be able to sort their values by size and each one will be a prefix of the
next." Checking neighbours suffices: neighbours each a prefix of the next makes every pair a
prefix, so the values lie on one trace (the paper's §4.2.1 "consistent" observation). -/

theorem isPrefix_iff (a b : List Int) : isPrefix a b = true ↔ a <+: b := by
  unfold isPrefix
  constructor
  · intro h
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    exact List.prefix_iff_eq_take.mpr h.2
  · intro h
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨h.length_le, List.prefix_iff_eq_take.mp h⟩

/-- Neighbours each a prefix of the next: every earlier value is a prefix of every later one. -/
theorem neighbours_prefix_pairwise :
    ∀ (vs : List (List Int)), (∀ p ∈ vs.zip (vs.drop 1), p.1 <+: p.2) → vs.Pairwise (· <+: ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: rest, h => by
    have hab : a <+: b := h (a, b) (by simp)
    have hrest : ∀ p ∈ (b :: rest).zip ((b :: rest).drop 1), p.1 <+: p.2 := by
      intro p hp
      exact h p (by simp [List.zip] at hp ⊢; exact Or.inr hp)
    have ih := neighbours_prefix_pairwise (b :: rest) hrest
    refine List.Pairwise.cons ?_ ih
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hab
    · exact hab.trans ((List.pairwise_cons.mp ih).1 c hc)

theorem incompatibleOrders_single (k : Nat) (vs : List (List Int)) :
    incompatibleOrders [(k, vs)] = (if (vs.zip (vs.drop 1)).any (fun (a, b) => !isPrefix a b) then [k] else []) := by
  unfold incompatibleOrders
  split <;> simp_all

/-- Neighbour pairs of a list are pairs of it in order. -/
theorem zip_drop_pairwise {R : List Int → List Int → Prop} :
    ∀ (vs : List (List Int)), vs.Pairwise R → ∀ p ∈ vs.zip (vs.drop 1), R p.1 p.2
  | [], _, p, hp => by simp at hp
  | [_], _, p, hp => by simp at hp
  | a :: b :: rest, h, p, hp => by
    simp only [List.drop_succ_cons, List.drop_zero, List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact (List.pairwise_cons.mp h).1 b (List.mem_cons_self ..)
    · exact zip_drop_pairwise (b :: rest) (List.pairwise_cons.mp h).2 p (by simpa using hp)

/-- No incompatible order is reported for a key exactly when its sorted values are pairwise
prefixes: Elle's neighbour check decides the chain property. -/
theorem incompatibleOrders_nil_iff (k : Nat) (vs : List (List Int)) :
    incompatibleOrders [(k, vs)] = [] ↔ vs.Pairwise (· <+: ·) := by
  rw [incompatibleOrders_single]
  constructor
  · intro h
    have hany : ((vs.zip (vs.drop 1)).any fun (a, b) => !isPrefix a b) = false := by
      cases hc : ((vs.zip (vs.drop 1)).any fun (a, b) => !isPrefix a b)
      · rfl
      · rw [hc] at h; simp at h
    apply neighbours_prefix_pairwise
    intro p hp
    have h1 := List.any_eq_false.mp hany p hp
    apply (isPrefix_iff p.1 p.2).mp
    obtain ⟨a, b⟩ := p
    cases hp' : isPrefix a b
    · exact absurd (by simp [hp']) h1
    · rfl
  · intro h
    have hany : ((vs.zip (vs.drop 1)).any fun (a, b) => !isPrefix a b) = false := by
      apply List.any_eq_false.mpr
      intro p hp
      have := (isPrefix_iff p.1 p.2).mpr (zip_drop_pairwise vs h p hp)
      obtain ⟨a, b⟩ := p
      simp [this]
    rw [hany]; rfl

/-! ## The cycle search's state machine (BFSPath.java:135-200)

A path that may take one anti-dependency (`SINGLE`, G-single) takes no second one, and a path
that just took one in `NONADJACENT` mode takes no other right after it. -/

theorem stepRel_none_mode_no_rw (p : BFSPath) (rel : Rels) (i : Nat)
    (hmode : p.rwMode = .none) (hlegal : Rels.inter rel p.legal = 0) :
    p.stepRel rel i = none := by
  unfold BFSPath.stepRel
  simp [hlegal, hmode]

theorem stepRel_single_then_none (p : BFSPath) (rel : Rels) (i : Nat) (q : BFSPath)
    (hmode : p.rwMode = .single) (hlegal : Rels.inter rel p.legal = 0)
    (h : p.stepRel rel i = some q) : q.rwMode = .none ∧ q.wantRW = 0 := by
  unfold BFSPath.stepRel at h
  by_cases hrw : Rels.isAnyRW rel = true
  · simp [hlegal, hmode, hrw] at h
    rw [← h]; exact ⟨rfl, rfl⟩
  · simp [hlegal, hrw] at h

theorem stepRel_no_adjacent_rw (p : BFSPath) (rel : Rels) (i : Nat)
    (hmode : p.rwMode = .nonadjacentTaken) (hlegal : Rels.inter rel p.legal = 0) :
    p.stepRel rel i = none := by
  unfold BFSPath.stepRel
  simp [hlegal, hmode]

/-- A path whose last step was a non-adjacent anti-dependency is not a valid cycle. -/
theorem taken_not_valid (p : BFSPath) (h : p.rwMode = .nonadjacentTaken) : p.isValid = false := by
  unfold BFSPath.isValid
  simp [h]

/-! ## The lattice (consistency_model.clj), by evaluation -/

/-- The memo tables agree with consistency_model.clj's functions on every pair of names (the
functions are unions over their arguments, so pairs check the distribution too). -/
theorem tables_agree :
    Model.allModelNames.all (fun m => Model.allModelNames.all fun m' =>
      Model.anomaliesProhibitedBy [m, m'] == Model.anomaliesProhibitedBySlow [m, m']) = true ∧
    Model.allAnomalyNames.all (fun a => Model.allAnomalyNames.all fun a' =>
      Model.anomaliesToImpossibleModels [a, a'] == Model.anomaliesToImpossibleModelsSlow [a, a']) = true := by
  native_decide

/-- A stronger model prohibits every anomaly a weaker one does (models graph edges). -/
theorem prohibited_monotone :
    Model.models.all (fun (a, b) => (Model.anomaliesProhibitedBy [b]).all
      (Model.anomaliesProhibitedBy [a]).contains) = true := by native_decide

/-- `implied-anomalies` names `:GSIb` and `:GSI` (consistency_model.clj:94,134-135); models
prohibit `:G-SIb` and `:G-SI` (consistency_model.clj:423,450). No model prohibits the first
spelling, and no anomaly implies the second. -/
theorem gsi_spellings_disconnected :
    (Model.dagVerts Model.models).all (fun m =>
      !(Model.anomaliesProhibitedBy [m]).contains "GSIb" &&
      !(Model.anomaliesProhibitedBy [m]).contains "GSI") = true ∧
    (Model.allImpliedAnomalies ["G-single", "G-single-item", "G0", "G1c"]).contains "G-SIb" = false ∧
    (Model.allImpliedAnomalies ["G-single", "G-single-item", "G0", "G1c"]).contains "GSIb" = true := by
  native_decide

/-- Lost update (an H_lu cycle has one anti-dependency) does not imply G-single-item. -/
theorem lost_update_not_g_single :
    (Model.allImpliedAnomalies ["lost-update"]).contains "G-single-item" = false ∧
    (Model.allImpliedAnomalies ["lost-update"]).contains "G2-item" = true := by native_decide

/-- Internal inconsistency is allowed by repeatable read and read committed. -/
theorem internal_not_prohibited_by_rr :
    (Model.anomaliesProhibitedBy ["repeatable-read"]).contains "internal" = false ∧
    (Model.anomaliesProhibitedBy ["read-committed"]).contains "internal" = false := by native_decide

/-- Asking for strong session SI and strong read uncommitted together picks the real-time graph
and no process graph (txn.clj:686-698), though strong session SI prohibits process anomalies. -/
theorem realtime_replaces_process :
    additionalGraphs { models := some ["strong-session-snapshot-isolation", "strong-read-uncommitted"] } = .realtime ∧
    additionalGraphs { models := some ["strong-session-snapshot-isolation"] } = .process ∧
    (prohibitedAnomalyTypes { models := some ["strong-session-snapshot-isolation", "strong-read-uncommitted"] }).contains
      "G-single-item-realtime" = false := by native_decide

/-! ## The disagreements, by evaluation of the replica and the specification -/

def caseH (n : String) : History := ((Cases.cases.find? (·.name == n)).map (·.h)).getD #[]

def laValid (n : String) (ms : List String) : Option Valid := (ListAppend.check { models := some ms } (caseH n)).valid
def rrValid (n : String) (ms : List String) : Option Valid := (RwRegister.check { models := some ms } (caseH n)).valid

theorem unobserved_appends :
    laValid "unobserved-appends-g-single" ["snapshot-isolation"] = some .true_ ∧
    laValid "unobserved-appends-g-single" ["consistent-view"] = some .true_ ∧
    Spec.verdict (Spec.interpsListAppend (caseH "unobserved-appends-g-single")) "snapshot-isolation" = .unsat ∧
    Spec.verdict (Spec.interpsListAppend (caseH "unobserved-appends-g-single")) "consistent-view" = .unsat := by
  native_decide

theorem process_order_skips_info :
    laValid "process-order-skips-info" ["strong-session-serializable"] = some .true_ ∧
    Spec.verdict (Spec.interpsListAppend (caseH "process-order-skips-info")) "strong-session-serializable" = .unsat := by
  native_decide

theorem realtime_model_hides_process_anomaly :
    laValid "realtime-replaces-process" ["strong-session-snapshot-isolation"] = some .false_ ∧
    laValid "realtime-replaces-process" ["strong-session-snapshot-isolation", "strong-read-uncommitted"] = some .true_ ∧
    Spec.verdict (Spec.interpsListAppend (caseH "realtime-replaces-process")) "strong-session-snapshot-isolation" = .unsat := by
  native_decide

theorem failed_append_hides_ww :
    laValid "failed-append-hides-ww" ["read-uncommitted"] = some .true_ ∧
    Spec.verdict (Spec.interpsListAppend (caseH "failed-append-hides-ww")) "read-uncommitted" = .unsat := by
  native_decide

theorem info_write_may_have_aborted :
    laValid "info-write-may-have-aborted" ["read-uncommitted"] = some .false_ ∧
    Spec.verdict (Spec.interpsListAppend (caseH "info-write-may-have-aborted")) "read-uncommitted" = .sat := by
  native_decide

theorem register_fuzzy_read :
    rrValid "register-fuzzy-read" ["repeatable-read"] = some .true_ ∧
    rrValid "register-fuzzy-read" ["consistent-view"] = some .true_ ∧
    Spec.verdict (Spec.interpsRegister (caseH "register-fuzzy-read")) "repeatable-read" = .unsat := by
  native_decide

theorem register_future_read :
    rrValid "register-future-read" ["strict-serializable"] = some .true_ ∧
    (Spec.interpsRegister (caseH "register-future-read")).isEmpty = true := by
  native_decide

theorem register_second_read_g1c :
    rrValid "register-second-read-g1c" ["read-committed"] = some .true_ ∧
    Spec.verdict (Spec.interpsRegister (caseH "register-second-read-g1c")) "read-committed" = .unsat := by
  native_decide

theorem register_initial_state_g_single :
    rrValid "register-initial-state-g-single" ["snapshot-isolation"] = some .true_ ∧
    rrValid "register-initial-state-g-single" ["consistent-view"] = some .true_ ∧
    Spec.verdict (Spec.interpsRegister (caseH "register-initial-state-g-single")) "snapshot-isolation" = .unsat := by
  native_decide

/-- Renaming x's two elements flips the read-uncommitted verdict. -/
theorem value_hash_order :
    laValid "value-hash-order-a" ["read-uncommitted"] = some .false_ ∧
    laValid "value-hash-order-b" ["read-uncommitted"] = some .true_ := by
  native_decide

theorem info_may_have_aborted_2txn :
    laValid "info-may-have-aborted-2txn" ["read-uncommitted"] = some .false_ ∧
    Spec.verdict (Spec.interpsListAppend (caseH "info-may-have-aborted-2txn")) "read-uncommitted" = .sat := by
  native_decide

theorem process_skips_info_2txn :
    laValid "process-skips-info-2txn" ["strong-session-read-committed"] = some .true_ ∧
    Spec.verdict (Spec.interpsListAppend (caseH "process-skips-info-2txn")) "strong-session-read-committed" = .unsat := by
  native_decide

theorem garbage_read_throws :
    laValid "list-append-garbage-read" ["strict-serializable"] = none := by
  native_decide

end Elle.Theorems

/-! ## closed-predicate: `(:insert :write :delete)` and `versions-after`, replica against real Elle -/

namespace CP
open Elle

def initOp (i : Nat) (kv : List (Nat × Int)) (t : OpType) : Op :=
  { index := i, type := t, process := 0, f := .init, value := kv.map fun (k, v) => { f := .w, k, v := .int v } }
def txOp (i p : Nat) (t : OpType) (ms : List Mop) : Op := { index := i, type := t, process := p, value := ms }

/-- init {0 0, 1 0}; T1 writes 1 := 1; T2 reads 1 = 1 and 0 = nil (before init). -/
def hWrite : History := #[initOp 0 [(0, 0), (1, 0)] .invoke, initOp 1 [(0, 0), (1, 0)] .ok,
  txOp 2 1 .invoke [{ f := .w, k := 1, v := .int 1 }], txOp 3 1 .ok [{ f := .w, k := 1, v := .int 1 }],
  txOp 4 2 .invoke [{ f := .r, k := 1, v := .nil }, { f := .r, k := 0, v := .nil }],
  txOp 5 2 .ok [{ f := .r, k := 1, v := .int 1 }, { f := .r, k := 0, v := .nil }]]

/-- init {0 0, 1 0}; T1 deletes 1; T2 reads predicate [:= 0] = {} and 1 = nil. -/
def hAfter : History := #[initOp 0 [(0, 0), (1, 0)] .invoke, initOp 1 [(0, 0), (1, 0)] .ok,
  txOp 2 1 .invoke [{ f := .delete, k := 1, v := .nil }], txOp 3 1 .ok [{ f := .delete, k := 1, v := .nil }],
  txOp 4 2 .invoke [{ f := .rp, k := 0, v := .nil, pred := .eq 0 }, { f := .r, k := 1, v := .nil }],
  txOp 5 2 .ok [{ f := .rp, k := 0, v := .kmap [], pred := .eq 0 }, { f := .r, k := 1, v := .nil }]]

def types (o : Outcome) : List String := match o with | .result r => r.anomalyTypes | .thrown _ => ["thrown"]

/-- As written: valid; with `:w` in ww-graph's case: G-single-item (as real Elle, both ways). -/
theorem write_keyword :
    (ClosedPredicate.check { models := some ["serializable"] } hWrite).valid = some .true_ ∧
    types (ClosedPredicate.check { models := some ["serializable"] } hWrite (fixedWrite := true)) = ["G-single-item"] := by
  native_decide

/-- As written: valid; with `versions-after`'s unborn branch in effect: G-single (as real Elle). -/
theorem versions_after_unborn :
    (ClosedPredicate.check { models := some ["snapshot-isolation"] } hAfter).valid = some .true_ ∧
    types (ClosedPredicate.check { models := some ["snapshot-isolation"] } hAfter (fixedVersionsAfter := true)) = ["G-single"] := by
  native_decide

/-- `version<` answers true for `:elle/dead < 0` on a key whose versions are `[0 :elle/dead]`. -/
theorem version_lt_ignores_b :
    ClosedPredicate.versionLt [.int 0, .dead] .dead (.int 0) = true := by native_decide

end CP
