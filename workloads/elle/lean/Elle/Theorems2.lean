import Elle.Props2
import Elle.Folds
import Elle.Boundary
import Elle.ServiceProps
import Elle.CPSpec
import Elle.Cases

/-!
# Round 2's theorems

The time limit's verdict is proved from the definitions (any options, any anomaly map). Facts
about particular histories, the lattice's 371 boundaries and the folds are proved by evaluation
(`native_decide`).
-/

namespace Elle.Theorems2

open Elle

/-! ## The cycle search's time limit never yields `:valid? true` -/

theorem mem_foldl_dedup {α : Type} [BEq α] [LawfulBEq α] (l : List α) (x : α) :
    ∀ acc : List α, (x ∈ acc ∨ x ∈ l) →
      x ∈ l.foldl (fun acc y => if acc.contains y then acc else acc ++ [y]) acc := by
  induction l with
  | nil => intro acc h; simpa using h
  | cons y ys ih =>
    intro acc h
    simp only [List.foldl_cons]
    apply ih
    by_cases hc : acc.contains y = true
    · rw [if_pos hc]
      rcases h with h | h
      · exact Or.inl h
      · rcases List.mem_cons.mp h with h | h
        · subst h; exact Or.inl (List.contains_iff_mem.mp hc)
        · exact Or.inr h
    · rw [if_neg hc]
      rcases h with h | h
      · exact Or.inl (List.mem_append_left _ h)
      · rcases List.mem_cons.mp h with h | h
        · subst h; exact Or.inl (List.mem_append_right _ (List.mem_singleton_self _))
        · exact Or.inr h

theorem mem_dedup {α : Type} [BEq α] [LawfulBEq α] (l : List α) (x : α) (h : x ∈ l) : x ∈ dedup l :=
  mem_foldl_dedup l x [] (Or.inr h)

/-- `:cycle-search-timeout` is reportable whatever the options (txn.clj:650-674). -/
theorem timeout_reportable (o : Opts) : "cycle-search-timeout" ∈ reportableAnomalyTypes o := by
  unfold reportableAnomalyTypes
  apply mem_dedup
  exact List.mem_append_right _ (by simp [unknownAnomalyTypes])

/-- No cycle-exists type is named `cycle-search-timeout`. -/
theorem timeout_not_cycle_exists :
    (cycleExistsSpecs.map (·.type)).contains "cycle-search-timeout" = false := by native_decide

/-- A search cut by its time limit (the anomaly map holds a `:cycle-search-timeout` case)
never yields `:valid? true`: `result-map` (txn.clj:1003) answers `false` or `:unknown`. -/
theorem timeout_never_valid (o : Opts) (m : Anomalies) (cs : List Case)
    (h : ("cycle-search-timeout", cs) ∈ m) (wb : Bool) :
    (resultMap o m wb).valid ≠ .true_ := by
  unfold resultMap
  simp only
  have hr : ("cycle-search-timeout", cs) ∈
      removeRedundantCycleExists (m.filter fun (k, _) => (reportableAnomalyTypes o).contains k) := by
    unfold removeRedundantCycleExists
    simp only [List.mem_filter]
    refine ⟨⟨h, ?_⟩, ?_⟩
    · exact List.contains_iff_mem.mpr (timeout_reportable o)
    · simp only [Bool.not_eq_true']
      apply Bool.eq_false_iff.mpr
      intro hc
      have hc' := List.contains_iff_mem.mp hc
      simp only [List.mem_map, List.mem_filter] at hc'
      obtain ⟨s, ⟨hs, _⟩, ht⟩ := hc'
      have : (cycleExistsSpecs.map (·.type)).contains "cycle-search-timeout" = true :=
        List.contains_iff_mem.mpr (List.mem_map.mpr ⟨s, hs, ht⟩)
      rw [timeout_not_cycle_exists] at this
      exact Bool.false_ne_true this
  split
  · rename_i he
    exact absurd (List.isEmpty_iff.mp he ▸ hr) (List.not_mem_nil)
  · intro hv
    split at hv <;> simp at hv

/-! ## The lattice's boundary on every anomaly set -/

/-- 371 distinct impossible-model unions (every anomaly set maps to one), none failing the
definitions (`Boundary`). -/
theorem boundary_definitions : Boundary.checkAll = (371, []) := by native_decide

/-! ## The disagreements and follow-ups, on their minimal histories -/

open Elle.Cases in
/-- D14's history: two acknowledged writes and an indeterminate one, the latter between them in the
transaction order. -/
def h14 : History := serial [{ p := 0, status := .ok, mops := [w 0 2] }, { p := 0, status := .ok, mops := [w 0 3] },
                             { p := 1, status := .info, mops := [w 0 1] }]
def ord14 : List (Nat × Int) := [(3, 0), (5, 1), (1, 2)]

def validOf (o : Outcome) : Option Valid := o.valid

theorem transaction_order_info_breaks_chain :
    validOf (RwRegister.check { models := some ["strict-serializable"], txnOrder := some ord14 } h14) = some .true_ ∧
    Spec.verdict ((Spec.interpsRegister h14).filter fun i =>
      ({ order := some ord14 } : SpecOpts.Assume).holds (Spec.txnViews h14) i) "strict-serializable" = .unsat ∧
    validOf (RwRegister.check { models := some ["strict-serializable"], txnOrder := some ord14, fixD13 := true } h14) =
      some .false_ := by native_decide

/-- D15: the pair index throws on a double invocation in one chunk; across a boundary it pairs the
first invocation with nothing (two chunks) or drops it (three). -/
def doubleInvoke : List Op := [
  { index := 0, type := .invoke, process := 0, value := [Cases.a 0 1] },
  { index := 1, type := .invoke, process := 0, value := [Cases.a 0 2] },
  { index := 2, type := .ok, process := 0, value := [Cases.a 0 2] }]

theorem pair_index_depends_on_chunking :
    (match Folds.pairIndexFold.onChunks [doubleInvoke] with
     | .error e => e == ":jepsen.history/double-invoke" | .ok _ => false) = true ∧
    (match Folds.pairIndexFold.onChunks [doubleInvoke.take 1, doubleInvoke.drop 1] with
     | .ok l => l == ["0=-1", "1=2", "2=1"] | .error _ => false) = true ∧
    (match Folds.pairIndexFold.onChunks (doubleInvoke.map ([·])) with
     | .ok l => l == ["1=2", "2=1"] | .error _ => false) = true := by
  native_decide

open Elle.Cases in
def dupRead : List Op := (serial [{ p := 0, status := .ok, mops := [r 0 []] },
                                  { p := 1, status := .ok, mops := [a 1 1, r 1 [1, 1]] }]).toList

/-- D16: after deduplication the answer is invalid with an empty `not`; the lattice's boundary of
`duplicate-elements` is read uncommitted. -/
theorem dedup_answer_not_empty :
    (match Service.check .listAppend "serializable" false dupRead with
     | .ok a => a.valid == .false_ && a.types.contains "duplicate-elements" && a.not_.isEmpty
     | .error _ => false) = true ∧
    (Model.friendlyBoundary ["duplicate-elements"]).1 = ["read-uncommitted"] := by native_decide

open Elle.Cases in
def dedupHides : History := build
  [{ p := 2, status := .ok, mops := [a 1 1, r 1 [2, 1]] }, { p := 1, status := .ok, mops := [a 0 1, a 0 2] },
   { p := 0, status := .ok, mops := [a 1 2, r 1 [1, 1, 2]] }, { p := 1, status := .ok, mops := [r 0 []] }]
  [.inv 0, .done 0, .inv 1, .inv 2, .done 2, .done 1, .inv 3, .done 3]

open Elle.Cases in
def dedupHidesWithout : History := build
  [{ p := 2, status := .ok, mops := [a 1 1, r 1 [2, 1]] }, { p := 1, status := .ok, mops := [a 0 1, a 0 2] },
   { p := 0, status := .ok, mops := [a 1 2] }, { p := 1, status := .ok, mops := [r 0 []] }]
  [.inv 0, .done 0, .inv 1, .inv 2, .done 2, .done 1, .inv 3, .done 3]

/-- D17: Elle finds G0-realtime without the duplicated read; the service's answer has no G0. -/
theorem dedup_hides_g0_realtime :
    (match ListAppend.check { models := some ["strict-serializable"] } dedupHidesWithout with
     | .result r => r.anomalyTypes.contains "G0-realtime"
     | _ => false) = true ∧
    (match Service.check .listAppend "strict-serializable" false dedupHides.toList with
     | .ok a => !(a.types.any (·.startsWith "G0")) && a.types.contains "duplicate-elements"
     | .error _ => false) = true := by native_decide

/-- D18: serializable with every key linearizable (reading (a)), not reading (b); the service
rejects it. -/
theorem per_key_readings_part :
    let h := ServiceProps.perKeyParts.toArray
    let is := Spec.interpsRegister h
    let txs := Spec.txnViews h
    Service.satA txs is = true ∧ Service.satB txs is = false ∧
    (match Service.check .register "strict-serializable-per-key" false ServiceProps.perKeyParts with
     | .ok a => a.valid == .false_ | .error _ => false) = true := by native_decide

/-- Closed-predicate operations: an init (its mops' keys and values), then transactions. -/
def cpOps (init : List (Nat × Int)) (ts : List (Nat × List Mop)) (concurrent : Bool := false) : List Op :=
  let i0 : Op := { index := 0, type := .invoke, process := 0, f := .init,
                   value := init.map fun (k, v) => { f := .w, k, v := .int v } }
  let i1 : Op := { i0 with index := 1, type := .ok }
  let inv (j : Nat) (t : Nat × List Mop) : Op := { index := 0, type := .invoke, process := t.1, value := t.2.map fun m =>
    if m.f == .r || m.f == .rp then { m with v := .nil } else m }
  let ok (t : Nat × List Mop) : Op := { index := 0, type := .ok, process := t.1, value := t.2 }
  let body := if concurrent then ts.map (inv 0) ++ ts.map ok else ts.flatMap fun t => [inv 0 t, ok t]
  ([i0, i1] ++ body).zipIdx.map fun (o, i) => { o with index := i }

def mr (k : Nat) (v : Int) : Mop := { f := .r, k, v := .int v }
def mw (k : Nat) (v : Int) : Mop := { f := .w, k, v := .int v }
def mdel (k : Nat) : Mop := { f := .delete, k, v := .nil }
def mrp (p : Pred) (rows : List (Nat × Int)) : Mop := { f := .rp, k := 0, pred := p, v := .kmap (rows.map fun (k, v) => (k, .int v)) }

/-- D20: an item and a predicate anti-dependency in one cycle: G2-item by Adya, G2 by Elle. -/
def cpMixed : History := (cpOps [(1, 1), (2, 0)] [(1, [mr 2 0, mw 1 3]), (2, [mrp (.eq 1) [(1, 1)], mdel 2])] true).toArray

theorem mixed_cycle_not_g2_item :
    validOf (ClosedPredicate.check { models := some ["repeatable-read"] } cpMixed) = some .true_ ∧
    CPSpec.violates cpMixed "repeatable-read" = true := by native_decide

/-- D21: a predicate read's rows as item reads (Adya) make a stale `:true` read a G-single-realtime;
Elle sees no edge. -/
def cpStale : History := (cpOps [(0, 0), (1, 0)] [(1, [mw 0 1]), (2, [mrp .tru [(0, 0), (1, 0)]])]).toArray

theorem predicate_rows_not_items :
    validOf (ClosedPredicate.check { models := some ["strict-serializable"] } cpStale) = some .true_ ∧
    CPSpec.violates cpStale "strict-serializable" (rowItems := true) = true := by native_decide

/-- D19: a predicate read that misses an earlier write which changed its match: Elle's strict
serializability catches it, the per-key model doesn't. -/
def cpStaleEq : List Op := cpOps [(0, 0), (1, 0)] [(1, [mw 0 1]), (2, [mrp (.eq 0) [(0, 0), (1, 0)]])]

theorem per_key_predicate_reads :
    (match Service.check .closedPredicate "strict-serializable" false cpStaleEq with
     | .ok a => a.valid == .false_ | .error _ => false) = true ∧
    (match Service.check .closedPredicate "strict-serializable-per-key" false cpStaleEq with
     | .ok a => a.valid == .true_ | .error _ => false) = true := by native_decide

/-- D10's follow-up: Elle's failure-to-observe history. The paren fix alone throws (the explainer);
with `version<` fixed too, a G-single-realtime, which the specification has. -/
def cpMiss : History := (cpOps [(5, 3)] [(1, [mrp (.mod 2 1) [], mrp (.eq 3) []])]).toArray

theorem d10_fix_complete :
    (match ClosedPredicate.check { models := some ["strict-serializable"] } cpMiss true false false with
     | .thrown _ => true | _ => false) = true ∧
    (match ClosedPredicate.check { models := some ["strict-serializable"] } cpMiss true false true with
     | .result r => r.anomalyTypes.contains "G-single-realtime" | _ => false) = true ∧
    CPSpec.violates cpMiss "strict-serializable" = true := by native_decide

open Elle.Cases in
/-- D3's follow-up: the two-transaction history is caught for strong session read committed; the
`[2 1]` history stays valid for strong session read uncommitted (its aborted interpretation). -/
theorem d3_fix :
    let h1 := serial [{ p := 0, status := .ok, mops := [r 0 [1]] }, { p := 0, status := .info, mops := [a 0 1] }]
    let h2 := serial [{ p := 0, status := .ok, mops := [a 0 1] }, { p := 0, status := .info, mops := [a 0 2] },
                      { p := 1, status := .ok, mops := [r 0 [2, 1]] }]
    validOf (ListAppend.check { models := some ["strong-session-read-committed"] } h1) = some .true_ ∧
    validOf (ListAppend.check { models := some ["strong-session-read-committed"], fixD3 := true } h1) = some .false_ ∧
    validOf (ListAppend.check { models := some ["strong-session-serializable"], fixD3 := true } h2) = some .false_ ∧
    validOf (ListAppend.check { models := some ["strong-session-read-uncommitted"], fixD3 := true } h2) = some .true_ ∧
    validOf (ListAppend.check { models := some ["strong-read-uncommitted"], fixD3 := true } h2) = some .true_ ∧
    Spec.verdict (Spec.interpsListAppend h2) "strong-session-read-uncommitted" = .sat := by native_decide

open Elle.Cases in
/-- D13's follow-up: the read `:info` write is caught; an unread one between two finished writes in
the order adds no cycle (its aborted interpretation is serializable in real time). -/
theorem d13_fix :
    let h1 := serial [{ p := 0, status := .ok, mops := [rv 0 1] }, { p := 0, status := .info, mops := [w 0 1] }]
    let h2 := serial [{ p := 0, status := .ok, mops := [w 0 1] }, { p := 0, status := .ok, mops := [w 0 3] },
                      { p := 1, status := .info, mops := [w 0 2] }]
    let o2 : List (Nat × Int) := [(1, 0), (5, 1), (3, 2)]
    validOf (RwRegister.check { models := some ["strict-serializable"] } h1) = some .true_ ∧
    validOf (RwRegister.check { models := some ["strict-serializable"], fixD13 := true } h1) = some .false_ ∧
    validOf (RwRegister.check { models := some ["strict-serializable"], txnOrder := some o2, fixD13 := true } h2) =
      some .true_ ∧
    Spec.verdict ((Spec.interpsRegister h2).filter fun i =>
      ({ order := some o2 } : SpecOpts.Assume).holds (Spec.txnViews h2) i) "strict-serializable" = .sat := by native_decide

open Elle.Cases in
/-- D13's refined fix: an `:info` write an `:ok` read saw keeps its ww edges for models prohibiting
G1a (strict serializable catches the G0-realtime), not for strong read uncommitted (its aborted
interpretation satisfies it). -/
theorem d13_fix_observed :
    let h := build [{ p := 0, status := .ok, mops := [w 0 2] }, { p := 1, status := .info, mops := [w 0 1, w 1 1] },
                    { p := 0, status := .ok, mops := [rv 1 1] }]
                   [.inv 0, .done 0, .inv 1, .done 1, .inv 2, .done 2]
    let o : List (Nat × Int) := [(5, 0), (3, 1), (1, 2)]
    validOf (RwRegister.check { models := some ["strict-serializable"], txnOrder := some o } h) = some .true_ ∧
    validOf (RwRegister.check { models := some ["strict-serializable"], txnOrder := some o, fixD13 := true } h) =
      some .false_ ∧
    validOf (RwRegister.check ({ models := some ["strong-read-uncommitted"], txnOrder := some o, fixD13 := true, fixD3 := true } : Opts) h) =
      some .true_ ∧
    Spec.verdict ((Spec.interpsRegister h).filter fun i =>
      ({ order := some o } : SpecOpts.Assume).holds (Spec.txnViews h) i) "strong-read-uncommitted" = .sat := by
  native_decide

/-- D22: an `:info` operation's unknown read (`nil`, its invocation's value) is explained as a
read of `:elle/dead`; the rw step becomes wr and consistent view passes a G-single. Without that
mop, G-single-item. Elle as written and with D9's and D10's fixes alike. -/
def cpInfoRead (withRead : Bool) : History :=
  let ops : List Op := [
    { index := 0, type := .invoke, process := 0, f := .init, value := [mw 1 0, mw 2 0] },
    { index := 1, type := .ok, process := 0, f := .init, value := [mw 1 0, mw 2 0] },
    { index := 2, type := .invoke, process := 3, value := [{ f := .insert, k := 0, v := .int 2 }, mw 1 3] ++
        (if withRead then [{ f := .r, k := 2, v := .nil }] else []) },
    { index := 3, type := .info, process := 3, value := [{ f := .insert, k := 0, v := .int 2 }, mw 1 3] ++
        (if withRead then [{ f := .r, k := 2, v := .nil }] else []) },
    { index := 4, type := .invoke, process := 5, value := [mrp (.eq 0) [], { f := .r, k := 0, v := .nil }, mdel 2] },
    { index := 5, type := .ok, process := 5, value := [mrp (.eq 0) [], { f := .r, k := 0, v := .nil }, mdel 2] }]
  ops.toArray

theorem info_read_explained_as_read :
    validOf (ClosedPredicate.check { models := some ["consistent-view"] } (cpInfoRead true)) = some .true_ ∧
    validOf (ClosedPredicate.check { models := some ["consistent-view"] } (cpInfoRead true) true true true) =
      some .true_ ∧
    validOf (ClosedPredicate.check { models := some ["consistent-view"] } (cpInfoRead false)) = some .false_ ∧
    CPSpec.violates (cpInfoRead true) "consistent-view" = true := by native_decide

end Elle.Theorems2
