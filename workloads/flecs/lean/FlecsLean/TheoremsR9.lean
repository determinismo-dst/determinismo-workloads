/-
  Round 9 theorems.  No `sorry`; the axioms used are printed by Axioms.lean.
  The concrete ones are checked by the kernel (`decide +kernel`).
-/
import FlecsLean.OrUp
import FlecsLean.SparseIter
import FlecsLean.SortGroup
import FlecsLean.EvHier
import FlecsLean.SpawnDepth

namespace Flecs.R9

/-- F59, for every program: a self term's select never touches the field's
    source or its up flag (`flecs_query_set_match` writes ids, trs and the
    column only).  So a self result after an up term inherits both. -/
theorem self_select_keeps_source_and_flag (p : OrUp.Prog) (ts : Array OrUp.Tab) (c : Nat)
    (st : OrUp.Step) (h : st ∈ OrUp.selectSteps p ts (.self, c)) (f : OrUp.F) :
    (st.1 f).src = f.src ∧ (st.1 f).up = f.up := by
  simp only [OrUp.selectSteps, List.mem_map] at h
  obtain ⟨t, _, rfl⟩ := h
  simp [OrUp.setMatch]

/-- F59: the restore of `flecs_query_select_or` (eval.c 1490-1494) keeps
    whatever source and up flag the duplicate check left. -/
theorem restore_keeps_source_and_flag (f prev : OrUp.F) :
    ({ f with ids := prev.ids, tr := prev.tr, col := prev.col } : OrUp.F).src = f.src ∧
    ({ f with ids := prev.ids, tr := prev.tr, col := prev.col } : OrUp.F).up = f.up := by
  exact ⟨rfl, rfl⟩

/-- F59: the C tests' programs and the controls. -/
theorem orup_cases :
    ((OrUp.check (OrUp.cases.getD 0 default).2).map (·.1)).eraseDups = ["P-OR1 an Or result names its source"] ∧
    (OrUp.check (OrUp.cases.getD 1 default).2).map (·.1) = ["P1 no crash or abort"] ∧
    (OrUp.check (OrUp.cases.getD 2 default).2).map (·.1) = ["P1 no crash or abort"] ∧
    OrUp.check (OrUp.cases.getD 3 default).2 = [] ∧
    OrUp.check (OrUp.cases.getD 4 default).2 = [] ∧
    OrUp.check (OrUp.cases.getD 5 default).2 = [] ∧
    (OrUp.check (OrUp.cases.getD 6 default).2).map (·.1) = ["P1 no crash or abort"] ∧
    OrUp.check (OrUp.cases.getD 7 default).2 = [] := by
  decide +kernel

/-- F60: the C test's programs: the trivial search skips, the VM's select
    repeats; the controls hold. -/
theorem sparse_iter_cases :
    (SparseIter.check (SparseIter.cases.getD 0 default).2).map (·.1) = ["P-IT4 removing a DontFragment id while iterating", "P-IT4 removing a DontFragment id while iterating"] ∧
    SparseIter.check (SparseIter.cases.getD 1 default).2 = [] ∧
    (SparseIter.check (SparseIter.cases.getD 2 default).2).map (·.1) = ["P-IT4 removing a DontFragment id while iterating"] ∧
    (SparseIter.check (SparseIter.cases.getD 3 default).2).map (·.1) = ["P-IT4 removing a DontFragment id while iterating"] ∧
    SparseIter.check (SparseIter.cases.getD 4 default).2 = [] ∧
    SparseIter.check (SparseIter.cases.getD 5 default).2 = [] := by
  decide +kernel

/-- F60: a swap-remove moves the last id into the removed slot. -/
theorem sparse_remove_moves_last (d : Array Nat) (x i : Nat) (hi : d.findIdx? (· == x) = some i)
    (hlast : i + 1 < d.size) :
    (SparseIter.sparseRemove d x).getD i 0 = d.getD (d.size - 1) 0 := by
  simp only [SparseIter.sparseRemove, hi]
  have hne : (i == d.size - 1) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; omega
  simp only [hne, Bool.false_eq_true, ↓reduceIte]
  rw [Array.getD, dif_pos (by simp; omega)]
  simp [Array.getElem_pop, Array.set!, Array.setIfInBounds, show i < d.size by omega]

/-- F61: the C test's program and the controls. -/
theorem sortgroup_cases :
    SortGroup.results (SortGroup.cases.getD 0 default).2 = [1, 3, 2, 4] ∧
    (SortGroup.check (SortGroup.cases.getD 0 default).2).map (·.1) = ["P-SO1 order_by results in order"] ∧
    SortGroup.check (SortGroup.cases.getD 1 default).2 = [] ∧
    SortGroup.check (SortGroup.cases.getD 2 default).2 = [] := by
  decide +kernel

/-- F62, for every world: setting the Parent component of a Parent-storage
    child to the parent it already has delivers the OnAdd of
    `(ChildOf, parent)`. -/
theorem same_parent_on_add (stor : EvHier.Stor) (hs : Array EvHier.HS) (st : EvHier.St)
    (x p : Nat) (hx : x < st.size) (hp : p < x) (hpar : (EvHier.ent st x).par = some p)
    (hh : hs.getD x .childOf = .parent) :
    (EvHier.Ev.pairAdd, x, p) ∈ (EvHier.step stor hs st (.link x p)).2 := by
  have h1 : ¬ (x ≥ st.size || p ≥ x) = true := by simp; omega
  have h2 : ((EvHier.ent st x).par == some p) = true := by rw [hpar]; simp
  have h3 : (hs.getD x .childOf == .parent) = true := by rw [hh]; decide
  simp only [EvHier.step, h1, h2, h3, ↓reduceIte]
  simp

/-- F62: the C test's program and its ChildOf control; the earlier cases
    keep their results. -/
theorem evhier9_cases :
    (EvHier.check (EvHier.cases.getD 8 default).2).map (·.1) = ["P-EV7 OnAdd only when added", "P-EV7 OnAdd only when added", "P-EV7 OnAdd only when added"] ∧
    EvHier.check (EvHier.cases.getD 9 default).2 = [] := by
  decide +kernel

/-- F58 repeated: each instantiation at depth 8 adds a keep; at depth 3 the
    cached vector keeps once. -/
theorem spawn_depth_repeat :
    SpawnDepth.keepOf ([8, 8, 8].foldl SpawnDepth.instantiate {}) 8 = 3 ∧
    SpawnDepth.keepOf ([3, 3, 3].foldl SpawnDepth.instantiate {}) 3 = 1 ∧
    SpawnDepth.deletePrefab ([8, 8, 8].foldl SpawnDepth.instantiate {}) = [8] := by
  decide +kernel

end Flecs.R9
