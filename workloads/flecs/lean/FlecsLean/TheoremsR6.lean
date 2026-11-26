/-
  Round 6 theorems.  No `sorry`; the axioms used are printed by Axioms.lean.
  The concrete ones are checked by the kernel (`decide +kernel`).
-/
import FlecsLean.OnSetInh
import FlecsLean.Spawner
import FlecsLean.Slices
import FlecsLean.OrVMFuel

namespace Flecs.R6

/-- A flatMap whose function gives [] everywhere is []. -/
theorem flatMap_nil_of {α β : Type} (l : List α) (f : α → List β) (h : ∀ x, f x = []) :
    l.flatMap f = [] := by
  induction l with
  | nil => rfl
  | cons a as ih => simp [List.flatMap_cons, h a, ih]

open Flecs.OSI in
/-- F41, for every world: the ids reachable through an IsA pair never
    include a DontFragment component (it is in no table type), at any
    depth. -/
theorem reach_dontFragment_nil (st : St) (fuel tgt : Nat) :
    reachF st .dontFragment fuel tgt = [] := by
  induction fuel generalizing tgt with
  | zero => rfl
  | succ n ih =>
    have hb : (Storage.dontFragment != Storage.dontFragment) = false := rfl
    have hsub : (ent st tgt).isa.flatMap (fun bb => reachF st .dontFragment n bb) = [] :=
      flatMap_nil_of _ _ ih
    first
      | (simp only [reachF, hb, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hsub,
          List.isEmpty_nil, List.nil_append]; done)
      | simp [reachF, hb, hsub]

open Flecs.OSI in
/-- F41, for every world: adding an IsA pair delivers no OnSet event unless
    the component has a column (a table component): the forward's
    `storage_i != -1` (observable.c 689). -/
theorem isa_onset_needs_column (st : St) (e b : Nat) (stor : Storage)
    (h : stor ≠ .table) : (step stor st (.isa e b)).2 = [] := by
  have hstep : step stor st (.isa e b) =
      (if e ≥ st.size || b ≥ e || (ent st e).isa.contains b then (st, []) else
        let st' := st.modify e (fun x => { x with isa := insertSorted b x.isa })
        let owned := stor != .dontFragment && (ent st' e).own.isSome
        (st', if stor == .table && !owned then (reach st' stor b).map (fun s => (e, s)) else [])) := rfl
  rw [hstep]
  cases stor with
  | table => exact absurd rfl h
  | sparse => split <;> rfl
  | dontFragment => split <;> rfl

open Flecs.OSI in
/-- The C tests' programs, call by call (entity, source):
    F41: one and two levels give no event for Sparse and DontFragment, one
    per level for the table component; F42: setting the base delivers an
    event for the overriding instance (e1) with source e0 for DontFragment,
    none for the table component; F43: the second base (e1) is forwarded
    although e0 stays the primary source, and the variant with two bases
    forwards two events. -/
theorem onset_cases :
    trace { storage := .dontFragment, nents := 3, ops := [.set 0 10, .isa 1 0, .isa 2 1] } = [[(0, 0)], [], []] ∧
    trace { storage := .sparse, nents := 3, ops := [.set 0 10, .isa 1 0, .isa 2 1] } = [[(0, 0)], [], []] ∧
    trace { storage := .table, nents := 3, ops := [.set 0 10, .isa 1 0, .isa 2 1] } = [[(0, 0)], [(1, 0)], [(2, 0)]] ∧
    trace { storage := .dontFragment, nents := 2, ops := [.set 0 10, .isa 1 0, .set 1 20, .set 0 30] } =
      [[(0, 0)], [], [(1, 1)], [(0, 0), (1, 0)]] ∧
    trace { storage := .table, nents := 2, ops := [.set 0 10, .isa 1 0, .set 1 20, .set 0 30] } =
      [[(0, 0)], [(1, 0)], [(1, 1)], [(0, 0)]] ∧
    trace { storage := .table, nents := 4, ops := [.set 0 10, .set 1 20, .isa 2 0, .isa 2 1, .isa 3 2] } =
      [[(0, 0)], [(1, 1)], [(2, 0)], [(2, 1)], [(3, 0), (3, 1)]] := by
  decide +kernel

open Flecs.Spawn6 in
/-- F44, for every prefab: the spawner's walk instantiates only Parent
    nodes. -/
theorem spawner_only_parent (p : Prog) (fuel n k : Nat) :
    k ∈ spawnerF p fuel n → (node p k).kind = .parent := by
  induction fuel generalizing n with
  | zero => simp [spawnerF]
  | succ f ih =>
    intro hk
    simp only [spawnerF, List.mem_flatMap] at hk
    obtain ⟨c, _, hc⟩ := hk
    cases hx : (node p c).kind with
    | parent =>
      rw [hx] at hc
      have hne : (Kind.parent != Kind.parent) = false := rfl
      rw [hne] at hc
      simp only [Bool.false_eq_true, ↓reduceIte, List.mem_cons] at hc
      rcases hc with h1 | h2
      · rw [h1]; exact hx
      · split at h2
        · exact ih c h2
        · simp at h2
    | childOf =>
      rw [hx] at hc
      have hne : (Kind.childOf != Kind.parent) = true := rfl
      rw [hne] at hc
      simp at hc

open Flecs.Spawn6 in
/-- F44 and F45: the C tests' prefabs.  Mixed children: only the Parent
    child (node 2) is instantiated; a Parent child's ChildOf child is not;
    the controls instantiate every node. -/
theorem spawner_cases :
    instantiated { nodes := #[{ parent := 0, kind := .childOf }, { parent := 0, kind := .parent }] } = [2] ∧
    instantiated { nodes := #[{ parent := 0, kind := .parent }, { parent := 1, kind := .childOf }] } = [1] ∧
    instantiated { nodes := #[{ parent := 0, kind := .childOf }, { parent := 0, kind := .childOf }] } = [1, 2] ∧
    instantiated { nodes := #[{ parent := 0, kind := .parent }, { parent := 0, kind := .parent }] } = [1, 2] := by
  decide +kernel

/-- F46's programs: the C test's, and the same without the new table. -/
def slReuse : Flecs.Slices.Prog :=
  { ntags := 2, delPolicy := #[true, false],
    init := [.newEnt true [] 2, .newEnt true [0] 4, .newEnt true [] 6],
    calls := [(1, .deleteTag 0), (1, .newEnt false [1] 0)] }

def slSkip : Flecs.Slices.Prog :=
  { ntags := 2, delPolicy := #[true, false],
    init := [.newEnt true [] 2, .newEnt true [0] 4, .newEnt true [] 6],
    calls := [(1, .deleteTag 0)] }

/-- F46: the C test's program breaks P1 and P-IT3 at the second result;
    without the new table the slice is skipped, but its freed monitor is
    synced (P1). -/
theorem reused_slot_case :
    (Flecs.Slices.check slReuse).map (·.1) = ["P1 no use after free", "P-IT3 results match the query"] ∧
    (Flecs.Slices.check slSkip).map (·.1) = ["P1 no use after free"] := by
  decide +kernel

open Flecs.OrVM in
/-- F34 through the fuel-indexed VM, evaluated by the kernel: the cached
    query `TagA || Position(Sparse), TagC` over the tables [TagA,
    Position], [TagA, TagC], [Position, TagC] yields table 0 only, while
    tables 1 and 2 match its terms. -/
theorem or_after_chain_iterate :
    runF { storage := #[.table, .sparse, .table],
           terms := #[{ comp := 0, oper := .or }, { comp := 1 }, { comp := 2 }],
           tables := #[[0, 1], [0, 2], [1, 2]] } = some ([0], [1, 2]) := by
  decide +kernel

end Flecs.R6
