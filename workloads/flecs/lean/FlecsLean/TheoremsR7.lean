/-
  Round 7 theorems.  No `sorry`; the axioms used are printed by Axioms.lean.
  The concrete ones are checked by the kernel (`decide +kernel`).
-/
import FlecsLean.EvInh
import FlecsLean.SpawnInh
import FlecsLean.IterKinds
import FlecsLean.Slices
import FlecsLean.TheoremsR6

namespace Flecs.R7

open Flecs.OSI in
/-- For every world, with table (or Sparse) storage the propagation of an
    event reaches no entity that owns C: `flecs_emit_propagate_id_for_range`
    skips owned tables and stops below them.  (With DontFragment storage it
    does reach owners: `prop_dontFragment_reaches_owner`.) -/
theorem propF_skips_owners (st : St) (stor : Storage) (hs : stor ≠ .dontFragment)
    (src fuel x y s : Nat) :
    (y, s) ∈ propF st stor src fuel x → (ent st y).own = none := by
  have hb : (stor != Storage.dontFragment) = true := by
    cases stor with
    | table => rfl
    | sparse => rfl
    | dontFragment => exact absurd rfl hs
  induction fuel generalizing x with
  | zero => simp [propF]
  | succ n ih =>
    intro h
    rw [propF, List.mem_flatMap] at h
    obtain ⟨y0, _, hy⟩ := h
    by_cases hc : (ent st y0).isa.contains x = true
    · rw [if_pos hc, hb, Bool.true_and] at hy
      by_cases ho : (ent st y0).own.isSome = true
      · rw [if_pos ho] at hy; simp at hy
      · rw [if_neg ho, List.mem_cons] at hy
        rcases hy with h1 | h2
        · cases h1
          cases hown : (ent st y).own with
          | none => rfl
          | some _ => rw [hown] at ho; exact absurd rfl ho
        · exact ih y0 h2
    · rw [if_neg hc] at hy; simp at hy

open Flecs.OSI in
/-- The counterpart for DontFragment (F48): an entity that owns C and
    inherits from e0 is reached by the propagation from e0. -/
theorem prop_dontFragment_reaches_owner :
    let st : St := #[{ isa := [], own := some 10 }, { isa := [0], own := some 20 }]
    (1, 0) ∈ propF st .dontFragment 0 depth 0 ∧ (ent st 1).own = some 20 := by
  decide +kernel

open Flecs.OSI Flecs.EvInh in
/-- F50, for every world: with DontFragment storage, adding or removing an
    IsA pair delivers no event at all (nothing is reachable). -/
theorem isa_dontFragment_silent (st : St) (e b : Nat) :
    (EvInh.step .dontFragment st (.isa e b)).2 = [] ∧ (EvInh.step .dontFragment st (.unIsa e b)).2 = [] := by
  constructor
  · simp only [EvInh.step]
    split
    · rfl
    · simp [reach, Flecs.R6.reach_dontFragment_nil]
  · simp only [EvInh.step]
    split
    · rfl
    · simp [reach, Flecs.R6.reach_dontFragment_nil]

open Flecs.EvInh in
/-- The C tests' programs, call by call: F48 (OnAdd and OnRemove for the
    owner e1 and its inheritor e2 with DontFragment; none with a table
    component), F49 (OnAdd and OnRemove from the second base e1 while e2
    reads e0), F50 (no event for the DontFragment pair), F51 (OnAdd but no
    OnSet for e2 when e1 gains a base; OnRemove but no OnSet when e1's
    override goes). -/
theorem ev_cases :
    EvInh.trace ({ storage := .dontFragment, nents := 3, ops := [.set 1 20, .isa 1 0, .isa 2 1, .set 0 10, .remove 0] } : EvInh.Prog) =
      [[(EvInh.Ev.onAdd, 1, 1), (EvInh.Ev.onSet, 1, 1)], [], [],
       [(EvInh.Ev.onAdd, 0, 0), (EvInh.Ev.onAdd, 1, 0), (EvInh.Ev.onAdd, 2, 0), (EvInh.Ev.onSet, 0, 0), (EvInh.Ev.onSet, 1, 0), (EvInh.Ev.onSet, 2, 0)],
       [(EvInh.Ev.onRemove, 0, 0), (EvInh.Ev.onRemove, 1, 0), (EvInh.Ev.onRemove, 2, 0)]] ∧
    EvInh.trace ({ storage := .table, nents := 3, ops := [.set 1 20, .isa 1 0, .isa 2 1, .set 0 10, .remove 0] } : EvInh.Prog) =
      [[(EvInh.Ev.onAdd, 1, 1), (EvInh.Ev.onSet, 1, 1)], [], [(EvInh.Ev.onAdd, 2, 1), (EvInh.Ev.onSet, 2, 1)],
       [(EvInh.Ev.onAdd, 0, 0), (EvInh.Ev.onSet, 0, 0)], [(EvInh.Ev.onRemove, 0, 0)]] ∧
    EvInh.trace ({ storage := .table, nents := 3, ops := [.set 0 10, .isa 2 0, .isa 2 1, .set 1 20, .remove 1] } : EvInh.Prog) =
      [[(EvInh.Ev.onAdd, 0, 0), (EvInh.Ev.onSet, 0, 0)], [(EvInh.Ev.onAdd, 2, 0), (EvInh.Ev.onSet, 2, 0)], [],
       [(EvInh.Ev.onAdd, 1, 1), (EvInh.Ev.onAdd, 2, 1), (EvInh.Ev.onSet, 1, 1), (EvInh.Ev.onSet, 2, 1)],
       [(EvInh.Ev.onRemove, 1, 1), (EvInh.Ev.onRemove, 2, 1)]] ∧
    EvInh.trace ({ storage := .dontFragment, nents := 2, ops := [.set 0 10, .isa 1 0, .unIsa 1 0] } : EvInh.Prog) =
      [[(EvInh.Ev.onAdd, 0, 0), (EvInh.Ev.onSet, 0, 0)], [], []] ∧
    EvInh.trace ({ storage := .sparse, nents := 2, ops := [.set 0 10, .isa 1 0, .unIsa 1 0] } : EvInh.Prog) =
      [[(EvInh.Ev.onAdd, 0, 0), (EvInh.Ev.onSet, 0, 0)], [(EvInh.Ev.onAdd, 1, 0)], [(EvInh.Ev.onRemove, 1, 0)]] ∧
    EvInh.trace ({ storage := .table, nents := 3, ops := [.set 0 10, .isa 2 1, .isa 1 0] } : EvInh.Prog) =
      [[(EvInh.Ev.onAdd, 0, 0), (EvInh.Ev.onSet, 0, 0)], [], [(EvInh.Ev.onAdd, 1, 0), (EvInh.Ev.onSet, 1, 0), (EvInh.Ev.onAdd, 2, 0)]] ∧
    EvInh.trace ({ storage := .table, nents := 3, ops := [.set 0 10, .isa 1 0, .set 1 20, .isa 2 1, .remove 1] } : EvInh.Prog) =
      [[(EvInh.Ev.onAdd, 0, 0), (EvInh.Ev.onSet, 0, 0)], [(EvInh.Ev.onAdd, 1, 0), (EvInh.Ev.onSet, 1, 0)], [(EvInh.Ev.onAdd, 1, 1), (EvInh.Ev.onSet, 1, 1)],
       [(EvInh.Ev.onAdd, 2, 1), (EvInh.Ev.onSet, 2, 1)], [(EvInh.Ev.onRemove, 1, 1), (EvInh.Ev.onRemove, 2, 1), (EvInh.Ev.onSet, 1, 0)]] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

open Flecs.Spawn7 in
/-- F52, for every prefab: with a Parent hierarchy, a prefab child that
    owns an Inherit component that is Sparse or has an on_set hook, and does
    not auto-override it, makes the instantiation assert. -/
theorem spawner_inherit_asserts (p : Prog) (k c v : Nat) (hh : p.hier = .parent)
    (hown : (c, v) ∈ (p.children.getD k default).own)
    (htr : (p.comps.getD c default).trait = .inherit)
    (hauto : c ∉ (p.children.getD k default).auto)
    (hkind : (p.comps.getD c default).storage = .sparse ∨ (p.comps.getD c default).hook = true) :
    ∃ e, instChild p k = .error e := by
  generalize hch : p.children.getD k default = ch at hown hauto
  have hty : c ∉ spawnerType p ch := by
    intro hm
    unfold spawnerType at hm
    rw [List.mem_eraseDups, List.mem_append] at hm
    rcases hm with hm | hm
    · rw [List.mem_filter, List.mem_map] at hm
      obtain ⟨⟨⟨c', v'⟩, _, hc'⟩, ht⟩ := hm
      simp only at hc'
      subst hc'
      rw [htr] at ht
      exact absurd ht (by decide)
    · exact hauto hm
  have h1 : ((p.comps.getD c default).trait != Trait.dontInherit) = true := by rw [htr]; rfl
  have h2 : (spawnerType p ch).contains c = false := by
    cases hcc : (spawnerType p ch).contains c
    · rfl
    · exact absurd (List.contains_iff_mem.mp hcc) hty
  have h3 : ((p.comps.getD c default).storage == Storage.sparse || (p.comps.getD c default).hook) = true := by
    rcases hkind with h | h
    · rw [h]; rfl
    · rw [h]; simp
  have hoff : offends p.comps (spawnerType p ch) c = true := by
    simp only [offends, h1, h2, h3]; rfl
  have hmem : (c, v) ∈ norm ch.own := by
    rw [mem_norm]; exact hown
  have hsome : ((norm ch.own).find?
      (fun (x : Nat × Nat) => offends p.comps (spawnerType p ch) x.1)).isSome := by
    rw [List.find?_isSome]
    exact ⟨(c, v), hmem, hoff⟩
  obtain ⟨⟨c1, v1⟩, hf⟩ := Option.isSome_iff_exists.mp hsome
  unfold instChild
  simp only [hh, hch]
  rw [hf]
  dsimp only
  by_cases hsp : ((p.comps.getD c1 default).storage == Storage.sparse) = true
  · rw [if_pos hsp]; exact ⟨_, rfl⟩
  · rw [if_neg hsp]; exact ⟨_, rfl⟩

open Flecs.Spawn7 in
/-- F52's C tests: the hook and the Sparse forms assert; the ChildOf,
    no-hook and auto-override controls do not. -/
theorem spawner_inherit_cases :
    (Spawn7.check ({ comps := #[{}, { trait := .inherit, hook := true }], hier := .parent,
                       children := #[{ own := [(0, 1), (1, 2)] }] } : Spawn7.Prog)).map (·.1) = ["P1 no-crash"] ∧
    (Spawn7.check ({ comps := #[{}, { trait := .inherit, storage := .sparse }], hier := .parent,
                       children := #[{ own := [(0, 1), (1, 2)] }] } : Spawn7.Prog)).map (·.1) = ["P1 no-crash"] ∧
    Spawn7.check ({ comps := #[{}, { trait := .inherit, hook := true }], hier := .childOf,
                       children := #[{ own := [(0, 1), (1, 2)] }] } : Spawn7.Prog) = [] ∧
    Spawn7.check ({ comps := #[{}, { trait := .inherit }], hier := .parent,
                       children := #[{ own := [(0, 1), (1, 2)] }] } : Spawn7.Prog) = [] ∧
    Spawn7.check ({ comps := #[{}, { trait := .inherit, hook := true }], hier := .parent,
                       children := #[{ own := [(0, 1), (1, 2)], auto := [1] }] } : Spawn7.Prog) = [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

open Flecs.IterKinds in
/-- F53, for every system: a multi-threaded system run with more than one
    stage gives its callback a worker iterator, on which ecs_iter_changed
    and ecs_iter_skip abort. -/
theorem worker_iter_calls_abort (s : Sys) (hs : s.stages > 1) (hm : s.multiThreaded = true)
    (hc : s.call = .iterChanged ∨ s.call = .iterSkip) :
    nextOf s = .workerNext ∧ ∃ e, outcome s = .error e := by
  have hn : nextOf s = .workerNext := by simp [nextOf, hs, hm]
  refine ⟨hn, ?_⟩
  rcases hc with h | h <;> simp only [outcome, hn, h] <;> exact ⟨_, if_pos rfl⟩

open Flecs.IterKinds in
/-- F54, for every system: a run callback of a system that does not get a
    worker iterator, over a query with a trivial cache, gets
    `flecs_query_trivial_cached_next`. -/
theorem run_trivial_next (s : Sys) (hw : ¬ (s.stages > 1 ∧ s.multiThreaded = true))
    (hr : s.run = true) (ht : trivialCache s = true) :
    nextOf s = .trivialCachedNext := by
  simp only [nextOf]
  rw [if_neg (by simpa using hw)]
  simp [hr, ht]

/-- F55's programs: the C test's, and the two controls. -/
def slDirty : Flecs.Slices.Prog7 :=
  { base := { ntags := 2, delPolicy := #[true, false],
              init := [.newEnt true [] 2, .newEnt true [0] 4, .newEnt true [] 6],
              calls := [(1, .deleteTag 0)] },
    post := [.newEnt true [1], .setP 0] }

def slDirtyNoDelete : Flecs.Slices.Prog7 :=
  { slDirty with base := { slDirty.base with calls := [] } }

def slDirtyDeleteBefore : Flecs.Slices.Prog7 :=
  { slDirty with base := { slDirty.base with
      init := slDirty.base.init ++ [.deleteTag 0], calls := [] } }

/-- F55: the skip of the deleted table's slice plants a dirty state in its
    slot (slot 1), the next table created there keeps it, and ecs_set on it
    writes past it; without the delete, or with the delete before the
    iterator is made, nothing is planted. -/
theorem dirty_state_case :
    ((Flecs.Slices.iterateLeaks slDirty.base).map (·.2.1)) = some [1] ∧
    (Flecs.Slices.check7 slDirty).map (·.1) = ["P1 no write past an allocation"] ∧
    Flecs.Slices.check7 slDirtyNoDelete = [] ∧
    Flecs.Slices.check7 slDirtyDeleteBefore = [] := by
  decide +kernel

end Flecs.R7
