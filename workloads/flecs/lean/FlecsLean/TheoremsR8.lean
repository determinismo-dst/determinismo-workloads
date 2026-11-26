/-
  Round 8 theorems.  No `sorry`; the axioms used are printed by Axioms.lean.
  The concrete ones are checked by the kernel (`decide +kernel`).
-/
import FlecsLean.SlicesR8
import FlecsLean.EvHier
import FlecsLean.SpawnDepth
import FlecsLean.IterKinds
import FlecsLean.TheoremsR7

namespace Flecs.R8

open Flecs.Slices8 in
/-- The F55 correction, for every world: a new table never starts with a
    dirty state planted in its slot (`flecs_init_table`, table_graph.c 424:
    `dirty_state = NULL`). -/
theorem new_table_drops_planted (w : W) (hasP : Bool) (tags : List Nat)
    (h : findTable w hasP tags = none) :
    let r := ensureTable w hasP tags
    ∀ e ∈ r.1.slotDirty, e.1 ≠ (r.1.tabs.getD r.2 default).slot := by
  intro r e he
  simp only [r, ensureTable, h] at he ⊢
  split at he <;> split <;> simp_all [Array.getD, Array.size_push] <;>
    (intro hc; simp_all)

/-- F55 (corrected) and F56: the properties each C test's program breaks,
    and the controls. -/
theorem slices8_cases :
    (Slices8.check (Slices8.cases.getD 0 default).2).map (·.1) = ["P1 no use after free", "P-L1 no leak at ecs_fini"] ∧
    (Slices8.check (Slices8.cases.getD 1 default).2).map (·.1) = ["P1 no use after free", "P-L1 no leak at ecs_fini"] ∧
    (Slices8.check (Slices8.cases.getD 2 default).2).map (·.1) = ["P1 no use after free", "P1 no use after free"] ∧
    Slices8.check (Slices8.cases.getD 3 default).2 = [] ∧
    (Slices8.check (Slices8.cases.getD 4 default).2).map (·.1) = ["P1 no use after free", "P-IT3 results match the query", "P1 no use after free"] ∧
    Slices8.check (Slices8.cases.getD 5 default).2 = [] ∧
    Slices8.check (Slices8.cases.getD 6 default).2 = [] := by
  decide +kernel

/-- Every event a forward produces has the forwarded kind. -/
theorem forward_kind (stor : EvHier.Stor) (st : EvHier.St) (k k' : EvHier.Ev) (x p y s : Nat) :
    (k', y, s) ∈ EvHier.forward stor st k x p → k' = k := by
  intro h
  simp only [EvHier.forward] at h
  split at h
  · simp at h
  · rw [List.mem_append, List.mem_map, List.mem_flatMap] at h
    rcases h with ⟨a, _, ha⟩ | ⟨a, _, hb⟩
    · cases ha; rfl
    · rw [List.mem_map] at hb
      obtain ⟨_, _, hc⟩ := hb
      cases hc; rfl

/-- F57, for every world: re-parenting an entity with Parent storage
    delivers no OnRemove of any kind. -/
theorem parent_reparent_no_remove (stor : EvHier.Stor) (hs : Array EvHier.HS) (st : EvHier.St)
    (x p : Nat) (hp : hs.getD x .childOf = .parent) :
    ∀ e ∈ (EvHier.step stor hs st (.link x p)).2,
      e.1 ≠ EvHier.Ev.onRemove ∧ e.1 ≠ EvHier.Ev.pairRemove := by
  intro e he
  obtain ⟨k, y, s⟩ := e
  have hb : (hs.getD x .childOf == .childOf) = false := by rw [hp]; decide
  simp only [EvHier.step, hb] at he
  split at he
  · simp at he
  · simp only [Bool.false_eq_true, ↓reduceIte, List.mem_cons] at he
    rcases he with h1 | h2
    · cases h1; exact ⟨by simp, by simp⟩
    · have := forward_kind _ _ _ _ _ _ _ _ h2; subst this; exact ⟨by simp, by simp⟩

/-- F57 and the Parent forms of F48 and F50: the C tests' programs. -/
theorem evhier_cases :
    (EvHier.check (EvHier.cases.getD 0 default).2).map (·.1) = ["P-EV2 OnAdd/OnRemove delivered", "P-EV6 ChildOf pair events with both storages"] ∧
    EvHier.check (EvHier.cases.getD 1 default).2 = [] ∧
    EvHier.check (EvHier.cases.getD 3 default).2 = [] ∧
    (EvHier.check (EvHier.cases.getD 4 default).2).map (·.1) = ["P-EV2 OnAdd/OnRemove delivered"] ∧
    EvHier.check (EvHier.cases.getD 7 default).2 = [] := by
  decide +kernel

/-- F58: an instance at depth 6 or more leaves a kept spawn table that the
    prefab's deletion cannot free; depths below 6 do not. -/
theorem spawn_depth_keeps (d : Nat) (hd : d ≥ SpawnDepth.cacheSize) :
    SpawnDepth.deletePrefab (SpawnDepth.instantiate {} d) = [d] := by
  have h0 : d ≠ 0 := by unfold SpawnDepth.cacheSize at hd; omega
  have h6 : ¬ d < SpawnDepth.cacheSize := by omega
  simp [SpawnDepth.instantiate, SpawnDepth.deletePrefab, SpawnDepth.bump, SpawnDepth.keepOf,
    h0, Ne.symm h0, h6]

theorem spawn_depth_cases :
    SpawnDepth.check { depths := [8] } ≠ [] ∧
    SpawnDepth.check { depths := [0] } = [] ∧
    SpawnDepth.check { depths := [1] } = [] ∧
    SpawnDepth.check { depths := [5] } = [] ∧
    SpawnDepth.check { depths := [6] } ≠ [] := by
  decide +kernel

open Flecs.IterKinds in
/-- F53 in a release build, for every system: a multi-threaded system
    with change detection run on more than one stage dereferences NULL in
    ecs_iter_changed. -/
theorem release_worker_iter_changed_crashes (s : Flecs.IterKinds.Sys) (hs : s.stages > 1)
    (hm : s.multiThreaded = true) (hr : s.release = true) (hc : s.call = .iterChanged)
    (ho : s.orderBy = false) :
    Flecs.IterKinds.outcome s = .error Flecs.IterKinds.releaseIterChangedCrash := by
  have hne : (Flecs.IterKinds.Next.workerNext != Flecs.IterKinds.Next.queryNext) = true := by decide
  have hwq : (Flecs.IterKinds.Next.workerNext == Flecs.IterKinds.Next.workerNext) = true := by decide
  obtain ⟨stages, mt, run, dc, ob, tr, call, rel⟩ := s
  simp only at hs hm hr hc ho
  subst hm hr hc ho
  cases run <;> cases tr <;> cases dc <;>
    simp [Flecs.IterKinds.outcome, Flecs.IterKinds.nextOf, Flecs.IterKinds.rejected,
      Flecs.IterKinds.sortAbortsFirst, hs, hne, hwq]

end Flecs.R8
