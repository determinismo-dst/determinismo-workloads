/-
  Round 3 theorems, for every input.

  F24: the reachable-cache generation (`cr->pair->reachable`, observable.c
  489-551 and 708-780) and the table override cache's freshness check
  (table.c 471-508).  `invalidate` is the per-record step of
  `flecs_emit_propagate_invalidate_tables` (the `W.invalidateTables` step in
  Ops.lean); `validate` is the end of `flecs_reachable_cache_ensure` with
  `validate = true`; `refreshes stored rc` is the test of
  `flecs_table_update_overrides` (table.c 483) for one base.

  F25: `Activity.addToCache` (group.c 216-245) and `Activity.apply` for an
  entity entering a table that already exists.
-/
import FlecsLean.Activity

namespace Flecs.R3

/-- `ecs_reachable_cache_t`: current and generation. -/
structure RC where
  cur : Int
  gen : Int
  deriving Repr, DecidableEq

/-- observable.c 504-510 -/
def invalidate (r : RC) : RC := if r.cur = r.gen then { r with gen := r.gen + 1 } else r

/-- observable.c 776-778 -/
def validate (r : RC) : RC := { r with cur := r.gen }

/-- table.c 483: the override cache recomputes its refs when the stored
    generation differs from the record's. -/
def refreshes (stored : Int) (r : RC) : Bool := stored != r.gen

/-- `n` changes of the base, each an invalidation. -/
def changes : Nat → RC → RC
  | 0, r => r
  | n + 1, r => changes n (invalidate r)

theorem invalidate_invalid (r : RC) (h : r.cur ≠ r.gen) : invalidate r = r := by
  simp [invalidate, h]

theorem invalidate_valid (r : RC) (h : r.cur = r.gen) : (invalidate r).gen = r.gen + 1 := by
  simp [invalidate, h]

/-- Any number of invalidations of an invalid cache change nothing. -/
theorem changes_invalid (r : RC) (h : r.cur ≠ r.gen) :
    ∀ n : Nat, changes n r = r
  | 0 => rfl
  | n + 1 => by
    show changes n (invalidate r) = r
    rw [invalidate_invalid r h]
    exact changes_invalid r h n

/-- F24, for every state and every number of later changes of the base:
    once the override cache stored the generation of an invalid reachable
    cache, no change of the base (each an `invalidate`) makes it refresh. -/
theorem override_cache_misses_changes (r : RC) (h : r.cur ≠ r.gen) (n : Nat) :
    refreshes r.gen (changes n r) = false := by
  rw [changes_invalid r h n]
  simp [refreshes]

/-- A valid cache's first invalidation is seen (the check is right when the
    cache was valid). -/
theorem override_cache_sees_first_change (r : RC) (h : r.cur = r.gen) :
    refreshes r.gen (invalidate r) = true := by
  simp [refreshes, invalidate, h]
  omega

/-- The states F24 needs are reachable from the initial record
    (component_index.c 432: current -1, generation 0): validate (an IsA pair
    added), then one change of the base. -/
theorem reachable_invalid_state :
    let r := invalidate (validate { cur := -1, gen := 0 })
    r.cur ≠ r.gen := by
  simp [invalidate, validate]

end Flecs.R3

namespace Flecs.Activity

/-- F25: adding a table to a cache that holds one removes no `EcsEmpty`
    (group.c 240-243 tests `was_empty`). -/
theorem addToCache_keeps_empty (st : St) (k t : Nat) (hk : k < st.sys.size)
    (hc : (st.sys.getD k default).cache ≠ []) :
    ((addToCache st k t).sys.getD k default).empty = (st.sys.getD k default).empty := by
  have hc' : st.sys[k].cache ≠ [] := by simpa [Array.getD, hk] using hc
  simp [addToCache, Array.getD, hk, hc']

end Flecs.Activity
