/-
  Round 8: the tree spawner at depth (instances that are themselves
  children), transcribed from flecs v4.2.0.

  `flecs_spawner_instantiate` (addons/prefab/tree_spawner.c 226-349) reads
  the instance's depth (`flecs_relation_depth`, 233) and takes the vector of
  spawn children for it:
  - depth 0: `spawner->data[0]`, built with the spawner (`flecs_prefab_
    spawner_build`, 201-223; its tables kept by `flecs_prefab_spawner_build_
    from_cr`, 99);
  - 0 < depth < FLECS_TREE_SPAWNER_DEPTH_CACHE_SIZE (6, flecs.h 374):
    `spawner->data[depth]`, filled once by `flecs_spawner_transpose_depth`
    (120-149), which adds `(ParentDepth, src_depth + depth)` to each table
    and keeps the result (148);
  - depth >= 6: a temporary vector (246-251), transposed and kept the same
    way on every instantiation, and freed without a release (348-350).
  `EcsTreeSpawner_free` (prefab.c 21-27) releases the tables of
  `data[0..5]`; deleting the prefab calls it first
  (`flecs_tree_spawner_fini`, on_delete.c 222 and 322).  The deleted prefab
  child c is the target of `(IsA, c)` in every spawn table; its cleanup
  releases the tables of that pair (`flecs_component_release_tables`,
  storage/component_index.c 753-776), which keeps a table with `keep > 0`;
  with `force_delete` (set by `ecs_delete`, entity.c 1356-1365) a debug
  build asserts (on_delete.c 729-735: "cannot delete component '%s': tables
  are keeping it alive (likely because of used prefab)").

  The type of a transposed table differs from the depth-0 one only by the
  `ParentDepth` pair, so the Inherit filter of `flecs_prefab_spawner_build_
  type` (tree_spawner.c 27-31) is the same at every depth, and the walk of
  `flecs_instantiate_sparse` (337-338) is the same: F52 holds at every
  depth (read; `Spawn7` has no depth parameter).

  Property P-PF1 (new): after its instances are deleted, deleting a prefab
  with Parent children works and leaves none of its spawn tables behind
  (HierarchiesManual.md "Prefab instantiation works with both storages";
  flecs's own `NonFragmentingChildOf_delete_instantiated_prefab_non_
  fragmenting_child`, at depth 0).
-/
import FlecsLean.Search2

namespace Flecs.SpawnDepth

def cacheSize : Nat := 6

structure W where
  /-- the keep count of the spawn table for each instance depth -/
  keeps : List (Nat × Nat) := []
  /-- depths whose vector is cached in the spawner (`data[d]`) -/
  cached : List Nat := []
  built : Bool := false
  deriving Inhabited, Repr

def keepOf (w : W) (d : Nat) : Nat := ((w.keeps.find? (·.1 == d)).map (·.2)).getD 0

def bump (w : W) (d : Nat) (by_ : Int) : W :=
  let k := (keepOf w d : Int) + by_
  { w with keeps := (d, k.toNat) :: w.keeps.filter (·.1 != d) }

/-- One instantiation for an instance at depth d. -/
def instantiate (w : W) (d : Nat) : W :=
  -- flecs_prefab_spawner_build: data[0]'s tables kept
  let w := if w.built then w else { bump w 0 1 with built := true, cached := [0] }
  if d == 0 then w
  else if d < cacheSize then
    (if w.cached.contains d then w else { bump w d 1 with cached := d :: w.cached })
  -- the temporary vector: kept on every instantiation, never released
  else bump w d 1

/-- Deleting the prefab (its instances already deleted): release the
    cached vectors, then the tables of `(IsA, c)`: the kept ones are left
    (a debug build asserts). -/
def deletePrefab (w : W) : List Nat :=
  let w' := w.cached.foldl (fun w d => bump w d (-1)) w
  (w'.keeps.filter (·.2 > 0)).map (·.1)

structure Prog where
  depths : List Nat
  deriving Inhabited, Repr

def check (p : Prog) : List (String × String) :=
  let w := p.depths.foldl instantiate {}
  match deletePrefab w with
  | [] => []
  | ds => [("P-PF1 deleting a used prefab after its instances", s!"after instances at depths {p.depths} were instantiated and deleted, deleting the prefab finds the spawn table(s) for depth(s) {ds} still kept: an instance at depth >= {cacheSize} (FLECS_TREE_SPAWNER_DEPTH_CACHE_SIZE) uses a temporary vector whose tables flecs_spawner_transpose_depth keeps (tree_spawner.c 148) and nothing releases (348-350); a debug build asserts in the cleanup of (IsA, prefab child) (on_delete.c 729-735), a release build leaves the table")]

section
variable {m : Type → Type} [Monad m] [Pick m]

def genProg (n : Nat) : m Prog := do
  let mut ds := []
  for _ in [0:n] do ds := ds ++ [← Pick.pick "sd.depth" 9]
  return { depths := ds }

end

def cases : List (String × Prog) := [
  ("prefab_parent_instantiate_depth_keeps_tables: an instance at depth 8", { depths := [8] }),
  ("control: an instance at depth 1", { depths := [1] }),
  ("control: depth 0 (flecs's own test)", { depths := [0] }),
  ("depth 5, the deepest cached", { depths := [5] }),
  ("depth 6, the first uncached", { depths := [6] }),
  ("round 9: three instances at depth 8 (the keep count grows by one each)", { depths := [8, 8, 8] }),
  ("round 9: three instances at depth 3 (cached: one keep)", { depths := [3, 3, 3] }) ]

end Flecs.SpawnDepth
