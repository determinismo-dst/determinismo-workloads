# flecs v4.2.0 in Lean 4 — round 6 report

Everything is in `this directory`.

New files under `FlecsLean/`:
- `OnSetInh.lean`: OnSet events for inherited components, for table, Sparse and DontFragment storage (F41, F42, F43).
- `Slices.lean`: order_by slices against the table store reusing a freed slot (F46).
- `WorkersSort.lean`: the iterator each stage creates for an order_by system (F47).
- `OrVMFuel.lean`: round 5's query VM as one fuel-indexed function that the kernel can evaluate.
- `TheoremsR6.lean`: this round's theorems.

Extended files:
- `Spawner.lean`: namespace `Spawn6`, hierarchies with both storages, nested children and auto overrides (F44, F45).
- `WorkersCD.lean`: pages of the allocator's size-class set (F33 extended).
- `World.lean`, `Query.lean`, `QueryProps.lean`: descending cascade, and the corrected slice skip.

Other files:
- `Main.lean`: the `flecs-search` program.
- `tests/flecs_lean/`: 65 C tests, 8 of them new; none of the earlier ones changed. `README.txt` maps them to predictions.
- `.jobs/r6x/*.log`: this round's logs. `scratch/r6-runs.sh a|b|c|d|e|f|g|s` re-runs the searches; `scratch/r6-quick.sh` prints the cases and compiles the new C tests.

New modes of `flecs-search`:
- `osi …` (F41–F43)
- `sp six-exhaust | six-lib | six-cases` (F44, F45)
- `sl …` (F46)
- `wsort MODE THREADS ROWS RACES N SEED FILTER` (F47; RACES 2 checks races on the table rows and slices only)
- `wcd … 4 …` (sparse-set pages)
- `query iter6-desc-exhaust | iter6-desc-lib`
- `or agree`

Line numbers refer to files under `src/` unless a path says otherwise. In a tape, `name=v/n` means the named decision took value `v` of `n` options.

## The real flecs on rounds 1–5

As the coordinator reported: F1–F40 are confirmed, except F2's original test (a model error, corrected) and F19's uninitialized read. No earlier test changed, and the `flecs_lean: valgrind` line stays.

## Counterexamples

### F41. An IsA add gives no OnSet for an inherited Sparse or DontFragment component

```c
Health: Sparse, (OnInstantiate, Inherit); Defense: DontFragment, Inherit
base = prefab {Position, Health, Defense}; variant = prefab IsA base
OnSet observers (default self|up IsA)
i1 = ecs_new_w_pair(world, EcsIsA, base);     // OnSet for Position only
i2 = ecs_new_w_pair(world, EcsIsA, variant);  // OnSet for Position only
```

**Property P-OS1:** every documented OnSet is delivered.
- ObserversManual.md "OnSet and Inheritance": these events are "enabled by default for components with the (OnInstantiate, Inherit) trait".
- "Adding an IsA pair": "an OnSet event is generated for each newly inherited component".
- ComponentTraits.md "Sparse trait": "ECS operations and queries work as expected with sparse components".

**Code path:**
- `flecs_emit` forwards the ids reachable through the new pair, with `er_onset` (observable.c 1196-1237; `flecs_emit_forward`, 799-890).
- The reachable ids are the Inherit ids of b's table type, recursing through b's own IsA pairs (`flecs_reachable_cache_ensure`, 708-780). A DontFragment component is in no table type, so it is never listed.
- `flecs_emit_forward_id` (613-706) invokes OnSet observers only when the id has a column (`if (storage_i != -1)`, 685). Sparse components have none (storage/table.c 162-165).
- `flecs_instantiate_dont_fragment` skips Inherit components (addons/prefab/instantiate.c 313-314).

**Story:** P-OS1 reports "after ecs_add_pair(e1, EcsIsA, e0) (sparse): entity e1 now sees C from e0, but no OnSet observer was invoked for it: flecs_emit_forward_id invokes OnSet observers only for an element with a column…".

**Tape** (`osi lib exhaust`, 3 entities, 5 calls), after 1,889,578 timelines: `osi.storage=1/3 osi.call=0/3 osi.e=0/3 osi.v=0/2` (×4) `osi.call=1/3 osi.e=1/3 osi.b=0/3`. Shrunk: `ecs_set(e0, C)`; `ecs_add_pair(e1, IsA, e0)`. DontFragment is the same program with `osi.storage=2/3`.

**C test:** `isa_onset_sparse_dont_fragment.c`. Position (a table component) is the control; one and two levels are both checked.

### F42. Setting a DontFragment component on a base sends OnSet to an instance that overrides it

```c
Defense: DontFragment, Inherit; base = prefab Defense {50}
inst = IsA base; ecs_set(inst, Defense, {7});            // inst owns 7
observer; ecs_set(world, base, Defense, {60});
// OnSet for inst, source base, value 60; ecs_get(inst) is 7
```

**Property P-OS2:** a delivered OnSet carries the entity's new source and value, for an entity whose value changed, and comes once.
- "Setting an Inherited Component": "an OnSet event is propagated to all entities that inherit the component".
- "If the base entity has a component that the entity already had no event is generated".

**Code path:**
- The set propagates down (observable.c 1316: `flecs_propagate_entities`, 571-611; `flecs_emit_propagate`, 440-465; `flecs_emit_propagate_id`, 378-438).
- `flecs_emit_propagate_id_for_range` (310-376) skips a table only when the table owns the component (`owned`, 324). A DontFragment component is in no table, so nothing is ever owned.
- With table or Sparse storage, the override is in inst's type, so no event (the controls).

**Story:** P-OS2 reports "after ecs_set(e0, C) (dontFragment): e1 owns C, yet the OnSet observer was invoked for e1 with source e0…".

**Tape**, after 3,779,947 timelines: `osi.storage=2/3 osi.call=0/3 osi.e=0/3 osi.v=0/2 osi.call=0/3 osi.e=0/3 osi.v=0/2 osi.call=0/3 osi.e=1/3 osi.v=0/2 osi.call=1/3 osi.e=1/3 osi.b=0/3 osi.call=0/3 osi.e=0/3 osi.v=0/2`. Shrunk: set e1; e1 IsA e0; set e0.

**C test:** `set_base_onset_dont_fragment_override.c`, with Position and Health as controls.

### F43. OnSet events name a base that is not the entity's source

```c
b1 < b2 prefabs, Position {1,1} and {2,2} (table, Inherit); inst IsA b1
ecs_add_pair(inst, EcsIsA, b2);    // OnSet, source b2; ecs_get(inst) = {1,1}
ecs_set(world, b2, Position, ...); // OnSet for inst, source b2
v IsA b1, IsA b2; i3 = IsA v       // two OnSet events (b1, b2)
```
A diamond also gets duplicates: e1 IsA e0, e2 IsA e0 and IsA e1, then set e0 gives e2 two events.

**Property P-OS2.** "Adding an IsA pair": "if a component from a base entity is already provided by another base entity, and the new base entity does not become the primary source for the component, no OnSet event is generated", where the primary source is "the lowest entity id of all base entities that provide the component".

**Code path:**
- `flecs_emit_forward_id` checks only whether the entity's own table has the component (`owned`, 662-663).
- The reachable list of `(IsA, v)` holds Position once per base of v (729-764).
- The propagation walks every `(IsA, b)` table (310-376).
- `ecs_get` takes the first base in type order (`flecs_get_base_component`, instantiate.c 485-555).

**Stories:**
- "the OnSet observer was invoked for e2 with source e1, but ecs_get(e2, C) reads the value of e0".
- "invoked twice for e2 with source e0".

**Tapes:**
- After 878 timelines: `osi.storage=0/3 osi.call=0/3 osi.e=0/3 osi.v=0/2 osi.call=0/3 osi.e=0/3 osi.v=0/2 osi.call=0/3 osi.e=1/3 osi.v=0/2 osi.call=1/3 osi.e=2/3 osi.b=0/3 osi.call=1/3 osi.e=2/3 osi.b=1/3`.
- The duplicate, after 276,445 timelines (4 entities).

**C test:** `isa_second_base_onset.c`. The control adds b1 after b2: one event, from b1.

### F44. A prefab with children in both storages: instances miss the ChildOf children

```c
P = prefab; a = ChildOf P {Position}; b = ecs_new_w_parent(P) {Velocity}
inst = IsA P          // one child (b's); none for a
Q: q1 = Parent Q; q2 = ChildOf q1   // inst_q's child has no child
```

**Property P-SP2:** an instance gets a counterpart for every prefab child.
- HierarchiesManual.md: "A single parent can contain children that use both ChildOf and Parent hierarchies"; "Prefab instantiation works with both storages".

**Code path:**
- With a Parent child, `flecs_instantiate` uses the TreeSpawner and returns (instantiate.c 424-440).
- The spawner keeps only children whose table has Parent (tree_spawner.c 79-81).
- It descends only into the ordered children of a kept child (104-113).

**Story:** "the instance has no counterpart for prefab nodes [1] (node 1 is a ChildOf child of the prefab, which has Parent children…)".

**Tape** (`sp six-lib`), after 5 timelines: `sp6.kind=0/2 sp6.auto=0/2 sp6.parent=0/2 sp6.kind=0/2 sp6.auto=0/2 sp6.parent=0/3 sp6.kind=0/2 sp6.auto=0/2 sp6.parent=0/4 sp6.kind=1/2 sp6.auto=0/2 sp6.rootauto=0/2`.

**C test:** `prefab_mixed_children_instance.c`, with all-ChildOf and all-Parent prefabs as controls.

### F45. Auto-overriding a DontFragment component on a prefab child aborts the instantiation

```c
Defense: DontFragment; P = prefab; child = ChildOf P (or Parent P)
ecs_set(child, Defense, {50}); ecs_auto_override(world, child, Defense);
inst = IsA P     // abort: "table type cannot contain DontFragment components"
```

**Property P1:** no internal assert. PrefabsManual.md "Auto Overriding" and "Prefab Hierarchies".

**Code path:**
- The `ECS_AUTO_OVERRIDE | Defense` id becomes plain Defense in the instance child's type:
  - `flecs_instantiate_children` (instantiate.c 197-205);
  - `flecs_prefab_spawner_build_type` (tree_spawner.c 33-42).
- The `AUTO_OVERRIDE|C` record has no trait flags (component_index.c 287-291), so nothing filters it.
- `flecs_table_init` then asserts (storage/table.c 249-259).
- On the prefab itself, `flecs_instantiate_override_dont_fragment` (370-391) handles it.

**Tape**, after 3 timelines: as F44's, with `sp6.auto=1/2` on node 4.

**C tests:**
- `prefab_child_auto_override_dont_fragment.c` (ChildOf; the prefab-level override is the control);
- `prefab_parent_child_auto_override_dont_fragment.c` (Parent; it includes the first file).

An abort confirms both.

### F46. Order_by slices of a deleted table name memory that a new table reuses

```c
Tag: OnDelete Delete; order_by Position; [P]: e0 (1), e2 (3); [P, Tag]: e1 (2)
after result 1: ecs_delete(world, Tag); eB = ecs_new_w_id(world, TagB);
result 2 is eB (no Position), from the freed [P, Tag] slice
```

**Properties:**
- P-IT3 (new): results match the query (Queries.md "Iteration").
- P1: no use of freed memory.

**Code path:**
- A freed table is zeroed in the store's sparse set, and the next table created gets its memory (storage/table.c 1333-1336; sparse.c 137-150, 365-395).
- The cache frees the match's arrays (cache.c 601-604, match.c 18-67).
- Slices are struct copies, built when the iterator is created (order_by.c 195-205).
- The iterator skips only slices with count 0 (cache_iter.c 81-99) and adopts the slice's `_trs` and columns (192-222).
- An order_by query always has change detection: `flecs_query_check_table_monitor` sets `EcsQueryHasChangeDetection` (change_detection.c 79-138). So even a skipped slice of a freed table has its freed monitor written (cache_iter.c 84-87, change_detection.c 581-633).

**Tapes:**
- P-IT3 (`sl lib explore`, seed 1), after 5,000 timelines: `sl.policy=0/2 sl.policy=0/2 sl.hasP=0/2 sl.tags=0/4 sl.hasP=0/2 sl.tags=3/4 sl.hasP=0/2 sl.tags=0/4 sl.k=0/3 sl.call=2/3 sl.k=1/2 sl.k=0/3 sl.call=0/3 sl.hasP=1/2 sl.tags=1/4 sl.v=0/3`. The program: delete T1, whose entity moves to `[P, T0]`, then `ecs_new [T0]`.
- P1 skip form, after 299 timelines.

**C test:** `query_order_by_reused_table_slot.c`. A crash also confirms.

### F47. Every stage of a multi-threaded order_by system sorts the table in place at once

**Property:** PW5 (no data race) and PW6 (new: sorting keeps every entity once). Systems.md "Threading": staging "makes it safe for multiple threads to iterate the same world without taking locks".

**Code path:**
- Each stage calls `ecs_query_iter` on the system's query (system.c 80-81).
- That runs `flecs_query_cache_sort_tables` (order_by.c 228-321): an in-place quicksort through `flecs_table_swap` (table.c 2014-2090), then slice and `match_count` writes.
- The monitor is synced only after the table is iterated (eval_iter.c 217-234).

**Tapes:**
- PW5 on the rows, after 5 timelines (2 stages, 3 rows): stage 0 runs 19 steps, then stage 1.
- PW6 with 2 rows, after 75,718 timelines: the entity column ends as [0, 0].

**C test:** `workers_order_by_sort_race.c`. The order_by callback is a rendezvous that detects two threads sorting at once; a crash or an abort also confirms.

## Seen again or extended
- **F33 extended:** two workers create the same page of `world->allocator.sizes` (sparse.c 11-54). Found after 24,762 timelines (PW4). With 2 tables, none in 3,000,000 (bound not reached).
- **F35 with a descending cascade:**
  - `iter6-desc-exhaust`: 3,000,000 programs (bound), 3,050 failing (freed group, P-IT1).
  - Tape after 28,640 timelines: the moved table's group is freed while it is iterated, and the default group (the roots) is never returned.

## Not counted as findings
- Inheritors of an entity that gains a base get only OnAdd, not OnSet: the forward's downward propagation passes the OnAdd observers (observable.c 835-890). This is not a documented scenario.
- The OnSet observer for a removed override receives `it->event == EcsOnRemove` (951-1001). flecs's own `Sparse_on_set_after_remove_override` asserts this.
- `ecs_iter_changed` fails its `it->next == ecs_query_next` check for worker iterators (change_detection.c 683). Read, not modelled.
- The depth arithmetic of the transposed spawner caches is consistent (tree_spawner.c 116-150). Read.

## What was replicated
- **OnSetInh:**
  - `ecs_get`'s source (instantiate.c 485-555);
  - the reachable walk (observable.c 708-780);
  - `flecs_emit_forward_id`'s storage and ownership checks;
  - the set propagation with per-table ownership.
- **Spawn6:** the `flecs_instantiate` dispatch, the spawner walk, and the auto-override type rules of both paths.
- **Slices:**
  - LIFO slot reuse of the sparse store;
  - deletes by OnDelete policy;
  - match frees and slice copies;
  - the skip with its monitor sync.
- **WSort:** the monitor check and allocation, swaps, slice and `match_count` writes, and the sync after iteration.
- **WCD:** page creation.
- **Query:** descending group order (group.c 41-48).
- **OrVMFuel:** the same VM as one structural function.

## What is not exact
- **OnSetInh:** one component and only the default observer. The remove-override event is taken as documented (F24 and flecs's test cover it). No prefab tags. The reachable list is computed fresh each call.
- **Spawn6:** one DontFragment component, and children fixed before instantiation.
- **Slices:** one order_by component and tags; the contents of freed memory are not modelled.
- **WSort:** one table; a selection sort stands in for the quicksort (the swap is the same).
- **WCD:** two size classes per page.
- **VM:** select, Or-select and DontFragment ops are not transcribed.

## Assumptions
- Debug build, asserts on. All new tests use `ecs_mini()` except F47 (`ecs_init()`, 2 threads).
- Iteration calls are world calls with the iterated table locked.
- Bases in the OnSet tests are prefabs; instances are not.

## Properties
New:
1. **P-OS1** (ObserversManual.md "OnSet and Inheritance"): broke (F41).
2. **P-OS2:** broke (F42, F43).
3. **P-SP2** (HierarchiesManual.md "Hierarchy storage"): broke (F44).
4. **P-IT3** (Queries.md "Iteration"): broke (F46).
5. **PW6** (Systems.md "Threading"): broke (F47).

Extended:
- P1 to instantiation auto-overrides (F45) and to stale slices (F46);
- PW5 to sorting (F47);
- PW4 to sparse pages (F33 extended);
- P-IT1 and P1 to the descending cascade (F35).

That makes 65 properties in all.

## Search runs
- **`osi exhaust 3 5`:** complete, 5,668,704 programs, 470,500 failing:
  - P-OS1: 212,906 Sparse, 212,906 DontFragment;
  - F42: 65,328;
  - IsA from a non-primary base (table): 2,976;
  - setting a non-primary base: 1,704 table, 1,704 Sparse, 3,312 DontFragment;
  - duplicates: 804, 804, 996.
- **`osi exhaust 4 4`:** complete, 1,843,968 programs, 93,704 failing.
- **`sp six-exhaust`:**
  - 4 nodes: complete, 12,288 programs, 12,114 failing (P1: 2,346 ChildOf and 6,900 Parent; P-SP2: 2,868);
  - 5 nodes: complete, 245,760 programs, 244,704 failing.
- **`sl exhaust 2 3 1`:** complete, 184,320 programs, 680 failing (P1 skip 488, P-IT2 192).
- **`sl explore`** (2 calls): 1,000,000 programs, 25,410 failing (P1 skip 22,020; reuse 223; P-IT3 135; P-IT2 3,197).
- **wsort and wcd:** as above.
- **`or agree 3 3 3`:** complete, 4,741,632 programs, 0 disagreements.
- **Regressions:**
  - `cases`, `val`, `or`, `sp`, `idf` and `pipe phase-cases`: identical to round 5;
  - `or exhaust`: 3,780 failing, as in round 5;
  - `query iter-exhaust`: 1,208 failing, as in round 5;
  - `sp exhaust 2 2 4`: 29,696 failing, as in round 5;
  - `iter5-explore`: 6,743 failing (round 5: 6,398); the difference is the new freed-slice P1 (438).

## Theorems
No `sorry`.
- `reach_dontFragment_nil` (all worlds) [propext]
- `isa_onset_needs_column` (all worlds) [no axioms]
- `onset_cases` (kernel) [propext]
- `spawner_only_parent` (all prefabs) [propext, Quot.sound]
- `spawner_cases` (kernel) [no axioms]
- `reused_slot_case` (kernel) [propext, Classical.choice, Quot.sound]
- `or_after_chain_iterate` (F34 through the fuel VM, kernel) [same]

## Library gaps
- Round 5's gaps remain: substring filters and truncated signatures (F42's detail had to be reworded to be filterable); no condition variables; no data-race notion, so this round's race logs are hand-written.
- `List.mergeSort` is well-founded recursion, which the kernel cannot evaluate; Slices uses a structural insertion sort.
- Derived `BEq` instances are not lawful for simp; the proofs use `rfl` on constructors.

## Model errors corrected
- **Round 5's slice skip:** a skipped slice of a freed table was taken as harmless. Corrected in Query.lean; F40 is unaffected.
- **This round, Slices:** the empty type took a store slot (it is the root table), and deleted tags could be added again. Both corrected; the numbers above are from the corrected runs.
- **This round, the OnSet model:** it stopped at the first violation, hiding F42 behind F41. Every call is now checked.
- **This round, WSort:** F33's monitor race masked the sort race; RACES 2 separates them.
- No earlier C test was changed.

## For round 7
- Run the F41–F47 C tests.
- Query VM: select and select_or on an unwritten `$this` (eval.c 52-150, 1390-1508), and Sparse and DontFragment ops in uncached parts (eval_sparse.c).
- OnSet for inheritors of an entity that gains a base.
- OnRemove and OnAdd propagation with DontFragment ownership.
- Spawner tables for auto-overridden Inherit table components.
- `ecs_iter_changed` in workers, and other lazy state in iterator init.
- The dirty state leaked on a zeroed table slot.
