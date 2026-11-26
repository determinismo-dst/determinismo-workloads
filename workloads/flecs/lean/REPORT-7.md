# flecs v4.2.0 in Lean 4 — round 7 report

Everything is in `this directory`.

New files under `FlecsLean/`:
- `EvInh.lean`: OnAdd, OnRemove and OnSet together for inherited components, with IsA adds and removes (F48–F51).
- `SpawnInh.lean`: prefab children with the OnInstantiate traits and auto overrides, through both hierarchy storages (F52).
- `IterKinds.lean`: the iterator a system's callback or run callback receives, and the iterator functions that check it (F53, F54).
- `TheoremsR7.lean`: this round's theorems.

Extended files:
- `OrVM.lean`: uncached queries — `select` and `select_or` on an unwritten `$this`, and the `All` op of `select_all`.
- `Slices.lean`: the dirty state the skip of a freed slice leaves in the table store (F55); the iterator's column assert noted.
- `WorkersSort.lean`: the debug-build assert of order_by.c 87-88 (the F47 correction).
- `OnSetInh.lean`, `OrVMFuel.lean`: comment line numbers corrected; an `All` case in the fuel VM (unmodelled there).

Other files:
- `Main.lean`: the `flecs-search` program.
- `tests/flecs_lean/`: 75 C tests, 10 of them new; none of the earlier ones changed. `README.txt` maps them to predictions.
- `.jobs/r7/*.log`: this round's logs. `scratch/r7-runs.sh a|b|c|d|e|f|g|h` re-runs the searches.

New modes of `flecs-search`:
- `ev explore|exhaust|lib|cases` (F48–F51)
- `si exhaust|lib|cases` (F52)
- `ik exhaust|lib|cases` (F53, F54)
- `sl7 explore|exhaust|lib|cases` (F55)
- `or uncached-exhaust|uncached-lib|uncached-cases`
- `wsort … debug` (the assert of order_by.c 87-88)

Line numbers refer to files under `src/` unless a path says otherwise. In a tape, `name=v/n` means the named decision took value `v` of `n` options.

## The real flecs on round 6, and the F47 correction

As the coordinator reported, F41–F46 are confirmed, and F47 stands.

F47's model missed an assert. `flecs_query_cache_build_sorted_table_range` (query/cache/order_by.c 81-214) asserts `!(world->flags & EcsWorldMultiThreaded)` at 87-88, ECS_UNSUPPORTED, "cannot sort query in multithreaded mode". Every stage that sorted a table, or saw `match_count` move, reaches it (order_by.c 315-321), before it writes the slices.

The model now has a `debug` mode (`WorkersSort.lean`, step 20):
- **Debug build:** the first timeline already reaches the assert (P-A1, "no undocumented assert"). With the race checks on the rows only (RACES 2), PW5 still comes first, after 4 timelines: the stages race in the in-place sort before either reaches the assert. Without race checks, no timeline reached PW6 in 3,000,000 (bound not reached): the abort ends every run first.
- **Release build:** unchanged, the races of round 6 (PW5 after 5 timelines; PW6 with 2 rows after 75,718).

The test `workers_order_by_sort_race.c` is unchanged: it already counts an abort as confirmation. No documentation page states the assert.

The same holds for F46. In a debug build, the result taken from a reused slot aborts in `flecs_iter_assert_columns` (query/engine/eval_iter.c 251-271, called at 585): the freed `columns` and `_trs` disagree there. That is what the coordinator saw. The model's detail now says so; the prediction and the test (an abort confirms) are unchanged.

## Counterexamples

### F48. A base's OnAdd and OnRemove of a DontFragment component reach an instance that owns it, and that instance's inheritors

```c
Defense: DontFragment, Inherit
base = prefab; inst = IsA base; ecs_set(inst, Defense, {7}); inst2 = IsA inst
OnAdd and OnRemove observers (default source self|up IsA)
ecs_set(world, base, Defense, {60});   // OnAdd for inst and inst2, source base
ecs_remove(world, base, Defense);      // OnRemove for inst and inst2, source base
// ChildOf: parent; child = ChildOf parent, owns Mass (DontFragment);
// grandchild = ChildOf child; OnSet observer Mass(self|up)
ecs_set(world, parent, Mass, {1});     // OnSet for child and grandchild
```

**Property P-EV1** (new): a delivered OnAdd or OnRemove names the source that up traversal finds, for an entity that gains or loses the component, once.
- ObserversManual.md "OnAdd Events": "An event only fires when the component is actually added to the entity".
- "Event Propagation": "Events propagate until a leaf entity is found, or an entity with the propagated component is found ... if an event for Position is propagated from a parent to a child with Position, that event will not be propagated to the child's children. This ensures that the results are consistent with up traversal".

**Code path:**
- Adding the component emits OnAdd for base's table (`flecs_actions_on_add_intern`, component_actions.c 286-331; for a DontFragment component `flecs_sparse_on_add`, 153-177, reports the new element). Removing it emits OnRemove (333-367).
- `flecs_emit` propagates both down (observable.c 1312-1317): `flecs_propagate_entities` (571-611), `flecs_emit_propagate` (440-475, every traversable relationship), `flecs_emit_propagate_id` (378-438).
- `flecs_emit_propagate_id_for_range` (310-376) decides ownership by the table: `owned = flecs_component_get_table(cr, table) != NULL` (324). It skips the self|up observers of an owned table (347-350) and stops below it (361).
- A DontFragment component is in no table type, so no inheritor ever "owns" it. The same mechanism gave F42 its OnSet.

**Story:** P-EV1 reports "owner: after ecs_set(e1, C, 1) (DontFragment), the OnAdd observer was invoked for e2 with source e1, but after the call e2's C is e2 (its own…)". For the owner's inheritor: "other source: … invoked for e2 with source e0, but after the call e2's C is e1".

**Tapes** (`ev lib exhaust`, 3 entities, 5 calls):
- OnAdd, after 28,701,084 timelines: `ev.storage=2/3 ev.call=0/4 ev.e=0/3 ev.v=0/2 ev.call=0/4 ev.e=0/3 ev.v=0/2 ev.call=0/4 ev.e=2/3 ev.v=0/2 ev.call=1/4 ev.e=2/3 ev.b=1/3 ev.call=0/4 ev.e=1/3 ev.v=0/2`. Shrunk: `ecs_set(e2)`; `e2 IsA e1`; `ecs_set(e1)`.
- OnRemove, after 28,699,531 timelines: `ev.storage=2/3 ev.call=0/4 ev.e=0/3 ev.v=0/2 ev.call=0/4 ev.e=0/3 ev.v=0/2 ev.call=0/4 ev.e=1/3 ev.v=0/2 ev.call=1/4 ev.e=1/3 ev.b=0/3 ev.call=2/4 ev.e=0/3`. Shrunk: `ecs_set(e0)`; `ecs_set(e1)`; `e1 IsA e0`; `ecs_remove(e0)`.

The ChildOf form is read, not modelled: the propagation walks every traversable relationship with the same function.

**C test:** `propagate_on_add_remove_dont_fragment_owner.c`. Position (table) and Health (Sparse) are the controls for IsA, Velocity (table) for ChildOf.

### F49. OnAdd and OnRemove name a base that is not the entity's source

```c
Position: table, Inherit; b1 < b2 prefabs; b1 has Position {1, 1}
inst = IsA b1, IsA b2
ecs_set(world, b2, Position, {2, 2});    // OnAdd for inst, source b2
ecs_remove(world, b2, Position);          // OnRemove for inst, source b2
inst_f = IsA b1; b3 has Position {3, 3}
ecs_add_pair(world, inst_f, EcsIsA, b3);  // OnAdd for inst_f, source b3
ecs_remove_pair(world, inst_f, EcsIsA, b3); // OnRemove for inst_f, source b3
// ecs_get returns b1's value throughout
v = IsA b4; d = IsA b4, IsA v; ecs_set(b4, Position) // OnAdd for d twice
```

**Property P-EV1.**
- "OnAdd Events" and "OnRemove Events": an event fires only when the component is actually added or removed.
- "Event Forwarding": "Only reachable components are forwarded … this ensures consistency with the behavior of up traversal in queries".
- "Adding an IsA pair": the primary source is "the lowest entity id of all base entities that provide the component".

**Code path:**
- Propagation: `flecs_emit_propagate_id_for_range` (observable.c 310-376) invokes every entity of every `(IsA, b2)` table that does not own Position. Nothing asks whether another base provides it first.
- Forwarding: `flecs_emit_forward` (799-888) and `flecs_emit_forward_id` (613-706) forward every reachable element of the new or removed pair, with the same omission.
- Diamond: the propagation from b4 reaches d once through `(IsA, b4)`, and once more through v: it walks on below every entity of an unowned table (361-375).
- `ecs_get` takes the first base in type order (`flecs_get_base_component`, addons/prefab/instantiate.c 485-555). The same mechanism gave F43 its OnSet.

**Story:** "other source: after ecs_set(e1, C, 1) (table), the OnAdd observer was invoked for e2 with source e1, but after the call e2's C is e0".

**Tapes** (`ev lib exhaust`, 3 entities, 5 calls):
- Propagated OnAdd, after 9,102 timelines: `ev.storage=0/3 ev.call=0/4 ev.e=0/3 ev.v=0/2 ev.call=0/4 ev.e=0/3 ev.v=0/2 ev.call=1/4 ev.e=2/3 ev.b=0/3 ev.call=1/4 ev.e=2/3 ev.b=1/3 ev.call=0/4 ev.e=1/3 ev.v=0/2`. Shrunk: `ecs_set(e0)`; `e2 IsA e0`; `e2 IsA e1`; `ecs_set(e1)`.
- Forwarded OnAdd, after 1,796 timelines: shrunk `ecs_set(e0)`; `ecs_set(e1)`; `e2 IsA e0`; `e2 IsA e1`.
- Propagated OnRemove, after 48,482 timelines; forwarded OnRemove (`ecs_remove_pair`), after 48,491.
- A diamond's OnRemove twice, after 186,262 timelines: `e1 IsA e0`, `e2 IsA e0`, `e2 IsA e1`, `ecs_remove(e0)`.

**C test:** `propagate_on_add_remove_second_base.c`. The control is an entity whose only base gains Position (one OnAdd).

### F50. No OnAdd or OnRemove is forwarded for an inherited DontFragment component

```c
Defense: DontFragment, Inherit; base = prefab with Defense
inst = ecs_new(world);
ecs_add_pair(world, inst, EcsIsA, base);     // no OnAdd for Defense
ecs_remove_pair(world, inst, EcsIsA, base);  // no OnRemove for Defense
// ChildOf, the documentation's example: parent has Mass (DontFragment);
// observer Mass(up), OnAdd; child = ecs_new_w_pair(EcsChildOf, parent): none
```

**Property P-EV2** (new): every documented OnAdd and OnRemove is delivered.
- ObserversManual.md "Event Forwarding": "if a (ChildOf, my_parent) pair is added to an entity, and my_parent has components Position and Velocity, an OnAdd event is produced for each component and emitted for the child"; "adding a pair results in forwarded OnAdd events, and removing a pair results in forwarded OnRemove events".
- ComponentTraits.md "DontFragment trait" names ECS operations among what works; its limitations name monitors, not observers.

**Code path:**
- The forward lists the ids of the target's table type (`flecs_reachable_cache_ensure`, observable.c 708-780). IsA keeps only Inherit ids (736-738); ChildOf keeps all of them. A DontFragment component is in no table type.
- Instantiation does not add it either: `flecs_instantiate_dont_fragment` skips Inherit components of a base the instance has an IsA pair to (addons/prefab/instantiate.c 313-316).
- The same mechanism gave F41 its missing OnSet. With a Sparse component the OnAdd and OnRemove are forwarded: `flecs_emit_forward_id` gates only the OnSet on a column (685).

**Story:** "missing OnAdd: after ecs_add_pair(e1, EcsIsA, e0) (DontFragment), e1 now has C (from e0), but the OnAdd observer was not invoked for it".

**Tapes** (`ev lib exhaust`):
- OnAdd, after 28,697,824 timelines: `ev.storage=2/3 ev.call=0/4 ev.e=0/3 ev.v=0/2` (×4) `ev.call=1/4 ev.e=1/3 ev.b=0/3`. Shrunk: `ecs_set(e0)`; `e1 IsA e0`.
- OnRemove, after 28,698,079 timelines: `ev.storage=2/3 ev.call=0/4 ev.e=0/3 ev.v=0/2` (×3) `ev.call=1/4 ev.e=1/3 ev.b=0/3 ev.call=3/4 ev.e=1/3 ev.b=0/3`. Shrunk: `ecs_set(e0)`; `e1 IsA e0`; `ecs_remove_pair(e1, IsA, e0)`.

**C test:** `forward_on_add_remove_dont_fragment.c`, with Position (table) and Health (Sparse) as the IsA controls and Velocity (table) as the ChildOf control.

### F51. When an entity's inheritance changes, its inheritors get no OnSet for their new value

```c
Position: table, Inherit
base = prefab {1, 2}; variant = prefab; inst = IsA variant
ecs_add_pair(world, variant, EcsIsA, base);  // inst now reads {1, 2}: OnAdd, no OnSet
variant2 = prefab IsA base, owns {5, 5}; inst2 = IsA variant2
ecs_remove(world, variant2, Position);       // inst2 now reads {1, 2}: OnRemove, no OnSet
```

**Property P-OS3** (new): an OnSet reaches the inheritors of an entity in a documented OnSet scenario, when their value changes with it.
- ObserversManual.md "OnSet and Inheritance": "To ensure that OnSet events can be used reliably to detect component changes, events can be produced by operations that change inheritance relationships or operate on inherited from components".
- "Adding an IsA pair": "an OnSet event is generated for each newly inherited component".
- "Removing an Override" reexposes the base's component and "produces OnSet event".

**Code path:**
- (a) The forward of `(IsA, base)` on variant (observable.c 1196-1237; 799-888) invokes, for variant itself, the OnAdd and, because Position has a column, the OnSet observers (`flecs_emit_forward_id`, 613-706).
- Then, because variant is the target of an IsA pair, each element is propagated down to variant's inheritors with the observers of the emitted event only, OnAdd (`er`, 835-888). The OnSet observers (`er_onset`) are not passed down.
- (b) The override's OnSet is emitted for variant2's table only (`flecs_emit_on_set_for_override_on_remove`, 951-1002), without propagation, while the OnRemove is propagated (component_actions.c 333-367).

**Story:**
- "inheritor: after ecs_add_pair(e1, EcsIsA, e0) (table), e2 inherits C through e1 and its value changed from nothing to e0's, but no OnSet observer was invoked for it (the same call delivered it an OnAdd or OnRemove)".
- In (b) the OnRemove inst2 does get also breaks P-EV4 (new, "OnRemove only when C is gone"): "still has C: after ecs_remove(e1, C) (table), the OnRemove observer was invoked for e2 with source e1, yet e2 still sees C from e0". Tape after 46,295 timelines.

**Tape** (`ev lib exhaust`, P-OS3), after 361 timelines: `ev.storage=0/3 ev.call=0/4 ev.e=0/3 ev.v=0/2 ev.call=0/4 ev.e=0/3 ev.v=0/2 ev.call=0/4 ev.e=0/3 ev.v=0/2 ev.call=1/4 ev.e=2/3 ev.b=1/3 ev.call=1/4 ev.e=1/3 ev.b=0/3`. Shrunk: `ecs_set(e0)`; `e2 IsA e1`; `e1 IsA e0`.

**C test:** `inheritor_onset_base_change.c`. The control is a new instance of variant after (a): one OnSet, the documented scenario.

### F52. A Parent-storage prefab child with an Inherit component that is Sparse or has an on_set hook aborts the instantiation

```c
Velocity: (OnInstantiate, Inherit) and an on_set hook (or: Sparse, Inherit)
p = prefab; c = ecs_new_w_parent(world, p, NULL); set Position and Velocity on c
ecs_new_w_pair(world, EcsIsA, p);   // abort
```

**Property P1** (no internal assert).
- ComponentTraits.md "OnInstantiate trait" (Inherit).
- HierarchiesManual.md: "Prefab instantiation works with both storages"; "When instantiating a prefab with a Parent hierarchy, instance children will inherit from the prefab children".
- ComponentTraits.md "Sparse trait".

**Code path:**
- A prefab with Parent children is instantiated by its TreeSpawner (addons/prefab/instantiate.c 424-440).
- The instance child's table leaves out every id whose record has the Inherit or DontInherit trait (`flecs_prefab_spawner_build_type`, tree_spawner.c 27-31). The instance child inherits Velocity through `(IsA, c)` instead (60).
- `flecs_spawner_instantiate` (226-349) then calls `flecs_instantiate_sparse(..., emit_non_sparse = true)` (337-338). It walks c's whole table type and skips only DontInherit ids (instantiate.c 73-133, 103):
  - for a Sparse id it copies the value into the instance child's sparse storage after `ecs_assert(dst_ptr != NULL)` (119-124);
  - for every id it calls `flecs_notify_on_set_w_cr(..., invoke_hook = true)` (129-130). For a component with an on_set hook, that looks the instance child's table up in the component's table cache and asserts it is there (component_actions.c 672-681, the assert at 679).
- The ChildOf path copies Inherit components to the instance child (instantiate.c 171-184), so they are in its table.
- flecs's own `NonFragmentingChildOf_instantiate_w_inherit` has neither a hook nor Sparse storage. Its `..._w_auto_override` (the auto-overridden Inherit table component, round 6's open item) behaves as documented in the model too: no P-SP3 failure anywhere.

**Story:** "prefab child 0 has C1 (table, Inherit, on_set hook), which the instance child's spawner table leaves out (tree_spawner.c 27-31): … flecs_notify_on_set_w_cr asserts …".

**Tapes** (`si lib exhaust`, 2 components, 1 child):
- Hook, after 130 timelines: `si.storage=0/2 si.hook=0/2 si.trait=0/3 si.storage=0/2 si.hook=1/2 si.trait=1/3 si.hier=0/2 si.has=0/4 si.has=1/4`.
- Sparse, after 226 timelines: `si.storage=0/2 si.hook=0/2 si.trait=0/3 si.storage=1/2 si.hook=0/2 si.trait=1/3 si.hier=0/2 si.has=0/4 si.has=1/4`.

**C tests:**
- `prefab_parent_child_inherit_on_set_hook.c`;
- `prefab_parent_child_inherit_sparse.c` (it includes the first with `FLECS_LEAN_SPARSE`).

Both check the ChildOf and auto-override controls first; an abort confirms.

### F53. ecs_iter_changed and ecs_iter_skip abort in a multi-threaded system

```c
system Sys: multi_threaded, query { Position, in }, .flags = EcsQueryDetectChanges
callback: ecs_iter_changed(it);      // (or ecs_iter_skip(it))
ecs_progress(world, 0);              // no threads: works
ecs_set_threads(world, 2); ecs_progress(world, 0);   // abort
```

**Properties:**
- **PI2** (new): `ecs_iter_changed` on the iterator a system gets works for a query with change detection. flecs.h: "This operation must be used in combination with a query that supports change detection (e.g., is cached)", no other condition. Queries.md "Change Detection".
- **PI3** (new): `ecs_iter_skip` on it works. Queries.md: "If no changes are made to the iterated table, the skip function can be called to prevent marking the matched components as dirty".
- Systems.md "Threading" (multi_threaded systems).

**Code path:**
- With more than one stage, `flecs_run_system` gives a multi_threaded system's callback a worker iterator (addons/system/system.c 97-101; `ecs_worker_iter`, src/iter.c 1008-1034: `next = ecs_worker_next`).
- `ecs_iter_changed` starts with `ecs_check(it->next == ecs_query_next, ECS_UNSUPPORTED)` (query/cache/change_detection.c 680). `ecs_iter_skip` has `ecs_assert(it->next == ecs_query_next, ECS_INVALID_PARAMETER)` (718).
- Release build, `ecs_iter_changed`: it reads `it->priv_.iter.query.elem` (704-705). The worker iterator's private data is its own; that field was copied when the worker iterator was made, before the first result (iter.c 1020), and `ecs_worker_next` copies only the part before `priv_` (1053-1054). The NULL goes to `flecs_query_check_match_monitor`.
- Release build, `ecs_iter_skip`: it sets EcsIterSkip on the worker iterator, whose flags `ecs_worker_next` overwrites from the query iterator, so the table is marked dirty anyway.

**Story:** "2 stage(s), multi_threaded system, callback, query with EcsQueryDetectChanges …: ecs_iter_changed: ecs_check(it->next == ecs_query_next, ECS_UNSUPPORTED) fails (change_detection.c 680; it->next is ecs_worker_next)".

**Tape** (`ik lib exhaust`, PI2), after 151 timelines: `ik.stages=1/2 ik.mt=1/2 ik.run=0/2 ik.dc=0/2 ik.orderby=1/2 ik.trivial=0/2 ik.call=0/3`. That is an order_by query, which has change detection (Queries.md "Sorting"). The exhaustive run has all 12 PI2 and 16 of the 19 PI3 failures in multi-threaded systems.

**C tests:**
- `iter_changed_multi_threaded_system.c`;
- `iter_skip_multi_threaded_system.c` (it includes the first with `FLECS_LEAN_SKIP`).

Both use `ecs_mini()` with FlecsPipeline and `ecs_set_os_api_impl()`, and link with -lpthread. The first frame runs without threads (control). An abort or a crash confirms.

### F54. The run callback of a single-threaded system over a trivially cached query does not get a query iterator, and ecs_iter_skip aborts there

```c
system Run: .run = Run, query { Position } (no phase); ecs_run(world, Run, 0, NULL)
Run: it->next == ecs_query_next                   // false
     while (ecs_iter_next(it)) ecs_iter_skip(it);  // abort
```

**Properties:**
- **PI1** (new): the run callback of a system that is neither multithreaded nor paged gets a query iterator. include/flecs/addons/system.h 55-66 (`ecs_system_desc_t::run`): "When a system is multithreaded and/or paged, the iterator can be either a worker or a paged iterator … An implementation can test whether the iterator is a query iterator by testing whether the it->next value is equal to ecs_query_next()".
- **PI3.**

**Code path:**
- A system's query is cached (query/api.c 107-115: a query with an entity).
- A cache of one self term without order_by, group_by or change detection is trivial (query/cache/cache.c 755-777). So `flecs_query_iter_constrain` sets EcsIterTrivialCached (query/engine/eval_iter.c 135-143).
- With a run callback, `flecs_run_system` then sets `it->next = flecs_query_trivial_cached_next` (system.c 119-121). `ecs_iter_skip` asserts `it->next == ecs_query_next` (change_detection.c 718).
- A release build honours the skip: `flecs_query_trivial_cached_next` reads EcsIterSkip before clearing it (eval_iter.c 640-646).
- With change detection the cache is not trivial and `next` stays `ecs_query_next`: the control.

**Story:** "1 stage(s), single-threaded system, run callback, query without change detection, trivial cache shape …: it->next is flecs_query_trivial_cached_next, not ecs_query_next (system.c 119-121)".

**Tapes** (`ik lib exhaust`):
- PI1, after 30 timelines: `ik.stages=0/2 ik.mt=0/2 ik.run=1/2 ik.dc=0/2 ik.orderby=0/2 ik.trivial=1/2 ik.call=2/3`.
- PI3, after 29: the same with `ik.call=1/3`.

**C test:** `system_run_trivial_cache_next.c` (`ecs_mini()` with FlecsPipeline). The control system has EcsQueryDetectChanges.

### F55. The skip of a deleted table's order_by slice plants a one-element dirty state in the table store; the next table created there writes past it

```c
Tag: OnDelete Delete; order_by Position; [P]: e0 (1), e2 (3); [P, Tag]: e1 (2)
after result 1 (table locked): ecs_delete(world, Tag);  // the iteration goes on
after the iteration: ev = ecs_new_w_id(world, ecs_id(Velocity));
ecs_set(world, ev, Velocity, {1, 2});   // writes dirty_state[1] of a 1-int block
```

**Property P1:** no write past an allocation. Manual.md "Error handling"; Queries.md "Iteration" (the delete does not touch the locked table) and "Sorting".

**Code path:**
- The delete frees `[P, Tag]`. `flecs_table_fini` zeroes its `ecs_table_t` in `world->store.tables` (storage/table.c 1333-1336; datastructures/sparse.c 391-393).
- The iterator skips the stale slice because its count, read from the zeroed memory, is 0. But first it syncs the slice's monitor (cache_iter.c 81-99: `flecs_query_sync_match_monitor`).
- That calls `flecs_table_get_dirty_state` on the zeroed table (change_detection.c 600-606). `dirty_state` is NULL, so it allocates `column_count + 1` = 1 int32 and stores the pointer into the zeroed slot (storage/table.c 1432-1450).
- `flecs_table_new` takes the slot freed last (table_graph.c 443: `flecs_sparse_add_t`, which does not zero it, sparse.c 258-269). Neither it nor `flecs_table_init` sets `dirty_state`, so the new table starts with the one-element block.
- `ecs_set` marks the column dirty (`ecs_set_id`, entity.c 2026, `flecs_copy_id`, 833: `flecs_table_mark_dirty`, storage/table.c 1397-1429): `dirty_state[column]++` with column ≥ 1, past the block. Query monitors read `dirty_state[tc.column + 1]` (change_detection.c 581-633).
- Without `FLECS_USE_OS_ALLOC` the block is a 16-byte chunk of the world's allocator. A table with 4 or more columns then writes into the next chunk, and the table's free returns the chunk to another size class (storage/table.c 1318: `flecs_wfree_n(world, int32_t, table->column_count + 1, ...)`).
- The same skip also writes the freed monitor (round 6's F46, P1); that is not counted again.

**Story:** "ecs_set(P) on an entity of table 2 [P, T1], created after the iteration in the slot of a table freed during it: the skip of that table's slice allocated a 1-element dirty state into the zeroed slot … flecs_table_mark_dirty writes dirty_state[1] … past the block".

**Tape** (`sl7 lib exhaust`, 2 tags, 3 entities, 1 call during, 2 after), after 4,628,919 timelines: `sl.policy=0/2 sl.policy=1/2 sl.hasP=0/2 sl.tags=0/4 sl.hasP=0/2 sl.tags=0/4 sl.hasP=0/2 sl.tags=2/4 sl.k=0/3 sl.call=2/3 sl.k=1/2 sl7.post=0/2 sl.hasP=0/2 sl.tags=1/4 sl7.post=1/2 sl7.k=0/2`. The program: delete T1 after the first result, then `ecs_new [P, T0]` and `ecs_set(P)` on it.

**C test:** `query_order_by_freed_slot_dirty_state.c`, built with `-DFLECS_USE_OS_ALLOC` (it returns 2 without it). Its OS API wrapper puts a guard after every block and keeps freed blocks, filled with 0xFF. A changed guard on a 4-byte block confirms.

## Seen again or extended
- **F41 → F50, F42 → F48, F43 → F49:** for each round-6 OnSet finding, the documented OnAdd and OnRemove paths have the same mechanism. So do the ChildOf examples of "Event Propagation" (F48 (b)) and "Event Forwarding" (F50 (b)): the propagation and the reachable cache take the relationship as a parameter.
- **F44, F45:** the auto override of an Inherit table component on a Parent child behaves as documented (`si`: no P-SP3 failure). F52 is the Inherit component without one.
- **F46 → F55:** the stale slice's skip, already a use after free, also leaves a dirty state behind.
- **F47:** the debug-build assert (above). The other lazy state in iterator init across workers is F33's (the dirty state) and F53's (the iterator kind).
- **The uncached query VM:** `select` and `select_or` on an unwritten `$this`, and `All` for a leading Not or Optional, agree with the documented results in every program run (see the search runs).

## Not counted as findings
- **P-EV4 alone:** an entity whose primary base loses C, but which still reads C from another base, gets an OnRemove (`ecs_remove` 192 and `ecs_remove_pair` 240 programs per storage in `ev exhaust 3 5`). For up observers that is the (entity, source) pair going away, so it is only filed inside F51's story.
- **Removing an IsA pair** re-exposes another base's value without an OnSet. That is not a documented OnSet scenario.
- **eval_sparse.c**, read and not modelled:
  - `flecs_query_sparse_select_id` walks the dense array from its end, so removing the current entity's component is safe, and an assert catches a shrunk set.
  - `flecs_query_trivial_sparse_search` walks forward in batches of 1024 (FLECS_QUERY_SPARSE_BATCH_SIZE). Removals during an undeferred iteration of more than 1024 entities would skip entities that the removal swaps into visited slots. Queries.md asks for deferred or staged changes during iteration, so not filed.
  - The range grouping of `flecs_query_sparse_next_entity` and of the select's `while (!op->src.var …)` loop is consistent.
- **The All op** starts at the second element of `world->store.tables` (eval.c 288-311: `cur` is 1 when the first store table is read). `flecs_clean_tables` does the same (world.c 414), so element 0 is reserved. Read.

## What was replicated
- **EvInh:** the OnAdd, OnRemove and OnSet paths of `ecs_set`, `ecs_remove`, `ecs_add_pair(IsA)` and `ecs_remove_pair(IsA)`:
  - the propagation with per-table ownership;
  - the reachable list;
  - the forward's OnAdd, its OnSet when the element has a column, and the downward OnAdd propagation;
  - the override OnSet on remove.
- **Spawn7:** the spawner's table type (trait filter, AUTO_OVERRIDE ids, `(IsA, child)`); `flecs_instantiate_sparse`'s walk with its two asserts; the ChildOf path's type.
- **IterKinds:** the iterator kind `flecs_run_system` hands out (worker, trivially cached run, query) and the checks of `ecs_iter_changed` and `ecs_iter_skip`.
- **Slices (sl7):** the dirty state planted by the skip, the slot reuse that keeps it, and `flecs_table_mark_dirty`'s index.
- **OrVM:**
  - `flecs_query_select_w_id` at table level;
  - `flecs_query_select_or` with its duplicate check (`flecs_query_run_until_for_select_or`, `flecs_query_last_op_for_or_cond`, the zeroed and restored op context of the first term);
  - `flecs_query_all`, `flecs_query_select_all`, and the uncached compile order.
- **WSort:** the assert of order_by.c 87-88.

## What is not exact
- **EvInh:**
  - one component, and the default self|up observers only (no `up`-only observer);
  - IsA only (the ChildOf forms are read);
  - plain entities: no prefab filter (`flecs_ignore_observer`). The C tests use prefab bases whose own events do not matter;
  - no deletes.
- **Spawn7:** one level of children, fixed before instantiation (changes after it are F39). No on_validate hooks; DontFragment components are left to round 6's model.
- **IterKinds:** configurations, not executions. Paged iterators are not modelled.
- **sl7:** the block sizes of the allocator are not modelled; P1 is the index past `column_count + 1`.
- **OrVM uncached:**
  - single-op `$this` self terms on table or fragmenting Sparse components;
  - all tables non-empty, none prefab or disabled;
  - only the yielded tables, not the fields (`ids`, `columns`).

## Assumptions
- Debug build, asserts on, for every new test. All use `ecs_mini()`:
  - with FlecsPipeline for systems;
  - with `ecs_set_os_api_impl()` for threads;
  - F55 additionally with `-DFLECS_USE_OS_ALLOC`.
- An observer created after the setup sees only the calls after it.
- ObserversManual.md's "consistent with up traversal" is read with up traversal finding the first base in type order, as `ecs_get` does.

## Properties
New:
1. **P-EV1** (ObserversManual.md "OnAdd Events", "Event Propagation", "Event Forwarding"): broke (F48, F49).
2. **P-EV2** ("Event Forwarding"): broke (F50).
3. **P-EV4** ("OnRemove Events"): broke, filed inside F51.
4. **P-OS3** ("OnSet and Inheritance"): broke (F51).
5. **P-SP3** (ComponentTraits.md "OnInstantiate trait", HierarchiesManual.md): held.
6. **PI1** (system.h, `ecs_system_desc_t::run`): broke (F54).
7. **PI2** (flecs.h, `ecs_iter_changed`): broke (F53).
8. **PI3** (Queries.md "Change Detection"): broke (F53, F54).
9. **P-A1** (no undocumented assert): broke (F47 in a debug build).

Extended:
- P1 to the spawner's Inherit components (F52) and to the store's dirty state (F55);
- PQ-OR1 to uncached queries (held).

That makes 74 properties in all.

## Search runs
- **`ev exhaust 3 4`:** complete, 1,594,323 programs, 44,566 failing.
- **`ev exhaust 3 5`:** complete, 43,046,721 programs, 1,857,196 failing:
  - F50: missing OnAdd 869,810 and missing OnRemove 69,462 (DontFragment);
  - F48: owner after `ecs_set` 137,172, after `ecs_remove` 8,664; through an owner 4,944 and 192 (DontFragment);
  - F49 (table; the same for Sparse): other source after `ecs_set` 2,520, `ecs_add_pair` 2,568, `ecs_remove` 96, `ecs_remove_pair` 96; twice after `ecs_set` 1,188, `ecs_remove` 48;
  - F51: P-OS3 after `ecs_add_pair` 17,290 and after `ecs_remove` 192 (per storage); P-EV4 192 and 240 (per storage);
  - round 6's, seen again: P-OS1 855,088 (Sparse and DontFragment each); P-OS2 158,160 (DontFragment), 3,960 and 2,568 (table).
- **`ev exhaust 4 4`:** complete, 11,244,288 programs, 252,100 failing, the same kinds.
- **`si exhaust`:**
  - 2 components, 1 child: complete, 4,608 programs, 279 failing (P1: 93 hook, 186 Sparse);
  - 2 components, 2 children: complete, 73,728 programs, 7,623 failing;
  - 3 components, 1 child: complete, 221,184 programs, 19,467 failing;
  - P-SP3: none, also by `si lib exhaust` (complete).
- **`ik exhaust`:** complete, 192 configurations, 33 failing (PI1 2, PI2 12, PI3 19).
- **`sl7`:**
  - `exhaust 2 3 1 2`: complete, 18,432,000 programs, 256 failing (P1);
  - `explore` (2 calls during the iteration, 3 after): 2,000,000 programs, 763 failing.
- **`wsort … debug`:** P-A1 at the first timeline; with RACES 2, PW5 after 4 timelines; with RACES 0 and filter PW, none in 3,000,000 (bound not reached).
- **`or uncached-exhaust`:**
  - 3 components, 3 terms, 3 tables: complete, 4,741,632 programs, 0 failing (1,224,720 ran, 317,520 of them with a select_or chain; the rest have duplicate table types or are rejected);
  - 2 components, 4 terms, 3 tables: complete, 442,368 programs, 0 failing (31,104 ran, 13,440 with a chain).
- **Regressions:**
  - `cases`, `val`, `or`, `query`, `sp`, `sp six`, `idf` and `pipe phase-cases`: identical to round 6;
  - `osi cases` and `sl cases`: differ only in the corrected detail text;
  - `or exhaust 3 3 3`: 3,780 failing, as round 6; `or agree 3 3 3`: 0 disagreements;
  - `sl exhaust 2 3 1`: 680, as round 6; `osi exhaust 4 4`: 93,704, as round 6;
  - `query iter-exhaust`: 1,208, as round 6; `sp exhaust 2 2 4`: 29,696, as round 6.

## Theorems
No `sorry`.
- `propF_skips_owners` (all worlds, table and Sparse storage): the propagation reaches no entity that owns C [propext, Quot.sound]
- `prop_dontFragment_reaches_owner` (kernel): with DontFragment it does [propext, Classical.choice, Quot.sound]
- `isa_dontFragment_silent` (all worlds): with DontFragment, adding or removing an IsA pair delivers no event [propext]
- `ev_cases` (kernel): the events of the F48–F51 C tests' programs, call by call [propext]
- `spawner_inherit_asserts` (all prefabs): a Parent child that owns an Inherit component that is Sparse or has an on_set hook, not auto-overridden, makes the instantiation assert [propext, Classical.choice, Quot.sound]
- `spawner_inherit_cases` (kernel): F52's programs and controls [propext, Quot.sound]
- `worker_iter_calls_abort` (all systems): with more than one stage, a multi-threaded system gets a worker iterator, and `ecs_iter_changed` and `ecs_iter_skip` abort [propext, Quot.sound]
- `run_trivial_next` (all systems): a run callback without workers over a trivial cache gets `flecs_query_trivial_cached_next` [propext]
- `dirty_state_case` (kernel): F55's program plants a dirty state in slot 1 and breaks P1; both controls do not [propext, Quot.sound]

## Library gaps
- Round 6's gaps remain:
  - no data-race notion (the debug-mode WSort timelines are read by hand);
  - `List.mergeSort` is not kernel-reducible, so SpawnInh sorts by a structural insertion sort, with its membership lemma proved;
  - derived `BEq` is not lawful for simp (the proofs use `rfl` on constructors).
- New: `decide +kernel` could not synthesize the `Decidable` instance of a 7-way conjunction of list equalities that it decides one by one. The theorems split the conjunction with `refine`.
- New: `simp` turns `Array.getD` into `a[i]?.getD`, so hypotheses about `getD` must be restated before rewriting.

## Model errors corrected
- **F47:** the debug-build assert (above). The test is unchanged.
- **F46:** the debug-build column assert (above). The test is unchanged.
- **This round, IterKinds:** corrected before the counts above:
  - the first version counted `ecs_iter_changed` on queries without change detection, whose documented precondition is unmet;
  - it counted run callbacks of multi_threaded systems run on one stage under PI1, which the documentation allows.
- **OnSetInh.lean:** its header comment had stale line numbers (`flecs_emit_propagate` 468-492 and others). They are corrected; the code and round 6's report were right.
- No earlier C test was changed.

## For round 8
- Run the F48–F55 C tests (F55 with `-DFLECS_USE_OS_ALLOC`; F53 with threads).
- Model the ChildOf forms of F48 and F50, and the non-fragmenting ChildOf (`Parent`) propagation path (observable.c 384-415, with its notify flag).
- eval_sparse.c in a model: DontFragment select and with ops on entity ranges, SparseNot after `select_all`, and the trivial sparse search under removals.
- select_or with multi-op terms (up traversal, DontFragment), and the fields (`ids`, `columns`) restored after the duplicate check.
- The release-build behaviours: F53's NULL dereference, F55 without the OS allocator.
- The spawner at depth (instances that are children: `flecs_spawner_transpose_depth`) with Inherit components.
