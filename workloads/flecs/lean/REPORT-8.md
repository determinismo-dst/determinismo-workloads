# flecs v4.2.0 in Lean 4 — round 8 report

Everything is in `this directory`.

New files under `FlecsLean/`:
- `SlicesR8.lean`: order_by slices across iterators, with the cache's match counters, its monitor allocator, and the dirty state a skipped stale slice plants (F55 corrected, F56).
- `EvHier.lean`: OnAdd and OnRemove through the hierarchy with both storages, `ChildOf` pairs and the `Parent` component (F57; the ChildOf and Parent forms of F48 and F50).
- `SpawnDepth.lean`: the tree spawner for instances at depth (F58).
- `TheoremsR8.lean`: this round's theorems.

Extended files:
- `Slices.lean`: round 7's `check7` corrected (`flecs_init_table` resets `dirty_state`).
- `IterKinds.lean`: release builds (F53's NULL dereference), the validator's refusal of change detection with order_by, and F47's assert ahead of the callback.
- `SpawnInh.lean`: F52's call chain from `ecs_new_w_id` in its header, with the amalgamation's line numbers.
- `TheoremsR7.lean`: `dirty_state_case` restated for the correction; `worker_iter_calls_abort` re-proved over the extended `outcome`.
- `Axioms.lean`: the new theorems.

Other files:
- `Main.lean`: the `flecs-search` program.
- `tests/flecs_lean/`: 81 C tests, 6 of them new; none of the earlier ones changed. `README.txt` maps them to predictions, with build flags.
- `.jobs/r8/*.log`: this round's logs. `scratch/r8-runs.sh a|b|c|d|e` and `scratch/r8-runs2.sh f|g|h` re-run the searches.

New modes of `flecs-search`:
- `s8 explore|exhaust|lib ALLOC …|cases`, with `ALLOC` one of `block|os|sanitize` (F55, F56)
- `eh explore|exhaust|lib|cases` (F57)
- `sd exhaust|cases` (F58)

Line numbers refer to files under `src/` unless a path says otherwise. In a tape, `name=v/n` means the named decision took value `v` of `n` options.

## F55: why the guard did not fire

The model was wrong; the test was right.

**Did the skip's dirty state land in the slot?** Yes, by the code. Round 7's test watched only guards, not the slot.
- `ecs_delete(world, Tag)` frees `[Position, Tag]`. `flecs_sparse_remove_w_gen_t` zeroes its `ecs_table_t` in `world->store.tables` (storage/table.c 1333-1336; datastructures/sparse.c 389-391).
- The next `ecs_query_next` reaches the stale slice. Its count, read from the zeroed memory, is 0, so the slice is skipped. First its monitor is synced (query/cache/cache_iter.c 81-99).
- `flecs_query_sync_match_monitor` (query/cache/change_detection.c 581-633) calls `flecs_table_get_dirty_state` on the zeroed table (603). `dirty_state` is NULL, so it allocates `column_count + 1` = 1 int32 and stores the pointer into the zeroed slot (storage/table.c 1432-1450).

**Did the new table take that slot?** Yes. The test printed that [Velocity] took the freed memory: `flecs_sparse_new_index` hands out the slot freed last (sparse.c 137-150).

**Why nothing was written past the block.**
- `flecs_table_new` (storage/table_graph.c 433-494) ends with `flecs_init_table` (418-430). That function sets `table->dirty_state = NULL` (424) before calling `flecs_table_init`.
- Round 7 read `flecs_table_new` and `flecs_table_init` and missed this one.
- So [Velocity] starts without a dirty state, and `flecs_table_mark_dirty` does nothing (storage/table.c 1404).
- "Changed guards before the set 0, after it 0" is exactly what the code does.

**The model, corrected:**
- `Slices.check7` now drops the planted block when a table is created in its slot. `sl7 exhaust 2 3 1 2` is complete with 18,432,000 programs and 0 failing; round 7 found 256 there.
- `dirty_state_case` (TheoremsR7) states the corrected result.
- `new_table_drops_planted` (TheoremsR8) proves, for every world of the new model, that a new table never starts with a planted block.

**What the skip does instead.** `SlicesR8` follows the planted block to `ecs_fini`, models the monitor allocator, and follows the slices into later iterators. There are three consequences:
- **The block leaks.** The new table forgets it, and a dead slot is never finalized. With `FLECS_SANITIZE`, `flecs_ballocator_fini` reports "Leak detected!" and aborts in `ecs_fini` (datastructures/block_allocator.c 96-115).
- **With the default allocator, the query's monitor allocator is corrupted.** The same skip writes the freed monitor; round 6's F46 counted that write. With the default allocator the write lands on the chunk's free-list link, and a later monitor allocation dereferences it.
  - This is F55 without the OS allocator, in debug and release builds alike: no assert is on the path.
- **The stale slice outlives the iteration.** This is F56, below.

### F55 (corrected). The skip of a deleted table's order_by slice leaks a block, and with the default allocator it corrupts the query's monitor allocator

```c
Tag: OnDelete Delete; order_by Position; [P]: e0 (1), e2 (3); [P, Tag]: e1 (2)
after result 1 (table locked): ecs_delete(world, Tag);  // the next call skips the stale slice
// leak: the 1-int dirty state planted in the zeroed slot is never freed
// default allocator: four new entities with Position and A, B, C, D (four new matched tables)
ecs_query_iter(world, q);   // crash: the second new monitor is a wild pointer
```

**Properties:**
- P-L1 (new): every block flecs allocates is freed by `ecs_fini`. flecs.h `FLECS_SANITIZE`: "Enables expensive checks that can detect issues early. Recommended for running tests"; its leak check aborts.
- P1: no use of freed memory, no crash. Manual.md "Error handling".
- Queries.md "Iteration" (the delete does not touch the locked table) and "Sorting".

**Code path, the leak:**
- The block is planted as above.
- `flecs_init_table` drops it when a table takes the slot (table_graph.c 424).
- A dead slot is never finalized: `ecs_fini` walks only the live tables.

**Code path, the default allocator:**
- The cache frees the deleted table's monitor to `cache->allocators.monitors` (query/cache/match.c 41-43). For a one-field query the monitor is 8 bytes (query/cache/cache.c 620-621).
- A freed chunk's first 8 bytes are its free-list link: `chunk->next = ba->head` (block_allocator.c 274). This holds without `FLECS_SANITIZE`; that mode puts a 16-byte header before the data.
- The sync writes `monitor[0] = dirty_state[0]` (change_detection.c 606), so the link's low half becomes 1.
- `monitor[1]` is the link's high half, a heap address, never -1. So the term loop goes on:
  - `flecs_query_get_column_for_field` (30-75) reads the freed `base.columns`. Their first bytes are that allocator's own link, so the "column" is a multiple of 16 and never -1.
  - The loop then stores `dirty_state[column + 1]` into `monitor[1]` (627-628). That value is read past the 1-int block just planted, and it overwrites the link's high half.
- The link is now a wild pointer `(X << 32) | 1`.
- The next monitors are allocated when the next iterator sorts: `flecs_query_check_table_monitor` → `flecs_query_get_match_monitor` (change_detection.c 79-138) → `flecs_balloc`.
  - The first new match pops the corrupted chunk.
  - The second pops the wild pointer: `ba->head = ba->head->next` (block_allocator.c 168) reads at `(X << 32) | 1`. That crashes, or hands out a monitor at a wild address that the sort and the syncs then write.
- The read past the block can itself fault, at the skip.
- With `FLECS_USE_OS_ALLOC` and round 7's wrapper, freed blocks are kept and never reused, so only the leak shows.

**Story:**
- "leak: 1 dirty-state block(s) planted by the skip of a freed table's slice (flecs_table_get_dirty_state on the zeroed slot, storage/table.c 1432-1450) are never freed: flecs_init_table resets dirty_state of the next table in the slot (table_graph.c 424), and a dead slot is never finalized";
- "crash: the query's monitor allocator hands out a wild pointer: its free-list link was overwritten by the skip of a freed table's slice (change_detection.c 581-633 wrote monitor[0] and monitor[1] of the freed chunk, block_allocator.c 168, 274)".

**Tapes:**
- Leak (`s8 lib block exhaust`, 2 tags, 3 entities, 2 phases), after 1,406 timelines: `s8.policy=0/2 s8.policy=0/2 s8.hasP=0/2 s8.tags=0/4 s8.hasP=0/2 s8.tags=0/4 s8.hasP=0/2 s8.tags=0/4 s8.phase=1/3 s8.after=0/3 s8.call=0/3 s8.hasP=0/2 s8.tags=3/4 s8.v=1/3 s8.phase=1/3 s8.after=0/3 s8.call=2/3 s8.k=0/2`.
  - Shrunk: [P] e0 (2).
  - Iteration 1: after result 1, `ecs_new [P, T0, T1]` (3).
  - Iteration 2 (slices rebuilt): after result 1, `ecs_delete(T0)`.
- Crash (`s8 lib block explore`, 3 tags, 4 phases), after 650 timelines: `s8.policy=0/2 s8.policy=0/2 s8.policy=0/2 s8.hasP=0/2 s8.tags=5/8 s8.hasP=0/2 s8.tags=2/8 s8.hasP=0/2 s8.tags=6/8 s8.phase=2/3 s8.call=1/3 s8.e=3/7 s8.phase=0/3 s8.phase=1/3 s8.after=0/3 s8.call=2/3 s8.k=1/3 s8.phase=0/3`.
  - Shrunk: [P, T0, T2] e0, [P, T1] e1, [P, T1, T2] e2, every tag OnDelete Remove.
  - Iteration 1: after result 1, `ecs_delete(T1)`. e1 and e2 move to two new tables, [P] and [P, T2], and both freed tables' slices are skipped.
  - Iteration 2's sort allocates the two new monitors.
  - No explicit new entity is needed.

**C tests:**
- `query_order_by_skip_leaks_dirty_state.c`, built with `-DFLECS_USE_OS_ALLOC` or `-DFLECS_SANITIZE`.
  - With OS alloc, the wrapper tags the blocks allocated by the `ecs_query_next` that skips, and reports tagged 4-byte blocks still live after `ecs_fini`.
  - With sanitize, an abort in `ecs_fini` confirms.
  - A control world deletes Tag before the iterator.
- `query_order_by_skip_corrupts_monitor_allocator.c`, the default build, debug or `-DNDEBUG`. A crash or an abort confirms. The control world deletes Tag outside the iteration.
- Round 7's `query_order_by_freed_slot_dirty_state.c` is unchanged; its exit 0 is what the corrected model predicts.

## F52: the path to flecs.c 7976

The abort is the assert the model predicted. flecs.c 7976 of the v4.2.0 amalgamation is `ecs_assert(elem != NULL, ECS_INTERNAL_ERROR, NULL)` in `flecs_notify_on_set_w_cr`.
- flecs.c 7938 opens `flecs_notify_on_set_w_cr`.
- Lines 7974-7976 are component_actions.c 677-679: the `flecs_table_cache_get_elem` lookup and the assert.
- `flecs_new_entity` (flecs.c 8472-8494, entity.c 126-148) has three asserts (`r != NULL`, `ecs_table_count(table) > row`, `table == r->table`). None is on `elem`.
- The amalgamation's `elem != NULL` asserts are at 7841, 7976, 22267, 25208 and 44170.

`flecs_new_entity` is seven frames below the assert. The stack, with source and amalgamation lines:
1. `ecs_new_w_id` (entity.c 801; flecs.c 9147), from the test's `ecs_new_w_pair(world, EcsIsA, p)`;
2. `flecs_new_entity` (entity.c 143; flecs.c 8489), which calls `flecs_actions_new`;
3. `flecs_actions_new` (component_actions.c 369-381; flecs.c 7666-7676) → `flecs_actions_on_add_intern` (286-331), whose `flecs_emit` carries the added ids;
4. `flecs_emit`, for the OnAdd of `(IsA, p)`, calls `flecs_instantiate` (observable.c 1196-1226; flecs.c 15515);
5. `flecs_instantiate`: p's children use Parent storage, so it takes the TreeSpawner path (addons/prefab/instantiate.c 424-440; flecs.c 64969);
6. `flecs_spawner_instantiate` (tree_spawner.c 337-338; flecs.c 65674) → `flecs_instantiate_sparse(..., true)`;
7. `flecs_instantiate_sparse` (instantiate.c 129-130; flecs.c 64661) → `flecs_notify_on_set_w_cr(..., invoke_hook = true)`;
8. the assert (component_actions.c 679; flecs.c 7976).

The model's code path stands, and so do both tests. `SpawnInh.lean`'s header now carries this chain. A debugger's `bt` on the hook test should show these frames.

## The real flecs on round 7: the rest

As the coordinator reported: F48–F54 are confirmed, F52's hook form at the assert above. F55 is corrected above. The tracker has none of F48–F54.

## Counterexamples

### F56. A table deleted during an order_by iteration keeps its slice in later iterators; a table created later in its memory is returned by the next iterator

```c
Tag: OnDelete Delete; order_by Position; [P]: e0 (1), e2 (3); [P, Tag]: e1 (2)
iteration 1: after result 3 (e2, the last; table locked): ecs_delete(world, Tag);
ev = ecs_new_w_id(world, ecs_id(Velocity));   // [Velocity] takes the freed memory
iteration 2 (a new ecs_query_iter): e0, ev (no Position), e2
```

**Properties:**
- P-IT3: results match the query. Queries.md "Iteration".
- Queries.md "Sorting": "A query determines whether a sort operation is needed when an iterator is created for it".
- P1, for the stale slice's freed arrays. Manual.md "Error handling".

**Code path:**
- Deleting the table removes its match: `flecs_query_cache_remove_table_from_group` increments `cache->match_count` (query/cache/group.c 176-181).
- Every `ecs_query_next` after a result first syncs that result's monitor (query/engine/eval_iter.c 494-502 → `flecs_query_change_detection`, 217-232).
- `flecs_query_sync_match_monitor` ends with `cache->prev_match_count = cache->match_count` (change_detection.c 632). So the next call after the delete makes the cache forget it.
- The next `ecs_query_iter` calls `flecs_query_cache_sort_tables` (cache_iter.c 27-34; order_by.c 228-321).
  - That function rebuilds `cache->table_slices` only when a remaining match's monitor reports a change, or `match_count != prev_match_count` (315). Neither holds.
  - So the slice of the freed table stays. It is a struct copy holding the table pointer (order_by.c 195-205).
- The store gave the freed memory to [Velocity] (sparse.c 137-150; table_graph.c 443). Its count is 1, so the slice is not skipped (cache_iter.c 81-99).
- `flecs_query_cache_search` copies the slice's freed `_trs` and columns (cache_iter.c 326-377) and returns ev's row.
- A debug build may abort first in `flecs_iter_assert_columns` (eval_iter.c 253-273), as in F46.
- If no new table takes the slot, the next iterator skips the stale slice and writes its freed monitor again. These are F55's mechanisms, now from a fresh iterator.
- The slice lasts until a remaining matched table changes, for example a row added to [Position] (the control).

Round 6's F46 needed the new table to be created during the iteration. Here iteration 1 ends normally, the table is created later, and a new iterator uses the stale slice.

**Story:**
- "F56 later iterator: iterator 2 still has the slice of table 1, freed during iterator 1 (prev_match_count was synced, change_detection.c 632; no rebuild, order_by.c 315), names table 2's memory (count 1); the iterator returns that table with the slice's freed _trs and columns";
- "P-IT3 results match the query: F56 later iterator: iterator 2 returns e3, which does not have P (its table [[T1]] took the memory of table 1)".

**Tapes** (`s8 lib block exhaust`, 2 tags, 3 entities, 2 phases):
- After 175,751 timelines: `s8.policy=0/2 s8.policy=0/2 s8.hasP=0/2 s8.tags=0/4 s8.hasP=0/2 s8.tags=1/4 s8.hasP=0/2 s8.tags=3/4 s8.phase=1/3 s8.after=0/3 s8.call=2/3 s8.k=1/2 s8.phase=0/3`.
  - Shrunk: [P] e0, [P, T0] e1, [P, T0, T1] e2, all OnDelete Remove.
  - Iteration 1: after result 1, `ecs_delete(T1)`.
  - Iteration 2 still has the freed table's slice: it skips it and writes the freed monitor.
- The P-IT3 form, after 175,767 timelines: `s8.policy=0/2 s8.policy=0/2 s8.hasP=0/2 s8.tags=0/4 s8.hasP=0/2 s8.tags=1/4 s8.hasP=0/2 s8.tags=3/4 s8.phase=1/3 s8.after=0/3 s8.call=2/3 s8.k=1/2 s8.phase=1/3 s8.after=0/3 s8.call=0/3 s8.hasP=1/2 s8.tags=1/4 s8.v=0/3`. Iteration 2 creates an entity in a new [T0] table after its result 1; that table takes the freed slot, and the stale slice returns it.

**C test:** `query_order_by_stale_slice_next_iterator.c`. Two controls, each in its own world, run first:
- Tag deleted before iteration 1: two results;
- Tag deleted after the last result, then a row added to [Position]: three results.

A crash or an abort also confirms.

### F57. Re-parenting a child with Parent storage delivers no OnRemove: not for (ChildOf, old parent), not for the old parent's components

```c
Tag; p1 has Tag; p2 has nothing; observers Tag(up) OnAdd|OnRemove, (ChildOf, *) OnRemove
e = ecs_new_w_parent(world, p1, NULL); g = ecs_new_w_parent(world, e, NULL);
ecs_set(world, e, EcsParent, {p2});   // e and g lose Tag(up): no OnRemove at all
// ChildOf storage: c = ecs_new_w_pair(EcsChildOf, p1); ecs_add_pair(c, EcsChildOf, p2):
//   OnRemove Tag(up) for c from p1, and OnRemove (ChildOf, p1)
```

**Properties:**
- P-EV2: an entity that loses C gets an OnRemove. ObserversManual.md "OnRemove Events"; "Event Forwarding": "adding a pair results in forwarded OnAdd events, and removing a pair results in forwarded OnRemove events".
- P-EV6 (new): a `(ChildOf, *)` observer gets an OnRemove for the old parent when an entity's parent changes, with either storage. HierarchiesManual.md: "Relationship traversal works for both storages (`Position(up)` …)" and "Queries with `ChildOf` terms work with both storages".
- flecs's own tests treat the Parent component as `(ChildOf, parent)` for observers:
  - `Observer_on_add_childof_wildcard_w_parent_component` expects the OnAdd of `(ChildOf, p2)` after such a re-parent;
  - `Observer_on_remove_childof_w_parent_component` expects the OnRemove of `(ChildOf, p1)` when the component is removed;
  - `Observer_propagate_reparent_from_owned_to_empty_parent` is this program with ChildOf storage, and expects the OnRemove.

**Code path:**
- The Parent component's events are re-emitted as `(ChildOf, parent)` events (observable.c 1160-1183, `pdesc.event = event == EcsOnSet ? EcsOnAdd : event`):
  - OnSet becomes the OnAdd of `(ChildOf, parent)`, and OnRemove stays OnRemove;
  - their forward delivers the parent's components (`flecs_emit_forward`, 799-888).
- `ecs_set(e, EcsParent, {p2})` on a child that already has a Parent:
  - `flecs_copy_id` (entity.c 812-834) runs the `on_replace` hook `flecs_on_replace_parent` (storage/non_fragmenting_childof.c 113-197). It updates the ordered children, the name index and the depth.
  - Then `flecs_notify_on_set` runs. The OnSet becomes the OnAdd of `(ChildOf, p2)`; its reachable list (p2's table type, observable.c 708-780) is empty here.
- Nothing emits the OnRemove of `(ChildOf, p1)`, and nothing forwards p1's components as removed. `flecs_remove_non_fragmenting_child` (59-78) only updates the ordered children and counters.
- With ChildOf storage, the same call moves the entity to another table. `flecs_actions_move_remove` emits the OnRemove of the replaced exclusive pair before the OnAdd, with its forward and the downward propagation.

**Story:** "missing OnRemove: after ecs_set(e2, EcsParent, {e1}) (table), e2 (Parent storage) no longer has C (from e0), but the OnRemove observer was not invoked for it: setting the Parent component to another parent runs its on_replace hook (non_fragmenting_childof.c 113-197) and emits OnSet, which observable.c 1160-1183 re-emits as the OnAdd of (ChildOf, new parent) only: nothing emits the OnRemove of (ChildOf, old parent) or forwards the old parent's components as removed". The grandchild case adds "e3 (Parent storage) no longer has C (from e0)".

**Tapes** (`eh lib exhaust`, 3 entities, 5 calls):
- P-EV2 missing OnRemove and P-EV6, both after 1,889,798 timelines: `eh.storage=0/2 eh.hs=0/2 eh.hs=0/2 eh.hs=1/2 eh.call=0/4 eh.e=0/3 eh.call=0/4 eh.e=0/3 eh.call=0/4 eh.e=0/3 eh.call=2/4 eh.e=2/3 eh.p=0/3 eh.call=2/4 eh.e=2/3 eh.p=1/3`.
- Shrunk: `ecs_set(e0, C)`; `ecs_set(e2, EcsParent, {e0})`; `ecs_set(e2, EcsParent, {e1})`. For P-EV6, the first call is not needed.

**C test:** `parent_reparent_no_on_remove.c`.
- The ChildOf re-parent is the control.
- Removing the Parent component is printed; the model predicts its OnRemove is delivered.
- The prediction checks e, its child g, and the pair observer.

### F58. Instantiating a Parent-hierarchy prefab for an instance at depth 6 or more keeps the children's table for good; deleting the prefab then aborts

```c
base = prefab; c = ecs_new_w_parent(world, base, NULL); ecs_add(world, c, Foo);
p = a chain of 7 Parent ancestors; i = ecs_new_w_parent(world, p, NULL);   // depth 8
ecs_add_pair(world, i, EcsIsA, base);
ecs_delete(world, i);
ecs_delete(world, base);   // debug: abort; release: a table left over
```

**Property P-PF1** (new): after its instances are deleted, deleting a prefab with Parent children works and leaves none of its spawn tables behind.
- HierarchiesManual.md: "Prefab instantiation works with both storages".
- flecs's own `NonFragmentingChildOf_delete_instantiated_prefab_non_fragmenting_child` is this program at depth 0.
- Manual.md "Error handling".

**Code path:**
- `flecs_spawner_instantiate` (addons/prefab/tree_spawner.c 226-349) picks the vector of spawn children for the instance's depth (233):
  - `spawner->data[depth]` when depth < FLECS_TREE_SPAWNER_DEPTH_CACHE_SIZE (6, flecs.h 374);
  - otherwise a temporary vector (246-251).
- `flecs_spawner_transpose_depth` (120-149) adds `(ParentDepth, src_depth + depth)` to each child table and keeps the result (`flecs_table_keep`, 148).
- Releases:
  - `EcsTreeSpawner_free` (addons/prefab/prefab.c 21-27) releases the tables of `data[0..5]`. Deleting the prefab calls it first (`flecs_tree_spawner_fini`, on_delete.c 222 and 322).
  - The temporary vector is freed without a release (tree_spawner.c 348-350). Its table keeps a count that nothing decrements, and every deeper instantiation adds one.
- Deleting the prefab deletes c.
  - The cleanup of `(IsA, c)` releases its tables (`flecs_component_release_tables`, storage/component_index.c 753-776), skipping kept ones.
  - `ecs_delete` sets `force_delete` (entity.c 1356-1365). With it, on_delete.c 729-735 asserts ECS_INVALID_OPERATION, "cannot delete component '%s': tables are keeping it alive (likely because of used prefab)".
- A release build leaves the table in the store, with `(IsA, c)` naming a dead c. `ecs_delete_empty_tables` skips it too (world.c 1418).

**Story:** "after instances at depths [8] were instantiated and deleted, deleting the prefab finds the spawn table(s) for depth(s) [8] still kept: an instance at depth >= 6 (FLECS_TREE_SPAWNER_DEPTH_CACHE_SIZE) uses a temporary vector whose tables flecs_spawner_transpose_depth keeps (tree_spawner.c 148) and nothing releases (348-350); a debug build asserts in the cleanup of (IsA, prefab child) (on_delete.c 729-735), a release build leaves the table".

**Tape** (`sd exhaust 3`, complete): the first failing program is `sd.depth=0/9 sd.depth=0/9 sd.depth=6/9`. 513 of the 729 programs fail: exactly those with any depth ≥ 6 (729 − 6³).

**C test:** `prefab_parent_instantiate_depth_keeps_tables.c`.
- The control world uses an instance at depth 1.
- A debug build confirms by the abort.
- A release build confirms by a table left over after `ecs_delete_empty_tables`, compared with the control.

## The ChildOf and Parent forms of F48 and F50 (round 7's list)

`EvHier` models both storages. The forms seen have the same mechanisms as round 7's:
- **F50, ChildOf (confirmed in round 7) and Parent.** `ecs_new_w_parent(e0)` under a parent with a DontFragment C gives no OnAdd. The reachable list of `(ChildOf, e0)` never lists a DontFragment component (observable.c 708-780). With Parent storage, that list is reached through the re-emitted OnAdd (1160-1183).
- **F48, Parent.** Setting C on e0 propagates to its Parent child e2, which owns C (DontFragment), and on to e2's child e3. The non-fragmenting path walks `ordered_children` one row at a time (observable.c 389-418) and decides ownership by the child's table (324), like the table path.
- **The `notify` flag** of the Parent path (395-404) is true whenever a user observer exists. It matters only for internal up-notify observers, which are not modelled.

**C test:** `parent_storage_dont_fragment_events.c`, the Parent forms, with Position (table) as the control. These are the same findings seen again, not new ones.

## Release-build behaviours (round 7's list)

- **F53, `ecs_iter_changed`:**
  - The checks are compiled out (change_detection.c 680-705).
  - The worker iterator's `priv_.iter.query.elem` was copied by `ecs_worker_iter` (iter.c 1020) before the first result (system.c 81-101), so it is NULL.
  - `ecs_worker_iter`'s assignment of `priv_.iter.worker` overwrites only the union's first 8 bytes (`vars`; flecs/private/api_types.h 99-103, 145-182), not `elem`.
  - `flecs_query_check_match_monitor` passes the NULL to `flecs_query_get_match_monitor`. Its first read is `match->_monitor` (change_detection.c 89): a NULL dereference.
  - Theorem `release_worker_iter_changed_crashes`. The round-7 test already counts a crash as confirmation.
  - Tape (`ik lib exhaust`, filter `PI2 … | release build`), after 302 timelines: `ik.stages=1/2 ik.mt=1/2 ik.run=0/2 ik.dc=0/2 ik.orderby=1/2 ik.trivial=0/2 ik.call=0/3 ik.release=1/2`.
- **F53, `ecs_iter_skip`:** no crash.
  - The skip flag is set on the worker iterator, and `ecs_worker_next` overwrites it from the query iterator (iter.c 1049-1054).
  - So the table is marked dirty anyway.
  - The round-7 test does not detect this.
- **F55 without the OS allocator:** the free-list corruption above, the same in debug and release. The leak is silent unless `FLECS_SANITIZE` is set.

## Model errors corrected

- **F55** (above): `flecs_init_table` resets `dirty_state`. The test was right.
- **IterKinds, found while extending it:**
  - The validator refuses `EcsQueryDetectChanges` together with order_by: "change detection is not supported for queries with order_by" (query/validator.c 1831-1840). Round 7's counts included configurations with both, which cannot exist. They are now rejected.
  - In a debug build, a multi-threaded order_by system run on more than one stage aborts in its stage's `ecs_query_iter`, during the sort (order_by.c 87-88, F47's assert), before any callback. Round 7's PI2 tape (`ik.stages=1/2 ik.mt=1/2 … ik.orderby=1/2`) is such a configuration: in a debug build its abort is F47's.
  - Debug-build counts, corrected: PI1 2, PI2 4, PI3 11. Round 7 reported PI1 2, PI2 12, PI3 19 over the same 192 configurations.
  - F53's C tests use `EcsQueryDetectChanges` without order_by, so they stand.
- **Search procedure:** a lib filter is matched against the signature, which has no digits. A filter naming "F56" matched nothing (its first run is in `s8-lib-F56_later_iterator__iter.log`). It was rerun with a filter without digits.
- No earlier C test was changed.

## Seen again or extended

- **F46 → F55 → F56:** round 6's stale slice, round 7's skip, and now the same slice in later iterators. The skip's write into the freed monitor (F46's P1) is what corrupts the allocator in F55's corrected form.
- **F52 at depth:** the transposed spawn table differs from the depth-0 one only by its `ParentDepth` pair (tree_spawner.c 140-145). The Inherit filter (27-31) and `flecs_instantiate_sparse`'s walk are the same at every depth, so F52 aborts the same way. This was read, not modelled: `Spawn7` has no depth parameter.
- **F48, F50:** the Parent forms above.

## Not counted as findings

- **The source change on re-parenting with Parent storage.** When both parents provide C, the child gets the new parent's OnAdd and no OnRemove from the old one. flecs's own `Observer_up_forward_w_parent_component_reparent` expects exactly that OnAdd. The (entity, source) change itself is not filed; F57 is filed through the entity that loses C and through the pair observer.
- **eval_sparse.c, read again but not modelled:**
  - `flecs_query_sparse_with_id` with `not` and no sparse storage returns true without touching the range, which the previous op already wrote; a redo returns false.
  - `flecs_query_sparse_select_id` groups adjacent rows consistently in both directions.
  - No counterexample in reading.
- **`ecs_query_changed` after a table deleted during an iteration.** It returns false: the sync reset `prev_match_count` (change_detection.c 270). flecs.h says it returns true "after … tables have been matched or unmatched" "since the last iteration"; the unmatch happened during that iteration, so the statement is ambiguous. Not filed.

## What was replicated

- **SlicesR8:**
  - table store slots: the slot freed last is reused, freed memory is zeroed, and `flecs_init_table` resets the dirty state;
  - per table `dirty_state[0]`; per match a monitor chunk and `monitor[0]`;
  - `match_count` and `prev_match_count`: matches added and removed, the sync, iterator creation, the sort's increment;
  - the rebuild condition of `flecs_query_cache_sort_tables`, with lazily created monitors;
  - slices as struct copies; the skip and the yield of stale slices; the yield sync at the next `ecs_query_next`;
  - the monitor allocator's free list, with three allocator modes;
  - the planted dirty state, followed to `ecs_fini`.
- **EvHier:**
  - propagation of C through both storages, with ownership decided by table;
  - the reachable list of `(ChildOf, p)`: the table type, recursively through `(ChildOf, pp)` and the Parent component;
  - the forward of OnAdd and OnRemove, and its downward propagation;
  - the exclusive replace of a `ChildOf` pair, OnRemove first;
  - the Parent component's re-emission and its `on_replace` re-parent;
  - pair observers on `(ChildOf, *)`.
- **SpawnDepth:** the spawner's per-depth vectors, their keeps and releases, and the prefab's deletion.
- **IterKinds:** release builds, the validator's refusal, F47's assert first.

## What is not exact

- **SlicesR8:**
  - the generator makes one call per iteration; the C tests' programs are cases;
  - the link values are not computed: a corrupted link simply crashes the second allocation after it;
  - `FLECS_SANITIZE`'s header is modelled only as "no corruption";
  - the order_by column's own dirty state is not modelled: P is never set after creation.
- **EvHier:**
  - one component, self|up observers only;
  - no IsA, and no storage conversion (each entity's storage is fixed);
  - no deletes;
  - up-notify observers are not modelled.
- **SpawnDepth:** depths only, with one prefab child.

## Assumptions

- **Builds:**
  - debug with asserts on for every new test, except as follows;
  - `query_order_by_skip_leaks_dirty_state.c` needs `-DFLECS_USE_OS_ALLOC` or `-DFLECS_SANITIZE`;
  - `query_order_by_skip_corrupts_monitor_allocator.c` needs neither.
- All new tests use `ecs_mini()`.
- An observer created after the setup sees only the calls after it.
- F52's attribution comes from the amalgamation's text; no debugger was available here.

## Properties

New:
1. **P-L1** (flecs.h `FLECS_SANITIZE`): broke (F55 corrected).
2. **P-EV6** (HierarchiesManual.md, ObserversManual.md "OnRemove Events"): broke (F57).
3. **P-PF1** (HierarchiesManual.md "Prefab instantiation works with both storages"): broke (F58).

Extended:
- P1 to later iterators and to the monitor allocator (F55, F56);
- P-IT3 to later iterators (F56);
- P-EV1 and P-EV2 to both hierarchy storages (F57; the Parent forms of F48 and F50);
- PI2 and PI3 to release builds (F53).

That makes 77 properties in all.

## Search runs

- **`s8 exhaust 2 3 2`** (2 tags, 3 entities, 2 phases): complete, 32,000,000 programs, the same counts for `block`, `os` and `sanitize`. The crash needs a third tag. 137,318 failing:
  - skip of a slice freed in the same iteration (P1): 120,688;
  - leak (P-L1): 137,174;
  - F56, later iterator, skip-sync (P1): 52,588, and yield (P1): 1,848;
  - F56, P-IT3: 984.
- **`s8 explore block 2 3 3`:** 3,000,000 programs, 40,748 failing (F56 sync 31,026; leak 40,689; P-IT3 257).
- **`s8 explore 3 3 4`:**
  - `block`: 3,000,000 programs, 60,754 failing, 1,624 of them the allocator crash;
  - `sanitize`: 60,285 failing and no crash.
- **`s8 lib`:**
  - P-L1 after 1,406 timelines;
  - F56 after 175,751; its P-IT3 form after 175,767;
  - crash (3 tags, explore) after 650.
- **`eh exhaust`:**
  - 3 entities, 4 calls: complete, 1,679,616 programs, 66,608 failing;
  - 3 entities, 5 calls: complete, 30,233,088 programs, 1,848,016 failing. Among them: F57 missing OnRemove (table) 32,992; P-EV6 788,784; missing OnAdd (DontFragment) 518,944 for each storage; P-EV1 owner 119,504 (`ecs_set`) and 11,232 (`ecs_remove`);
  - 4 entities, 4 calls: complete, 19,668,992 programs, 923,344 failing.
- **`eh lib`:**
  - P-EV6 and missing OnRemove after 1,889,798 timelines;
  - missing OnAdd after 15,116,554; owner after 15,117,034; other source after 15,125,530;
  - "twice": none (complete, 30,233,088): a hierarchy has no diamonds.
- **`sd exhaust 3`:** complete, 729 programs, 513 failing.
- **`ik exhaust`:** complete, 384 configurations (debug and release), 39 failing:
  - debug: PI1 2, PI2 4, PI3 11;
  - release: PI1 2, PI2 8, PI3 12.
- **`sl7 exhaust 2 3 1 2`:** complete, 18,432,000 programs, 0 failing (the correction).
- **Regressions:**
  - `cases`, `val`, `or`, `query`, `sp`, `sp six`, `idf`, `osi`, `sl`, `ev`, `si`, `or uncached` and `pipe phase-cases`: identical to round 7;
  - `or exhaust 3 3 3`: 3,780 failing; `sl exhaust 2 3 1`: 680; `osi exhaust 4 4`: 93,704; `ev exhaust 3 4`: 44,566; `si exhaust 2 1`: 279. All as in round 7.

## Theorems

No `sorry`.
- `new_table_drops_planted` (all worlds): a new table never starts with a planted dirty state [propext, Classical.choice, Quot.sound]
- `slices8_cases` (kernel): the properties of the F55 and F56 programs and their controls [propext, Classical.choice, Quot.sound]
- `forward_kind` (all): a forward produces only its own event kind [propext, Quot.sound]
- `parent_reparent_no_remove` (all worlds): a Parent-storage re-parent delivers no OnRemove of any kind [propext, Quot.sound]
- `evhier_cases` (kernel): F57's program, the Parent form of F50, and the controls [propext, Classical.choice, Quot.sound]
- `spawn_depth_keeps` (all depths ≥ 6): the deep instance's spawn table survives the prefab's deletion [propext, Classical.choice, Quot.sound]
- `spawn_depth_cases` (kernel): depths 0, 1 and 5 work; 6 and 8 do not [propext]
- `release_worker_iter_changed_crashes` (all systems): F53's NULL dereference in a release build [propext]
- Round 7's `dirty_state_case` (restated) [propext, Quot.sound] and `worker_iter_calls_abort` (re-proved) [propext, Quot.sound]

## Library gaps

- Round 7's gaps remain:
  - no data-race notion;
  - `List.mergeSort` is not kernel-reducible, so the models use a structural insertion sort;
  - derived `BEq` is not lawful for simp: `(Next.workerNext != Next.queryNext) = true` had to be proved by `decide` and passed to `simp`.
- New:
  - `matches` is a keyword, so it cannot name a structure field;
  - a namespace's own `Op` shadows an `open`ed one: `Slices8` uses `abbrev Op := Flecs.Slices.Op`, and inside `do` blocks constructors need the full name.

## For round 9

- Run the new C tests:
  - `query_order_by_skip_leaks_dirty_state.c` with `-DFLECS_USE_OS_ALLOC`, and again with `-DFLECS_SANITIZE`;
  - `query_order_by_skip_corrupts_monitor_allocator.c` in a debug and a `-DNDEBUG` build;
  - `query_order_by_stale_slice_next_iterator.c`, `parent_reparent_no_on_remove.c`, `prefab_parent_instantiate_depth_keeps_tables.c` (debug and release), and `parent_storage_dont_fragment_events.c`.
- A debugger backtrace of F52's hook form, to settle the frame names.
- eval_sparse.c in a model: DontFragment select and with ops on entity ranges, SparseNot after `select_all`, and the trivial sparse search under removals.
- select_or with multi-op terms (up traversal, DontFragment), and the fields restored after the duplicate check.
- Other users of `prev_match_count` and of stale slices: `ecs_query_changed`, and group_by combined with order_by.
- The Parent storage's other re-emitted events: OnSet for `(ChildOf, parent)` observers, and a re-parent that changes depth (the `ParentDepth` replace in `flecs_on_replace_parent`).
- The spawner's temporary vector at depth: repeated instantiations at the same depth (the keep count grows), and a prefab child added after a deep instantiation.
