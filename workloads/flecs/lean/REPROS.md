# flecs repros

From the Lean replica of flecs v4.2.0 (the latest release), written blind from its source in eight
rounds (REPORT.md to REPORT-8.md: each finding's minimal program, story, tape, code path and the
documentation it breaks). Every entry below was reproduced on the real flecs v4.2.0: its C test
(tests/flecs_lean) compiled against the release's single-file distribution with asserts on (a
debug build: `FLECS_DEBUG` without `NDEBUG`), on macOS and on Linux (the
`flecs-lean` workflow); F47's race also in a release build (`NDEBUG`), as its entry says. A
test returns 0 when flecs behaves as documented; the output shown is the real flecs's. Each entry's
"Tracker" line says whether flecs's issues or PRs already have it (searched 2026-11-25).

Each block runs from this directory with flecs v4.2.0's source in `flecs/`:

```sh
curl -fsSL https://github.com/SanderMertens/flecs/archive/refs/tags/v4.2.0.tar.gz | tar -xz && mv flecs-4.2.0 flecs
```

## Crashes: flecs's own internal or parameter asserts on documented use

- [ ] **F34: A cached query whose Or chain starts with a table term and ends with a Sparse term, with a term after the chain, returns wrong entities, and compiling it writes 42 bytes before the op array**. Story, code path and the docs it breaks: REPORT-5.md, F34.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-26).
  Proposed fix: F29's patch ([fixes/F29.diff](fixes/F29.diff); verified: its test passes with it on v4.2.0 and fails without; flecs's core, query, addons, collections and cpp suites as on v4.2.0).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/query_or_sparse_term_after_chain.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# guard of a 384-byte block changed at offset 22 (42 bytes before the block)
# uncached: 2 entities: e2 e3
# cached: 1 entities: e1
```

- [ ] **F35: While a cascade query is iterated, a call that changes a parent's depth returns a table again, or frees the group being iterated (a read of freed memory)**. Story, code path and the docs it breaks: REPORT-5.md, F35.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-26).
  No small fix: F30's design question, for cascade groups (fixes/README.md).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/query_cascade_table_twice.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: c1 returned 2 times, c2 returned 1 times (expected 1 and 1); 4 results
```

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/query_cascade_group_freed.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# p1 is now a child of m; continuing the iteration
# (SIGSEGV)
```

- [ ] **F36: With change detection on, a call during an iteration that adds a table to the iterated group reallocates the group's array, and the next ecs_query_next reads and writes the freed array**. Story, code path and the docs it breaks: REPORT-5.md, F36.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-26).
  Proposed fix: the iterator looks the cache entry up again instead of keeping a pointer into a reallocated array ([fixes/F36.diff](fixes/F36.diff); verified: its test passes with it on v4.2.0 and fails without; flecs's core, query, addons, collections and cpp suites as on v4.2.0).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/query_iter_table_array_realloc.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# created the 33rd table; continuing the iteration
# (SIGSEGV)
```

- [ ] **F39: With a Parent hierarchy, instances made after a prefab child changes copy the child's old type; a Sparse component added to it aborts the next instantiation**. Story, code path and the docs it breaks: REPORT-5.md, F39.
  Tracker: not found (searched 2026-11-26); related, another symptom: #2284 (closed, adding a component to an instantiated prefab aborted).
  Proposed fix: the tree spawner is rebuilt when a prefab child changed table (a field added to a public flecs.h struct) ([fixes/F39.diff](fixes/F39.diff); verified: its test passes with it on v4.2.0 and fails without; flecs's core, query, addons, collections and cpp suites as on v4.2.0).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/tree_spawner_stale_child_type.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# ChildOf: i2's child has Velocity: 1 (owned 1)
# Parent: i2's child has Velocity: 0 (owned 0)
# FAIL: with a Parent hierarchy, i2's child lacks the Velocity its prefab child has
```

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/tree_spawner_stale_sparse_assert.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# fatal: flecs.c: 64655: assert(dst_ptr != NULL) (INTERNAL_ERROR)
```

- [ ] **F29: A cached query (or a system) whose Or chain ends with a Sparse component crashes when it is created**. Story, code path and the docs it breaks: REPORT-4.md, F29.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-25).
  Proposed fix: an Or chain with a Sparse term is kept out of the cache as a whole (also F34) ([fixes/F29.diff](fixes/F29.diff); verified: its test passes with it on v4.2.0 and fails without; flecs's core, query, addons, collections and cpp suites as on v4.2.0).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/query_or_sparse_cache_crash.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# creating the cached query
# (SIGSEGV)
```

- [ ] **F3: A queued set of a pair whose target is deleted before the merge aborts the merge**. Story, code path and the docs it breaks: REPORT.md, F3.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-25, by mechanism, error text and the recent list).
  Proposed fix: a queued set, ensure, emplace or add-modified of a pair with a dead target goes through the queued add's check ([fixes/F3.diff](fixes/F3.diff); verified: its test passes with it on v4.2.0 and fails without; flecs's core, query, addons, collections and cpp suites as on v4.2.0).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/staged_set_pair_dead_target.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# fatal: flecs.c: 11175: assert(!ecs_exists(world, t)): second element of pair is not alive (INVALID_PARAMETER)
```

- [ ] **F4: Batched commands plus an observer that deletes its entity through it->stage: internal assert**. Story, code path and the docs it breaks: REPORT.md, F4.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-25, by mechanism, error text and the recent list).
  Proposed fix: the batch stops if an observer deleted the entity ([fixes/F4.diff](fixes/F4.diff); verified: its test passes with it on v4.2.0 and fails without; flecs's core, query, addons, collections and cpp suites as on v4.2.0).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/batch_observer_deletes_entity.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# fatal: flecs.c: 6924: assert(r->table != NULL) (INTERNAL_ERROR), in flecs_commands_flush
```

- [ ] **F5: ecs_set/ecs_ensure abort when an OnAdd observer deletes the entity through it->stage**. Story, code path and the docs it breaks: REPORT.md, F5.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-25, by mechanism, error text and the recent list).
  Proposed fix: set ends quietly when an OnAdd observer deleted the entity; ensure gives its documented INVALID_OPERATION ([fixes/F5.diff](fixes/F5.diff); verified: its test passes with it on v4.2.0 and fails without; flecs's core, query, addons, collections and cpp suites as on v4.2.0).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/set_observer_deletes_entity.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# fatal: flecs.c: 8921: assert(r->table != NULL) (INTERNAL_ERROR), in flecs_ensure
```

- [ ] **F8: Entity ranges: make_alive of an id recycled while its range was inactive**. Story, code path and the docs it breaks: REPORT.md, F8.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-25, by mechanism, error text and the recent list).
  Proposed fix: make_alive removes the id from its range's recycled list ([fixes/F8.diff](fixes/F8.diff); verified: its test passes with it on v4.2.0 and fails without; flecs's core, query, addons, collections and cpp suites as on v4.2.0).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/range_make_alive_recycled.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# fatal: flecs.c: 24178: assert(r->table == NULL) (INTERNAL_ERROR), in flecs_entity_index_set_range
```

- [ ] **F8: Entity ranges: make_alive of an id recycled while its range was inactive** (a second program for the same mechanism). Story, code path and the docs it breaks: REPORT.md, F8.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-25, by mechanism, error text and the recent list).
  Proposed fix: make_alive removes the id from its range's recycled list ([fixes/F8.diff](fixes/F8.diff); verified: its test passes with it on v4.2.0 and fails without; flecs's core, query, addons, collections and cpp suites as on v4.2.0).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/range_new_from_range_duplicate.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# fatal: flecs.c: 9007: assert(r->table == NULL) (INTERNAL_ERROR), in ecs_new_from_range
```

- [ ] **F15: A system that annotates a write of a component and then reads it aborts the pipeline build**. Story, code path and the docs it breaks: REPORT-2.md, F15.
  Tracker: reported: #2408 (closed 2026-11-16), fixed by PR #2417 (merged 2026-11-16, after v4.2.0: in no release yet).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/pipeline_write_read_same_system.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# fatal: flecs.c: 63591: assert(needs_merge == false) (INTERNAL_ERROR), in flecs_pipeline_update
```

- [ ] **F17: A system that disables itself makes the pipeline skip the next systems in that frame** (the assert half). Story, code path and the docs it breaks: REPORT-2.md, F17.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-25, by mechanism, error text and the recent list).
  Proposed fix: after a mid-frame rebuild the frame resumes from the schedule's start when none of its systems ran ([fixes/F17.diff](fixes/F17.diff); verified: its test passes with it on v4.2.0 and fails without; flecs's core, query, addons, collections and cpp suites as on v4.2.0).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/pipeline_disabled_systems_assert.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# fatal: flecs.c: 63706: assert((pq->cur_op <= ecs_vec_last_t(&pq->ops, ecs_pipeline_op_t))) (INTERNAL_ERROR)
```

- [ ] **F24: The table override cache misses changes of the base, so overrides are copied from the wrong place**. Story, code path and the docs it breaks: REPORT-3.md, F24.
  Tracker: reported with a fix: open PR #2397 (2026-11-12, "Fix override refs not refreshing after a base changes"; depends on open PR #2396).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/override_cache_stale_ref.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# fatal: flecs.c: 42239: assert(base_ptr != NULL) (INTERNAL_ERROR), in flecs_table_invoke_ctor
```

- [ ] **F26: The worker threads' synchronization does not re-check its condition after a wait**. Story, code path and the docs it breaks: REPORT-3.md, F26.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-25, by mechanism, error text and the recent list).
  Proposed fix: every condition-variable wait of the worker sync re-checks its condition in a loop ([fixes/F26.diff](fixes/F26.diff); verified: its test passes with it on v4.2.0 and fails without; flecs's core, query, addons, collections and cpp suites as on v4.2.0).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/workers_spurious_wakeup.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# fatal: flecs.c: 64383: assert(world->workers_waiting == (stage_count - 1)) (INTERNAL_ERROR)
```

- [ ] **F45: `ecs_auto_override` of a DontFragment component on a prefab child aborts the instantiation** ("table type cannot contain DontFragment components"), with ChildOf and with Parent children; on the prefab itself it works. Story, code path and the docs it breaks: REPORT-6.md, F45.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-26); related: #1334 added AUTO_OVERRIDE on prefab children (2024).
  Proposed fix: a DontFragment auto override on a prefab child stays out of the instance child's table type and is added as an override on the prefab is ([fixes/F45.diff](fixes/F45.diff); verified on macOS: its test(s) fail on v4.2.0 and pass with it; flecs's core, query, addons, collections and cpp suites as on v4.2.0, with it alone and with every patch together).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/prefab_child_auto_override_dont_fragment.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# ChildOf child: instantiating
# fatal: flecs.c: 41518: assert(!(id_cr->flags & EcsIdDontFragment)): table type cannot contain DontFragment components (INVALID_OPERATION)
```

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/prefab_parent_child_auto_override_dont_fragment.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# Parent child: instantiating
# fatal: flecs.c: 41518: assert(!(id_cr->flags & EcsIdDontFragment)): ... (INVALID_OPERATION)
```

- [ ] **F46: during an order_by iteration, deleting a table and creating another lets the new table take the freed one's memory; the iterator returns its entities, which don't match the query, with the slice's freed arrays** (without a new table, skipping the slice still writes its freed monitor). Story, code path and the docs it breaks: REPORT-6.md, F46.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-26).
  Proposed fix: a table leaving an order_by cache clears the sorted slices that point at it, and the iterator and change detection skip cleared slices (AddressSanitizer: a use after free on v4.2.0, none with it) ([fixes/F46.diff](fixes/F46.diff); verified on macOS: its test(s) fail on v4.2.0 and pass with it; flecs's core, query, addons, collections and cpp suites as on v4.2.0, with it alone and with every patch together).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/query_order_by_reused_table_slot.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# fatal: flecs.c: 85074: assert(columns[i] == expected): it->columns[0]=-27088 does not match expected 1 (tr=... src=0 ...)
#   flecs_iter_assert_columns <- ecs_query_next <- main
```

- [ ] **F47: a multi-threaded system whose query has order_by**: in a debug build flecs aborts ("cannot sort query in multithreaded mode", UNSUPPORTED, src/query/cache/order_by.c:88), which no page says (Systems.md "Threading": staging "makes it safe for multiple threads to iterate the same world without taking locks"); in a release build (`NDEBUG`) the assert is gone and every worker sorts the same table in place and rebuilds its slices at once. Story, code path: REPORT-6.md, F47.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-26).
  Proposed fix: the pipeline sorts a multi-threaded op's order_by queries on the main thread before the workers start; iterators made on worker threads don't sort (ThreadSanitizer: 19 reports a run in the sort on v4.2.0, none there with it) ([fixes/F47.diff](fixes/F47.diff); verified on macOS: its test(s) fail on v4.2.0 and pass with it; flecs's core, query, addons, collections and cpp suites as on v4.2.0, with it alone and with every patch together).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/workers_order_by_sort_race.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# fatal: flecs.c: 79891: assert(!(world->flags & EcsWorldMultiThreaded)): cannot sort query in multithreaded mode (UNSUPPORTED)
```

```sh
# Release build: the race itself (3 of 3 runs), and ThreadSanitizer's 19 reports, most in the sort
cc -std=gnu99 -O1 -g -DNDEBUG -I flecs/distr tests/flecs_lean/workers_order_by_sort_race.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# system runs: 2; compares during the frame: 895; two threads sorting at once: 1; table intact: 1
# FAIL: two threads sorted the system's table in place at once
cc -std=gnu99 -O1 -g -DNDEBUG -fsanitize=thread -I flecs/distr tests/flecs_lean/workers_order_by_sort_race.c flecs/distr/flecs.c -lm -lpthread -o t && TSAN_OPTIONS="halt_on_error=0" ./t
# WARNING: ThreadSanitizer: data race (x19): flecs_query_cache_build_sorted_tables (18),
#   flecs_query_cache_sort_tables, flecs_query_sync_match_monitor, flecs_run_system
```

- [ ] **F55: the skip of a deleted table's order_by slice leaks a block, and with the default allocator corrupts the query's monitor allocator** (the next new monitor is a wild pointer: a SIGSEGV in debug and release builds). The skip plants a one-int dirty state in the freed table's zeroed slot (round 7's reading; the next table there resets it, so no write past it) and writes the freed monitor, whose first bytes are the allocator's free-list link. Story, code path and the docs it breaks: REPORT-8.md, F55.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-26).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/query_order_by_skip_corrupts_monitor_allocator.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# control: 6 entities after the new tables (sum of x 50)
# FAIL: signal 11 (ecs_query_iter after the new tables (their monitors)) after the skip of the stale slice wrote the freed monitor
```

```sh
cc -std=gnu99 -O1 -g -DFLECS_SANITIZE -I flecs/distr tests/flecs_lean/query_order_by_skip_leaks_dirty_state.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# error: flecs.c: 31895: Leak detected! (size 16, remaining = 1)
# fatal: flecs.c: 31909: abort(): LEAK_DETECTED
```

- [ ] **F56: a table deleted during an order_by iteration keeps its slice in later iterators; a new iterator uses it** (a table created later in the freed memory can be returned; a debug build aborts at the columns check first). The result sync resets `prev_match_count` (change_detection.c 632), so the next iterator's sort doesn't rebuild the slices. Story, code path and the docs it breaks: REPORT-8.md, F56.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-26).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/query_order_by_stale_slice_next_iterator.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# fatal: flecs.c: 85074: assert(columns[i] == expected): it->columns[0]=-28112 does not match expected 1
# FAIL: signal 6 while a new iterator used the slice of the table freed during the previous iteration
```

- [ ] **F58: instantiating a Parent-hierarchy prefab for an instance at depth 6 or more keeps its spawn table for good**: deleting the prefab afterwards aborts in a debug build ("tables are keeping it alive"), and a release build leaves the table behind. The spawner's temporary vector for depths past its cache (FLECS_TREE_SPAWNER_DEPTH_CACHE_SIZE, 6) keeps its tables and is freed without releasing them (tree_spawner.c 148, 348-350). Story, code path and the docs it breaks: REPORT-8.md, F58.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-26).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/prefab_parent_instantiate_depth_keeps_tables.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# fatal: flecs.c: 18120: assert(!force_delete || ...): cannot delete component '(*,#387)': tables are keeping it alive
# FAIL: signal 6 deleting the prefab after an instance at depth 8 was instantiated and deleted
# (release, -DNDEBUG) FAIL: the deep instantiation left 1 table(s) that no delete or cleanup can free
```

## Panics where the docs say none, and none where they say one

- [ ] **F2: The same with a Panic relationship: the merge panics**. Story, code path and the docs it breaks: REPORT.md, F2.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-25, by mechanism, error text and the recent list).
  Proposed fix: F1's patch: the remove no longer panics ([fixes/F1.diff](fixes/F1.diff); verified: its test passes with it on v4.2.0 and fails without; flecs's core, query, addons, collections and cpp suites as on v4.2.0).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/batch_remove_dead_target_panic_record.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# fatal: flecs.c: 18164: abort(): (OnDelete, Panic) constraint violated while deleting entities with (#385,#387) (CONSTRAINT_VIOLATED)
```

- [ ] **F7: Panic isn't enforced when another pair to the same target follows it in the type, or any pair has Delete**. Story, code path and the docs it breaks: REPORT.md, F7.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-25, by mechanism, error text and the recent list).
  Proposed fix: a Panic pair wins over Delete and Remove when its target is deleted ([fixes/F7.diff](fixes/F7.diff); verified: its test passes with it on v4.2.0 and fails without; flecs's core, query, addons, collections and cpp suites as on v4.2.0).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/panic_target_order.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: deleting the target of a Panic relationship did not panic (e alive: 1, has (RPanic, t): 0)
```

## Wrong values, wrong entities, wrong ids

- [ ] **F38: An instance of a prefab variant does not own a DontFragment component that the variant's base auto-overrides**. Story, code path and the docs it breaks: REPORT-5.md, F38.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-26).
  Proposed fix: the DontFragment auto-override walk follows the base's own IsA bases ([fixes/F38.diff](fixes/F38.diff); verified: its test passes with it on v4.2.0 and fails without; flecs's core, query, addons, collections and cpp suites as on v4.2.0).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/auto_override_dont_fragment_variant.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# inst owns Defense: 0; value 50
# FAIL: the instance of the variant does not own Defense
```

- [ ] **F40: While an order_by query is iterated, deleting an entity from a table with a later slice makes the iterator return rows past that table's count**. Story, code path and the docs it breaks: REPORT-5.md, F40.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-26).
  Proposed fix: order_by slices are clamped to the table's current row count ([fixes/F40.diff](fixes/F40.diff); verified: its test passes with it on v4.2.0 and fails without; flecs's core, query, addons, collections and cpp suites as on v4.2.0).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/query_order_by_stale_rows.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: e3 returned 2 times (expected 1); a result extends past its table's count: 1
```

- [ ] **F16: No sync point between a wildcard or Any write annotation and an overlapping read**. Story, code path and the docs it breaks: REPORT-2.md, F16.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-25, by mechanism, error text and the recent list).
  Proposed fix: the sync-point check treats Wildcard and Any as overlapping on both sides (needs F15's upstream fix, PR #2417) ([fixes/F16.diff](fixes/F16.diff); verified: its test passes with it on v4.2.0 and fails without; flecs's core, query, addons, collections and cpp suites as on v4.2.0).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/pipeline_wildcard_sync_point.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL (variant a): reader saw 1 entities in the first frame, expected 2 (no sync point after the writer)
# FAIL (variant b): reader saw 1 entities in the first frame, expected 2 (no sync point after the writer)
```

- [ ] **F30: A call during an iteration that removes a table from the query's cache makes the iterator skip another table**. Story, code path and the docs it breaks: REPORT-4.md, F30.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-25).
  No small fix: the cache iterator can't survive tables leaving mid-iteration without deferring cache changes or a redesign; or the docs say such calls must be deferred (fixes/README.md).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/query_iter_skips_table.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: e2 returned 1 times, e3 returned 0 times (expected 1 and 1); neither moved, the call deleted another table
```

- [ ] **F32: Overriding a DontFragment Inherit component inherited through two IsA levels constructs it instead of copying it**. Story, code path and the docs it breaks: REPORT-4.md, F32.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-25).
  Proposed fix: the base search goes on through deeper IsA levels for DontFragment components ([fixes/F32.diff](fixes/F32.diff); verified: its test passes with it on v4.2.0 and fails without; flecs's core, query, addons, collections and cpp suites as on v4.2.0).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/override_dont_fragment_2_levels.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: DontFragment, 2 levels: after ecs_add the instance owns=1 Position = {0, 0}, expected the inherited {10, 20}
```

- [ ] **F33: Worker threads of a multi-threaded change-detection system allocate a table's dirty state without synchronization (double allocation, a leak, a data race)**. Story, code path and the docs it breaks: REPORT-4.md, F33.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-25).
  Proposed fix: only worker 0 runs change detection, so one thread allocates the dirty state ([fixes/F33.diff](fixes/F33.diff); verified: its test passes with it on v4.2.0 and fails without; flecs's core, query, addons, collections and cpp suites as on v4.2.0).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/workers_dirty_state_double_alloc.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: the dirty state of one table was allocated 2 times by the worker threads of one system; all but one leak
```

- [ ] **F1: A batched remove of a pair whose target died earlier in the merge deletes the entity**. Story, code path and the docs it breaks: REPORT.md, F1.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-25, by mechanism, error text and the recent list).
  Proposed fix: a batched remove of a pair whose target is gone is skipped instead of deleting the entity (also F2) ([fixes/F1.diff](fixes/F1.diff); verified: its test passes with it on v4.2.0 and fails without; flecs's core, query, addons, collections and cpp suites as on v4.2.0).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/batch_remove_dead_target.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: entity deleted by remove of (ChildOf, deleted parent) it never had
```

- [ ] **F6: An on_set hook that moves its entity makes OnSet observers run for another entity**. Story, code path and the docs it breaks: REPORT.md, F6.
  Tracker: related, another path: #2368 (observers after one that writes to the event's table; closed 2026-11-02, before v4.2.0). F6 is an on_set hook, still on v4.2.0.
  Proposed fix: OnSet goes to the entity where it is after the on_set hook ran ([fixes/F6.diff](fixes/F6.diff); verified: its test passes with it on v4.2.0 and fails without; flecs's core, query, addons, collections and cpp suites as on v4.2.0).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/on_set_hook_moves_entity.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: OnSet observer got entity 388 (f=388), expected e=387
# FAIL: OnSet observer saw x=2.000000, expected 99
```

- [ ] **F9: A queued set is written in place, and is lost if the component goes away before the merge**. Story, code path and the docs it breaks: REPORT.md, F9.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-25, by mechanism, error text and the recent list).
  No small fix: writing a queued set straight into storage is intended (flecs's own tests assert it; always queueing broke 10 of them): a design or docs decision (fixes/README.md).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/staged_set_value_lost.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: e has Position {-1.000000, -1.000000} after the merge, expected {1, 1}
```

- [ ] **F10: Batched ChildOf changes emit OnAdd/OnRemove for a pair the entity doesn't have**. Story, code path and the docs it breaks: REPORT.md, F10.
  Tracker: reported: open issue #2363 (2026-10-30, "Command batch applies adds that a later command in the same batch undid"; its ChildOf cases are these).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/batch_childof_replaced_onadd.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: add+clear of (ChildOf, p1): 1 OnAdd vs 0 OnRemove calls
# FAIL: 2 OnAdd observer call(s) for a ChildOf pair e does not have
```

- [ ] **F11: Under batching, OnSet observers and on_set hooks see later values**. Story, code path and the docs it breaks: REPORT.md, F11.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-25, by mechanism, error text and the recent list).
  Proposed fix: a second set of one component in a batch runs in queue order; ensure after a queued set gets its own copy ([fixes/F11.diff](fixes/F11.diff); verified: its test passes with it on v4.2.0 and fails without; flecs's core, query, addons, collections and cpp suites as on v4.2.0).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/batch_onset_values.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: OnSet calls for e saw x = 3.000000 then 3.000000, expected 1 then 3
```

- [ ] **F12: Batching runs an entity's later commands before other entities' earlier ones; a child survives its parent's deletion**. Story, code path and the docs it breaks: REPORT.md, F12.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-25, by mechanism, error text and the recent list).
  Proposed fix: the batch is split before a remove or clear that undoes a Delete or Panic pair it just added ([fixes/F12.diff](fixes/F12.diff); verified: its test passes with it on v4.2.0 and fails without; flecs's core, query, addons, collections and cpp suites as on v4.2.0).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/batch_child_survives_parent_delete.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: child survived the deletion of its parent
```

- [ ] **F21: Instantiating a prefab with children makes a deleted entity handle alive again**. Story, code path and the docs it breaks: REPORT-2.md, F21.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-25, by mechanism, error text and the recent list).
  Proposed fix: an instance child's reused id never gets an older generation ([fixes/F21.diff](fixes/F21.diff); verified: its test passes with it on v4.2.0 and fails without; flecs's core, query, addons, collections and cpp suites as on v4.2.0).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/instantiate_resurrects_deleted_handle.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: the deleted handle b is alive again (parent: 387)
```

- [ ] **F22: A batched set, remove and add of the same component keeps the set's value**. Story, code path and the docs it breaks: REPORT-2.md, F22.
  Tracker: related: open issue #2363 (the batch's diff keeps ids a later command undid); this set/remove/add value case isn't in it.
  Proposed fix: a later remove in the batch drops the earlier set's value ([fixes/F22.diff](fixes/F22.diff); verified: its test passes with it on v4.2.0 and fails without; flecs's core, query, addons, collections and cpp suites as on v4.2.0).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/batch_set_remove_add_value.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: e has Position {1.000000, 1.000000}, expected the constructed {-1, -1}
```

- [ ] **F23: A queued ChildOf to a parent that was deleted, and whose id was recycled, attaches the child to the new entity**. Story, code path and the docs it breaks: REPORT-2.md, F23.
  Tracker: related, another path: #2362 (ecs_table_clear_entities leaves pairs a recycled id inherits; closed 2026-11-02, before v4.2.0). F23 is a queued ChildOf, still on v4.2.0.
  Proposed fix: a queued pair add records the target's generation, so a recycled parent counts as deleted (8 bytes more a command) ([fixes/F23.diff](fixes/F23.diff); verified: its test passes with it on v4.2.0 and fails without; flecs's core, query, addons, collections and cpp suites as on v4.2.0).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/staged_childof_recycled_parent.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: child alive after its parent was deleted; its parent is now the new entity q
```

- [ ] **F24: The table override cache misses changes of the base, so overrides are copied from the wrong place** (wrong copied values). Story, code path and the docs it breaks: REPORT-3.md, F24.
  Tracker: reported with a fix: open PR #2397 (2026-11-12, "Fix override refs not refreshing after a base changes"; depends on open PR #2396).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/override_cache_stale_value.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: inst2 Position is {-1, -1}, base has {99, 99}
# FAIL: inst3 Position is {-1, -1}, base has {99, 99}
```

- [ ] **F24: The table override cache misses changes of the base, so overrides are copied from the wrong place** (a missing OnSet). Story, code path and the docs it breaks: REPORT-3.md, F24.
  Tracker: reported with a fix: open PR #2397 (2026-11-12, "Fix override refs not refreshing after a base changes"; depends on open PR #2396).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/override_cache_onset_missing.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: removing the override re-exposed {50, 50} but no OnSet was emitted for inst
```

- [ ] **F24: The table override cache misses changes of the base, so overrides are copied from the wrong place** (an OnSet whose source lacks the component). Story, code path and the docs it breaks: REPORT-3.md, F24.
  Tracker: reported with a fix: open PR #2397 (2026-11-12, "Fix override refs not refreshing after a base changes"; depends on open PR #2396).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/override_cache_onset_source.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: OnSet for entity 387 with source 386, which has no Position
```

- [ ] **F28: With an entity range active, instantiating a prefab with children creates instance children outside the range**. Story, code path and the docs it breaks: REPORT-3.md, F28.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-25, by mechanism, error text and the recent list).
  No small fix: flecs's own test requires instance children beside their instance, outside the active range: the docs should change (fixes/README.md).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/instantiate_child_outside_range.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: instance child 388 is outside the active range [5000, 5010]
```

- [ ] **F13: The generation wraps after 2^16 recycles** (by design (16-bit generation), against the docs' "a deleted handle is not alive"). Story, code path and the docs it breaks: REPORT.md, F13.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-25, by mechanism, error text and the recent list).
  No small fix: the 16-bit generation is part of the public id layout: the docs should say a stale handle can test alive again after 65,536 recycles (fixes/README.md).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/generation_wraps.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: deleted handle 385 reports alive (current 385)
```

- [ ] **F14: Inside an on_add hook the entity doesn't have the component yet (lower confidence)** (lower confidence: the docs show the order only in a diagram). Story, code path and the docs it breaks: REPORT.md, F14.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-25, by mechanism, error text and the recent list).
  No small fix: showing the entity inside on_add needs a two-pass table move: a design and docs question (fixes/README.md).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/on_add_hook_view.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: ecs_has false inside on_add hook
# FAIL: ecs_get NULL inside on_add hook
```

- [ ] **F44: a prefab with a ChildOf child and a Parent child gives instances no copy of the ChildOf child; a ChildOf child below a Parent child is dropped too** (HierarchiesManual.md: one parent can hold children of both storages, and instantiation works with both). Story, code path and the docs it breaks: REPORT-6.md, F44.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-26).
  Proposed fix: after the tree spawner, a prefab's ChildOf children (and each spawned Parent child's) are instantiated too ([fixes/F44.diff](fixes/F44.diff); verified on macOS: its test(s) fail on v4.2.0 and pass with it; flecs's core, query, addons, collections and cpp suites as on v4.2.0, with it alone and with every patch together).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/prefab_mixed_children_instance.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# children: mixed 1 (copy of the ChildOf child: 0), two ChildOf 2, two Parent 2; nested: 1 child with 0 grandchild
# FAIL: the instance has no child for a ChildOf prefab child next to or below a Parent child
```

## Missed or extra events (observers, monitors, change detection, system activity)

- [ ] **F37: A system whose commands reorder the phases makes the pipeline skip, in that frame, the systems now ordered before it (with or without ProgressTasks)**. Story, code path and the docs it breaks: REPORT-5.md, F37.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-26).
  No small fix: the fix tried broke 9 of flecs's Pipeline tests, which require a system joining mid-frame to wait for the next frame: a redesign, flecs's decision (fixes/README.md).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/pipeline_phase_reorder_skips.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# frame 1: S1 1, S2 0; after frame 2: S1 2, S2 1
# FAIL: S2 ran 0 times in the first frame (expected 1)
```

- [ ] **F31: The pipeline keeps a stale schedule when its query's match changes outside the cache (a system in a disabled module's Parent hierarchy keeps running; custom pipelines with a fixed-source or DontFragment term too)**. Story, code path and the docs it breaks: REPORT-4.md, F31.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-25).
  Proposed fix: each frame compares the matched systems with the schedule and rebuilds if they differ (about 0.5 us a frame, 200 systems) ([fixes/F31.diff](fixes/F31.diff); verified: its test passes with it on v4.2.0 and fails without; flecs's core, query, addons, collections and cpp suites as on v4.2.0).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/pipeline_parent_module_disabled.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: the system in the Parent hierarchy ran 2 times in the two frames after its module was disabled
```

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/pipeline_custom_uncached_term.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: variant 0 (System, Running(Game)): the system ran 3 times; the pipeline query stopped matching it after the first frame
# FAIL: variant 1 (System, Foo (DontFragment)): the system ran 3 times; the pipeline query stopped matching it after the first frame
```

- [ ] **F17: A system that disables itself as the first of its frame makes the pipeline skip the next system (corrected tests: no builtin system first, it->stage)**. Story, code path and the docs it breaks: REPORT-2.md and REPORT-4.md, F17.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-25).
  Proposed fix: after a mid-frame rebuild the frame resumes from the schedule's start when none of its systems ran ([fixes/F17.diff](fixes/F17.diff); verified: its test passes with it on v4.2.0 and fails without; flecs's core, query, addons, collections and cpp suites as on v4.2.0).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/pipeline_disabled_system_skips_next.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: after one frame Init ran 1 times, Update ran 0 times (expected 1 and 1)
```

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/pipeline_disabled_system_skips_next_init.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: after one frame Init ran 1 times, Update ran 0 times (expected 1 and 1)
```

- [ ] **F18: Change detection misses a write to a source entity that moved to another table**. Story, code path and the docs it breaks: REPORT-2.md, F18.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-25, by mechanism, error text and the recent list).
  Proposed fix: change monitors record which table the source entity was in (also F19) ([fixes/F18.diff](fixes/F18.diff); verified: its test passes with it on v4.2.0 and fails without; flecs's core, query, addons, collections and cpp suites as on v4.2.0).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/change_detection_fixed_source_moved.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: ecs_query_changed is false after Velocity was set on the fixed source
```

- [ ] **F19: Change detection on a fixed source that lacks the component: removal is missed, addition reads uninitialized memory**. Story, code path and the docs it breaks: REPORT-2.md, F19.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-25, by mechanism, error text and the recent list).
  Proposed fix: F18's patch: a missing component is recorded, not skipped (the uninitialized read shown with checks/F19_fixed_source_added_optional.c) ([fixes/F18.diff](fixes/F18.diff); verified: its test passes with it on v4.2.0 and fails without; flecs's core, query, addons, collections and cpp suites as on v4.2.0).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/change_detection_fixed_source_removed.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: ecs_query_changed is false after the fixed source lost Velocity
```

- [ ] **F20: Monitors with up traversal report OnAdd for an entity that already matched, and OnRemove for one that still matches**. Story, code path and the docs it breaks: REPORT-2.md, F20.
  Tracker: related, another path: #2373 (Not-term observers and monitors check the whole table; closed 2026-11-02, before v4.2.0). F20 is up traversal, still on v4.2.0.
  Proposed fix: propagated events carry a flag, and monitors skip them while the component is reachable through another parent ([fixes/F20.diff](fixes/F20.diff); verified: its test passes with it on v4.2.0 and fails without; flecs's core, query, addons, collections and cpp suites as on v4.2.0).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/monitor_up_grandparent.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: OnAdd for an entity that already matched (3 OnAdd in total)
# FAIL: OnRemove for an entity that still matches (1 OnRemove)
```

- [ ] **F25: After `ecs_run_aperiodic(EcsAperiodicEmptyQueries)`, a system stays inactive when its query matches entities again**. Story, code path and the docs it breaks: REPORT-3.md, F25.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-25, by mechanism, error text and the recent list).
  Proposed fix: queries tagged empty are re-tested at each frame's start (includes F27's change) ([fixes/F25.diff](fixes/F25.diff); verified: its test passes with it on v4.2.0 and fails without; flecs's core, query, addons, collections and cpp suites as on v4.2.0).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/pipeline_system_stays_inactive.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: Sys matches e but ran for 0 entities (EcsEmpty: 1)
```

- [ ] **F27: `ecs_query_is_true` and `ecs_query_count` clear the change state that `ecs_query_changed` reports**. Story, code path and the docs it breaks: REPORT-3.md, F27.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-25, by mechanism, error text and the recent list).
  Proposed fix: ecs_query_is_true and ecs_query_count no longer clear the change state (or F25.diff) ([fixes/F27.diff](fixes/F27.diff); verified: its test passes with it on v4.2.0 and fails without; flecs's core, query, addons, collections and cpp suites as on v4.2.0).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/query_is_true_consumes_change.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: after ecs_query_is_true, q1 no longer reports the set
# FAIL: after ecs_query_is_true, q2 no longer reports the unmatched table
# FAIL: after ecs_query_count, q2 no longer reports the unmatched table
```

- [ ] **F41: adding an IsA pair produces no OnSet for an inherited Sparse or DontFragment component with the Inherit trait**, at one or two levels (a table component gets it; ObserversManual.md "OnSet and Inheritance"). Story, code path and the docs it breaks: REPORT-6.md, F41.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-26).
  Proposed fix: OnSet is emitted for inherited Sparse components when an IsA pair is added, and for DontFragment Inherit ones by a new function; owners of the component get no self|up event ([fixes/F41.diff](fixes/F41.diff); verified on macOS: its test(s) fail on v4.2.0 and pass with it; flecs's core, query, addons, collections and cpp suites as on v4.2.0, with it alone and with every patch together).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/isa_onset_sparse_dont_fragment.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# OnSet events (one level, two levels): Position 1 1, Health (Sparse) 0 0, Defense (DontFragment) 0 0
# FAIL: an IsA add produced no OnSet for an inherited Sparse or DontFragment component
```

- [ ] **F42: setting a DontFragment component on a base sends an OnSet, with the base's value, to an instance that overrides it** ("If the base entity has a component that the entity already had no event is generated"). Story, code path and the docs it breaks: REPORT-6.md, F42.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-26).
  Proposed fix: the down-propagation of a set on a base decides DontFragment ownership per entity, so an overriding instance and its inheritors get no base event ([fixes/F42.diff](fixes/F42.diff); verified on macOS: its test(s) fail on v4.2.0 and pass with it; flecs's core, query, addons, collections and cpp suites as on v4.2.0, with it alone and with every patch together).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/set_base_onset_dont_fragment_override.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# OnSet events for inst after setting base: Position 0, Health 0, Defense 1; ecs_get(inst, Defense) = 7
#   Defense event for inst: source base, value 60
# FAIL: inst owns Defense (7) but got an OnSet for the base's value
```

- [ ] **F43: OnSet events name a base that is not the entity's source** (table components too): a second base that doesn't become the primary source, setting it, a variant with two bases (two events), a diamond (two events from one set). Story, code path and the docs it breaks: REPORT-6.md, F43.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-26).
  Proposed fix: OnSet through IsA comes only from the base `ecs_get` reads (the first base in type order, depth first) ([fixes/F43.diff](fixes/F43.diff); verified on macOS: its test(s) fail on v4.2.0 and pass with it; flecs's core, query, addons, collections and cpp suites as on v4.2.0, with it alone and with every patch together).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/isa_second_base_onset.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# 1. second base added: 1 event(s) for inst, 1 from b2
# 2. second base set: 1 event(s) for inst (its Position: 1)
# 3. variant with two bases: 2 event(s) for i3, 1 from b1 (its Position: 1)
# control: b1 added after b2: 1 event(s) for inst2, 1 from b1
# FAIL: OnSet events name a base that is not the entity's source for Position
```

- [ ] **F48: adding or removing a DontFragment component on a base sends OnAdd and OnRemove to an instance that owns that component itself, and to its inheritors**; the ChildOf example of "Event Propagation" shows the same for OnSet (it reaches a grandchild through a child that owns the component). Story, code path and the docs it breaks: REPORT-7.md, F48.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-26; #2445, open, is IsA between component ids, another feature).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/propagate_on_add_remove_dont_fragment_owner.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# events with source base: Position and Health (inst, inst2) 0; Defense OnAdd inst 1, inst2 1; Defense OnRemove inst 1, inst2 1
# (b) OnSet from parent: Velocity (child, grandchild) 0; Mass child 1, grandchild 1
# FAIL: inst owns Defense (7) throughout, yet it and inst2 got OnAdd and OnRemove events from base
```

- [ ] **F49: OnAdd and OnRemove, propagated or forwarded, name a base that is not the entity's source; in a diamond the same event comes twice** (table storage too). Story, code path and the docs it breaks: REPORT-7.md, F49.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-26; #2445, open, is IsA between component ids, another feature).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/propagate_on_add_remove_second_base.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# (a) inst sees x=1, then x=1; OnAdd from b2 1, OnRemove from b2 1
# (c) d: OnAdd from b4 2 (expected 1); control: OnAdd from b5 1 (expected 1)
# FAIL: OnAdd/OnRemove events name a base that is not the entity's source (or come twice)
```

- [ ] **F50: no OnAdd or OnRemove is forwarded for an inherited DontFragment component**, through IsA and through the ChildOf example of "Event Forwarding". Story, code path and the docs it breaks: REPORT-7.md, F50.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-26; #2445, open, is IsA between component ids, another feature).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/forward_on_add_remove_dont_fragment.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# inst: Position OnAdd 1 OnRemove 1; Health OnAdd 1 OnRemove 1; Defense OnAdd 0 OnRemove 0
# (b) child = ChildOf parent: Velocity(up) OnAdd 1; Mass(up) OnAdd 0
# FAIL: inst gained and lost the inherited Defense without an OnAdd and an OnRemove
```

- [ ] **F51: when a variant gains a base or loses an override, its inheritors get OnAdd or OnRemove but no OnSet, though their value changed** ("OnSet and Inheritance"). Story, code path and the docs it breaks: REPORT-7.md, F51.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-26; #2445, open, is IsA between component ids, another feature).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/inheritor_onset_base_change.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# (a) inst reads x=-1, then x=1: OnSet 0, OnAdd 1
# (b) inst2 reads x=5, then x=1: OnSet 0, OnRemove 1
# FAIL: inst and inst2 got a new inherited value without an OnSet event
```

- [ ] **F52: instantiating a prefab whose Parent-storage child has an Inherit component aborts if that component has an on_set hook or is Sparse** (the ChildOf and auto-override controls work). The hook form stops at another internal assert than the replica's (`elem != NULL` in `flecs_new_entity`, not component_actions.c 679), an abort all the same. Story, code path and the docs it breaks: REPORT-7.md, F52.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-26; #2445, open, is IsA between component ids, another feature).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/prefab_parent_child_inherit_on_set_hook.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# controls: ChildOf child's Velocity {3, 4} (owned 1); auto-overridden Parent child's Velocity {3, 4} (owned 1)
# fatal: flecs.c: 7976: assert(elem != NULL) (INTERNAL_ERROR)   <- flecs_new_entity <- ecs_new_w_id
```

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/prefab_parent_child_inherit_sparse.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# fatal: flecs.c: 64655: assert(dst_ptr != NULL) (INTERNAL_ERROR)
```

- [ ] **F53: `ecs_iter_changed` and `ecs_iter_skip` abort inside a multi-threaded system once the world has worker threads** (a worker iterator; flecs.h states no such condition). Story, code path and the docs it breaks: REPORT-7.md, F53.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-26; #2445, open, is IsA between component ids, another feature).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/iter_changed_multi_threaded_system.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# frame without threads: callback calls 1, changed 1
# fatal: flecs.c: 79057: assert(it->next == ecs_query_next) (UNSUPPORTED)
# FAIL: signal 6 in the frame with worker threads (the system's callback calls ecs_iter_changed)
```

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/iter_skip_multi_threaded_system.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# fatal: flecs.c: 79095: assert(it->next == ecs_query_next) (INVALID_PARAMETER)
```

- [ ] **F54: the run callback of a single-threaded system over a trivially cached query gets `flecs_query_trivial_cached_next`, not `ecs_query_next` as system.h says, and `ecs_iter_skip` aborts there**. Story, code path and the docs it breaks: REPORT-7.md, F54.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-26; #2445, open, is IsA between component ids, another feature).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/system_run_trivial_cache_next.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# control (EcsQueryDetectChanges): it->next == ecs_query_next 1, results 1, skipped without abort
# system: it->next == ecs_query_next 0, results 1
# fatal: flecs.c: 79095: assert(it->next == ecs_query_next) (INVALID_PARAMETER)
```

- [ ] **F57: re-parenting a Parent-storage child (`ecs_set(e, EcsParent, {p2})`) delivers no OnRemove**: not for `(ChildOf, p1)`, not for p1's components the child and its children lose; the same re-parent with ChildOf storage delivers both. The Parent component's OnSet is re-emitted as the OnAdd of `(ChildOf, p2)` only (observable.c 1160-1183). The Parent-storage forms of F48 and F50 show too (their test: parent_storage_dont_fragment_events.c). Story, code path and the docs it breaks: REPORT-8.md, F57.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-26).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/parent_reparent_no_on_remove.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# controls: ChildOf re-parent: OnRemove Tag(up) 1, OnRemove (ChildOf, p1) 1; Parent removed: OnRemove Tag(up) 1, OnRemove (ChildOf, p1) 1
# prediction: e re-parented to p2: 1; OnRemove Tag(up) for e 0, for its child g 0; OnRemove (ChildOf, p1) for e 0; events seen 0
# FAIL: e and its child g lost Tag(up) from p1 without an OnRemove
```

## Predicted but not reproduced

- F55 as round 7 wrote it (a write past the planted block): the next table in the slot resets its dirty
  state (table_graph.c 424), so nothing is written past it; the corrected F55 is above.
- F2 as first predicted (`batch_remove_dead_target_panic.c`): flecs behaved as documented; a model
  error, corrected in round 2 (the entry above).
- F17's first test (`ecs_init()`, whose builtin ProgressTasks system ran first): Update still ran.
  Corrected in round 4 (the entry above), where the skip shows.
- F19's uninitialized read (`change_detection_fixed_source_added.c`): its plain run, valgrind and
  MemorySanitizer (on Linux) showed nothing.
