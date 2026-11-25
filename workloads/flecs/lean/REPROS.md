# flecs repros

From the Lean replica of flecs v4.2.0 (the latest release), written blind from its source in three
rounds (REPORT.md, REPORT-2.md, REPORT-3.md: each finding's minimal program, story, tape, code path
and the documentation it breaks). Every entry below was reproduced on the real flecs v4.2.0: its C
test (tests/flecs_lean) compiled against the release's single-file distribution with asserts on (a
debug build: `FLECS_DEBUG` without `NDEBUG`), on macOS and on Linux (the `flecs-lean` workflow). A
test returns 0 when flecs behaves as documented; the output shown is the real flecs's. Each entry's
"Tracker" line says whether flecs's issues or PRs already have it (searched 2026-11-25).

Each block runs from this directory with flecs v4.2.0's source in `flecs/`:

```sh
curl -fsSL https://github.com/SanderMertens/flecs/archive/refs/tags/v4.2.0.tar.gz | tar -xz && mv flecs-4.2.0 flecs
```

## Crashes: flecs's own internal or parameter asserts on documented use

- [ ] **F29: A cached query (or a system) whose Or chain ends with a Sparse component crashes when it is created**. Story, code path and the docs it breaks: REPORT-4.md, F29.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-25).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/query_or_sparse_cache_crash.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# creating the cached query
# (SIGSEGV)
```

- [ ] **F3: A queued set of a pair whose target is deleted before the merge aborts the merge**. Story, code path and the docs it breaks: REPORT.md, F3.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-25, by mechanism, error text and the recent list).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/staged_set_pair_dead_target.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# fatal: flecs.c: 11175: assert(!ecs_exists(world, t)): second element of pair is not alive (INVALID_PARAMETER)
```

- [ ] **F4: Batched commands plus an observer that deletes its entity through it->stage: internal assert**. Story, code path and the docs it breaks: REPORT.md, F4.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-25, by mechanism, error text and the recent list).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/batch_observer_deletes_entity.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# fatal: flecs.c: 6924: assert(r->table != NULL) (INTERNAL_ERROR), in flecs_commands_flush
```

- [ ] **F5: ecs_set/ecs_ensure abort when an OnAdd observer deletes the entity through it->stage**. Story, code path and the docs it breaks: REPORT.md, F5.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-25, by mechanism, error text and the recent list).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/set_observer_deletes_entity.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# fatal: flecs.c: 8921: assert(r->table != NULL) (INTERNAL_ERROR), in flecs_ensure
```

- [ ] **F8: Entity ranges: make_alive of an id recycled while its range was inactive**. Story, code path and the docs it breaks: REPORT.md, F8.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-25, by mechanism, error text and the recent list).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/range_make_alive_recycled.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# fatal: flecs.c: 24178: assert(r->table == NULL) (INTERNAL_ERROR), in flecs_entity_index_set_range
```

- [ ] **F8: Entity ranges: make_alive of an id recycled while its range was inactive** (a second program for the same mechanism). Story, code path and the docs it breaks: REPORT.md, F8.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-25, by mechanism, error text and the recent list).

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

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/workers_spurious_wakeup.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# fatal: flecs.c: 64383: assert(world->workers_waiting == (stage_count - 1)) (INTERNAL_ERROR)
```

## Panics where the docs say none, and none where they say one

- [ ] **F2: The same with a Panic relationship: the merge panics**. Story, code path and the docs it breaks: REPORT.md, F2.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-25, by mechanism, error text and the recent list).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/batch_remove_dead_target_panic_record.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# fatal: flecs.c: 18164: abort(): (OnDelete, Panic) constraint violated while deleting entities with (#385,#387) (CONSTRAINT_VIOLATED)
```

- [ ] **F7: Panic isn't enforced when another pair to the same target follows it in the type, or any pair has Delete**. Story, code path and the docs it breaks: REPORT.md, F7.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-25, by mechanism, error text and the recent list).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/panic_target_order.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: deleting the target of a Panic relationship did not panic (e alive: 1, has (RPanic, t): 0)
```

## Wrong values, wrong entities, wrong ids

- [ ] **F16: No sync point between a wildcard or Any write annotation and an overlapping read**. Story, code path and the docs it breaks: REPORT-2.md, F16.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-25, by mechanism, error text and the recent list).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/pipeline_wildcard_sync_point.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL (variant a): reader saw 1 entities in the first frame, expected 2 (no sync point after the writer)
# FAIL (variant b): reader saw 1 entities in the first frame, expected 2 (no sync point after the writer)
```

- [ ] **F30: A call during an iteration that removes a table from the query's cache makes the iterator skip another table**. Story, code path and the docs it breaks: REPORT-4.md, F30.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-25).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/query_iter_skips_table.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: e2 returned 1 times, e3 returned 0 times (expected 1 and 1); neither moved, the call deleted another table
```

- [ ] **F32: Overriding a DontFragment Inherit component inherited through two IsA levels constructs it instead of copying it**. Story, code path and the docs it breaks: REPORT-4.md, F32.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-25).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/override_dont_fragment_2_levels.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: DontFragment, 2 levels: after ecs_add the instance owns=1 Position = {0, 0}, expected the inherited {10, 20}
```

- [ ] **F33: Worker threads of a multi-threaded change-detection system allocate a table's dirty state without synchronization (double allocation, a leak, a data race)**. Story, code path and the docs it breaks: REPORT-4.md, F33.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-25).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/workers_dirty_state_double_alloc.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: the dirty state of one table was allocated 2 times by the worker threads of one system; all but one leak
```

- [ ] **F1: A batched remove of a pair whose target died earlier in the merge deletes the entity**. Story, code path and the docs it breaks: REPORT.md, F1.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-25, by mechanism, error text and the recent list).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/batch_remove_dead_target.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: entity deleted by remove of (ChildOf, deleted parent) it never had
```

- [ ] **F6: An on_set hook that moves its entity makes OnSet observers run for another entity**. Story, code path and the docs it breaks: REPORT.md, F6.
  Tracker: related, another path: #2368 (observers after one that writes to the event's table; closed 2026-11-02, before v4.2.0). F6 is an on_set hook, still on v4.2.0.

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/on_set_hook_moves_entity.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: OnSet observer got entity 388 (f=388), expected e=387
# FAIL: OnSet observer saw x=2.000000, expected 99
```

- [ ] **F9: A queued set is written in place, and is lost if the component goes away before the merge**. Story, code path and the docs it breaks: REPORT.md, F9.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-25, by mechanism, error text and the recent list).

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

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/batch_onset_values.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: OnSet calls for e saw x = 3.000000 then 3.000000, expected 1 then 3
```

- [ ] **F12: Batching runs an entity's later commands before other entities' earlier ones; a child survives its parent's deletion**. Story, code path and the docs it breaks: REPORT.md, F12.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-25, by mechanism, error text and the recent list).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/batch_child_survives_parent_delete.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: child survived the deletion of its parent
```

- [ ] **F21: Instantiating a prefab with children makes a deleted entity handle alive again**. Story, code path and the docs it breaks: REPORT-2.md, F21.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-25, by mechanism, error text and the recent list).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/instantiate_resurrects_deleted_handle.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: the deleted handle b is alive again (parent: 387)
```

- [ ] **F22: A batched set, remove and add of the same component keeps the set's value**. Story, code path and the docs it breaks: REPORT-2.md, F22.
  Tracker: related: open issue #2363 (the batch's diff keeps ids a later command undid); this set/remove/add value case isn't in it.

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/batch_set_remove_add_value.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: e has Position {1.000000, 1.000000}, expected the constructed {-1, -1}
```

- [ ] **F23: A queued ChildOf to a parent that was deleted, and whose id was recycled, attaches the child to the new entity**. Story, code path and the docs it breaks: REPORT-2.md, F23.
  Tracker: related, another path: #2362 (ecs_table_clear_entities leaves pairs a recycled id inherits; closed 2026-11-02, before v4.2.0). F23 is a queued ChildOf, still on v4.2.0.

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

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/instantiate_child_outside_range.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: instance child 388 is outside the active range [5000, 5010]
```

- [ ] **F13: The generation wraps after 2^16 recycles** (by design (16-bit generation), against the docs' "a deleted handle is not alive"). Story, code path and the docs it breaks: REPORT.md, F13.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-25, by mechanism, error text and the recent list).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/generation_wraps.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: deleted handle 385 reports alive (current 385)
```

- [ ] **F14: Inside an on_add hook the entity doesn't have the component yet (lower confidence)** (lower confidence: the docs show the order only in a diagram). Story, code path and the docs it breaks: REPORT.md, F14.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-25, by mechanism, error text and the recent list).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/on_add_hook_view.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: ecs_has false inside on_add hook
# FAIL: ecs_get NULL inside on_add hook
```

## Missed or extra events (observers, monitors, change detection, system activity)

- [ ] **F31: The pipeline keeps a stale schedule when its query's match changes outside the cache (a system in a disabled module's Parent hierarchy keeps running; custom pipelines with a fixed-source or DontFragment term too)**. Story, code path and the docs it breaks: REPORT-4.md, F31.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-25).

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

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/change_detection_fixed_source_moved.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: ecs_query_changed is false after Velocity was set on the fixed source
```

- [ ] **F19: Change detection on a fixed source that lacks the component: removal is missed, addition reads uninitialized memory**. Story, code path and the docs it breaks: REPORT-2.md, F19.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-25, by mechanism, error text and the recent list).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/change_detection_fixed_source_removed.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: ecs_query_changed is false after the fixed source lost Velocity
```

- [ ] **F20: Monitors with up traversal report OnAdd for an entity that already matched, and OnRemove for one that still matches**. Story, code path and the docs it breaks: REPORT-2.md, F20.
  Tracker: related, another path: #2373 (Not-term observers and monitors check the whole table; closed 2026-11-02, before v4.2.0). F20 is up traversal, still on v4.2.0.

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/monitor_up_grandparent.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: OnAdd for an entity that already matched (3 OnAdd in total)
# FAIL: OnRemove for an entity that still matches (1 OnRemove)
```

- [ ] **F25: After `ecs_run_aperiodic(EcsAperiodicEmptyQueries)`, a system stays inactive when its query matches entities again**. Story, code path and the docs it breaks: REPORT-3.md, F25.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-25, by mechanism, error text and the recent list).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/pipeline_system_stays_inactive.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: Sys matches e but ran for 0 entities (EcsEmpty: 1)
```

- [ ] **F27: `ecs_query_is_true` and `ecs_query_count` clear the change state that `ecs_query_changed` reports**. Story, code path and the docs it breaks: REPORT-3.md, F27.
  Tracker: not found in SanderMertens/flecs's issues or PRs (searched 2026-11-25, by mechanism, error text and the recent list).

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/query_is_true_consumes_change.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: after ecs_query_is_true, q1 no longer reports the set
# FAIL: after ecs_query_is_true, q2 no longer reports the unmatched table
# FAIL: after ecs_query_count, q2 no longer reports the unmatched table
```

## Predicted but not reproduced

- F2 as first predicted (`batch_remove_dead_target_panic.c`): flecs behaved as documented; a model
  error, corrected in round 2 (the entry above).
- F17's first test (`ecs_init()`, whose builtin ProgressTasks system ran first): Update still ran.
  Corrected in round 4 (the entry above), where the skip shows.
- F19's uninitialized read (`change_detection_fixed_source_added.c`): its plain run, valgrind and
  MemorySanitizer (on Linux) showed nothing.
