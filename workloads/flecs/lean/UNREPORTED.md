# flecs findings not reported upstream

From the Lean replica of flecs v4.2.0 (the latest release), written blind from its source in three
rounds (REPORT.md, REPORT-2.md, REPORT-3.md: each finding's minimal program, story, tape, code path
and the documentation it breaks). Every entry below was reproduced on the real flecs v4.2.0: its C
test (tests/flecs_lean) compiled against the release's single-file distribution with asserts on (a
debug build: `FLECS_DEBUG` without `NDEBUG`), on macOS and on Linux (the `flecs-lean` workflow). A
test returns 0 when flecs behaves as documented; the output shown is the real flecs's. Not yet
searched against flecs's issues.

Each block runs from this directory with flecs v4.2.0's source in `flecs/`:

```sh
curl -fsSL https://github.com/SanderMertens/flecs/archive/refs/tags/v4.2.0.tar.gz | tar -xz && mv flecs-4.2.0 flecs
```

## Crashes: flecs's own internal or parameter asserts on documented use

- [ ] **F3: A queued set of a pair whose target is deleted before the merge aborts the merge**. Story, code path and the docs it breaks: REPORT.md, F3.

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/staged_set_pair_dead_target.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# fatal: flecs.c: 11175: assert(!ecs_exists(world, t)): second element of pair is not alive (INVALID_PARAMETER)
```

- [ ] **F4: Batched commands plus an observer that deletes its entity through it->stage: internal assert**. Story, code path and the docs it breaks: REPORT.md, F4.

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/batch_observer_deletes_entity.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# fatal: flecs.c: 6924: assert(r->table != NULL) (INTERNAL_ERROR), in flecs_commands_flush
```

- [ ] **F5: ecs_set/ecs_ensure abort when an OnAdd observer deletes the entity through it->stage**. Story, code path and the docs it breaks: REPORT.md, F5.

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/set_observer_deletes_entity.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# fatal: flecs.c: 8921: assert(r->table != NULL) (INTERNAL_ERROR), in flecs_ensure
```

- [ ] **F8: Entity ranges: make_alive of an id recycled while its range was inactive**. Story, code path and the docs it breaks: REPORT.md, F8.

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/range_make_alive_recycled.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# fatal: flecs.c: 24178: assert(r->table == NULL) (INTERNAL_ERROR), in flecs_entity_index_set_range
```

- [ ] **F8: Entity ranges: make_alive of an id recycled while its range was inactive** (a second program for the same mechanism). Story, code path and the docs it breaks: REPORT.md, F8.

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/range_new_from_range_duplicate.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# fatal: flecs.c: 9007: assert(r->table == NULL) (INTERNAL_ERROR), in ecs_new_from_range
```

- [ ] **F15: A system that annotates a write of a component and then reads it aborts the pipeline build**. Story, code path and the docs it breaks: REPORT-2.md, F15.

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/pipeline_write_read_same_system.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# fatal: flecs.c: 63591: assert(needs_merge == false) (INTERNAL_ERROR), in flecs_pipeline_update
```

- [ ] **F16: No sync point between a wildcard or Any write annotation and an overlapping read**. Story, code path and the docs it breaks: REPORT-2.md, F16.

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/pipeline_wildcard_sync_point.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# fatal: flecs.c: 44780: assert(!(world->flags & EcsWorldReadonly)) (INTERNAL_ERROR), in flecs_table_ensure
```

- [ ] **F17: A system that disables itself makes the pipeline skip the next systems in that frame** (the assert half). Story, code path and the docs it breaks: REPORT-2.md, F17.

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/pipeline_disabled_systems_assert.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# fatal: flecs.c: 44780: assert(!(world->flags & EcsWorldReadonly)) (INTERNAL_ERROR), in flecs_table_ensure
```

- [ ] **F24: The table override cache misses changes of the base, so overrides are copied from the wrong place**. Story, code path and the docs it breaks: REPORT-3.md, F24.

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/override_cache_stale_ref.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# fatal: flecs.c: 42239: assert(base_ptr != NULL) (INTERNAL_ERROR), in flecs_table_invoke_ctor
```

- [ ] **F26: The worker threads' synchronization does not re-check its condition after a wait**. Story, code path and the docs it breaks: REPORT-3.md, F26.

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/workers_spurious_wakeup.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# fatal: flecs.c: 64383: assert(world->workers_waiting == (stage_count - 1)) (INTERNAL_ERROR), in flecs_wait_for_sync
```

## Panics where the docs say none, and none where they say one

- [ ] **F2: The same with a Panic relationship: the merge panics**. Story, code path and the docs it breaks: REPORT.md, F2.

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/batch_remove_dead_target_panic_record.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# fatal: flecs.c: 18164: abort(): (OnDelete, Panic) constraint violated while deleting entities with (#385,#387) (CONSTRAINT_VIOLATED)
```

- [ ] **F7: Panic isn't enforced when another pair to the same target follows it in the type, or any pair has Delete**. Story, code path and the docs it breaks: REPORT.md, F7.

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/panic_target_order.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: deleting the target of a Panic relationship did not panic (e alive: 1, has (RPanic, t): 0)
```

## Wrong values, wrong entities, wrong ids

- [ ] **F1: A batched remove of a pair whose target died earlier in the merge deletes the entity**. Story, code path and the docs it breaks: REPORT.md, F1.

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/batch_remove_dead_target.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: entity deleted by remove of (ChildOf, deleted parent) it never had
```

- [ ] **F6: An on_set hook that moves its entity makes OnSet observers run for another entity**. Story, code path and the docs it breaks: REPORT.md, F6.

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/on_set_hook_moves_entity.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: OnSet observer got entity 388 (f=388), expected e=387
# FAIL: OnSet observer saw x=2.000000, expected 99
```

- [ ] **F9: A queued set is written in place, and is lost if the component goes away before the merge**. Story, code path and the docs it breaks: REPORT.md, F9.

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/staged_set_value_lost.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: e has Position {-1.000000, -1.000000} after the merge, expected {1, 1}
```

- [ ] **F10: Batched ChildOf changes emit OnAdd/OnRemove for a pair the entity doesn't have**. Story, code path and the docs it breaks: REPORT.md, F10.

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/batch_childof_replaced_onadd.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: add+clear of (ChildOf, p1): 1 OnAdd vs 0 OnRemove calls
# FAIL: 2 OnAdd observer call(s) for a ChildOf pair e does not have
```

- [ ] **F11: Under batching, OnSet observers and on_set hooks see later values**. Story, code path and the docs it breaks: REPORT.md, F11.

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/batch_onset_values.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: OnSet calls for e saw x = 3.000000 then 3.000000, expected 1 then 3
```

- [ ] **F12: Batching runs an entity's later commands before other entities' earlier ones; a child survives its parent's deletion**. Story, code path and the docs it breaks: REPORT.md, F12.

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/batch_child_survives_parent_delete.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: child survived the deletion of its parent
```

- [ ] **F21: Instantiating a prefab with children makes a deleted entity handle alive again**. Story, code path and the docs it breaks: REPORT-2.md, F21.

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/instantiate_resurrects_deleted_handle.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: the deleted handle b is alive again (parent: 387)
```

- [ ] **F22: A batched set, remove and add of the same component keeps the set's value**. Story, code path and the docs it breaks: REPORT-2.md, F22.

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/batch_set_remove_add_value.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: e has Position {1.000000, 1.000000}, expected the constructed {-1, -1}
```

- [ ] **F23: A queued ChildOf to a parent that was deleted, and whose id was recycled, attaches the child to the new entity**. Story, code path and the docs it breaks: REPORT-2.md, F23.

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/staged_childof_recycled_parent.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: child alive after its parent was deleted; its parent is now the new entity q
```

- [ ] **F24: The table override cache misses changes of the base, so overrides are copied from the wrong place** (wrong copied values). Story, code path and the docs it breaks: REPORT-3.md, F24.

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/override_cache_stale_value.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: inst2 Position is {-1, -1}, base has {99, 99}
# FAIL: inst3 Position is {-1, -1}, base has {99, 99}
```

- [ ] **F24: The table override cache misses changes of the base, so overrides are copied from the wrong place** (a missing OnSet). Story, code path and the docs it breaks: REPORT-3.md, F24.

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/override_cache_onset_missing.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: removing the override re-exposed {50, 50} but no OnSet was emitted for inst
```

- [ ] **F24: The table override cache misses changes of the base, so overrides are copied from the wrong place** (an OnSet whose source lacks the component). Story, code path and the docs it breaks: REPORT-3.md, F24.

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/override_cache_onset_source.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: OnSet for entity 387 with source 386, which has no Position
```

- [ ] **F28: With an entity range active, instantiating a prefab with children creates instance children outside the range**. Story, code path and the docs it breaks: REPORT-3.md, F28.

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/instantiate_child_outside_range.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: instance child 388 is outside the active range [5000, 5010]
```

- [ ] **F13: The generation wraps after 2^16 recycles** (by design (16-bit generation), against the docs' "a deleted handle is not alive"). Story, code path and the docs it breaks: REPORT.md, F13.

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/generation_wraps.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: deleted handle 385 reports alive (current 385)
```

- [ ] **F14: Inside an on_add hook the entity doesn't have the component yet (lower confidence)** (lower confidence: the docs show the order only in a diagram). Story, code path and the docs it breaks: REPORT.md, F14.

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/on_add_hook_view.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: ecs_has false inside on_add hook
# FAIL: ecs_get NULL inside on_add hook
```

## Missed or extra events (observers, monitors, change detection, system activity)

- [ ] **F18: Change detection misses a write to a source entity that moved to another table**. Story, code path and the docs it breaks: REPORT-2.md, F18.

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/change_detection_fixed_source_moved.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: ecs_query_changed is false after Velocity was set on the fixed source
```

- [ ] **F19: Change detection on a fixed source that lacks the component: removal is missed, addition reads uninitialized memory**. Story, code path and the docs it breaks: REPORT-2.md, F19.

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/change_detection_fixed_source_removed.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: ecs_query_changed is false after the fixed source lost Velocity
```

- [ ] **F20: Monitors with up traversal report OnAdd for an entity that already matched, and OnRemove for one that still matches**. Story, code path and the docs it breaks: REPORT-2.md, F20.

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/monitor_up_grandparent.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: OnAdd for an entity that already matched (3 OnAdd in total)
# FAIL: OnRemove for an entity that still matches (1 OnRemove)
```

- [ ] **F25: After `ecs_run_aperiodic(EcsAperiodicEmptyQueries)`, a system stays inactive when its query matches entities again**. Story, code path and the docs it breaks: REPORT-3.md, F25.

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/pipeline_system_stays_inactive.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: Sys matches e but ran for 0 entities (EcsEmpty: 1)
```

- [ ] **F27: `ecs_query_is_true` and `ecs_query_count` clear the change state that `ecs_query_changed` reports**. Story, code path and the docs it breaks: REPORT-3.md, F27.

```sh
cc -std=gnu99 -O1 -g -I flecs/distr tests/flecs_lean/query_is_true_consumes_change.c flecs/distr/flecs.c -lm -lpthread -o t && ./t
# FAIL: after ecs_query_is_true, q1 no longer reports the set
# FAIL: after ecs_query_is_true, q2 no longer reports the unmatched table
# FAIL: after ecs_query_count, q2 no longer reports the unmatched table
```

## Predicted but not reproduced

- F2 as first predicted (`batch_remove_dead_target_panic.c`): flecs behaved as documented; a model
  error, corrected in round 2 (the entry above).
- F17's other half (`pipeline_disabled_system_skips_next.c`): the system after a self-disabling one
  still ran in that frame.
- F19's uninitialized read (`change_detection_fixed_source_added.c`): its plain run, valgrind and
  MemorySanitizer (on Linux) showed nothing.
