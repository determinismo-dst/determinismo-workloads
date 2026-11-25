# A Lean replica of flecs

flecs (SanderMertens/flecs, the C entity component system, MIT) at its latest release, v4.2.0,
replicated in Lean 4 function by function from its source, blind (from the code, its docs and its
own tests only), and searched for departures from what its docs promise, under every order of API
calls and every interleaving of worker threads within bounds.

## Round 1

[REPORT.md](REPORT.md): 14 predictions, F1-F14, each with a minimal API program, the property and
its source in flecs's docs, the code path at v4.2.0, the search's story and tape, and a C test.
Storage (the entity index, tables, the table graph), deferred commands and stages, hooks and
observers, relationships and their cleanup policies are replicated; queries, systems and the
pipeline, and prefabs aren't yet.

The C tests ([tests/flecs_lean/](tests/flecs_lean/)) each return 0 when flecs behaves as
documented, built with `distr/flecs.c` and asserts on: a failure confirms its prediction. None
has run on the real flecs yet.

## Round 2

[REPORT-2.md](REPORT-2.md): queries and their caches (matching, rematch, groups, `order_by`,
change detection), the pipeline's schedule and sync points, monitors and up observers, prefab
instantiation. F2's model corrected: the `(Rel, *)` record that carries the Panic policy exists
only once `Rel` was used in a pair (`flecs_register_flag_for_trait` updates records that exist),
so round 1's program drops the command, as the real flecs did; with the record, the panic stands
(`batch_remove_dead_target_panic_record.c`). Nine new predictions, F15-F23, 13 new C tests (none
run yet):
- F15: a system annotating `[out] X()` then reading `[in] X()` makes `ecs_progress` abort at an
  internal assert (pipeline.c 354).
- F16: no sync point between a wildcard or Any write annotation and an overlapping read.
- F17: a system that disables itself in a frame skips the next system that frame; with three, an
  internal assert (pipeline.c 467-470).
- F18: change detection misses a write to a fixed or up source that moved to another table.
- F19: a fixed source lacking the component: its removal goes unseen, and its addition compares a
  monitor slot never written (an uninitialized read; its test runs under valgrind).
- F20: a monitor on `X(up)` reports OnAdd for an entity already matching, OnRemove for one still
  matching, when an ancestor in between changes.
- F21: instantiating a prefab with children makes a deleted entity handle alive again.
- F22: a batched set, remove and add of one component keeps the set's value.
- F23: a queued ChildOf to a deleted parent whose id was recycled attaches the child to the new
  entity (the docs: the child is deleted).

Query caches, grouping and sorting agreed with a fresh evaluation in every run. The round-1
generation lemmas are re-proved without `bv_decide`.

## Round 3

[REPORT-3.md](REPORT-3.md): prefab inheritance (the override cache, OnInstantiate traits,
auto-override, OnSet through IsA), worker-thread synchronization, system activity, reachable
caches. Five new predictions, F24-F28, 8 new C tests (none run yet):
- F24: a table's override cache refreshes only when its base's reachable-cache generation changes,
  which stops once that cache is invalid: later changes of the base are missed (an internal
  assert at table.c 979 with default traits, new instances constructed instead of copied, a
  missing or misdirected OnSet).
- F25: after `ecs_run_aperiodic(EcsAperiodicEmptyQueries)`, a system stays inactive when its query
  matches entities again.
- F26: the worker threads' sync waits without re-checking its condition: one spurious wakeup
  trips internal asserts or runs systems during a merge.
- F27: `ecs_query_is_true` and `ecs_query_count` clear the change state `ecs_query_changed`
  reports.
- F28: with an entity range active, instantiating a prefab with children creates children
  outside the range.

## On the real flecs

Round 1's 20 C tests on flecs v4.2.0 (the latest release), through determinismo-ci, flecs compiled
with coverage, 3 timelines each, every verdict the same in all 3
([validation/round-1-evidence.txt](validation/round-1-evidence.txt)):
- 13 of the 14 predictions behave as predicted (19 of 20 tests):
  - F1, F6, F7, F9, F10, F11, F12, F13 and F14 with the wrong values or callbacks their tests check
    for;
  - F4, F5 and F8 by flecs's own internal-error asserts (`ECS_INTERNAL_ERROR`: its invariants, not
    a misuse check);
  - F3 aborts the merge as predicted, at another assert than the one predicted:
    `ecs_make_alive_id`'s `!ecs_exists(world, t)` (`ECS_INVALID_PARAMETER`), not "second element
    of pair is not alive".
- F2 (the batched remove with a Panic relationship) passes: flecs behaves as documented there.
- F13 is the 16-bit generation wrapping by design, a defect only against the docs' "a deleted
  handle is not alive"; F14 the report marks lower confidence (the docs show the order only in a
  diagram). The behaviors are confirmed either way.
- Not yet searched against flecs's issues.

Rounds 2 and 3's tests (F15-F28, F2's corrected test) on flecs v4.2.0, compiled with asserts on
and run directly (one process each; the workflow `flecs-lean` runs them on GitHub's Linux runners):
- F2's corrected prediction aborts as predicted (`(OnDelete, Panic)` constraint violated in the
  merge).
- Internal-error asserts (`ECS_INTERNAL_ERROR`):
  - F15: `needs_merge == false` in the pipeline's update;
  - F16, F17: the readonly assert in `flecs_table_ensure`;
  - F24: `base_ptr != NULL` in `flecs_table_invoke_ctor`;
  - F26: `workers_waiting == stage_count - 1` in `flecs_wait_for_sync`, after one spurious wakeup.
- Wrong values or callbacks, as their tests check: F18, F19 (the source that lost the component),
  F20, F21, F22, F23, F24 (new instances constructed, not copied; OnSet missing or with a source
  that lacks the component), F25, F27, F28.
- Not confirmed:
  - F17's other half, the next system skipped after a self-disabling one: Update ran (back to the
    replica, round 4).
  - F19's uninitialized read (`change_detection_fixed_source_added.c`): neither its plain run nor
    MemorySanitizer showed it; valgrind on Linux is in the workflow.

## Building and running

    lake update && lake build flecs-search FlecsLean
    .lake/build/bin/flecs-search cases                    # each C test's program in the model
    .lake/build/bin/flecs-search explore SEED N ENTS LEN  # random API programs
    .lake/build/bin/flecs-search pipe|query|obs-explore|isa-explore ...  # round 2's (REPORT-2.md)

The replica's own fixes, when a round adds any, are switches off by default: the replica is flecs
as written.

## License

MIT, as flecs (copyright Sander Mertens; portions copyright Meta Platforms, Inc. and affiliates).
