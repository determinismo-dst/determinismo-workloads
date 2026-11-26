C tests for the predictions in ../../REPORT.md (round 1, F1-F14),
../../REPORT-2.md (round 2, F2 corrected and F15-F23), ../../REPORT-3.md
(round 3, F24-F28), ../../REPORT-4.md (round 4, F29-F33, and the
corrected F16, F17 and F26 tests), ../../REPORT-5.md (round 5,
F34-F40), ../../REPORT-6.md (round 6, F41-F47), ../../REPORT-7.md
(round 7, F48-F55), REPORT-8 (round 8, F55 corrected-F58) and round 9
(F59-F62; the round 9 report is in the agent's final message), against
flecs v4.2.0.

Each file is one program.  main() returns 0 when flecs behaves as its
documentation says; a non-zero return or an abort confirms the prediction.
A few round 2 tests return 2 when their setup does not hold ("INCONCLUSIVE").
Build each with the single-file distribution, debug build (asserts on):

    cc -std=c99 -I ../../upstream/distr <test>.c ../../upstream/distr/flecs.c -o t && ./t; echo $?

Tests that expect flecs to panic install an abort handler that exits 0
(documented panic) and return 1 when no panic happens.  Tests that predict an
abort install a handler that prints FAIL and exits 1.

Round 2:
  F2 (corrected)  batch_remove_dead_target_panic_record.c
  F15             pipeline_write_read_same_system.c
  F16             pipeline_wildcard_sync_point.c
  F17             pipeline_disabled_system_skips_next.c,
                  pipeline_disabled_systems_assert.c
  F18             change_detection_fixed_source_moved.c,
                  change_detection_parent_moved.c
  F19             change_detection_fixed_source_removed.c,
                  change_detection_fixed_source_added.c (run under valgrind
                  or MemorySanitizer: the read is of uninitialized memory)
  F20             monitor_up_grandparent.c
  F21             instantiate_resurrects_deleted_handle.c
  F22             batch_set_remove_add_value.c
  F23             staged_childof_recycled_parent.c

Round 3:
  F24             override_cache_stale_ref.c (abort at table.c 979),
                  override_cache_stale_value.c,
                  override_cache_onset_missing.c,
                  override_cache_onset_source.c
  F25             pipeline_system_stays_inactive.c
  F26             workers_spurious_wakeup.c (needs threads: link with
                  -lpthread; it installs a cond_wait that wakes once
                  without a signal)
  F27             query_is_true_consumes_change.c
  F28             instantiate_child_outside_range.c

Round 4:
  F29             query_or_sparse_cache_crash.c (a crash, SIGSEGV, confirms)
  F30             query_iter_skips_table.c
  F31             pipeline_parent_module_disabled.c,
                  pipeline_custom_uncached_term.c
  F32             override_dont_fragment_2_levels.c
  F33             workers_dirty_state_double_alloc.c (needs threads: link
                  with -lpthread; it wraps the OS API malloc so that two
                  threads meet in the allocation of one table's dirty state)

Round 4 corrections to earlier tests (see REPORT-4.md, "Model errors and
test errors corrected"):
  F17             pipeline_disabled_system_skips_next.c and
                  pipeline_disabled_systems_assert.c now use ecs_mini() with
                  the pipeline module (ecs_init()'s ProgressTasks, an always
                  active immediate system in PreUpdate, ran before the OnUpdate
                  systems and gave the rebuild a correct resume point), and
                  enqueue through it->stage. New:
                  pipeline_disabled_system_skips_next_init.c (ecs_init(),
                  systems in OnLoad).
  F16             pipeline_wildcard_sync_point.c: the writer enqueues through
                  it->stage (it->world executes at once; in a readonly
                  system that is the readonly assert of flecs_table_ensure).
  F26             workers_spurious_wakeup.c: the worker's stage id comes from
                  it->stage (it->world is the world on every thread).

Round 5 (all use ecs_mini(); none was run in round 5):
  F34             query_or_sparse_term_after_chain.c (wraps the OS API
                  allocator with a zeroed guard before every block; a
                  changed guard or the wrong entities confirm)
  F35             query_cascade_table_twice.c,
                  query_cascade_group_freed.c (the OS API free fills the
                  block with 0xA5 and keeps it; a crash confirms)
  F36             query_iter_table_array_realloc.c (the same free wrapper;
                  a crash confirms)
  F37             pipeline_phase_reorder_skips.c (ecs_mini() with
                  FlecsPipeline: no builtin systems)
  F38             auto_override_dont_fragment_variant.c
  F39             tree_spawner_stale_child_type.c,
                  tree_spawner_stale_sparse_assert.c (an abort confirms:
                  the handler prints FAIL and exits 1)
  F40             query_order_by_stale_rows.c

Round 6 (all use ecs_mini() except the threaded test; none was run in
round 6):
  F41             isa_onset_sparse_dont_fragment.c (OnSet on an IsA add,
                  one and two levels; a table component is the control)
  F42             set_base_onset_dont_fragment_override.c
  F43             isa_second_base_onset.c
  F44             prefab_mixed_children_instance.c
  F45             prefab_child_auto_override_dont_fragment.c (ChildOf child),
                  prefab_parent_child_auto_override_dont_fragment.c (Parent
                  child; it includes the first file with
                  FLECS_LEAN_PARENT_CHILD set). An abort confirms: the
                  handler prints FAIL and exits 1.
  F46             query_order_by_reused_table_slot.c
  F47             workers_order_by_sort_race.c (needs threads: link with
                  -lpthread; ecs_init(); the order_by callback is a
                  rendezvous that detects two threads sorting at once; a
                  crash or an abort also confirms)

Round 7 (all use ecs_mini() unless noted; none was run in round 7):
  F48             propagate_on_add_remove_dont_fragment_owner.c (an instance
                  that owns a DontFragment component gets the OnAdd and
                  OnRemove of its base, and so does its own inheritor; (b)
                  the ChildOf example of "Event Propagation": an OnSet
                  reaches the grandchild through a child that owns the
                  DontFragment component; table and Sparse are the controls)
  F49             propagate_on_add_remove_second_base.c (OnAdd and OnRemove
                  from a second base that is not the source, propagated and
                  forwarded; a diamond gives OnAdd twice)
  F50             forward_on_add_remove_dont_fragment.c (no forwarded OnAdd
                  or OnRemove for an inherited DontFragment component, IsA
                  and the ChildOf example of "Event Forwarding")
  F51             inheritor_onset_base_change.c (no OnSet for the inheritors
                  of a variant that gains a base or loses an override)
  F52             prefab_parent_child_inherit_on_set_hook.c,
                  prefab_parent_child_inherit_sparse.c (it includes the first
                  file with FLECS_LEAN_SPARSE set). An abort confirms: the
                  handler prints FAIL and exits 1.
  F53             iter_changed_multi_threaded_system.c,
                  iter_skip_multi_threaded_system.c (it includes the first
                  file with FLECS_LEAN_SKIP set). Needs threads: link with
                  -lpthread; ecs_mini() with FlecsPipeline and
                  ecs_set_os_api_impl(). An abort or a crash confirms.
  F54             system_run_trivial_cache_next.c (ecs_mini() with
                  FlecsPipeline; an abort also confirms)
  F55             query_order_by_freed_slot_dirty_state.c: build flecs.c and
                  the test with -DFLECS_USE_OS_ALLOC (every flecs allocation
                  is then one OS allocation, which the test's wrapper guards;
                  the test returns 2, INCONCLUSIVE, without it):

    cc -std=c99 -DFLECS_USE_OS_ALLOC -I ../../upstream/distr \
        query_order_by_freed_slot_dirty_state.c ../../upstream/distr/flecs.c \
        -o t && ./t; echo $?

  F47 (round 6)   workers_order_by_sort_race.c is unchanged: a debug build
                  confirms it by the abort at query/cache/order_by.c 87-88
                  (ECS_UNSUPPORTED, "cannot sort query in multithreaded
                  mode"), a release build (-DNDEBUG) by the race.

Round 8 (all use ecs_mini(); none was run in round 8):
  F55 (corrected) query_order_by_freed_slot_dirty_state.c (round 7) is
                  unchanged and its result stands: it showed no write
                  past the planted block because flecs_init_table resets
                  dirty_state (storage/table_graph.c 424). The corrected
                  prediction has two tests:
                  query_order_by_skip_leaks_dirty_state.c: the block the
                  skip plants is never freed. Build flecs.c and the test
                  with -DFLECS_USE_OS_ALLOC (the wrapper reports tagged
                  4-byte blocks live after ecs_fini) or with
                  -DFLECS_SANITIZE (ecs_fini aborts with "Leak detected!";
                  the handler prints FAIL); a plain build returns 2:

    cc -std=c99 -DFLECS_USE_OS_ALLOC -I ../../upstream/distr \
        query_order_by_skip_leaks_dirty_state.c ../../upstream/distr/flecs.c \
        -o t && ./t; echo $?
    cc -std=c99 -DFLECS_SANITIZE -I ../../upstream/distr \
        query_order_by_skip_leaks_dirty_state.c ../../upstream/distr/flecs.c \
        -o t && ./t; echo $?

                  query_order_by_skip_corrupts_monitor_allocator.c: the
                  default build (debug, and also -DNDEBUG); the skip's
                  writes into the freed monitor overwrite the monitor
                  allocator's free-list link, and the second monitor
                  allocated afterwards is a wild pointer. A crash or an
                  abort confirms (the handler prints FAIL and exits 1);
                  OS_ALLOC and SANITIZE builds return 2.
  F56             query_order_by_stale_slice_next_iterator.c (a table
                  deleted during an order_by iteration keeps its slice in
                  the next iterator; a crash or an abort also confirms)
  F57             parent_reparent_no_on_remove.c (no OnRemove when a
                  Parent-storage child is re-parented; the ChildOf storage
                  is the control)
  F58             prefab_parent_instantiate_depth_keeps_tables.c (an
                  instance at depth 8 keeps its children's table for good;
                  a debug build aborts when the prefab is deleted, a
                  release build leaves a table the control does not)
  F48, F50        parent_storage_dont_fragment_events.c: the Parent-storage
  (Parent forms)  forms of round 7's ChildOf forms, same mechanisms
  F53 (round 7)   iter_changed_multi_threaded_system.c is unchanged; a
                  release build (-DNDEBUG) crashes with a NULL dereference
                  in flecs_query_get_match_monitor (change_detection.c 89),
                  which the handler also counts. iter_skip_..., release:
                  no abort, the skip is ignored (not detected by the test).
  F52 (round 7)   the abort at flecs.c 7976 is the predicted assert:
                  flecs.c 7938 opens flecs_notify_on_set_w_cr, 7974-7976
                  are component_actions.c 677-679. The tests are unchanged.

Round 9 (all use ecs_mini(); none was run in round 9):
  F59             query_or_up_then_self_fields.c (uncached Position(up) ||
                  Velocity: form b, a result that names the wrong source and
                  reads another entity's Velocity; then form a, an
                  ecs_field read of entity 0's record: debug abort "entity
                  0 does not exist", release crash),
                  query_or_self_up_then_self_columns.c (Position(self|up) ||
                  Velocity: debug abort in ecs_query_next, "it->columns[0]=-1
                  does not match expected 0"; release: columns -1 and a
                  crash in ecs_field),
                  query_or_self_then_up_fields.c (Position || Velocity(up):
                  D2's result names Position; ecs_field crashes).
                  Build each in the default debug build and again with
                  -DNDEBUG:

    cc -std=c99 -DNDEBUG -I ../../upstream/distr \
        query_or_up_then_self_fields.c ../../upstream/distr/flecs.c \
        -o t && ./t; echo $?

                  A crash or an abort confirms (the handler prints FAIL and
                  exits 1); a signal in a control prints INCONCLUSIVE and
                  exits 2.
  F60             sparse_remove_while_iterating.c (removing a DontFragment
                  tag while iterating: part A, the trivial sparse search
                  over 2100 entities returns 1076, the VM's select "Df,
                  !Unused" is the control; part B, the VM's select returns
                  one entity twice). Default debug build.
  F61             query_order_by_set_group_unsorted.c (ecs_iter_set_group on
                  a query with group_by and order_by returns 1 3 2 4; the
                  full iteration is the control). Default debug build.
  F62             parent_set_same_parent_on_add.c (ecs_set of EcsParent to
                  the parent the entity already has, and ecs_modified on it,
                  deliver OnAdd (ChildOf, p) and the forwarded OnAdd of p's
                  Tag again; ChildOf storage is the control). Default debug
                  build.
