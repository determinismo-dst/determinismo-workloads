C tests for the predictions in ../../REPORT.md (round 1, F1-F14),
../../REPORT-2.md (round 2, F2 corrected and F15-F23), ../../REPORT-3.md
(round 3, F24-F28) and ../../REPORT-4.md (round 4, F29-F33, and the
corrected F16, F17 and F26 tests), against flecs v4.2.0.

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
