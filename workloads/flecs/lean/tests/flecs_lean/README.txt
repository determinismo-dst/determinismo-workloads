C tests for the predictions in ../../REPORT.md (round 1, F1-F14) and
../../REPORT-2.md (round 2, F2 corrected and F15-F23), against flecs v4.2.0.

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
