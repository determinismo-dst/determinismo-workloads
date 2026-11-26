
## Everything together

`fixes/all-fixes.diff` was built and checked as one patch (`bin/verify-combo.sh`), with every test in `tests/`:

- **The finding tests of the fixed findings:** all 64 exit 0 (the 42 of rounds 1–5, the 8 of round 6, and the 14 of rounds 7 and 8, `parent_storage_dont_fragment_events.c` among them). Two of them also pass on v4.2.0: `batch_remove_dead_target_panic.c` (F2's first form) and `change_detection_fixed_source_added.c` (F19).
- **The tests that are still red:**
  - the no-fix findings: `staged_set_value_lost.c` and `staged_set_after_remove_all.c` (F9), `generation_wraps.c` (F13), `on_add_hook_view.c` (F14), `instantiate_child_outside_range.c` (F28), `query_iter_skips_table.c` (F30), `query_cascade_table_twice.c` and `query_cascade_group_freed.c` (F35), `pipeline_phase_reorder_skips.c` (F37);
  - the findings left to upstream: `batch_childof_replaced_onadd.c` (F10), `pipeline_write_read_same_system.c` (F15), and the four `override_cache_*.c` tests (F24).
- **Tests that need another build:** in the default build `query_order_by_skip_leaks_dirty_state.c` (F55) and round 7's `query_order_by_freed_slot_dirty_state.c` return 2 by design. In their modes (`build/modes/together/summary.txt`) every round-8 test exits 0: release builds of F53's, F55's, F56's and F58's tests, and F55's leak test with `FLECS_USE_OS_ALLOC` and with `FLECS_SANITIZE`.
- **F10's test:** the F12 patch fixes its add-then-clear half. The other half, a ChildOf pair replaced within one batch, still fails.
- **Suites:** core 3870 / 0, query 4798 / 6 (the baseline's 6), addons 643 / 0, collections 97 / 0, cpp 1919 / 0: unchanged.
- **Warnings:** the amalgamation compiles without warnings with all patches.
- **The extra checks of rounds 6–8** (`fixes/checks/F41_*.c` to `F58_*.c`) all pass on the combined build. The earlier checks give the results their sections describe (F5's check stops at the documented INVALID_OPERATION; F20's Parent `self|up` variant still fails).
- **AddressSanitizer, all patches:** with `FLECS_USE_OS_ALLOC`, F55's leak test, F56's test and check, F46's test and check are clean; with the default allocator, F55's corruption test and F56's test are clean.
- **ThreadSanitizer, all patches** (release build):
  - `workers_order_by_sort_race.c`, 3 runs: "two threads sorting at once: 0; table intact: 1" and 1, 4 and 1 race reports, none in sorting, slices or monitors (F47 removes those, F33 the monitor syncs). They are statistics counters that every worker increments without atomics (`q->eval_count` in `flecs_query_iter`, `world->info.queries_ran_total` and `systems_ran_total`) and the worker loop's read of `world->flags` against `ecs_frame_begin`. The build of F1–F47 gives the same kinds (4, 1 and 4 reports in a run of it now). No patch here changes them.
  - `fixes/checks/F53_mt_changed_frames.c`, 2 runs: 12 reports in each, the same counters (and `ecs_os_api_malloc`'s), the frame flags, and `cache->prev_match_count`, which every stage's new iterator writes (src/query/cache/cache_iter.c 36) while worker 0 syncs a monitor. None is in F53's code or in a monitor.
