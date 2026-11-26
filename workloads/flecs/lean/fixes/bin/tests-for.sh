#!/bin/bash
# usage: tests-for.sh F<n>  -- the tests/ files a patch must turn green
case $1 in
F1) echo batch_remove_dead_target.c batch_remove_dead_target_panic_record.c batch_remove_dead_target_panic.c;;
F3) echo staged_set_pair_dead_target.c staged_set_pair_existing_dead_target.c;;
F4) echo batch_observer_deletes_entity.c;;
F5) echo set_observer_deletes_entity.c staged_set_observer_deletes_entity.c;;
F6) echo on_set_hook_moves_entity.c;;
F7) echo panic_target_order.c panic_target_with_childof.c;;
F8) echo range_make_alive_recycled.c range_new_from_range_duplicate.c;;
F11) echo batch_onset_values.c staged_ensure_rewrites_set.c;;
F12) echo batch_child_survives_parent_delete.c;;
F16) echo pipeline_wildcard_sync_point.c;;
F17) echo pipeline_disabled_system_skips_next.c pipeline_disabled_system_skips_next_init.c pipeline_disabled_systems_assert.c;;
F18) echo change_detection_fixed_source_moved.c change_detection_parent_moved.c change_detection_fixed_source_removed.c change_detection_fixed_source_added.c;;
F20) echo monitor_up_grandparent.c;;
F21) echo instantiate_resurrects_deleted_handle.c;;
F22) echo batch_set_remove_add_value.c;;
F23) echo staged_childof_recycled_parent.c;;
F25) echo pipeline_system_stays_inactive.c query_is_true_consumes_change.c;;
F26) echo workers_spurious_wakeup.c;;
F27) echo query_is_true_consumes_change.c;;
F29) echo query_or_sparse_cache_crash.c query_or_sparse_term_after_chain.c;;
F31) echo pipeline_parent_module_disabled.c pipeline_custom_uncached_term.c;;
F32) echo override_dont_fragment_2_levels.c;;
F33) echo workers_dirty_state_double_alloc.c;;
F36) echo query_iter_table_array_realloc.c;;
F38) echo auto_override_dont_fragment_variant.c;;
F39) echo tree_spawner_stale_child_type.c tree_spawner_stale_sparse_assert.c;;
F40) echo query_order_by_stale_rows.c;;
F41) echo isa_onset_sparse_dont_fragment.c;;
F42) echo set_base_onset_dont_fragment_override.c;;
F43) echo isa_second_base_onset.c;;
F44) echo prefab_mixed_children_instance.c;;
F45) echo prefab_child_auto_override_dont_fragment.c prefab_parent_child_auto_override_dont_fragment.c;;
F46) echo query_order_by_reused_table_slot.c;;
F47) echo workers_order_by_sort_race.c;;
F48) echo propagate_on_add_remove_dont_fragment_owner.c;;
F49) echo propagate_on_add_remove_second_base.c;;
F50) echo forward_on_add_remove_dont_fragment.c;;
F51) echo inheritor_onset_base_change.c;;
F52) echo prefab_parent_child_inherit_on_set_hook.c prefab_parent_child_inherit_sparse.c;;
F53) echo iter_changed_multi_threaded_system.c iter_skip_multi_threaded_system.c;;
F54) echo system_run_trivial_cache_next.c;;
F55) echo query_order_by_skip_corrupts_monitor_allocator.c;;
F56) echo query_order_by_stale_slice_next_iterator.c;;
F57) echo parent_reparent_no_on_remove.c;;
F58) echo prefab_parent_instantiate_depth_keeps_tables.c;;
esac
