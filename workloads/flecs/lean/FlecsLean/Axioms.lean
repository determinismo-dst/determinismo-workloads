import FlecsLean.Theorems
import FlecsLean.TheoremsPipe
import FlecsLean.TheoremsInh
import FlecsLean.TheoremsR4
import FlecsLean.TheoremsR5
import FlecsLean.TheoremsR6

/-! The axioms each theorem depends on (printed at build time). -/
#print axioms Flecs.genInc_lo32
#print axioms Flecs.genInc_generation
#print axioms Flecs.genInc_high
#print axioms Flecs.gen_of_pack
#print axioms Flecs.pack_mask
#print axioms Flecs.unpack
#print axioms Flecs.arith16
#print axioms Flecs.arith16_period
#print axioms Flecs.genInc_genIter
#print axioms Flecs.genIter_zero
#print axioms Flecs.toUInt64_succ
#print axioms Flecs.iterate_genInc
#print axioms Flecs.genInc_period
#print axioms Flecs.deleteAction_delete
#print axioms Flecs.deleteAction_no_delete
#print axioms Flecs.deleteAction_panic_iff
#print axioms Flecs.EIndex.tryGetAny_some
#print axioms Flecs.EIndex.not_alive_of_dead_slot
#print axioms Flecs.EIndex.newId_recycled_not_alive
#print axioms Flecs.Pipe.getWS_empty
#print axioms Flecs.Pipe.checkTerm_empty
#print axioms Flecs.Pipe.single_term_no_assert
#print axioms Flecs.Pipe.write_then_read_asks_merge
#print axioms Flecs.Pipe.wildcard_write_missed
#print axioms Flecs.Pipe.any_read_missed
#print axioms Flecs.R3.invalidate_invalid
#print axioms Flecs.R3.invalidate_valid
#print axioms Flecs.R3.changes_invalid
#print axioms Flecs.R3.override_cache_misses_changes
#print axioms Flecs.R3.override_cache_sees_first_change
#print axioms Flecs.R3.reachable_invalid_state
#print axioms Flecs.Activity.addToCache_keeps_empty
#print axioms Flecs.R4.or_sparse_cache_crash
#print axioms Flecs.R4.or_sparse_uncached_ok
#print axioms Flecs.R4.or_sparse_merges_chain
#print axioms Flecs.R4.searchUp_dontFragment_one_level
#print axioms Flecs.R4.two_levels_get_vs_search
#print axioms Flecs.R4.two_levels_sparse_found
#print axioms Flecs.R4.update_keeps_schedule
#print axioms Flecs.R4.parent_disable_keeps_count
#print axioms Flecs.R4.childof_disable_bumps_count
#print axioms Flecs.R5.or_after_chain_compile
#print axioms Flecs.R5.or_sparse_first_complete_block
#print axioms Flecs.R5.auto_override_variant_inherits
#print axioms Flecs.R5.auto_override_controls
#print axioms Flecs.R5.autoVisit_direct_first
#print axioms Flecs.R5.spawner_stale_type
#print axioms Flecs.R5.reorder_resume_past_end
#print axioms Flecs.R5.pushMatch_full_reallocates
#print axioms Flecs.R6.reach_dontFragment_nil
#print axioms Flecs.R6.isa_onset_needs_column
#print axioms Flecs.R6.onset_cases
#print axioms Flecs.R6.spawner_only_parent
#print axioms Flecs.R6.spawner_cases
#print axioms Flecs.R6.reused_slot_case
#print axioms Flecs.R6.or_after_chain_iterate
