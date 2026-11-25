import FlecsLean.Theorems
import FlecsLean.TheoremsPipe

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
