import FlecsLean.Theorems

/-! The axioms each theorem depends on (printed at build time). -/
#print axioms Flecs.genInc_lo32
#print axioms Flecs.genInc_generation
#print axioms Flecs.genInc_high
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
