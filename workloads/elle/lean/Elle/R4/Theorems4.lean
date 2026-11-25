import Elle.R4.LACycle
import Elle.R4.GInterp
import Elle.R4.Fixes
import Elle.R4.Rename
import Elle.R4.Lattice

/-!
# Round 4: the headline theorems, and their axioms

Every theorem here holds for every history (no bound on its size), with no `sorry`, no
`native_decide` and no axiom beyond Lean's three (`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace Elle.R4.Theorems4

open Elle Elle.R4 Elle.R4.LA

/-- Soundness of list-append's inferred edges, clean interpretations (models prohibiting G1a). -/
example := @ww_lift
example := @wr_lift
example := @rw_lift
example := @unread_lift
/-- The process and real-time steps. -/
example := @lt_invIdx_of_proc
example := @lt_invIdx_of_realtime
example := @pairIndex_ok
/-- Theorem 1 for list-append's cycles, clean interpretations, the service as deployed next. -/
example := @la_cycle_clean
/-- D4 with D5: read uncommitted's G0 cycles in every interpretation. -/
example := @ww_lift_d5
example := @la_g0_cycle_d5
/-- D23's restored edge. -/
example := @d23_ww
/-- D8 and D7. -/
example := @garbage_no_interp
example := @RR.future_read_no_interp
/-- D12's refinement under renaming. -/
example := @Rename.sortedValues_d12b_ren
example := @Rename.appendIndex_d12b_ren
/-- The generic cycle lifting. -/
example := @lift_cycle

end Elle.R4.Theorems4

#print axioms Elle.R4.LA.ww_lift
#print axioms Elle.R4.LA.wr_lift
#print axioms Elle.R4.LA.rw_lift
#print axioms Elle.R4.LA.unread_lift
#print axioms Elle.R4.LA.pairIndex_ok
#print axioms Elle.R4.LA.lt_invIdx_of_proc
#print axioms Elle.R4.LA.lt_invIdx_of_realtime
#print axioms Elle.R4.LA.la_cycle_clean
#print axioms Elle.R4.LA.ww_lift_d5
#print axioms Elle.R4.LA.la_g0_cycle_d5
#print axioms Elle.R4.LA.d23_ww
#print axioms Elle.R4.LA.garbage_no_interp
#print axioms Elle.R4.RR.future_read_no_interp
#print axioms Elle.R4.Rename.sortedValues_d12b_ren
#print axioms Elle.R4.Rename.appendIndex_d12b_ren
#print axioms Elle.R4.lift_cycle
