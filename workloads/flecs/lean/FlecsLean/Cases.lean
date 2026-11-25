/-
  The C tests of tests/flecs_lean as model programs (one per prediction), so
  the replica can be checked against each prediction and each shrunk
  counterexample can be replayed.
-/
import FlecsLean.Search

namespace Flecs

def s0 : Tgt := .stage 0

/-- batch_remove_dead_target.c -/
def caseBatchRemoveDeadTarget : Scenario := { ops := [
  .new, .new, .new,                       -- 0 parent, 1 e, 2 lone
  .delete s0 0,
  .add s0 1 .tag,
  .remove s0 1 (.pair .childOf 0),
  .remove s0 2 (.pair .childOf 0),
  .merge 0 ] }

/-- batch_remove_dead_target_panic.c -/
def caseBatchRemovePanic : Scenario := { ops := [
  .new, .new,                             -- 0 tgt, 1 e
  .delete s0 0,
  .add s0 1 .tag,
  .remove s0 1 (.pair .panic 0),
  .merge 0 ] }

/-- batch_remove_dead_target_panic_record.c (F2 corrected): the same program
    after the relationship was used in a pair, so its (Rel, *) record exists -/
def caseBatchRemovePanicRecord : Scenario := { caseBatchRemovePanic with relRecords := true }

/-- staged_set_pair_dead_target.c -/
def caseStagedSetPairDeadTarget : Scenario := { ops := [
  .new, .new,                             -- 0 tgt, 1 e
  .set s0 1 (.pair .c0 0) 1,
  .delete .world 0,
  .merge 0 ] }

/-- staged_set_pair_existing_dead_target.c -/
def caseStagedSetPairExisting : Scenario := { ops := [
  .new, .new,
  .set .world 1 (.pair .c0 0) 1,
  .delete s0 0,
  .set s0 1 (.pair .c0 0) 2,
  .merge 0 ] }

/-- batch_observer_deletes_entity.c (menu 2: OnRemove C1 deletes through the stage) -/
def caseBatchObserverDeletes : Scenario := { cfg := 2, ops := [
  .new,
  .set .world 0 .c1 1,
  .remove s0 0 .c1,
  .add s0 0 .tag,
  .merge 0 ] }

/-- set_observer_deletes_entity.c (menu 3: OnAdd C1 deletes through the stage) -/
def caseSetObserverDeletes : Scenario := { cfg := 3, ops := [
  .new, .new,
  .add .world 0 .c1,
  .set .world 1 .c1 1 ] }

/-- on_set_hook_moves_entity.c (menu 1) -/
def caseOnSetHookMoves : Scenario := { cfg := 1, ops := [
  .new, .new,
  .set .world 0 .c0 1,
  .set .world 1 .c0 2,
  .set .world 0 .c0 99 ] }

/-- panic_target_order.c -/
def casePanicOrder : Scenario := { panicFirst := true, ops := [
  .new, .new,                             -- 0 t, 1 e
  .add .world 1 (.pair .panic 0),
  .add .world 1 (.pair .remove 0),
  .delete .world 0 ] }

/-- the same with the relationships created the other way round (panics) -/
def casePanicOrderControl : Scenario := { panicFirst := false, ops := casePanicOrder.ops }

/-- range_make_alive_recycled.c -/
def caseRangeMakeAlive : Scenario := { ops := [
  .rangeNew 5000 6000, .rangeNew 7000 8000,
  .rangeSet 1, .newFromRange 1,          -- slot 0 = 7000 (new_from_range on the active range = ecs_new)
  .rangeSet 0,
  .delete .world 0,
  .makeAlive 0 0,
  .rangeSet 1,
  .new ] }

/-- staged_set_after_remove_all.c -/
def caseSetAfterRemoveAll : Scenario := { ops := [
  .new,
  .set .world 0 .c0 1,
  .removeAll s0 .c0,
  .set s0 0 .c0 2,
  .merge 0 ] }

/-- batch_childof_replaced_onadd.c (menu 5) -/
def caseChildOfReplaced : Scenario := { cfg := 5, ops := [
  .new, .new, .new,                       -- 0 p1, 1 p2, 2 e
  .add s0 2 (.pair .childOf 0),
  .add s0 2 (.pair .childOf 1),
  .merge 0 ] }

/-- on_add_hook_view.c (menu 4) -/
def caseOnAddHookView : Scenario := { cfg := 4, ops := [
  .new,
  .add .world 0 .c0 ] }

/-- batch_onset_values.c (menu 8: recording observers) -/
def caseBatchOnSetValues : Scenario := { cfg := 8, ops := [
  .new, .new,
  .set s0 0 .c0 1,
  .set s0 1 .c0 2,
  .set s0 0 .c0 3,
  .merge 0 ] }

/-- batch_child_survives_parent_delete.c -/
def caseChildSurvives : Scenario := { ops := [
  .new, .new,                             -- 0 p, 1 c
  .add s0 1 (.pair .childOf 0),
  .delete s0 0,
  .remove s0 1 (.pair .childOf 0),
  .merge 0 ] }

/-- staged_set_observer_deletes_entity.c (menu 3) -/
def caseStagedSetObserverDeletes : Scenario := { cfg := 3, ops := [
  .new,
  .set s0 0 .c1 1,
  .merge 0 ] }

/-- staged_ensure_rewrites_set.c (menu 8) -/
def caseEnsureRewritesSet : Scenario := { cfg := 8, ops := [
  .new,
  .set s0 0 .c0 99,
  .ensure s0 0 .c0 1,
  .merge 0 ] }

/-- panic_target_with_childof.c -/
def casePanicWithChildOf : Scenario := { ops := [
  .new, .new,                             -- 0 t, 1 e
  .add .world 1 (.pair .panic 0),
  .add .world 1 (.pair .childOf 0),
  .delete .world 0 ] }

/-- staged_set_value_lost.c -/
def caseSetValueLost : Scenario := { ops := [
  .new,
  .set .world 0 .c0 7,
  .set s0 0 .c0 1,
  .remove .world 0 .c0,
  .merge 0 ] }

/-- range_new_from_range_duplicate.c -/
def caseRangeNewFromRangeDup : Scenario := { ops := [
  .rangeNew 5000 6000,
  .newFromRange 0,
  .delete .world 0,
  .makeAlive 0 1,
  .newFromRange 0 ] }

/-- monitor_up_grandparent.c (menu 9, monitor on C0(up)): the grandparent
    and then the parent get C0; the child already matched -/
def caseMonitorGrandparent : Scenario := { cfg := 9, ops := [
  .new, .new, .new,                         -- 0 grandparent, 1 parent, 2 child
  .add .world 1 (.pair .childOf 0),
  .add .world 2 (.pair .childOf 1),
  .add .world 0 .c0,                        -- child starts matching: OnAdd
  .add .world 1 .c0,                        -- child still matches
  .remove .world 1 .c0 ] }                  -- child still matches

/-- the same with a C0(self|up) monitor (menu 10) -/
def caseMonitorGrandparentSelfUp : Scenario := { caseMonitorGrandparent with cfg := 10 }

/-- instantiate_resurrects_deleted_handle.c: the prefab's child sits at
    offset 1 from the prefab; the instance's id + 1 was deleted -/
def caseInstantiateResurrects : Scenario := { ops := [
  .new, .new,                               -- 0 prefab, 1 prefab child (= prefab + 1)
  .add .world 0 .prefab,
  .add .world 1 (.pair .childOf 0),
  .new, .new,                               -- 2 instance, 3 b (= instance + 1)
  .delete .world 3,
  .add .world 2 (.pair .isA 0) ] }

/-- staged_childof_recycled_parent.c: the queued parent is deleted and its
    id recycled before the merge -/
def caseChildOfRecycledParent : Scenario := { ops := [
  .new, .new,                               -- 0 p, 1 c
  .add s0 1 (.pair .childOf 0),
  .delete .world 0,
  .new,                                     -- 2 q (recycles p's id)
  .merge 0 ] }

def allCases : List (String × Scenario) := [
  ("batch_remove_dead_target", caseBatchRemoveDeadTarget),
  ("batch_remove_dead_target_panic", caseBatchRemovePanic),
  ("batch_remove_dead_target_panic_record (F2 corrected)", caseBatchRemovePanicRecord),
  ("staged_set_pair_dead_target", caseStagedSetPairDeadTarget),
  ("staged_set_pair_existing_dead_target", caseStagedSetPairExisting),
  ("batch_observer_deletes_entity", caseBatchObserverDeletes),
  ("set_observer_deletes_entity", caseSetObserverDeletes),
  ("on_set_hook_moves_entity", caseOnSetHookMoves),
  ("panic_target_order", casePanicOrder),
  ("panic_target_order (control, other creation order)", casePanicOrderControl),
  ("range_make_alive_recycled", caseRangeMakeAlive),
  ("staged_set_after_remove_all", caseSetAfterRemoveAll),
  ("batch_childof_replaced_onadd", caseChildOfReplaced),
  ("on_add_hook_view", caseOnAddHookView),
  ("batch_onset_values", caseBatchOnSetValues),
  ("batch_child_survives_parent_delete", caseChildSurvives),
  ("staged_set_observer_deletes_entity", caseStagedSetObserverDeletes),
  ("staged_ensure_rewrites_set", caseEnsureRewritesSet),
  ("panic_target_with_childof", casePanicWithChildOf),
  ("staged_set_value_lost", caseSetValueLost),
  ("range_new_from_range_duplicate", caseRangeNewFromRangeDup),
  ("monitor_up_grandparent", caseMonitorGrandparent),
  ("monitor_up_grandparent (self|up)", caseMonitorGrandparentSelfUp),
  ("instantiate_resurrects_deleted_handle", caseInstantiateResurrects),
  ("staged_childof_recycled_parent", caseChildOfRecycledParent) ]

end Flecs
