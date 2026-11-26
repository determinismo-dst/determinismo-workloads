/-
  Round 5 theorems.  No `sorry`; the axioms used are printed by Axioms.lean.
  The concrete ones are checked by the kernel (`decide +kernel`).
-/
import FlecsLean.OrVM
import FlecsLean.InhDF
import FlecsLean.Spawner
import FlecsLean.Pipeline
import FlecsLean.Query

namespace Flecs.R5

open Flecs.Val Flecs.OrVM in
/-- F34: `TagA || Position, TagC` with Position Sparse compiles to SetIds,
    Cache, And(Position), End, Yield; the And and the End get the label -1
    (`flecs_query_end_block_or` with `lbl_begin == -1`, compiler_term.c
    306-311), and the compiler accesses `ops[-1]` once. -/
theorem or_after_chain_compile :
    (match finalizeTerms #[.table, .sparse, .table]
        #[{ comp := 0, oper := .or }, { comp := 1 }, { comp := 2 }] with
      | .ok q =>
        let c := compile q #[{ comp := 0, oper := .or }, { comp := 1 }, { comp := 2 }]
        (c.ops.map (·.kind), c.ops.map (fun o => (o.prev, o.next)), c.oob.size)
      | .error _ => (#[], #[], 99)) =
    (#[.setIds, .cache, .and_, .end_, .yield], #[(-1, 1), (0, 2), (-1, 3), (-1, 4), (3, 5)], 1) := by
  decide +kernel

open Flecs.Val Flecs.OrVM in
/-- F34's control: with the Sparse term first in the chain, the validator
    makes the whole chain uncached (its consistency pass sees the Sparse
    term's cleared flag), so the compiler builds a complete Or block and
    nothing is accessed out of bounds. -/
theorem or_sparse_first_complete_block :
    (match finalizeTerms #[.table, .sparse, .table]
        #[{ comp := 1, oper := .or }, { comp := 0 }, { comp := 2 }] with
      | .ok q =>
        let c := compile q #[{ comp := 1, oper := .or }, { comp := 0 }, { comp := 2 }]
        (q.terms.map (·.cacheable), c.ops.map (·.kind), c.oob.size)
      | .error _ => (#[], #[], 99)) =
    (#[false, false, true], #[.setIds, .cache, .or_, .and_, .and_, .end_, .yield], 0) := by
  decide +kernel

open Flecs.IDF in
def runSt (p : Prog) : St := p.ops.foldl (fun st op => (step st op).1) { comps := p.comps }

open Flecs.IDF in
/-- F38: Defense (DontFragment, Inherit) = 50 on SpaceShip (0), auto
    overridden; Freighter (1) IsA SpaceShip; inst (2) IsA Freighter.  The
    variant owns Defense (its own instantiation overrode it); the instance
    does not own it and inherits 50. -/
theorem auto_override_variant_inherits :
    let st := runSt { comps := #[{ storage := .dontFragment, trait := .inherit }],
                      ops := [.new, .new, .new, .set 0 0 50, .autoOverride 0 0, .isa 1 0, .isa 2 1] }
    owns st 1 0 = some 50 ∧ owns st 2 0 = none ∧ get st 2 0 = some 50 := by
  decide +kernel

open Flecs.IDF in
/-- F38's controls: with a table component the instance of the variant owns
    it (the table graph recurses, table_graph.c 780-789); one IsA level owns
    the DontFragment component. -/
theorem auto_override_controls :
    owns (runSt { comps := #[{ storage := .table, trait := .inherit }],
                  ops := [.new, .new, .new, .set 0 0 50, .autoOverride 0 0, .isa 1 0, .isa 2 1] }) 2 0 = some 50 ∧
    owns (runSt { comps := #[{ storage := .dontFragment, trait := .inherit }],
                  ops := [.new, .new, .set 0 0 50, .autoOverride 0 0, .isa 1 0] }) 1 0 = some 50 := by
  decide +kernel

open Flecs.IDF in
/-- F38, for every world: an instantiation's own DontFragment overrides read
    only the direct base's auto-override flags; a base of the base that
    auto-overrides a component the direct base does not is not consulted
    (the flags `autoVisit` collects beyond the direct base are used only for
    fragmenting components). -/
theorem autoVisit_direct_first (st : St) (b fuel : Nat) :
    autoVisit st (fuel + 1) b =
      ((st.ents.getD b default).auto.map (fun c => (c, b))) ++
        (st.ents.getD b default).isa.flatMap (fun bb => autoVisit st fuel bb) := by
  rfl

open Flecs.Spawn in
/-- F39: a Parent hierarchy; Velocity (C1) is set on the prefab child after
    the first instance.  The second instance's child has Position only; with
    a ChildOf hierarchy it has both. -/
theorem spawner_stale_type :
    instances { comps := #[{}, {}], hier := .parent, children := #[[(0, 1)]],
                ops := [.inst, .set 0 1 3, .inst] } = [#[[(0, 1)]], #[[(0, 1)]]] ∧
    instances { comps := #[{}, {}], hier := .childOf, children := #[[(0, 1)]],
                ops := [.inst, .set 0 1 3, .inst] } = [#[[(0, 1)]], #[[(0, 1), (1, 3)]]] := by
  decide +kernel

open Flecs.Pipe in
/-- F37: S0 in phase 0, S1 in phase 1 (immediate).  After S0 ran and its
    command moved phase 0 after phase 1, the rebuild orders S1 before S0 and
    resumes after S0, the last system that ran: the next step ends the
    frame, so S1 does not run. -/
theorem reorder_resume_past_end :
    let p : Prog := { sys := #[{ terms := [], phase := 0, effect := .reorder 0 },
                               { terms := [], phase := 1, immediate := true }] }
    let st0 : RunSt := { sys := p.sys, lastFrame := #[0, 0] }
    (match update st0 true with
     | .ok st1 =>
       -- S0's op ran, then its commands were merged
       let st2 := applyEffects { st1 with lastFrame := #[1, 0], curI := 0 } [0]
       match update st2 false with
       | .ok st3 => (st1.sched.systems, st3.sched.systems, st3.curOp)
       | .error _ => (#[], #[], some 99)
     | .error _ => (#[], #[], some 99)) = (#[0, 1], #[1, 0], none) := by
  decide +kernel

open Flecs.W in
/-- F36, for every group and world: appending to a full group's table array
    gives the group a new array and frees the old one (the realloc of
    `ecs_vec_append`), so a pointer into the old array dangles. -/
theorem pushMatch_full_reallocates (g : QGroup) (mt : QMatch) (w : World)
    (h : g.tables.size = g.cap) (h0 : g.arr ≠ 0) :
    let g' : QGroup := { g with tables := g.tables.push mt, cap := max 2 (nextPow2 (g.tables.size + 1)), arr := w.vecNext }
    let w' : World := { w with vecFreed := w.vecFreed.push g.arr, vecNext := w.vecNext + 1 }
    (pushMatch g mt).run w = Except.ok (g', w') := by
  have h1 : (g.arr == 0) = false := by simp [h0]
  simp only [pushMatch, h, beq_self_eq_true, ↓reduceIte, freeVec, newVec, h1, Bool.false_eq_true]
  rfl

end Flecs.R5
