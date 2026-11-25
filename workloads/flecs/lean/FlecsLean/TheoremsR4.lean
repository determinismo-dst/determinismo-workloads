/-
  Round 4 theorems.  No `sorry`; the axioms used are printed by Axioms.lean.
-/
import FlecsLean.Validator
import FlecsLean.InhDF
import FlecsLean.PipeQ

namespace Flecs.R4

def isCrash : Flecs.Val.Outcome → Bool
  | .crash _ => true
  | _ => false

def isCreated : Flecs.Val.Outcome → Bool
  | .created .. => true
  | _ => false

open Flecs.Val in
/-- F29: `TagA || Position` with Position Sparse crashes when it is created
    with a cache (Auto), and as a system's query (default kind, entity). -/
theorem or_sparse_cache_crash :
    isCrash (createQuery #[.table, .sparse] #[{ comp := 0, oper := .or }, { comp := 1 }] .auto false false) = true ∧
    isCrash (createQuery #[.table, .sparse] #[{ comp := 0, oper := .or }, { comp := 1 }] .default_ true false) = true := by
  decide +kernel

open Flecs.Val in
/-- F29's control: the same terms without a cache are accepted, and with
    Position a plain table component the cached query is created. -/
theorem or_sparse_uncached_ok :
    isCreated (createQuery #[.table, .sparse] #[{ comp := 0, oper := .or }, { comp := 1 }] .none false false) = true ∧
    isCreated (createQuery #[.table, .table] #[{ comp := 0, oper := .or }, { comp := 1 }] .auto false false) = true := by
  decide +kernel

open Flecs.Val in
/-- F29, the field count: with a term after the chain, the cache's query
    merges the chain's head with that term into one Or chain (one field). -/
theorem or_sparse_merges_chain :
    (match createQuery #[.table, .sparse, .table]
        #[{ comp := 0, oper := .or }, { comp := 1 }, { comp := 2 }] .auto false false with
      | .created _ cts n _ => (cts.map (·.comp), n)
      | _ => (#[], 99)) = (#[0, 2], 1) := by
  decide +kernel

open Flecs.IDF in
/-- F32, for every world: for a DontFragment component that is not
    DontInherit, the search an override uses looks only at the direct IsA
    targets' own components (search.c 216-221), never at their bases. -/
theorem searchUp_dontFragment_one_level (st : St) (c e fuel : Nat)
    (h : (st.comps.getD c default).storage = .dontFragment)
    (h2 : (st.comps.getD c default).trait ≠ .dontInherit) :
    searchUpF st c (fuel + 1) e =
      (st.ents.getD e default).isa.findSome? (fun b => if (owns st b c).isSome then some b else none) := by
  have h2' : ((st.comps.getD c default).trait == Trait.dontInherit) = false := by
    cases ht : (st.comps.getD c default).trait <;> simp_all <;> rfl
  simp only [searchUpF, h2', h]
  rfl

open Flecs.IDF in
/-- F32, the C test's world: base 0 owns C0 = 5, 1 IsA 0, 2 IsA 1.  `ecs_get`
    finds 5 for entity 2; the override's search finds no base. -/
theorem two_levels_get_vs_search :
    let st : St := { comps := #[{ storage := .dontFragment, trait := .inherit }],
                     ents := #[{ own := [(0, 5)] }, { isa := [0] }, { isa := [1] }] }
    baseComponent st 2 0 = some 5 ∧ searchUp st 2 0 = none := by
  decide +kernel

open Flecs.IDF in
/-- F32's control: the same chain with a fragmenting Sparse component finds
    base 0. -/
theorem two_levels_sparse_found :
    let st : St := { comps := #[{ storage := .sparse, trait := .inherit }],
                     ents := #[{ own := [(0, 5)] }, { isa := [0] }, { isa := [1] }] }
    searchUp st 2 0 = some 0 := by
  decide +kernel

open Flecs.PipeQ in
/-- F31, for every state: when the cache's match count equals the count the
    pipeline recorded, `flecs_pipeline_update` keeps the schedule. -/
theorem update_keeps_schedule (st : St) (h : st.pqCount = some st.matchCount) :
    update st = st := by
  simp [update, h]

open Flecs.PipeQ in
/-- F31, the C test's builtin case: disabling the module of a system in a
    Parent hierarchy leaves the cache's match count as it was, so the next
    frame runs the old schedule. -/
theorem parent_disable_keeps_count :
    let st0 : St := syncCache { kind := .builtin, sys := #[{ parent := .parentComp }] } [] false
    let st1 := update st0
    (step st1 .disableModule).1.matchCount = st1.matchCount ∧
    (step st1 .disableModule).1.pqCount = some st1.matchCount := by
  decide +kernel

open Flecs.PipeQ in
/-- ...while for a ChildOf child the rematch bumps it (the control). -/
theorem childof_disable_bumps_count :
    let st0 : St := syncCache { kind := .builtin, sys := #[{ parent := .childOf }] } [] false
    let st1 := update st0
    (step st1 .disableModule).1.matchCount ≠ st1.matchCount := by
  decide +kernel

end Flecs.R4
