/-
  Program generators and the properties checked on each program.

  Generators are written against `pick n` (a choice in [0, n)), so the same
  generator is driven by seeded random choices (explore), by enumeration of
  every choice sequence within bounds (exhaust), or by a recorded tape.
-/
import FlecsLean.Program

namespace Flecs
open Std

/-! ### Generators -/

class Pick (m : Type → Type) where
  /-- a named decision among `n` options -/
  pick : String → Nat → m Nat

section
variable {m : Type → Type} [Monad m] [Pick m]

def pickOf {α} [Inhabited α] (name : String) (xs : Array α) : m α := do
  return xs.getD (← Pick.pick name xs.size) default

def genTgt (stages : Nat) : m Tgt := do
  let k ← Pick.pick "flecs.target" (stages + 1)
  return if k == 0 then .world else .stage (k - 1)

def genIdS (ents : Nat) : m IdS := do
  match (← Pick.pick "flecs.id" 7) with
  | 0 => return .c0
  | 1 => return .c1
  | 2 => return .tag
  | 3 => return .pair .childOf (← Pick.pick "flecs.pair.target" ents)
  | 4 => return .pair .remove (← Pick.pick "flecs.pair.target" ents)
  | 5 => return .pair .delete (← Pick.pick "flecs.pair.target" ents)
  | _ => return .pair .c0 (← Pick.pick "flecs.pair.target" ents)

def genVal : m Nat := pickOf "flecs.value" #[1, 2, 99]

/-- One API call on entities 0..ents-1. -/
def genOp (ents stages : Nat) : m Op := do
  let e ← Pick.pick "flecs.entity" ents
  match (← Pick.pick "flecs.call" 12) with
  | 0 => return .delete (← genTgt stages) e
  | 1 | 2 => return .add (← genTgt stages) e (← genIdS ents)
  | 3 => return .remove (← genTgt stages) e (← genIdS ents)
  | 4 | 5 => return .set (← genTgt stages) e (← pickOf "flecs.set.id" #[IdS.c0, .c1, .pair .c0 0, .pair .c0 1]) (← genVal)
  | 6 => return .ensure (← genTgt stages) e (← pickOf "flecs.id.component" #[IdS.c0, .c1]) (← genVal)
  | 7 => return .modified (← genTgt stages) e (← pickOf "flecs.id.component" #[IdS.c0, .c1])
  | 8 => return .clear (← genTgt stages) e
  | 9 => return .merge (← Pick.pick "flecs.merge.stage" stages)
  | 10 => return if (← Pick.pick "flecs.readonly" 2) == 0 then .readonlyBegin else .readonlyEnd
  | _ => return .add (← genTgt stages) e (.pair .panic (← Pick.pick "flecs.pair.target" ents))

/-- A scenario: `ents` entities, then `len` calls, then a final merge of
    every stage (readonly_end if needed). -/
def genScenario (ents len : Nat) : m Scenario := do
  let stages := (← Pick.pick "flecs.stages" 2) + 1
  let cfg ← Pick.pick "flecs.hooks" menuSize
  let panicFirst := (← Pick.pick "flecs.rel.order" 2) == 0
  let mut ops : Array Op := Array.replicate ents .new
  for _ in [0:len] do
    ops := ops.push (← genOp ents stages)
  ops := ops.push .readonlyEnd
  for k in [0:stages] do ops := ops.push (.merge k)
  return { stages, panicFirst, ops := ops.toList, hooks := [], obs := [],
           cfg := cfg }

/-- A smaller call menu for exhaustive enumeration: world or stage 0, the
    calls that batching and cleanup touch. -/
def genOpSmall (ents : Nat) : m Op := do
  let e ← Pick.pick "flecs.entity" ents
  let tg : Tgt := if (← Pick.pick "flecs.target" 2) == 0 then .world else .stage 0
  let x ← pickOf "flecs.id" #[IdS.c0, .c1, .tag, .pair .childOf 0, .pair .childOf 1, .pair .delete 0,
    .pair .delete 1, .pair .panic 0, .pair .panic 1, .pair .c0 0, .pair .c0 1]
  match (← Pick.pick "flecs.call" 6) with
  | 0 => return .delete tg e
  | 1 => return .add tg e x
  | 2 => return .remove tg e x
  | 3 => return .set tg e (if x == .c1 || x == .pair .c0 0 || x == .pair .c0 1 then x else .c0) (← pickOf "flecs.value" #[1, 99])
  | 4 => return .clear tg e
  | _ => return .merge 0

def genSmallScenario (cfg stages ents len : Nat) (panicFirst : Bool) : m Scenario := do
  let mut ops : Array Op := Array.replicate ents .new
  for _ in [0:len] do
    ops := ops.push (← genOpSmall ents)
  for k in [0:stages] do ops := ops.push (.merge k)
  return { stages, panicFirst, cfg, ops := ops.toList }

/-- Entity-index programs: entities, deletes, make_alive, ranges. -/
def genEIOp (maxEnts : Nat) : m Op := do
  match (← Pick.pick "flecs.ei.call" 7) with
  | 0 | 1 => return .new
  | 2 => return .delete .world (← Pick.pick "flecs.entity" maxEnts)
  | 3 => return .makeAlive (← Pick.pick "flecs.entity" maxEnts) (← Pick.pick "flecs.generation" 3)
  | 4 => return .rangeNew (← pickOf "flecs.range.min" #[5000, 7000, 9000]) (← pickOf "flecs.range.max" #[0, 6000, 8000, 10000])
  | 5 => return .rangeSet (← Pick.pick "flecs.range" 3)
  | _ => return .newFromRange (← Pick.pick "flecs.range" 3)

def genEIScenario (len : Nat) : m Scenario := do
  let mut ops : Array Op := #[]
  for _ in [0:len] do ops := ops.push (← genEIOp 4)
  return { ops := ops.toList }

end

/-! ### Properties -/

/-- Failures the docs allow: a Panic delete of a target that is in use, and
    locked-storage errors raised by world calls from inside hooks/observers
    (Manual.md "Deferred operations"). -/
def allowedFail (f : Fail) : Bool :=
  f.code == .lockedStorage ||
  (f.code == .constraintViolated && f.site == "on_delete.c 395-397") ||
  -- calls the docs (or the call's own argument checks) reject:
  -- make_alive of an id alive with another generation (EntitiesComponents.md
  -- "Manual Ids"), ranges created after deletes, overlapping or inverted
  -- (entity_ranges.c 145-184), and an exhausted range (EntitiesComponents.md
  -- "Ranges": operations that create entities assert)
  [ "entity.c 2774-2778", "addons/entity_ranges.c 145", "addons/entity_ranges.c 146-147",
    "addons/entity_ranges.c 151-153", "addons/entity_ranges.c 160-162",
    "addons/entity_ranges.c 160-162 (nested default range)", "addons/entity_ranges.c 180-184",
    "addons/entity_ranges.c 254-255", "storage/entity_index.c 280-281" ].contains f.site

structure Verdict where
  ok : Bool
  property : String
  detail : String
  deriving Repr, Inhabited

/-- The properties, each with its source:
    P1 no-crash: no assert, crash or use-after-free on calls the docs allow
       (Manual.md "Error handling": asserts are for invalid inputs).
    P1 no-stale-read: no read of table storage past its row count.
    P2 oracle: OnSet goes to the entity set (ObserversManual.md "OnSet Events");
       OnAdd/OnRemove only for ids the entity has ("OnAdd Events",
       "OnRemove Events"); Panic targets panic (ComponentTraits.md
       "OnDeleteTarget"); make_alive makes alive (EntitiesComponents.md
       "Manual Ids"); storage invariants (each alive entity in one table at its
       row, no pair with a dead target after cleanup: Relationships.md
       "Cleanup properties").
    P3 batching: the merge gives the same state and the same failure as
       running each command alone (ObserversManual.md "Event order is undefined
       between entities": batching may reorder events, not change results).
    P4 hook view: inside an on_add hook the entity has the component
       (EntitiesComponents.md component lifecycle diagram: table move, then
       on_add hook).
    P5 staged = replayed: merging a stage gives the state of replaying its
       calls on the world one at a time, in order, discarding calls on
       entities deleted before they run (Manual.md "Deferred operations"). -/
def checkAll (s : Scenario) : List Verdict := _root_.Id.run do
  let a := runScenario s false
  let mut out : List Verdict := []
  if let some f := a.fail then
    if !allowedFail f then
      out := out ++ [{ ok := false, property := "P1 no-crash", detail := toString f }]
  if !a.stale.isEmpty then
    out := out ++ [{ ok := false, property := "P1 no-stale-read", detail := a.stale[0]! }]
  let strong := a.violations.filter (fun v => !v.startsWith "view:")
  if !strong.isEmpty then
    out := out ++ [{ ok := false, property := "P2 oracle", detail := strong[0]! }]
  let b := runScenario s true
  let af := a.fail.map (·.code)
  let bf := b.fail.map (·.code)
  -- a locked-storage error is a hook body's misuse (Manual.md "Deferred
  -- operations"); runs where it occurs on either side are not compared
  let misuse := af == some .lockedStorage || bf == some .lockedStorage
  if misuse then pure ()
  else if af != bf then
    out := out ++ [{ ok := false, property := "P3 batching", detail := s!"batched fail {repr af} vs one-by-one {repr bf}" }]
  else if a.fail.isNone && a.state.toList != b.state.toList then
    out := out ++ [{ ok := false, property := "P3 batching", detail := s!"final state differs: batched {repr a.state.toList} vs one-by-one {repr b.state.toList}" }]
  -- P3b/P5b: per entity, the OnSet observer calls (entity, id, value) are the
  -- same, in order (ObserversManual.md "OnSet order is maintained")
  let onSets := fun (o : Outcome) (e : UInt64) =>
    (o.log.filter (fun l => !l.hook && l.ev == .onSet && l.entity == e)).toList.map (fun l => (l.id, l.val))
  let ents := (a.log.filter (fun l => !l.hook && l.ev == .onSet)).toList.map (·.entity) |>.eraseDups
  if a.fail.isNone && b.fail.isNone then
    for e in ents do
      if onSets a e != onSets b e then
        out := out ++ [{ ok := false, property := "P3b OnSet values under batching", detail := s!"entity {e}: batched OnSet {repr (onSets a e)} vs one-by-one {repr (onSets b e)}" }]
        break
  let view := a.violations.filter (fun v => v.startsWith "view:")
  if !view.isEmpty then
    out := out ++ [{ ok := false, property := "P4 hook view", detail := view[0]! }]
  -- P5: the merge gives the state of the documented one-call-at-a-time replay
  let c := runScenario s false true true
  let cf := c.fail.map (·.code)
  if af == some .lockedStorage || cf == some .lockedStorage then pure ()
  else if a.fail.isNone && c.fail.isNone && a.state.toList != c.state.toList then
    out := out ++ [{ ok := false, property := "P5 staged = replayed", detail := s!"final state differs: merge {repr a.state.toList} vs replay {repr c.state.toList}" }]
  else if a.fail.isNone && c.fail.isNone &&
      ents.any (fun e => onSets a e != onSets c e) then
    let e := (ents.find? (fun e => onSets a e != onSets c e)).getD 0
    out := out ++ [{ ok := false, property := "P5b OnSet values staged = replayed", detail := s!"entity {e}: merge OnSet {repr (onSets a e)} vs replay {repr (onSets c e)}" }]
  else if a.fail.isNone != c.fail.isNone then
    out := out ++ [{ ok := false, property := "P5 staged = replayed", detail := s!"merge fail {repr af} vs replay fail {repr cf}" }]
  return out

/-- First failing property among `props` (all when empty). -/
def check (s : Scenario) (props : List String := []) : Verdict :=
  let vs := checkAll s
  let vs := if props.isEmpty then vs else vs.filter (fun v => props.any (fun p => v.property.startsWith p))
  match vs with
  | v :: _ => v
  | [] => { ok := true, property := "", detail := "" }

end Flecs
