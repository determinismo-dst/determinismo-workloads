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

/-- Round 2: hierarchies with C0 on parents, monitors and up observers
    (menu 9-11).  ChildOf pairs point at a lower slot (a forest). -/
def genObsOp (ents stages : Nat) : m Op := do
  let e ← Pick.pick "flecs.entity" ents
  let tg ← genTgt stages
  match (← Pick.pick "flecs.call" 7) with
  | 0 => return .delete tg e
  | 1 | 2 =>
    if (← Pick.pick "flecs.obs.what" 2) == 0 || e == 0 then return .add tg e .c0
    else return .add tg e (.pair .childOf (← Pick.pick "flecs.pair.target" e))
  | 3 =>
    if (← Pick.pick "flecs.obs.what" 2) == 0 || e == 0 then return .remove tg e .c0
    else return .remove tg e (.pair .childOf (← Pick.pick "flecs.pair.target" e))
  | 4 => return .set tg e .c0 (← genVal)
  | 5 => return .add tg e .tag
  | _ => return .merge (← Pick.pick "flecs.merge.stage" stages)

def genObsScenario (ents len : Nat) : m Scenario := do
  let stages := (← Pick.pick "flecs.stages" 2) + 1
  let cfg := 9 + (← Pick.pick "flecs.hooks" 3)
  let mut ops : Array Op := Array.replicate ents .new
  for _ in [0:len] do
    ops := ops.push (← genObsOp ents stages)
  for k in [0:stages] do ops := ops.push (.merge k)
  return { stages, ops := ops.toList, cfg }

/-- Round 2: prefabs with children, instances (IsA), deletes and new
    entities in between. -/
def genIsAOp (ents stages : Nat) : m Op := do
  let e ← Pick.pick "flecs.entity" ents
  let tg ← genTgt stages
  match (← Pick.pick "flecs.call" 8) with
  | 0 => return .delete tg e
  | 1 => return .add tg e .prefab
  | 2 => if e == 0 then return .add tg e .c0
         else return .add tg e (.pair .childOf (← Pick.pick "flecs.pair.target" e))
  | 3 => if e == 0 then return .add tg e .prefab
         else return .add tg e (.pair .isA (← Pick.pick "flecs.pair.target" e))
  | 4 => return .set tg e .c0 (← genVal)
  | 5 => return .new
  | 6 => return .remove tg e .prefab
  | _ => return .merge (← Pick.pick "flecs.merge.stage" stages)

def genIsAScenario (ents len : Nat) : m Scenario := do
  let stages := (← Pick.pick "flecs.stages" 2) + 1
  let mut ops : Array Op := Array.replicate ents .new
  for _ in [0:len] do
    ops := ops.push (← genIsAOp ents stages)
  for k in [0:stages] do ops := ops.push (.merge k)
  return { stages, ops := ops.toList, cfg := 0 }

/-- Round 3: prefab inheritance.  Prefabs, IsA (to lower slots: no
    cycles), prefab variants, children of prefabs, set/add/remove/ensure of
    C0 and C1 on prefabs and instances (overrides), auto-overrides, deletes,
    new entities, staged calls and merges. -/
def genInhOp (ents stages : Nat) : m Op := do
  let e ← Pick.pick "flecs.entity" ents
  let tg ← if stages == 0 then pure Tgt.world else genTgt stages
  let comp : m IdS := pickOf "flecs.id.component" #[IdS.c0, .c1]
  match (← Pick.pick "flecs.call" 13) with
  | 0 => return .add tg e .prefab
  | 1 | 2 => if e == 0 then return .add tg e .prefab
             else return .add tg e (.pair .isA (← Pick.pick "flecs.pair.target" e))
  | 3 => if e == 0 then return .remove tg e .c1
         else return .remove tg e (.pair .isA (← Pick.pick "flecs.pair.target" e))
  | 4 | 5 => return .set tg e (← comp) (← genVal)
  | 6 => return .remove tg e (← comp)
  | 7 => return .add tg e (← comp)
  | 8 => return .add tg e (← pickOf "flecs.id.auto" #[IdS.auto0, .auto1])
  | 9 => return .ensure tg e (← comp) (← genVal)
  | 10 => if e == 0 then return .delete tg e
          else return .add tg e (.pair .childOf (← Pick.pick "flecs.pair.target" e))
  | 11 => if (← Pick.pick "flecs.new" 2) == 0 then return .delete tg e else return .new
  | _ => if stages == 0 then return .add tg e .tag
         else return .merge (← Pick.pick "flecs.merge.stage" stages)

/-- `staged`: calls on stages too (else world calls only). -/
def genInhScenario (ents len : Nat) (staged : Bool := true) : m Scenario := do
  let stages ← if staged then do pure ((← Pick.pick "flecs.stages" 2) + 1) else pure 1
  let cfg := if (← Pick.pick "flecs.hooks" 2) == 0 then 0 else 12
  let c1 ← pickOf "inh.c1" #[InstK.inherit, .copy]
  let c0 ← pickOf "inh.c0" #[InstK.copy, .dontInherit, .inherit]
  let mut ops : Array Op := Array.replicate ents .new
  for _ in [0:len] do
    ops := ops.push (← genInhOp ents (if staged then stages else 0))
  for k in [0:stages] do ops := ops.push (.merge k)
  return { stages, ops := ops.toList, cfg, traits := [(C0, c0), (C1, c1)] }

/-- Round 3, small exhaustive menu: entity 0 is the base, entities 1 and
    2 may become its instances; world calls only. -/
def genInhSmallOp : m Op := do
  match (← Pick.pick "inh.call" 9) with
  | 0 => return .set .world 0 .c1 (← pickOf "flecs.value" #[50, 99])
  | 1 => return .remove .world 0 .c1
  | 2 => return .add .world 0 .tag
  | k =>
    let e := if k % 2 == 1 then 1 else 2
    match (k - 3) / 2 with
    | 0 => return .add .world e (.pair .isA 0)
    | 1 => return .add .world e .c1
    | _ => return .remove .world e .c1

def genInhSmall (len : Nat) : m Scenario := do
  let c1 ← pickOf "inh.c1" #[InstK.inherit, .copy]
  let cfg := if (← Pick.pick "flecs.hooks" 2) == 0 then 0 else 12
  let mut ops : Array Op := #[.new, .new, .new]
  for _ in [0:len] do ops := ops.push (← genInhSmallOp)
  return { cfg, ops := ops.toList, traits := [(C1, c1)] }

/-- Round 3: instantiation with entity ranges (F21's area meets F8's): a
    prefab (slot 0) with a child (slot 1), then entities, ranges, instances
    and deletes. -/
def genRangeInstOp (ents : Nat) : m Op := do
  match (← Pick.pick "ri.call" 6) with
  | 0 => return .new
  | 1 => return .rangeNew (← pickOf "flecs.range.min" #[5000, 6000]) (← pickOf "flecs.range.max" #[0, 5003, 6003])
  | 2 => return .rangeSet (← Pick.pick "flecs.range" 2)
  | 3 => return .add .world ((← Pick.pick "flecs.entity" ents) + 2) (.pair .isA 0)
  | 4 => return .delete .world ((← Pick.pick "flecs.entity" ents) + 2)
  | _ => return .newFromRange (← Pick.pick "flecs.range" 2)

def genRangeInst (ents len : Nat) : m Scenario := do
  let mut ops : Array Op := #[.new, .new, .add .world 0 .prefab, .add .world 1 (.pair .childOf 0)]
  for _ in [0:len] do ops := ops.push (← genRangeInstOp ents)
  return { ops := ops.toList }

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
    "addons/entity_ranges.c 254-255", "storage/entity_index.c 280-281",
    -- an instance that is a child of its own prefab (instantiate.c 253-260)
    "addons/prefab/instantiate.c 253-260" ].contains f.site

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
  let isP7 := fun (v : String) => ((v.splitOn "P7 monitor").length > 1)
  let isI := fun (v : String) => v.startsWith "P-I2" || v.startsWith "P-I3" || v.startsWith "P-RC"
  let strong := a.violations.filter (fun v => !v.startsWith "view:" && !isP7 v && !v.startsWith "P8" && !isI v)
  if !strong.isEmpty then
    out := out ++ [{ ok := false, property := "P2 oracle", detail := strong[0]! }]
  -- round 3: P-I2 override values, P-I3 OnSet for inheritance
  for (pfx, name) in [("P-I2", "P-I2 override value"), ("P-I3", "P-I3 OnSet for inheritance"),
                      ("P-RC", "P-RC reachable cache")] do
    let vs := a.violations.filter (·.startsWith pfx)
    if !vs.isEmpty then
      out := out ++ [{ ok := false, property := name, detail := vs[0]! }]
  let p7 := a.violations.filter isP7
  if !p7.isEmpty then
    out := out ++ [{ ok := false, property := "P7 monitor", detail := p7[0]! }]
  let p8 := a.violations.filter (fun v => v.startsWith "P8")
  if !p8.isEmpty then
    out := out ++ [{ ok := false, property := "P8 deleted handle", detail := p8[0]! }]
  let b := runScenario s true
  let af := a.fail.map (·.code)
  let bf := b.fail.map (·.code)
  -- a locked-storage error is a hook body's misuse (Manual.md "Deferred
  -- operations"); runs where it occurs on either side are not compared
  let misuse := af == some .lockedStorage || bf == some .lockedStorage ||
    -- round 3: whether the instance is its prefab's own child depends on
    -- batching (round 2, "Not counted"): not compared
    (a.fail.map (·.site == "addons/prefab/instantiate.c 253-260")).getD false ||
    (b.fail.map (·.site == "addons/prefab/instantiate.c 253-260")).getD false
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
  if af == some .lockedStorage || cf == some .lockedStorage ||
      (a.fail.map (·.site == "addons/prefab/instantiate.c 253-260")).getD false ||
      (c.fail.map (·.site == "addons/prefab/instantiate.c 253-260")).getD false then pure ()
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
