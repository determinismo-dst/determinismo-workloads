/-
  API programs and their runner, with the oracles the search checks.

  A program is a scenario (hooks, observers, relationship traits, stage
  count) plus a list of API calls on the world or on a stage.  Entities are
  referred to by slot: slot i is the i-th entity the program created.
-/
import FlecsLean.Ops

namespace Flecs
open Std

/-- Relationship entities created by every scenario (user entities, so their
    ids are above the builtins and ordered by creation). -/
structure Rels where
  tag : UInt64      -- a tag
  rRemove : UInt64  -- (OnDeleteTarget, Remove): the default
  rDelete : UInt64  -- (OnDeleteTarget, Delete)
  rPanic : UInt64   -- (OnDeleteTarget, Panic)
  deriving Repr, Inhabited

inductive RelK | childOf | remove | delete | panic | c0
  deriving Repr, BEq, Inhabited, DecidableEq

inductive IdS | c0 | c1 | tag | pair (r : RelK) (t : Nat)
  deriving Repr, BEq, Inhabited, DecidableEq

inductive Op where
  | new
  | delete (tg : Tgt) (e : Nat)
  | add (tg : Tgt) (e : Nat) (x : IdS)
  | remove (tg : Tgt) (e : Nat) (x : IdS)
  | set (tg : Tgt) (e : Nat) (x : IdS) (v : Nat)
  | ensure (tg : Tgt) (e : Nat) (x : IdS) (v : Nat)
  | modified (tg : Tgt) (e : Nat) (x : IdS)
  | clear (tg : Tgt) (e : Nat)
  | deleteWith (tg : Tgt) (x : IdS)
  | removeAll (tg : Tgt) (x : IdS)
  | merge (k : Nat)
  | readonlyBegin
  | readonlyEnd
  /-- entity index: make_alive of a slot's handle (or of its id with
      generation `gen`) -/
  | makeAlive (e : Nat) (gen : Nat)
  | rangeNew (min max : Nat)
  | rangeSet (h : Nat)
  | newFromRange (h : Nat)
  deriving Repr, BEq, Inhabited

/-- Hook and observer bodies offered to the search. -/
structure Scenario where
  stages : Nat := 1
  /-- index into `menu` -/
  cfg : Nat := 0
  /-- relationship creation order: true creates rPanic before rRemove -/
  panicFirst : Bool := true
  hooks : List (Id × Hooks) := []
  obs : List Obs := []
  ops : List Op := []
  deriving Repr, Inhabited

/-! ### Scenario menu: hooks and observers that call back into the world -/

/-- Hook/observer configurations.  Bodies use only the calls the docs allow
    from inside: structural changes on the event's (locked) table go through
    the stage; `it->world` is used where flecs' own tests use it. -/
def menu (tag : UInt64) (k : Nat) : List (Id × Hooks) × List Obs :=
  match k with
  | 0 => ([], [])
  -- on_set hook moves the entity through it->world
  -- (ComponentLifecycle_locked_storage_on_set), plus an OnSet observer
  | 1 => ([(C0, { onSet := some [.whenVal 99 (.add .world .self (.id tag))] })],
          [{ event := .onSet, pattern := C0 }])
  -- OnRemove observer deletes its entity through it->stage
  | 2 => ([], [{ event := .onRemove, pattern := C1, acts := [.delete .stage .self] }])
  -- OnAdd observer deletes its entity through it->stage
  | 3 => ([], [{ event := .onAdd, pattern := C1, acts := [.delete .stage .self] }])
  -- on_add hook (its view of the entity is checked)
  | 4 => ([(C0, { onAdd := some [] })], [{ event := .onSet, pattern := C0 }])
  -- observers on ChildOf pairs
  | 5 => ([], [{ event := .onAdd, pattern := mkPair EcsChildOf EcsWildcard },
               { event := .onRemove, pattern := mkPair EcsChildOf EcsWildcard }])
  -- OnRemove observer on C1 sets C0 on another entity through the world
  | 6 => ([], [{ event := .onRemove, pattern := C1, acts := [.set .world (.slot 0) (.id C0) 7] },
               { event := .onSet, pattern := C0 }])
  -- on_remove hook enqueues a set on its entity
  | 7 => ([(C1, { onRemove := some [.set .stage .self (.id C0) 5] })],
          [{ event := .onSet, pattern := C0 }])
  -- observers on everything (OnAdd/OnRemove/OnSet), recording only
  | _ => ([], [{ event := .onAdd, pattern := C0 }, { event := .onRemove, pattern := C0 },
               { event := .onSet, pattern := C0 }, { event := .onAdd, pattern := C1 },
               { event := .onRemove, pattern := C1 }, { event := .onSet, pattern := C1 }])

def menuSize : Nat := 9

structure Outcome where
  fail : Option Fail
  /-- oracle violations found while running -/
  violations : Array String
  /-- final state: (slot, alive, type, values) -/
  state : Array (Nat × Bool × List Id × List (Id × Nat))
  log : Array LogEv
  stale : Array String
  deriving Inhabited

namespace W

/-- `world init` for a scenario: components C0/C1 exist, then the relationship
    entities are created with ecs_new and given their traits. -/
def initWorld (s : Scenario) (noBatch : Bool) : Except Fail (World × Rels) := do
  let w : World := {}
  let act : M Rels := do
    -- builtin entities alive in a table of their own (they are never touched)
    let mut ix ← getIx
    for b in [EcsPrefab, EcsWildcard, EcsAny, EcsExclusive, EcsChildOf, EcsIsA, EcsOnDelete,
              EcsOnDeleteTarget, EcsRemove, EcsDelete, EcsPanic, C0, C1] do
      ix ← liftE (ix.ensure b)
    setIx { ix with maxId := EcsFirstUserEntityId }
    for b in [EcsPrefab, EcsWildcard, EcsAny, EcsExclusive, EcsChildOf, EcsIsA, EcsOnDelete,
              EcsOnDeleteTarget, EcsRemove, EcsDelete, EcsPanic, C0, C1] do
      let row ← appendRaw 0 b
      modRec b (fun r => { r with table := some 0, row := row })
    discard <| crEnsure C0
    discard <| crEnsure C1
    discard <| crEnsure (mkPair EcsChildOf EcsWildcard)
    let tag ← apiNew .world
    discard <| crEnsure tag
    let rRemove ← if s.panicFirst then pure 0 else apiNew .world
    let rPanic ← apiNew .world
    let rRemove ← if s.panicFirst then apiNew .world else pure rRemove
    let rDelete ← apiNew .world
    modify fun w => { w with
      odt := (w.odt.insert rDelete .delete).insert rPanic .panic,
      stages := Array.replicate s.stages {},
      hooks := HashMap.ofList (s.hooks ++ (menu tag s.cfg).1),
      obs := (s.obs ++ (menu tag s.cfg).2).toArray }
    -- the traits create (R, *) records (they are set through the OnDeleteTarget pair)
    for r in [rRemove, rDelete, rPanic] do
      discard <| crEnsure (mkPair r EcsWildcard)
    -- non_trivial_set (type_info.c 646-649, observer.c 133-141)
    for (c, h) in s.hooks ++ (menu tag s.cfg).1 do
      if h.onSet.isSome then modify fun w => { w with nonTrivialSet := w.nonTrivialSet.insert c }
    for o in s.obs ++ (menu tag s.cfg).2 do
      if o.event == .onSet && o.pattern < HI then
        modify fun w => { w with nonTrivialSet := w.nonTrivialSet.insert o.pattern }
    let _ := noBatch
    return { tag, rRemove, rDelete, rPanic }
  match act.run w with
  | .ok (r, w) => return ({ w with log := #[] }, r)
  | .error e => throw e

def relOf (rs : Rels) : RelK → UInt64
  | .childOf => EcsChildOf
  | .remove => rs.rRemove
  | .delete => rs.rDelete
  | .panic => rs.rPanic
  | .c0 => C0

def idOfS (rs : Rels) (slots : Array UInt64) : IdS → Id
  | .c0 => C0
  | .c1 => C1
  | .tag => rs.tag
  | .pair r t => mkPair (relOf rs r) (slots.getD t 0)

/-- Every alive entity sits in exactly one live table at its recorded row,
    rows below `count` hold alive entities, and live tables are in the
    records of their ids (storage/entity_index.h, table.c 27-96). -/
def checkStorage : M (Array String) := do
  let w ← get
  let mut out := #[]
  for i in [1:w.ix.alive] do
    let e := w.ix.denseAt i
    let r := w.ix.recOf e
    match r.table with
    | none => out := out.push s!"alive entity {e} has no table"
    | some t =>
      match w.tables[t]? with
      | none => out := out.push s!"entity {e} in missing table {t}"
      | some x =>
        if !x.live then out := out.push s!"entity {e} in freed table {t}"
        else if r.row >= x.count || x.ents.getD r.row 0 != e then
          out := out.push s!"entity {e} record row {r.row} does not match table {t}"
  for t in [0:w.tables.size] do
    let x := w.tables.getD t default
    if !x.live then continue
    for row in [0:x.count] do
      let e := x.ents.getD row 0
      if !w.ix.isAlive e then out := out.push s!"table {t} row {row} holds dead entity {e}"
    for id in x.type do
      match w.crs[id]? with
      | none => out := out.push s!"table {t} id {id} has no component record"
      | some c => if !c.cache.contains t then out := out.push s!"table {t} missing from record of {id}"
      if isPair id && x.count > 0 then
        if !w.ix.isAlive (pairSecond id) && !(w.ix.isAlive (w.ix.getAlive (pairSecond id))) then
          out := out.push s!"table {t} ({x.count} entities) has pair {pairFirst id},{pairSecond id} with a dead target"
  return out

/-- Run one op.  `noBatch` makes `ecs_merge` execute each command on its own
    (the single-command path of `flecs_commands_flush`), the sequential
    semantics batching must preserve. -/
def runOp (rs : Rels) (op : Op) : M Unit := do
  let slots := (← get).slots
  let ent := fun (i : Nat) => slots.getD i 0
  let idS := idOfS rs slots
  match op with
  | .new =>
    let before ← getIx
    let e ← apiNew .world
    modify fun w => { w with slots := w.slots.push e }
    -- a new id is not an alive one, and falls in the active range
    -- (EntitiesComponents.md "Ranges": newly issued and recycled ids fall
    -- within the active range)
    if before.isAlive e then
      modify fun w => { w with viol := w.viol.push s!"ecs_new returned {e}, which was alive" }
    match before.activeRange with
    | some r =>
      if !EIndex.rangeContains r (lo32 e) then
        modify fun w => { w with viol := w.viol.push s!"ecs_new returned {lo32 e} outside the active range [{r.min}, {r.max}]" }
    | none => pure ()
  | .delete tg e => apiDelete tg (ent e)
  | .add tg e x => apiAdd tg (ent e) (idS x)
  | .remove tg e x => apiRemove tg (ent e) (idS x)
  | .set tg e x v => apiSet tg (ent e) (idS x) v
  | .ensure tg e x v => apiEnsureWrite tg (ent e) (idS x) v
  | .modified tg e x => apiModified tg (ent e) (idS x)
  | .clear tg e => apiClear tg (ent e)
  | .deleteWith tg x => apiOnDeleteAction tg (idS x) .delete
  | .removeAll tg x => apiOnDeleteAction tg (idS x) .remove
  | .merge k => merge k
  | .readonlyBegin => readonlyBegin false
  | .readonlyEnd => readonlyEnd
  | .makeAlive e gen =>
    let h := ent e
    let h := if gen == 0 then h else (lo32 h) ||| (gen.toUInt64 <<< 32)
    makeAlive h
    if !(← isAlive h) then
      modify fun w => { w with viol := w.viol.push s!"make_alive({h}) returned but the id is not alive" }
  | .rangeNew mn mx =>
    let (ix, h) ← liftE ((← getIx).rangeNew mn.toUInt64 mx.toUInt64)
    setIx ix
    modify fun w => { w with rangeHandles := w.rangeHandles.push h }
  | .rangeSet h =>
    let some rh := (← get).rangeHandles[h]? | pure ()
    setIx (← liftE ((← getIx).setRange rh))
  | .newFromRange h =>
    let some rh := (← get).rangeHandles[h]? | pure ()
    let e ← newFromRange rh
    modify fun w => { w with slots := w.slots.push e }

/-- Whether the docs allow this call in the current state.  The search only
    issues allowed calls; a disallowed one is skipped. -/
def allowed (rs : Rels) (op : Op) : M Bool := do
  let w ← get
  let slots := w.slots
  let alive := fun (i : Nat) => i < slots.size && w.ix.isAlive (slots.getD i 0)
  let tgOk := fun (tg : Tgt) => match tg with
    | .world => !w.readonly
    | .stage k => k < w.stages.size
  let idOk := fun (x : IdS) => match x with
    | .pair _ t => alive t
    | _ => true
  -- no entity is made its own parent (flecs keeps ChildOf depths,
  -- component_index.c 1166-1176, which the replica does not model)
  let notSelfParent := fun (e : Nat) (x : IdS) => match x with
    | .pair .childOf t => t != e
    | _ => true
  match op with
  | .new => return !w.mt
  | .delete tg e | .clear tg e => return tgOk tg && alive e
  | .add tg e x | .remove tg e x =>
    return tgOk tg && alive e && idOk x && notSelfParent e x
  | .modified tg e x =>
    -- on the world, modified() requires the component (entity.c 1912-1915)
    let hasIt := match tg with
      | .world => (match (W.has (slots.getD e 0) (idOfS rs slots x)).run w with
          | .ok (b, _) => b
          | .error _ => false)
      | .stage _ => true
    return tgOk tg && alive e && idOk x && hasIt
  | .set tg e x _ | .ensure tg e x _ =>
    return tgOk tg && alive e && idOk x && (match x with | .tag => false | .pair r _ => r == .c0 | _ => true)
  | .deleteWith tg x | .removeAll tg x => return tgOk tg && idOk x
  | .merge k => return !w.readonly && k < w.stages.size
  | .readonlyBegin => return !w.readonly
  | .readonlyEnd => return w.readonly
  | .makeAlive e _ => return !w.readonly && e < slots.size
  | .rangeNew _ _ | .rangeSet _ | .newFromRange _ => return !w.readonly

end W

def summarize (w : World) : Array (Nat × Bool × List Id × List (Id × Nat)) := _root_.Id.run do
  let mut out := #[]
  for i in [0:w.slots.size] do
    let e := w.slots.getD i 0
    if !w.ix.isAlive e then
      out := out.push (i, false, [], [])
    else
      let r := w.ix.recOf e
      let x := w.tables.getD (r.table.getD 0) default
      let vals := x.colIds.toList.zipIdx.map (fun (c, k) => (c, (x.cols.getD k #[]).getD r.row 0))
      out := out.push (i, true, x.type.toList, vals)
  return out

namespace W

/-- The target slot of an op's id, if it is a pair. -/
def opPairTarget : IdS → Option (RelK × Nat)
  | .pair r t => some (r, t)
  | _ => none

def opEntity : Op → Option Nat
  | .delete _ e | .add _ e _ | .remove _ e _ | .set _ e _ _ | .ensure _ e _ _
  | .modified _ e _ | .clear _ e => some e
  | _ => none

def toWorld : Op → Op
  | .delete _ e => .delete .world e
  | .add _ e x => .add .world e x
  | .remove _ e x => .remove .world e x
  | .set _ e x v => .set .world e x v
  | .ensure _ e x v => .ensure .world e x v
  | .modified _ e x => .modified .world e x
  | .clear _ e => .clear .world e
  | .deleteWith _ x => .deleteWith .world x
  | .removeAll _ x => .removeAll .world x
  | op => op

def opTgt : Op → Option Tgt
  | .delete tg _ | .add tg _ _ | .remove tg _ _ | .set tg _ _ _ | .ensure tg _ _ _
  | .modified tg _ _ | .clear tg _ | .deleteWith tg _ | .removeAll tg _ => some tg
  | _ => none

def opId : Op → Option IdS
  | .add _ _ x | .remove _ _ x | .set _ _ x _ | .ensure _ _ x _ | .modified _ _ x
  | .deleteWith _ x | .removeAll _ x => some x
  | _ => none

/-- Replay one queued call as the docs describe the merge (Manual.md
    "Deferred operations"): calls on an entity deleted before they run are
    discarded; a call that adds a pair whose target was deleted follows the
    relationship's OnDeleteTarget policy (ChildOf: the child is deleted). -/
def replayOne (rs : Rels) (op : Op) : M Unit := do
  let slots := (← get).slots
  let alive := fun (i : Nat) => do return (← isAlive (slots.getD i 0))
  if let some e := opEntity op then
    if !(← alive e) then return
  -- a queued modified() of a component the entity does not have is ignored
  -- (entity.c 1906-1910: the check is skipped while deferred)
  if let .modified _ e x := op then
    if !(← has (slots.getD e 0) (idOfS rs slots x)) then return
  if let some x := opId op then
    if let some (r, t) := opPairTarget x then
      if !(← alive t) then
        match op with
        | .add .. | .set .. | .ensure .. =>
          match (← policyOf (relOf rs r)) with
          | .delete => if let some e := opEntity op then apiDelete .world (slots.getD e 0)
          | .panic => fail .constraintViolated "reference" "pair target deleted (Panic)"
          | .remove => pure ()
          return
        | _ => return
  runOp rs (toWorld op)

end W

/-- Run a scenario.  Stops at the first failure.  With `reference`, calls on
    a stage are not enqueued in the replica's command queue: they are kept
    aside and replayed as world calls when the stage is merged, in order,
    with the documented discard rules (the reference semantics). -/
def runScenario (s : Scenario) (noBatch : Bool := false) (checkEach : Bool := true)
    (reference : Bool := false) : Outcome := _root_.Id.run do
  match W.initWorld s noBatch with
  | .error f => return { fail := some f, violations := #[s!"init failed: {f}"], state := #[], log := #[], stale := #[] }
  | .ok (w0, rs) =>
    let mut w := { w0 with noBatch := noBatch }
    let mut viol : Array String := #[]
    let mut bufs : Array (Array Op) := Array.replicate s.stages #[]
    for op in s.ops do
      let ok := match (W.allowed rs op).run w with
        | .ok (b, _) => b
        | .error _ => false
      if !ok then continue
      let mut steps : Array (Bool × Op) := #[(false, op)]
      if reference then
        match W.opTgt op with
        | some (.stage k) =>
          bufs := bufs.modify k (·.push op)
          steps := #[]
        | _ =>
          match op with
          | .merge k =>
            steps := (bufs.getD k #[]).map (fun o => (true, o)) |>.push (false, op)
            bufs := bufs.set! k #[]
          | .readonlyEnd =>
            steps := #[(false, op)]
            for k in [0:s.stages] do
              steps := steps ++ (bufs.getD k #[]).map (fun o => (true, o))
            bufs := Array.replicate s.stages #[]
          | _ => pure ()
      for (isReplay, o) in steps do
        let act := if isReplay then W.replayOne rs o else W.runOp rs o
        match act.run w with
        | .error f =>
          return { fail := some f, violations := viol ++ w.viol, state := summarize w, log := w.log, stale := w.staleReads }
        | .ok ((), w2) => w := w2
      if checkEach && !w.readonly then
        match W.checkStorage.run w with
        | .ok (vs, _) => viol := viol ++ vs.map (fun v => s!"after {repr op}: {v}")
        | .error f => viol := viol.push s!"storage check failed: {f}"
    return { fail := none, violations := viol ++ w.viol, state := summarize w, log := w.log, stale := w.staleReads }

end Flecs
