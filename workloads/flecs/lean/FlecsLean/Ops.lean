/-
  Operations: table moves, hooks, observers, the command queue, deletion and
  cleanup, and the public API, transcribed from flecs v4.2.0.  Each function
  names the C function and lines it follows.
-/
import FlecsLean.World

namespace Flecs
open Std

/-- `world` or a stage (`ecs_get_stage(world, k)`). -/
inductive Tgt | world | stage (k : Nat)
  deriving Repr, BEq, Inhabited, DecidableEq

/-- Where `ecs_ensure` on a stage returned its pointer. -/
inductive EnsurePtr | table (p : W.Ptr) | cmd (k lvl idx : Nat) | null
  deriving Repr, Inhabited

namespace W

/-! ### Round 3: inheritance (IsA) helpers -/

def hasIsA (x : Table) : Bool := x.type.any (fun i => isPair i && pairFirst i == EcsIsA)

/-- `EcsTableHasTraversable` (`table->_->traversable_count != 0`, table.c
    89-90, 1366-1377): some entity in the table is a target of a traversable
    pair. -/
def hasTraversable (t : Nat) : M Bool := do
  let w ← get
  let some x := w.tables[t]? | return false
  for i in [0:x.count] do
    if hasFlag (w.ix.recOf (x.ents.getD i 0)).flags FIsTraversable then return true
  return false

/-- `flecs_emit_propagate_invalidate_tables` (observable.c 489-551): bump
    the generation of each traversable record `(R, e)` whose cache is valid,
    then do the same below it.  A record whose cache is already invalid is
    skipped with its subtree ("Subtree is already marked invalid", 505-508). -/
partial def invalidateTables (e : UInt64) (depth : Nat := 0) : M Unit := do
  if depth > 64 then return
  if (← crGet (mkPair EcsWildcard (lo32 e))).isNone then return
  for rel in [EcsIsA, EcsChildOf] do
    let some c ← crGet (mkPair rel (lo32 e)) | continue
    if c.reachCur != c.reachGen then continue
    crSet { c with reachGen := c.reachGen + 1 }
    for t in c.cache do
      if !(← hasTraversable t) then continue
      let x := (← get).tables.getD t default
      for i in [0:x.count] do
        let y := x.ents.getD i 0
        let r := (← getIx).recOf y
        if (← isAlive y) && hasFlag r.flags FIsTraversable then
          invalidateTables y (depth + 1)

/-- `flecs_emit_propagate_invalidate` (observable.c 553-569) -/
def propagateInvalidate (t row count : Nat) : M Unit := do
  for i in [0:count] do
    let x ← tbl t
    let e := x.ents.getD (row + i) 0
    let r := (← getIx).recOf e
    if (← isAlive e) && hasFlag r.flags FIsTraversable then invalidateTables e

/-- `ecs_search_relation(world, table, 0, id, EcsIsA, EcsUp, &base, ...)`
    (search.c 203-350): depth first over the table's IsA pairs in type order,
    the target's own table first, then its IsA pairs; components with the
    DontInherit trait are never found (`flecs_type_can_inherit_id`,
    175-200).  Returns the entity that has `id`. -/
partial def searchIsA (t : Nat) (id : Id) (depth : Nat := 0) : M (Option UInt64) := do
  if depth > 32 then fail .invalidOperation "search.c" "cycle detected in IsA relationship"
  if (← instOf id) == .dontInherit then return none
  let x ← tbl t
  for p in x.type do
    if isPair p && pairFirst p == EcsIsA then
      let b := pairSecond p
      let r := (← getIx).recOf b
      match r.table with
      | none => continue
      | some bt =>
        let bx ← tbl bt
        if bx.type.contains id then return some (← getAlive b)
        if let some f ← searchIsA bt id (depth + 1) then return some f
  return none

/-- `flecs_table_update_overrides` (table.c 471-508) -/
def updateOverrides (t : Nat) : M Unit := do
  let x ← tbl t
  let some o := x.over | return
  let gen := fun (pid : Id) => do return ((← crGet pid).map (·.reachGen)).getD 0
  let mut stale := false
  for (pid, g) in o.bases do
    if g != (← gen pid) then stale := true
  if !stale then return
  let mut bases := #[]
  for (pid, _) in o.bases do bases := bases.push (pid, ← gen pid)
  let mut refs := #[]
  for c in x.colIds do refs := refs.push (← searchIsA t c)
  setTbl t { (← tbl t) with over := some { bases, refs } }

/-- the value of component `id` on entity `b`, if its table has the column -/
def ownVal (b : UInt64) (id : Id) : M (Option Nat) := do
  let r := (← getIx).recOf b
  match r.table with
  | none => return none
  | some bt =>
    let bx ← tbl bt
    match colIndex bx id with
    | some c => return (bx.cols.getD c #[])[r.row]?
    | none => return none

/-- `flecs_table_invoke_ctor` (table.c 963-993) for one row of column `ci`:
    with an override ref the value is copied from the base through
    `ecs_ref_get_id` (ref.c 90-162, which re-resolves the base's current
    table); otherwise the ctor runs (0 in the model).  The P-I2 oracle
    compares with a fresh search (PrefabsManual.md "Component Overriding":
    an override is "initialized with the value from the prefab component";
    ComponentTraits.md "DontInherit": "its value is not copied"). -/
def ctorVal (t ci : Nat) : M Nat := do
  let x ← tbl t
  let cid := x.colIds.getD ci 0
  let mut produced : Nat := 0
  let mut via : Option UInt64 := none
  if let some o := x.over then
    if let some b := o.refs.getD ci none then
      via := some b
      if !(← isAlive b) then
        fail .internalError "storage/table.c 979" s!"ecs_assert(base_ptr != NULL): the override ref of table {t} for {cid} points at {b}, which is not alive"
      match (← ownVal b cid) with
      | some v => produced := v
      | none =>
        fail .internalError "storage/table.c 979" s!"ecs_assert(base_ptr != NULL): the override ref of table {t} for {cid} points at {b}, which no longer has it"
  if (← get).checkOverrides && hasIsA x then
    let fresh ← searchIsA t cid
    let expect ← match fresh with
      | some b => do pure ((← ownVal b cid).getD 0)
      | none => pure 0
    if fresh != via || expect != produced then
      modify fun w => { w with viol := w.viol.push s!"P-I2 override value: table {t} constructs {cid} from {via} = {produced}, but the base the entity inherits from is {fresh} = {expect}" }
  return produced

/-! ### Small storage helpers -/

/-- Append `e` at row `count`; columns get a default-constructed value. -/
def appendRaw (t : Nat) (e : UInt64) : M Nat := do
  -- flecs_table_grow_data (table.c 1562): tables with IsA refresh the
  -- override cache before they grow
  if ((← tbl t).over).isSome then updateOverrides t
  let x ← tbl t
  let row := x.count
  let ents := if row < x.ents.size then x.ents.set! row e else x.ents.push e
  let cols := x.cols.map (fun c => if row < c.size then c.set! row 0 else c.push 0)
  setTbl t { x with ents, cols, count := row + 1 }
  -- flecs_table_grow_data (table.c 1558/1586)
  markTableDirty t 0
  bumpMember t
  return row

/-- `ecs_get_alive` (entity.c 2713-2745) -/
def ecsGetAlive (e : UInt64) : M UInt64 := do
  if e == 0 then return 0
  let ix ← getIx
  if ix.isAlive e then return e
  if lo32 e != e then return 0
  let c := ix.getAlive e
  if c == 0 || !ix.isAlive c then return 0
  return c

/-- `ecs_make_alive` (entity.c 2748-2804) -/
def makeAlive (e : UInt64) : M Unit := do
  if (← get).mt then fail .invalidOperation "entity.c 2763-2764" "make_alive in multithreaded mode"
  let cur ← ecsGetAlive (lo32 e)
  if cur == e then return
  if cur != 0 then
    fail .invalidOperation "entity.c 2774-2778" "make_alive: entity is alive with different generation"
  let ix := (← getIx).makeAlive e
  let ix ← liftE (ix.ensure e)
  setIx ix
  let r ← getRec e
  if r.table.isSome then fail .internalError "entity.c 2796" "make_alive: record already has a table"
  let row ← appendRaw 0 e
  modRec e (fun r => { r with table := some 0, row := row })

/-- `ecs_make_alive_id` (entity.c 2806-2839) -/
def makeAliveId (id : Id) : M Unit := do
  if isPair id then
    let r := pairFirst id
    let t := pairSecond id
    if (← getAlive r) == 0 then
      if (← getIx).exists_ r then
        fail .invalidParameter "entity.c 2821-2822" "first element of pair is not alive"
      makeAlive r
    if (← getAlive t) == 0 then
      if (← getIx).exists_ t then
        fail .invalidParameter "entity.c 2828-2829" "second element of pair is not alive"
      makeAlive t
  else
    if (← getAlive id) == 0 then makeAlive id

/-- `flecs_type_new_with` + exclusive replacement (table_graph.c 104-134, 792-867) -/
def typeWith (type : Array Id) (with_ : Id) : M (Option (Array Id)) := do
  if isPair with_ then
    let r := pairFirst with_
    if (← isExclusive r) then
      match type.findIdx? (fun i => isPair i && pairFirst i == r) with
      | some k => return some (type.set! k with_)
      | none => pure ()
  if type.contains with_ then return none
  let lt := type.filter (· < with_)
  let gt := type.filter (· > with_)
  return some (lt ++ #[with_] ++ gt)

/-- `flecs_type_new_without` (table_graph.c 136-194) -/
def typeWithout (type : Array Id) (without : Id) : Option (Array Id) :=
  match type.findIdx? (fun i => idMatch i without) with
  | none => none
  | some _ =>
    if isWildcard without then some (type.filter (fun i => !idMatch i without))
    else some (type.filter (· != without))

structure Diff where
  added : Array Id := #[]
  removed : Array Id := #[]
  deriving Repr, Inhabited

def diffOf (src dst : Array Id) : Diff :=
  { added := dst.filter (fun i => !src.contains i), removed := src.filter (fun i => !dst.contains i) }

/-- `flecs_type_add`: sorted insert, no duplicate -/
def typeAdd (ty : Array Id) (id : Id) : Array Id :=
  if ty.contains id then ty
  else ty.filter (· < id) ++ #[id] ++ ty.filter (· > id)

/-- `flecs_add_overrides_for_base` (table_graph.c 718-790): the base's
    auto-overridden ids and ids with the Copy trait join the new type, then
    the same for the base's own IsA targets. -/
partial def addOverridesForBase (ty : Array Id) (pair : Id) (depth : Nat := 0) : M (Array Id) := do
  if depth > 32 then fail .invalidOperation "table_graph.c" "cycle detected in IsA relationship"
  let b ← getAlive (pairSecond pair)
  if b == 0 then fail .invalidParameter "table_graph.c 723-724" "target of IsA pair is not alive"
  let r := (← getIx).recOf b
  let some bt := r.table | return ty
  let bx ← tbl bt
  let mut ty := ty
  for id in bx.type do
    let mut toAdd : Id := 0
    if (id &&& AUTO_OVERRIDE) != 0 then toAdd := id &&& ~~~AUTO_OVERRIDE
    else if (← instOf id) == .copy then toAdd := id
    if toAdd != 0 then
      let excl := isPair toAdd && (← isExclusive (pairFirst toAdd))
      if !excl || !ty.any (fun i => isPair i && pairFirst i == pairFirst toAdd) then
        ty := typeAdd ty toAdd
  for id in bx.type do
    if isPair id && pairFirst id == EcsIsA then ty ← addOverridesForBase ty id (depth + 1)
  return ty

/-- `flecs_table_traverse_add` (table_graph.c 1047-1070) through
    `flecs_table_traverse_dont_fragment` (923-977) and
    `flecs_find_table_with` (792-867).  Graph edges are not cached: the only
    behaviour that depends on an edge existing is `ecs_make_alive_id`, which
    for a pair whose target is dead runs on every path (an edge to a table
    with a dead target is removed when that table is freed, table.c 1306). -/
def traverseAdd (t : Nat) (id : Id) : M (Nat × Diff) := do
  if (← crGet id).isNone then
    makeAliveId id
    discard <| crEnsure id
  makeAliveId id
  if isPair id then discard <| crEnsure (mkPair (pairFirst id) EcsWildcard)
  else discard <| crEnsure id
  let x ← tbl t
  match (← typeWith x.type id) with
  | none => return (t, {})
  | some ty =>
    -- flecs_find_table_with (table_graph.c 833-844): a new IsA pair brings
    -- the base's overrides; a child of a prefab is a prefab
    let mut ty := ty
    if isPair id && pairFirst id == EcsIsA then ty ← addOverridesForBase ty id
    if isPair id && pairFirst id == EcsChildOf then
      let o ← getAlive (pairSecond id)
      if o != 0 then
        if let some ot := ((← getIx).recOf o).table then
          if (← tbl ot).type.contains EcsPrefab then ty := typeAdd ty EcsPrefab
    let d ← tableEnsure ty
    return (d, diffOf x.type ty)

/-- `flecs_table_traverse_remove` (table_graph.c 1023-1045) -/
def traverseRemove (t : Nat) (id : Id) : M (Nat × Diff) := do
  if (← crGet id).isNone then return (t, {})
  let x ← tbl t
  match typeWithout x.type id with
  | none => return (t, {})
  | some ty =>
    let d ← tableEnsure ty
    return (d, diffOf x.type ty)

/-- `flecs_get_component_ptr` (entity.c 48-96), non-sparse part. -/
def componentPtr (t : Nat) (row : Nat) (id : Id) : M (Option Ptr) := do
  if (← crGet id).isNone then return none
  let x ← tbl t
  match colIndex x id with
  | some c => return some { t, col := c, row }
  | none => return none

/-- the record memory of `e`, without the liveness asserts of
    `flecs_entities_get` (C code that already holds `ecs_record_t *r` reads it
    after calls that may have deleted the entity) -/
def rawRec (e : UInt64) : M Rec := return (← getIx).recOf e

/-- `flecs_get_mut` (entity.c 580-623), on a record the caller holds. -/
def getMutR (r : Rec) (id : Id) : M (Option Ptr) := do
  let some t := r.table | fail .internalError "entity.c 601" "flecs_get_mut: record has no table (entity deleted)"
  if id < HI then
    let x ← tbl t
    return (colIndex x id).map (fun c => { t, col := c, row := r.row })
  componentPtr t r.row id

/-- `flecs_get_mut` (entity.c 580-623) -/
def getMut (e : UInt64) (id : Id) : M (Option Ptr) := do
  let r ← getRec e
  let some t := r.table | fail .internalError "entity.c 601" "flecs_get_mut: record has no table"
  if id < HI then
    let x ← tbl t
    return (colIndex x id).map (fun c => { t, col := c, row := r.row })
  componentPtr t r.row id

/-! ### Command queue plumbing (stage.h 74-85, commands.c 113-133, 1577-1588) -/

def stageCur (k : Nat) : M Nat := return ((← get).stages.getD k default).cur
def getCmds (k lvl : Nat) : M Cmds := return (((← get).stages.getD k default).levels.getD lvl default)
def setCmds (k lvl : Nat) (c : Cmds) : M Unit := modify fun w =>
  { w with stages := w.stages.modify k (fun s => { s with levels := s.levels.set! lvl c }) }
def modCmds (k lvl : Nat) (f : Cmds → Cmds) : M Unit := do setCmds k lvl (f (← getCmds k lvl))

def commandsBegin (k : Nat) : M Unit := modify fun w =>
  { w with stages := w.stages.modify k (fun s =>
      let s := if s.levels.size <= s.cur + 1 then { s with levels := s.levels.push {} } else s
      { s with cur := s.cur + 1 }) }

def setStageCur (k lvl : Nat) : M Unit := modify fun w =>
  { w with stages := w.stages.modify k (fun s => { s with cur := lvl }) }

def getEntry (c : Cmds) : ERef → Option Entry
  | .inl0 => some c.entry
  | .inl1 => some c.secondEntry
  | .sp k => c.entries[k]?
def putEntry (c : Cmds) (r : ERef) (e : Entry) : Cmds :=
  match r with
  | .inl0 => { c with entry := e }
  | .inl1 => { c with secondEntry := e }
  | .sp k => { c with entries := c.entries.insert k e }

/-- `flecs_cmd_new_batched` (commands.c 38-111).  Appends `mk` and returns its
    index and entry. -/
def cmdNewBatched (k : Nat) (e : UInt64) (mk : Cmd) : M (Nat × ERef) := do
  let lvl ← stageCur k
  let mut c ← getCmds k lvl
  let cur := c.queue.size
  if cur == 0 then
    c := { c with entity := e, entry := { c.entry with first := -1 }, second := 0, lastEntity := 0 }
  let mut eref : Option ERef := none
  if e == c.lastEntity then eref := c.lastEntry
  else if e == c.entity then eref := some .inl0
  else if e == c.second then eref := some .inl1
  else if cur == 1 then
    c := { c with second := e, secondEntry := { c.secondEntry with first := -1 } }
    eref := some .inl1
  else
    eref := if c.entries.contains (lo32 e) then some (.sp (lo32 e)) else none
  let mut cmd := { mk with next := 0, entry := none }
  let mut isNew := false
  let mut ref : ERef := .sp (lo32 e)
  match eref with
  | some er =>
    ref := er
    let ent := (getEntry c er).getD {}
    if ent.first == -1 then
      c := putEntry c er { ent with first := cur, removed := 0 }
      cmd := { cmd with entry := some er }
    else
      let last := ent.last
      let lastOp := c.queue.getD last default
      if lastOp.entity == e then
        let nxt : Int := if (last : Int) == ent.first then -(cur : Int) else cur
        c := { c with queue := c.queue.set! last { lastOp with next := nxt } }
      else
        isNew := true
  | none => isNew := true
  if isNew then
    ref := .sp (lo32 e)
    let ent := (c.entries[lo32 e]?).getD {}
    c := { c with entries := c.entries.insert (lo32 e) { ent with first := cur, removed := 0 } }
    cmd := { cmd with entry := some ref }
  let ent := (getEntry c ref).getD {}
  c := putEntry c ref { ent with last := cur }
  c := { c with lastEntity := e, lastEntry := some ref, queue := c.queue.push cmd }
  setCmds k lvl c
  return (cur, ref)

/-- `flecs_cmd_new` (commands.c 25-36) -/
def cmdNew (k : Nat) (mk : Cmd) : M Nat := do
  let lvl ← stageCur k
  let c ← getCmds k lvl
  setCmds k lvl { c with queue := c.queue.push { mk with next := 0, entry := none } }
  return c.queue.size

/-- `flecs_cmd_entry_get` (commands.c 335-354) -/
def cmdEntryGet (c : Cmds) (e : UInt64) : Option Entry :=
  let er : Option ERef :=
    if e == c.lastEntity then c.lastEntry
    else if e == c.entity then some .inl0
    else if e == c.second then some .inl1
    else if c.entries.contains (lo32 e) then some (.sp (lo32 e)) else none
  match er.bind (getEntry c) with
  | none => none
  | some ent =>
    if ent.first == -1 then none
    else if (c.queue.getD ent.last default).entity != e then none
    else some ent

def absI (i : Int) : Nat := i.natAbs

/-- `flecs_defer_has_remove` (commands.c 356-377) -/
def deferHasRemove (c : Cmds) (ent : Entry) (id : Id) : Bool := _root_.Id.run do
  let mut cur := ent.first.toNat
  for _ in [0:c.queue.size + 1] do
    let cmd := c.queue.getD cur default
    if cmd.kind == .clear then return true
    if cmd.kind == .remove && idMatch id cmd.id then return true
    cur := absI cmd.next
    if cur == 0 then return false
  return false

/-- `flecs_defer_skip_removed` (commands.c 379-406) -/
def deferSkipRemoved (k : Nat) (e : UInt64) (id : Id) (p : Option Ptr) : M (Bool × Option Ptr) := do
  let c ← getCmds k (← stageCur k)
  if p.isNone || !c.hasRemove then return (false, p)
  match cmdEntryGet c e with
  | none => return (false, p)
  | some ent =>
    if ent.removed == 0 then return (false, p)
    if ent.removed != REMOVED_MANY then
      if id != ent.removed then return (false, p)
    else if !deferHasRemove c ent id then return (false, p)
    return (true, none)

/-- `flecs_defer_find_cmd_value` (commands.c 489-545): index of the command
    whose storage holds the value. -/
def deferFindCmdValue (k : Nat) (e : UInt64) (id : Id) : M (Option Nat) := do
  let c ← getCmds k (← stageCur k)
  match cmdEntryGet c e with
  | none => return none
  | some ent =>
    let mut cur := ent.first.toNat
    let mut result : Option Nat := none
    for _ in [0:c.queue.size + 1] do
      let cmd := c.queue.getD cur default
      match cmd.kind with
      | .set | .ensure => if cmd.id == id then result := some cur
      | .remove => if idMatch id cmd.id then result := none
      | .clear | .delete => result := none
      | _ => pure ()
      cur := absI cmd.next
      if cur == 0 then break
    return result

/-- `flecs_remove_invalid` (commands.c 893-942).  `none`: the entity must be
    deleted; `some 0`: drop the id; `some id`: keep it. -/
def removeInvalid (id : Id) : M (Option Id) := do
  if isPair id then
    let rel := pairFirst id
    if !(← isValid rel) then return some 0
    let tgt := pairSecond id
    if !(← isValid tgt) then
      match (← crGet (mkPair rel EcsWildcard)) with
      | some _ =>
        match (← policyOf rel) with
        | .delete => return none
        | .panic =>
          fail .constraintViolated "on_delete.c 777-779 via commands.c 917-920"
            "(OnDelete, Panic) constraint violated (flecs_throw_invalid_delete)"
        | .remove => return some 0
      | none => return some 0
    return some id
  else
    if !(← isValid (id &&& COMPONENT_MASK)) then return some 0
    return some id

end W

/-! ### The re-entrant core -/
namespace W

def whoOf (self : UInt64) : Who → M UInt64
  | .self => pure self
  | .slot i => return (← get).slots.getD i 0
def idOf (self : UInt64) : IdRef → M Id
  | .id x => pure x
  | .pair r t => return mkPair r (← whoOf self t)

def tgtOf : Via → Tgt
  | .world => .world
  | .stage => .stage 0

def logEv (hook : Bool) (ev : Ev) (e : UInt64) (id : Id) (v : Option Nat) : M Unit :=
  modify fun w => { w with log := w.log.push { hook, ev, entity := e, id, val := v } }

/-- observers invoked for an event on the entity's own table (`ider->self`
    and `ider->self_up`), monitors excluded -/
def obsFor (ev : Ev) (id : Id) : M (Array Obs) := do
  return (← get).obs.filter (fun o => !o.monitor && o.src != .up && o.event == ev && idMatch id o.pattern)

/-- any observer (self, up, self|up, monitor) for the event and id: the
    `ider_count` flecs_emit checks before it propagates (observable.c 1308) -/
def anyObsFor (ev : Ev) (id : Id) : M Bool := do
  return (← get).obs.any (fun o => idMatch id o.pattern &&
    (if o.monitor then ev == .onAdd || ev == .onRemove else o.event == ev))

/-- Does a monitor's single term match table `t` now?  (the observer query
    evaluated on the range, observer.c 289-340) -/
partial def monMatches (o : Obs) (t : Nat) : M Bool := do
  let w ← get
  let some x := w.tables[t]? | return false
  let self := x.type.contains o.pattern
  let rec up (tt : Nat) (depth : Nat) : M Bool := do
    if depth > 64 then return false
    let w ← get
    let some xx := w.tables[tt]? | return false
    match xx.type.find? (fun i => isPair i && pairFirst i == EcsChildOf) with
    | none => return false
    | some pr =>
      let p ← getAlive (pairSecond pr)
      if p == 0 then return false
      match ((← getIx).recOf p).table with
      | none => return false
      | some pt =>
        if ((← get).tables.getD pt default).type.contains o.pattern then return true
        up pt (depth + 1)
  match o.src with
  | .self => return self
  | .up => up t 0
  | .selfUp => return self || (← up t 0)

/-- Is `e` the target of a ChildOf pair (EcsEntityIsTraversable)? -/
def isParent (e : UInt64) : M Bool := do
  return (← crGet (mkPair EcsChildOf (lo32 e))).isSome

/-- `flecs_multi_observer_invoke` for a monitor (observer.c 654-773): the
    term must match the event's table, and not the other table (the root
    table when the event has none). -/
def monitorInvoke (oi : Nat) (o : Obs) (ev : Ev) (t : Nat) (other : Option Nat) (row count : Nat)
    (src : UInt64) : M Unit := do
  if ev != .onAdd && ev != .onRemove then return
  if !(← monMatches o t) then return
  if (← monMatches o (other.getD 0)) then return
  for i in [0:count] do
    let e ← tableEnt t (row + i)
    modify fun w => { w with obsLog := w.obsLog.push (oi, ev, e, src) }
    let w ← get
    let believed := (w.monBelief[(oi, e)]?).getD false
    if ev == .onAdd && believed then
      modify fun w => { w with viol := w.viol.push s!"P7 monitor: OnAdd for entity {e}, which already matched monitor {oi} (source {src})" }
    if ev == .onRemove && !believed then
      modify fun w => { w with viol := w.viol.push s!"P7 monitor: OnRemove for entity {e}, which did not match monitor {oi} (source {src})" }
    modify fun w => { w with monBelief := w.monBelief.insert (oi, e) (ev == .onAdd) }

/-- Invoke up observers (and self|up ones when the table does not own the
    id) for a propagated or forwarded event, and the monitors among them
    (observable.c 339-358, 666-702).  Only observers whose term traverses
    `trav` are invoked (`flecs_uni_observer_invoke`, observer.c 409-412). -/
def invokeUp (ev : Ev) (id : Id) (t : Nat) (other : Option Nat) (row count : Nat) (src : UInt64)
    (skipUpNotify : Bool) (trav : Id := EcsChildOf) : M Unit := do
  let _ := skipUpNotify
  let w ← get
  let owned := ((w.tables.getD t default).type.contains id)
  for oi in [0:w.obs.size] do
    let o := w.obs.getD oi default
    if !idMatch id o.pattern then continue
    if o.src == .self then continue
    if o.src == .selfUp && owned then continue
    if o.trav != trav then continue
    if o.monitor then monitorInvoke oi o ev t other row count src
    else if o.event == ev then
      for i in [0:count] do
        let e ← tableEnt t (row + i)
        modify fun w => { w with obsLog := w.obsLog.push (oi, ev, e, src) }
        if ev == .onSet then
          let v ← ownVal src id
          logEv false .onSet e id v
          if v.isNone then
            modify fun w => { w with viol := w.viol.push s!"OnSet observer for {id} invoked for entity {e} with source {src}, which does not have the component" }

/-- `flecs_emit_propagate` (observable.c 310-475): every table holding a
    traversable pair `(R, x)`; below a table that does not own `id`, the
    targets among its entities.  Below a ChildOf hop only ChildOf is
    followed; below an IsA hop every relationship is (424-430).  The
    source stays the entity the event started from. -/
partial def propagate (ev : Ev) (id : Id) (x : UInt64) (src : UInt64) (depth : Nat := 0)
    (propTrav : Id := 0) : M Unit := do
  if depth > 64 then return
  for rel in [EcsIsA, EcsChildOf] do
    if propTrav != 0 && propTrav != rel && propTrav != EcsIsA then continue
    let some c ← crGet (mkPair rel (lo32 x)) | continue
    for t in c.cache do
      let w ← get
      let some tx := w.tables[t]? | continue
      if !tx.live then continue
      let owned := tx.type.contains id
      if tx.count != 0 then invokeUp ev id t none 0 tx.count src false rel
      if owned then continue
      let tx := ((← get).tables.getD t default)
      for i in [0:tx.count] do
        let y := tx.ents.getD i 0
        if hasFlag ((← getIx).recOf y).flags FIsTraversable then
          propagate ev id y src (depth + 1) rel

/-- `flecs_reachable_cache_ensure` (observable.c 708-780): the ids reachable
    through `(trav, tgt)`: the target's ids (for IsA only those with the
    Inherit trait, 734-736), and through its own `(trav, x)` and `(IsA, x)`
    pairs the ids reachable there that the target's table does not have.
    Kept in the record; valid while `current == generation`. -/
partial def reachEnsure (pid : Id) (depth : Nat) (validate : Bool) : M (Array RElem) := do
  let some c ← crGet pid | return #[]
  if c.reachCur == c.reachGen then return c.reach
  if depth >= 64 then fail .internalError "observable.c 720-722" "cycle in traversable relationship"
  let trav := pairFirst pid
  let tgt ← getAlive (pairSecond pid)
  let mut out : Array RElem := #[]
  if tgt != 0 then
    let r := (← getIx).recOf tgt
    if let some t := r.table then
      let x ← tbl t
      for id in x.type do
        if trav == EcsIsA && (← instOf id) != .inherit then continue
        if isPair id && (pairFirst id == trav || pairFirst id == EcsIsA) then
          let sub ← reachEnsure id (depth + 1) true
          for el in sub do
            if !x.type.contains el.id then out := out.push el
        else out := out.push { id, src := tgt, table := t }
  let some c ← crGet pid | return out
  crSet { c with reach := out, reachCur := if validate then c.reachGen else c.reachCur }
  return out

/-- The reachable ids of `(trav, tgt)` computed from scratch (the same walk
    as `reachEnsure`, without reading or writing any cache). -/
partial def reachFresh (pid : Id) (depth : Nat := 0) : M (Array RElem) := do
  if depth >= 64 then return #[]
  let trav := pairFirst pid
  let tgt ← getAlive (pairSecond pid)
  let mut out : Array RElem := #[]
  if tgt != 0 then
    let r := (← getIx).recOf tgt
    if let some t := r.table then
      let x ← tbl t
      for id in x.type do
        if trav == EcsIsA && (← instOf id) != .inherit then continue
        if isPair id && (pairFirst id == trav || pairFirst id == EcsIsA) then
          let sub ← reachFresh id (depth + 1)
          for el in sub do
            if !x.type.contains el.id then out := out.push el
        else out := out.push { id, src := tgt, table := t }
  return out

/-- P-RC (internal invariant): a reachable cache that says it is valid
    (`current == generation`) holds what a fresh walk finds. -/
def reachInvariant : M (Array String) := do
  let w ← get
  let mut out := #[]
  for (id, c) in w.crs.toList do
    if !isPair id || isWildcard id then continue
    if pairFirst id != EcsIsA && pairFirst id != EcsChildOf then continue
    if c.reachCur != c.reachGen then continue
    if !(← isAlive (← getAlive (pairSecond id))) then continue
    let f ← reachFresh id
    if f != c.reach then
      out := out.push s!"P-RC reachable cache: ({pairFirst id}, {pairSecond id}) is valid (generation {c.reachGen}) but holds {repr (c.reach.map (fun e => (e.id, e.src, e.table)))}; a fresh walk finds {repr (f.map (fun e => (e.id, e.src, e.table)))}"
  return out

/-- `flecs_emit_forward` (observable.c 799-888) for a traversable pair
    `(ChildOf, p)` or `(IsA, b)`: the cached reachable ids (validated for
    OnAdd/OnRemove, 811-812) are forwarded to up observers (and, for an
    added IsA pair, as OnSet for ids with storage, 690-704), then events for
    newly reachable ids propagate downwards. -/
def forward (ev : Ev) (pairId : Id) (t : Nat) (other : Option Nat) (row count : Nat)
    (onset : Bool := false) : M Unit := do
  let trav := pairFirst pairId
  let reach ← reachEnsure pairId 0 (ev == .onAdd || ev == .onRemove)
  for el in reach do
    -- observable.c 827-829
    if !(← isAlive el.src) then
      fail .internalError "observable.c 827-828" s!"ecs_assert(flecs_entities_get(world, elem->src) == r): reachable source {el.src} is not alive"
    let r := (← getIx).recOf el.src
    if r.table != some el.table then
      fail .internalError "observable.c 829" s!"ecs_dbg_assert(r->table == elem->table): reachable id {el.id} from {el.src} cached for table {el.table}, now in {r.table}"
    invokeUp ev el.id t other row count el.src true trav
    if onset && hasTypeInfo el.id then
      invokeUp .onSet el.id t other row count el.src false trav
  -- propagate events for new reachable ids downwards (observable.c 836-887)
  let x ← tbl t
  for el in reach do
    if x.type.contains el.id then continue
    if !(← anyObsFor ev el.id) then continue
    for i in [0:count] do
      let e ← tableEnt t (row + i)
      if hasFlag ((← getIx).recOf e).flags FIsTraversable then propagate ev el.id e el.src

/-- `ecs_new_from_range` (entity_ranges.c 228-267) -/
def newFromRange (h : Nat) : M UInt64 := do
  if (← get).mt then fail .invalidOperation "addons/entity_ranges.c 239-240" "cannot create entities in multithreaded mode"
  let ix ← getIx
  let r := ix.ranges.getD h default
  let mut e : UInt64 := 0
  if ix.active == some h then
    let (ix', e') ← liftE ix.newId
    setIx ix'
    e := e'
  else if r.recycled.size != 0 then
    e := r.recycled.back!
    let ix := ix.modRange h (fun r => { r with recycled := r.recycled.pop })
    setIx (← liftE (ix.ensure e))
  else
    let lim := if r.max != 0 then r.max else 0xFFFFFFFF
    if !(r.cur < lim) then fail .outOfRange "addons/entity_ranges.c 254-255" "range exhausted"
    e := r.cur + 1
    let ix := ix.modRange h (fun r => { r with cur := e })
    if ix.exists_ e then fail .invalidOperation "addons/entity_ranges.c 257-259" s!"new entity {e} id already in use"
    setIx (← liftE (ix.ensure e))
  let r ← getRec e
  if r.table.isSome then fail .internalError "entity.c 660" "add_to_root_table: record already has a table"
  let row ← appendRaw 0 e
  modRec e (fun r => { r with table := some 0, row := row })
  return e

def checkAlive (e : UInt64) (fn : String) : M Unit := do
  if e == 0 || !(← isAlive e) then
    fail .invalidParameter "entity.h 18-23" s!"invalid entity passed to {fn}()"

/-- Alive entities that hold `(R, e)` for a relationship `R` with the
    (OnDeleteTarget, Panic) trait (ComponentTraits.md, OnDeleteTarget). -/
def panicHolders (e : UInt64) : M (Array UInt64) := do
  let w ← get
  let panics := w.odt.toList.filter (fun (_, p) => p == .panic) |>.map (·.1)
  let mut out := #[]
  for i in [1:w.ix.alive] do
    let x := w.ix.denseAt i
    let r := w.ix.recOf x
    if let some t := r.table then
      let ty := (w.tables.getD t default).type
      if ty.any (fun id => isPair id && pairSecond id == lo32 e && panics.contains (pairFirst id)) then
        out := out.push x
  return out

def qGet (qi : Nat) : M QCache := do
  match (← get).queries[qi]? with
  | some q => return q
  | none => fail .internalError "model" s!"no query {qi}"

def cachedTerms (q : QCache) : Array QTerm := q.terms.filter fun t => match t.src with
  | .fixed _ => false
  | _ => true

/-- Tables an OnAdd/OnRemove of `id` on `x` propagates to (observable.c
    301-475): every table holding (ChildOf, x); below a table that does not
    own `id`, the tables of its entities' children. -/
partial def propagateTables (x : UInt64) (id : Id) (depth : Nat := 0) : M (Array Nat) := do
  if depth > 64 then return #[]
  let some c ← crGet (mkPair EcsChildOf (lo32 x)) | return #[]
  let mut out := #[]
  for t in c.cache do
    let w ← get
    let some tx := w.tables[t]? | continue
    if !tx.live then continue
    out := out.push t
    if tx.type.contains id then continue
    for i in [0:tx.count] do
      out := out ++ (← propagateTables (tx.ents.getD i 0) id (depth + 1))
  return out

/-- The rematch and ancestry observers of every cached query with up terms
    (cache.c 299-432): an OnAdd/OnRemove of an up term's id, or of a ChildOf
    pair, on an entity with children enqueues a revalidation of each table
    the event propagates to. -/
def rematchEvents (ids : Array Id) (t : Nat) (row count : Nat) : M Unit := do
  let w ← get
  if w.queries.isEmpty then return
  for i in [0:count] do
    let e ← tableEnt t (row + i)
    if (← crGet (mkPair EcsChildOf (lo32 e))).isNone then continue
    for id in ids do
      for qi in [0:(← get).queries.size] do
        let q ← qGet qi
        let ups := (cachedTerms q).filter (fun t => t.src == .up)
        if ups.isEmpty then continue
        let rel := ups.any (fun t => t.id == id) || (isPair id && pairFirst id == EcsChildOf)
        if !rel then continue
        for tt in (← propagateTables e id) do
          modify fun w => { w with revalidate := w.revalidate.push (qi, tt) }

mutual

/-- Run a hook/observer body for one entity. -/
partial def runActs (self : UInt64) (val : Option Nat) : List Act → M Unit
  | [] => pure ()
  | a :: rest => do
    tick
    match a with
    | .add v w x => apiAdd (tgtOf v) (← whoOf self w) (← idOf self x)
    | .remove v w x => apiRemove (tgtOf v) (← whoOf self w) (← idOf self x)
    | .set v w x n => apiSet (tgtOf v) (← whoOf self w) (← idOf self x) n
    | .delete v w => apiDelete (tgtOf v) (← whoOf self w)
    | .whenVal n b => if val == some n then runActs self val [b] else pure ()
    runActs self val rest

/-- `flecs_invoke_hook` (component_actions.c 16-69): locks the table for
    OnAdd/OnRemove only. -/
partial def invokeHook (t : Nat) (ents : Array UInt64) (row : Nat) (id : Id) (ev : Ev)
    (acts : List Act) (ptr : Option Ptr) : M Unit := do
  let lockIt := ev == .onAdd || ev == .onRemove
  if lockIt then lockT t
  for i in [0:ents.size] do
    let e := ents.getD i 0
    let v ← match ptr with
      | some p => some <$> readPtr p
      | none => do
        let x ← tbl t
        match colIndex x id with
        | some c => pure ((x.cols.getD c #[])[row + i]?)
        | none => pure none
    logEv true ev e id v
    if ev == .onAdd && (← get).checkHookView then
      let r ← rawRec e
      let w ← get
      let inTable := match r.table with
        | some tt => ((w.tables.getD tt default).type.contains id)
        | none => false
      if !inTable then
        modify fun w => { w with viol := w.viol.push s!"view: inside the on_add hook for {id}, entity {e} does not have it (record still in its old table)" }
    runActs e v acts
  if lockIt then unlockT t

/-- `flecs_emit` (observable.c 1009-1376) for single-term, self-source
    observers: for each id, the observers that match it; skipped when the
    table has no record for the id (1265-1274).  The table is locked while
    observers run (observer.c 488-525). -/
partial def emit (ev : Ev) (ids : Array Id) (t : Nat) (row count : Nat) (setPtr : Option Ptr)
    (expect : Option UInt64 := none) (other : Option Nat := none) : M Unit := do
  if ev == .onAdd || ev == .onRemove then rematchEvents ids t row count
  for id in ids do
    if id != EcsAny && isWildcard id then continue
    if (← crGet id).isNone then continue
    -- a traversable pair (observable.c 1196-1240): adding (IsA, base)
    -- instantiates the base's children (1200-1228), once per emitted
    -- entity; then the target's reachable ids are forwarded, with OnSet for
    -- the newly inherited ones when IsA is added
    if (ev == .onAdd || ev == .onRemove) && isPair id &&
        (pairFirst id == EcsChildOf || pairFirst id == EcsIsA) then
      if ev == .onAdd && pairFirst id == EcsIsA && !(← get).instantiating then
        let base ← getAlive (pairSecond id)
        if base != 0 then
          modify fun w => { w with instantiating := true }
          for i in [0:count] do
            let e ← tableEnt t (row + i)
            instantiate base e base e 0
          modify fun w => { w with instantiating := false }
      forward ev id t other row count (ev == .onAdd && pairFirst id == EcsIsA)
    if !(← anyObsFor ev id) then continue
    -- monitors on the entity's own table (self and self|up terms)
    do
      let x ← tbl t
      if tableHas x id then
        let w ← get
        for oi in [0:w.obs.size] do
          let o := w.obs.getD oi default
          if o.monitor && o.src != .up && idMatch id o.pattern then
            monitorInvoke oi o ev t other row count 0
    -- propagation to the children of the event's entities (observable.c 1308-1318)
    do
      let x ← tbl t
      if (tableHas x id || (isPair id && pairFirst id == EcsChildOf)) && count != 0 then
        for i in [0:count] do
          let e ← tableEnt t (row + i)
          if hasFlag ((← getIx).recOf e).flags FIsTraversable then propagate ev id e e
    let os ← obsFor ev id
    if os.isEmpty then continue
    let x ← tbl t
    if !tableHas x id && !(isPair id && pairFirst id == EcsChildOf) then continue
    lockT t
    for o in os do
      for i in [0:count] do
        let e ← tableEnt t (row + i)
        let v ← match setPtr with
          | some p => if ids.size == 1 then some <$> readPtr p else pure none
          | none => do
            let x ← tbl t
            match colIndex x id with
            | some c => pure ((x.cols.getD c #[])[row + i]?)
            | none => pure none
        logEv false ev e id v
        if ev == .onAdd || ev == .onRemove then
          let w ← get
          let r := w.ix.recOf e
          let holds := w.ix.isAlive e && (match r.table with
            | some tt => (w.tables.getD tt default).type.contains id
            | none => false)
          if !holds then
            modify fun w => { w with viol := w.viol.push s!"{repr ev} observer for id {id} invoked for entity {e}, which does not have the id" }
        if let some x := expect then
          if x != e then
            modify fun w => { w with viol := w.viol.push s!"OnSet observer for id {id} invoked for entity {e}, but the set was on entity {x}" }
        runActs e v o.acts
    unlockT t
  -- OnSet for overrides (observable.c 1325-1360)
  if count != 0 then
    let x ← tbl t
    let canAdd := ev == .onAdd && hasIsA x
    let mut canRemove := false
    if ev == .onRemove then
      if let some o := other then
        canRemove := hasIsA (← tbl o)
    if canAdd || canRemove then
      for id in ids do
        if id < HI && !(← nonTrivialSet id) then continue
        if (← crGet id).isNone then continue
        if (← instOf id) == .dontInherit || !hasTypeInfo id then continue
        if canAdd then onSetOverrideOnAdd id t other row count
        else onSetOverrideOnRemove id t row count

/-- `flecs_table_get_override` (table.c 2310-2340) -/
partial def getOverride (t : Nat) (id : Id) : M (Option UInt64) := do
  let x ← tbl t
  if !hasIsA x then return none
  let some _ := x.over | return none
  let some ci := colIndex x id | return none
  updateOverrides t
  let x ← tbl t
  return (x.over.bind (fun o => o.refs.getD ci none))

/-- OnSet observers on an id (any source), for the override events -/
partial def onSetObs (id : Id) : M Bool :=
  return (← get).obs.any (fun o => !o.monitor && o.event == .onSet && idMatch id o.pattern)

/-- `flecs_emit_on_set_for_override_on_add` (observable.c 890-943): an
    override that came with its (IsA, base) in the same event gets an OnSet
    for the entity's own value (self and self|up observers). -/
partial def onSetOverrideOnAdd (id : Id) (t : Nat) (other : Option Nat) (row count : Nat) : M Unit := do
  let some base ← getOverride t id | return
  if let some o := other then
    if (← tbl o).type.contains (mkPair EcsIsA (lo32 base)) then return
  if !(← onSetObs id) then return
  let w ← get
  for oi in [0:w.obs.size] do
    let o := w.obs.getD oi default
    if o.monitor || o.event != .onSet || !idMatch id o.pattern || o.src == .up then continue
    for i in [0:count] do
      let e ← tableEnt t (row + i)
      let v ← ownVal e id
      modify fun w => { w with obsLog := w.obsLog.push (oi, .onSet, e, 0) }
      logEv false .onSet e id v

/-- `flecs_emit_on_set_for_override_on_remove` (observable.c 946-1001):
    removing an override re-exposes the base's value: OnSet with the base
    from the table's override ref as source, for self|up and up observers
    traversing IsA. -/
partial def onSetOverrideOnRemove (id : Id) (t : Nat) (row count : Nat) : M Unit := do
  let some base ← getOverride t id | return
  if !(← onSetObs id) then return
  let w ← get
  for oi in [0:w.obs.size] do
    let o := w.obs.getD oi default
    if o.monitor || o.event != .onSet || !idMatch id o.pattern || o.src == .self || o.trav != EcsIsA then continue
    for i in [0:count] do
      let e ← tableEnt t (row + i)
      modify fun w => { w with obsLog := w.obsLog.push (oi, .onSet, e, base) }
      let v ← ownVal base id
      logEv false .onSet e id v
      if v.isNone then
        -- flecs_field_shared (iter.c 206-245) reads the column of a table
        -- record that is NULL
        modify fun w => { w with viol := w.viol.push s!"OnSet observer for {id} invoked for entity {e} with source {base}, which does not have the component (observable.c 978-1000: base_tr is NULL)" }

/-- `flecs_instantiate_alloc_child_id` (addons/prefab/instantiate.c 45-71):
    the instance child keeps the prefab child's offset from the prefab.  The
    id is `root_instance + offset` (64-bit: it takes the root instance's
    generation) and it is made alive with `make_alive` + `ensure`, unless an
    entity with that 32-bit id is alive. -/
partial def allocChildId (prefabChild rootPrefab rootInstance : UInt64) : M UInt64 := do
  let newId : M UInt64 := do
    let (ix, e) ← liftE ((← getIx).newId)
    setIx ix
    return e
  if lo32 prefabChild < lo32 rootPrefab then return (← newId)
  let off := lo32 prefabChild - lo32 rootPrefab
  if off == 0 then fail .internalError "instantiate.c 57" "prefab_offset != 0"
  let child32 := lo32 rootInstance + off
  let ix ← getIx
  let aliveId := ix.getAlive child32
  if aliveId != 0 && ix.isAlive aliveId then return (← newId)
  let child := rootInstance + off
  let ix := ix.makeAlive child
  setIx (← liftE (ix.ensure child))
  if !(← getIx).isAlive child then fail .internalError "instantiate.c 68" "instance child not alive"
  return child

/-- `flecs_instantiate` + `flecs_instantiate_children` (instantiate.c
    135-300, 393-480) for fragmenting ChildOf: each child of the prefab gets
    a copy under the instance (ids from `allocChildId`, the prefab's
    DontInherit tag `Prefab` dropped, (ChildOf, base) replaced by
    (ChildOf, instance)), then its own children recursively. -/
partial def instantiate (base inst rootPrefab rootInstance : UInt64) (depth : Nat) : M Unit := do
  if depth > 32 then fail .internalError "instantiate.c 403-405" "likely cycle detected during instantiation"
  let r := (← getIx).recOf base
  let some bt := r.table | fail .internalError "instantiate.c 402" "base_table != NULL"
  let bx ← tbl bt
  if !bx.type.contains EcsPrefab then return
  let some c ← crGet (mkPair EcsChildOf (lo32 base)) | return
  for t in c.cache do
    let w ← get
    let some tx := w.tables[t]? | continue
    if !tx.live || tx.count == 0 then continue
    let children := tx.ents.extract 0 tx.count
    -- instantiate.c 253-260: the instance is one of the base's children
    if children.contains inst then
      fail .invalidParameter "addons/prefab/instantiate.c 253-260" "cycle detected in IsA relationship"
    let ids := (tx.type.filter (fun i => i != EcsPrefab && i != mkPair EcsChildOf (lo32 base))).push
      (mkPair EcsChildOf (lo32 inst))
    let ty := ids.qsort (· < ·)
    let mut newIds := #[]
    for ch in children do
      newIds := newIds.push (← allocChildId ch rootPrefab rootInstance)
    -- flecs_bulk_new (entity.c 260-388) into the instance child table
    let it ← tableEnsure ty
    for k in [0:children.size] do
      let e := newIds.getD k 0
      let row ← appendRaw it e
      modRec e (fun r => { r with table := some it, row := row })
      -- component values copied from the prefab child
      let src := children.getD k 0
      for cid in [C0, C1] do
        if let some v ← (do
            let sr := (← getIx).recOf src
            match sr.table with
            | some st =>
              let sx ← tbl st
              match colIndex sx cid with
              | some ci => pure ((sx.cols.getD ci #[])[sr.row]?)
              | none => pure none
            | none => pure none) then
          let ix ← tbl it
          if let some ci := colIndex ix cid then
            setTbl it { ix with cols := ix.cols.modify ci (fun col => col.set! row v) }
      emit .onAdd ty it row 1 none none none
    for k in [0:children.size] do
      instantiate (children.getD k 0) (newIds.getD k 0) rootPrefab rootInstance (depth + 1)

/-- `flecs_notify_on_set_w_cr` (component_actions.c 641-702) -/
partial def notifyOnSet (t : Nat) (row : Nat) (id : Id) (invokeHook_ : Bool) (ptr : Option Ptr) : M Unit := do
  let x ← tbl t
  let ent := x.ents.getD row 0
  if invokeHook_ then
    if let some acts := (← hooksOf id).onSet then
      if !(tableHas x id) then fail .internalError "component_actions.c 679" "on_set hook: table has no record"
      invokeHook t #[ent] row id .onSet acts ptr
  emit .onSet #[id] t row 1 ptr (some ent)

/-- `flecs_table_grow_data` (table.c 1521-1589) for one entity. -/
partial def tableAppend (t : Nat) (e : UInt64) (onAdd : Bool) : M Nat := do
  let x ← tbl t
  if x.lock != 0 then fail .lockedStorage "storage/table.c 1529-1530" "table append on locked table"
  let row ← appendRaw t e
  if (← isComplex x) && onAdd then
    lockT t
    for c in x.colIds do
      if let some acts := (← hooksOf c).onAdd then
        invokeHook t #[e] row c .onAdd acts none
    unlockT t
  return row

/-- `flecs_table_delete` (table.c 1653-1784) -/
partial def tableDelete (t : Nat) (row : Nat) (destruct : Bool) : M Unit := do
  let x ← tbl t
  if x.lock != 0 then fail .lockedStorage "storage/table.c 1661-1662" "table delete on locked table"
  if x.count == 0 then fail .internalError "storage/table.c 1667" "delete from empty table"
  let last := x.count - 1
  if row > last then fail .internalError "storage/table.c 1669" "row out of range"
  -- table.c 1689
  markTableDirty t 0
  bumpMember t
  let x ← tbl t
  let toMove := x.ents.getD last 0
  let toDelete := x.ents.getD row 0
  setTbl t { x with ents := x.ents.set! row toMove }
  if row != last then
    let r ← getRec toMove
    modRec toMove (fun r => { r with row := row })
    if r.table != some t then fail .internalError "storage/table.c 1683-1684" "moved record not in table"
  let x ← tbl t
  let moveLast := fun (x : Table) => { x with cols := x.cols.map (fun c => c.set! row (c.getD last 0)) }
  if !(← isComplex x) then
    let x := if row != last then moveLast x else x
    setTbl t { x with count := last }
    return
  lockT t
  if row == last then
    if destruct && (← hasDtors x) then
      for c in x.colIds do
        if let some acts := (← hooksOf c).onRemove then
          invokeHook t #[toDelete] row c .onRemove acts none
  else
    if (← hasDtors x) then
      if destruct then
        for c in x.colIds do
          if let some acts := (← hooksOf c).onRemove then
            invokeHook t #[toDelete] row c .onRemove acts none
    modTbl t moveLast
  unlockT t
  modTbl t (fun x => { x with count := last })

/-- `flecs_table_move` (table.c 1817-1922) -/
partial def tableMove (e : UInt64) (dst : Nat) (dstRow : Nat) (src : Nat) (srcRow : Nat) : M Unit := do
  let d ← tbl dst
  let s ← tbl src
  if d.lock != 0 || s.lock != 0 then fail .lockedStorage "storage/table.c 1829-1830" "move on locked table"
  let copyCol : Id → Id → M Unit := fun did sid => do
    let d ← tbl dst
    let s ← tbl src
    match colIndex d did, colIndex s sid with
    | some dc, some sc =>
      let v := (s.cols.getD sc #[]).getD srcRow 0
      setTbl dst { d with cols := d.cols.modify dc (fun col => col.set! dstRow v) }
    | _, _ => pure ()
  -- table.c 1838-1843: the fast path needs neither table complex nor with IsA
  if !(← isComplex d) && !(← isComplex s) && !hasIsA d && !hasIsA s then
    for c in d.colIds do
      if s.colIds.contains c then copyCol c c
    return
  -- table.c 1845
  updateOverrides dst
  -- flecs_table_invoke_add_hooks (table.c 1009-1033): ctor (from the
  -- override ref when there is one), then the on_add hook
  let ctorCol : Nat → M Unit := fun ci => do
    let v ← ctorVal dst ci
    let d ← tbl dst
    setTbl dst { d with cols := d.cols.modify ci (fun col => if dstRow < col.size then col.set! dstRow v else col) }
  lockT dst
  lockT src
  let mut i := 0
  let mut j := 0
  while i < d.colIds.size && j < s.colIds.size do
    let did := d.colIds.getD i 0
    let sid := s.colIds.getD j 0
    if did == sid then copyCol did sid
    else if did < sid then
      ctorCol i
      if let some acts := (← hooksOf did).onAdd then invokeHook dst #[e] dstRow did .onAdd acts none
    else
      if let some acts := (← hooksOf sid).onRemove then invokeHook src #[e] srcRow sid .onRemove acts none
    if did <= sid then i := i + 1
    if did >= sid then j := j + 1
  while i < d.colIds.size do
    let did := d.colIds.getD i 0
    ctorCol i
    if let some acts := (← hooksOf did).onAdd then invokeHook dst #[e] dstRow did .onAdd acts none
    i := i + 1
  while j < s.colIds.size do
    let sid := s.colIds.getD j 0
    if let some acts := (← hooksOf sid).onRemove then invokeHook src #[e] srcRow sid .onRemove acts none
    j := j + 1
  unlockT src
  unlockT dst

/-- `flecs_move_entity` (entity.c 150-207) -/
partial def moveEntity (e : UInt64) (dst : Nat) (diff : Diff) : M Unit := do
  let r ← getRec e
  let some src := r.table | fail .internalError "entity.c 162" "move: no source table"
  if src == dst then fail .internalError "entity.c 163" "move to same table"
  -- flecs_actions_move_remove (component_actions.c 435-502): the reachable
  -- caches below the entity are invalidated (466-467), then OnRemove
  if !diff.removed.isEmpty then
    if (← hasTraversable src) then propagateInvalidate src r.row 1
    emit .onRemove diff.removed src r.row 1 none none (some dst)
  let r ← getRec e
  let srcRow := r.row
  let dstRow := (← tbl dst).count
  discard <| tableAppend dst e false
  tableMove e dst dstRow src srcRow
  modRec e (fun r => { r with table := some dst, row := dstRow })
  tableDelete src srcRow false
  -- flecs_actions_move_add (component_actions.c 404-433): invalidation
  -- (421-423), then OnAdd observers
  if !diff.added.isEmpty then
    if (← hasTraversable dst) then propagateInvalidate dst dstRow 1
    emit .onAdd diff.added dst dstRow 1 none none (some src)
  -- entity.c 198-200
  if diff.added.isEmpty && hasFlag ((← getIx).recOf e).flags FIsTraversable then
    let r ← getRec e
    if r.table == some dst then propagateInvalidate dst r.row 1

/-- `flecs_commit` (entity.c 209-258) -/
partial def commit (e : UInt64) (dst : Nat) (diff : Diff) : M Unit := do
  if (← get).readonly then fail .internalError "entity.c 218" "commit while world is readonly"
  let r ← getRec e
  if r.table == some dst then return
  moveEntity e dst diff

/-- `flecs_add_id_now` (entity.c 421-435) -/
partial def addIdNow (e : UInt64) (id : Id) : M Unit := do
  let r ← getRec e
  let some t := r.table | fail .internalError "entity.c 427" "no table"
  let (d, diff) ← traverseAdd t id
  commit e d diff

/-- `flecs_remove_id_now` (entity.c 452-465) -/
partial def removeIdNow (e : UInt64) (id : Id) : M Unit := do
  let r ← getRec e
  let some t := r.table | fail .internalError "entity.c 458" "no table"
  let (d, diff) ← traverseRemove t id
  commit e d diff

/-- `flecs_add_id_w_record` (entity.c 395-419) -/
partial def addIdWRecord (e : UInt64) (id : Id) : M Unit := do
  let r ← getRec e
  let some t := r.table | fail .internalError "entity.c 404" "no table"
  let (d, diff) ← traverseAdd t id
  let prev := (← get).ensureAdd
  modify fun w => { w with ensureAdd := some (e, #[id]) }
  commit e d diff
  modify fun w => { w with ensureAdd := prev }

/-- `flecs_commands_end` (commands.c 1577-1588) -/
partial def commandsEnd (k : Nat) : M Unit := do
  let lvl ← stageCur k
  if lvl == 0 then fail .internalError "commands.c 1582" "commands_end without begin"
  if (← getCmds k lvl).queue.size != 0 then
    discard <| flush k
  setStageCur k (lvl - 1)

/-- `flecs_ensure` (entity.c 507-578) -/
partial def ensureNow (e : UInt64) (id : Id) : M (Option Ptr) := do
  let r ← getRec e
  let some t := r.table | fail .internalError "entity.c 520" "ensure: no table"
  let x ← tbl t
  if id < HI then
    if let some c := colIndex x id then return some { t, col := c, row := r.row }
  else
    if let some p ← componentPtr t r.row id then return some p
  addIdWRecord e id
  commandsEnd 0
  commandsBegin 0
  if (← crGet id).isNone then fail .internalError "entity.c 568" "ensure: record missing"
  let r ← rawRec e
  let some t := r.table | fail .internalError "entity.c 575" "ensure: r->table is NULL after the flush (entity deleted by a hook/observer)"
  componentPtr t r.row id

/-- `flecs_modified_id_if` (entity.c 1854-1887) -/
partial def modifiedIdIf (e : UInt64) (id : Id) (invoke : Bool) : M Unit := do
  if !(← isAlive e) then fail .invalidParameter "entity.c 1861" "modified: entity not alive"
  let r ← getRec e
  let some t := r.table | fail .internalError "entity.c 1869" "no table"
  let p ← componentPtr t r.row id
  match p with
  | none => return
  | some p =>
    notifyOnSet t r.row id invoke (some p)
    -- entity.c 1884 (the table read before the hooks ran)
    markDirty t id
    bumpWrite e id

/-- `flecs_set_id_move` (entity.c 1931-1979) for Set/Ensure commands. -/
partial def setIdMove (e : UInt64) (id : Id) (v : Nat) (isSet : Bool) : M Unit := do
  let some p ← ensureNow e id | fail .invalidParameter "entity.c 1943" "set_id_move: no storage after ensure"
  let r ← getRec e
  let some t := r.table | fail .internalError "entity.c 1950" "no table"
  lockT t
  writePtr p v
  unlockT t
  -- entity.c 1963
  markDirty t id
  if isSet then bumpWrite e id
  if isSet then
    let x ← tbl t
    -- EcsTableHasOnSet (entity.c 1966): set for tables with an id that has
    -- OnSet observers of any source kind (observer.c 104-127: up and self|up
    -- observers count too); round 3 correction, round 2 counted self only
    let hasObs := (← get).obs.any (fun o => !o.monitor && o.event == .onSet && idMatch id o.pattern) && tableHas x id
    if hasObs || (← hooksOf id).onSet.isSome then
      notifyOnSet t r.row id true (some p)

/-- `flecs_cmd_batch_for_entity` (commands.c 968-1298).  Mutates the queue
    level `lvl` of stage `k` in place, as the C code does. -/
partial def batchForEntity (k lvl : Nat) (e : UInt64) (start : Nat) : M Unit := do
  let r ← getRec e
  let some startTable := r.table | fail .internalError "commands.c 979" "batch: no table"
  let mut table := startTable
  let mut setIds : Array Id := #[]
  let mut hasSet := false
  let mut cur := start
  let mut split := 0
  let mut added : Array Id := #[]
  let mut removed : Array Id := #[]
  let setKind := fun (i : Nat) (kind : CK) => modCmds k lvl (fun c =>
    { c with queue := c.queue.modify i (fun cmd => { cmd with kind := kind }) })
  for _ in [0:4096] do
    let cmd := (← getCmds k lvl).queue.getD cur default
    let id := cmd.id
    let mut nextE := absI cmd.next
    let mut skipRest := false
    if id != 0 then
      match (← removeInvalid id) with
      | none =>
        setKind cur .skip
        apiDelete .world e
        return
      | some x =>
        if x == 0 then
          setKind cur .skip
          skipRest := true
    if !skipRest then
      let kind := cmd.kind
      let mut inTable := false
      let mut doSplit := false
      if kind == .add || kind == .addModified || kind == .set || kind == .ensure then
        let x ← tbl table
        let crId ← crGet id
        if id < HI then inTable := tableHas x id
        else if !removed.isEmpty then
          inTable := crId.isSome && tableHas x id
        if !inTable && !removed.isEmpty then
          let sx ← tbl startTable
          let crOk := if id < HI then true else crId.isSome
          if crOk && tableHas sx id then doSplit := true
      if doSplit then
        split := cur
        break
      match kind with
      | .addModified =>
        setKind cur .modified
        if !inTable then
          let (d, df) ← traverseAdd table id
          table := d
          added := added ++ df.added
          removed := removed ++ df.removed
      | .add =>
        if !inTable then
          let (d, df) ← traverseAdd table id
          table := d
          added := added ++ df.added
          removed := removed ++ df.removed
        setKind cur .skip
      | .set | .ensure =>
        if !inTable then
          let (d, df) ← traverseAdd table id
          table := d
          added := added ++ df.added
          removed := removed ++ df.removed
        setIds := setIds.push id
        hasSet := true
      | .remove =>
        let (d, df) ← traverseRemove table id
        table := d
        added := added ++ df.added
        removed := removed ++ df.removed
        setKind cur .skip
      | .clear =>
        let x ← tbl table
        removed := removed ++ x.type
        table := 0
        setKind cur .skip
      | .delete => nextE := 0
      | _ => pure ()
    cur := nextE
    if cur == 0 then break
  -- commit without the added ids (commands.c 1138-1159)
  let prev := (← get).ensureAdd
  if !setIds.isEmpty then modify fun w => { w with ensureAdd := some (e, setIds) }
  commandsBegin 0
  commit e table { added := #[], removed := removed }
  commandsEnd 0
  modify fun w => { w with ensureAdd := prev }
  -- copy values of set/ensure commands (commands.c 1179-1275)
  if hasSet then
    let mut cur2 := start
    for _ in [0:4096] do
      let cmd := (← getCmds k lvl).queue.getD cur2 default
      let mut nextE := absI cmd.next
      match cmd.kind with
      | .set | .ensure =>
        match (← getMutR (← rawRec e) cmd.id) with
        | some p =>
          let r ← rawRec e
          let some t := r.table | fail .internalError "commands.c 1222" "no table"
          lockT t
          writePtr p (cmd.value.getD 0)
          unlockT t
          if cmd.kind == .ensure && cmd.fromSet then bumpWrite e cmd.id
          modCmds k lvl (fun c => { c with queue := c.queue.modify cur2 (fun cm =>
            { cm with value := none, kind := if cm.kind == .set then .modified else .skip }) })
        | none => setKind cur2 .skip
      | .delete => nextE := 0
      | _ => pure ()
      cur2 := nextE
      if cur2 == 0 || cur2 == split then break
  let r ← rawRec e
  let some t := r.table | fail .internalError "commands.c 1277" "batch: r->table is NULL after commit (entity deleted by a hook/observer)"
  if !added.isEmpty then
    commandsBegin 0
    -- flecs_actions_move_add (commands.c 1282-1290, component_actions.c 421)
    if (← hasTraversable t) then propagateInvalidate t r.row 1
    emit .onAdd added t r.row 1 none none (some startTable)
    commandsEnd 0
  if split != 0 then
    modCmds k lvl (fun c => { c with queue := c.queue.modify split (fun cm => { cm with next := -cm.next }) })

/-- `flecs_commands_flush` (commands.c 1300-1575) -/
partial def flush (k : Nat) : M Bool := do
  let root ← stageCur k
  if (← getCmds k root).queue.size == 0 then return false
  let dst := 0
  let mut commands := root
  let mut i := 0
  let mut entering := true
  for _ in [0:100000] do
    if entering then
      commandsBegin k
      if dst != k then commandsBegin dst
      i := 0
      entering := false
    let count := (← getCmds k commands).queue.size
    -- resume: process commands i..count
    let mut nested := false
    while i < count do
      tick
      let cmd := (← getCmds k commands).queue.getD i default
      if cmd.kind == .skip && cmd.value.isNone then
        if let some er := cmd.entry then
          modCmds k commands (fun c => putEntry c er { (getEntry c er).getD {} with first := -1 })
        i := i + 1
        continue
      let e := cmd.entity
      let mut alive ← isAlive e
      if cmd.next < 0 && !(← get).noBatch then
        if alive then
          batchForEntity k commands e i
          alive ← isAlive e
      let cmd := (← getCmds k commands).queue.getD i default
      if let some er := cmd.entry then
        modCmds k commands (fun c => putEntry c er { (getEntry c er).getD {} with first := -1 })
      let kind := cmd.kind
      if kind == .skip || (e != 0 && !alive) then
        pure ()  -- discard
      else
        match kind with
        | .add =>
          let x ← tbl ((← getRec e).table.getD 0)
          if cmd.id < HI && tableHas x cmd.id then pure ()
          else
            match (← removeInvalid cmd.id) with
            | some id =>
              if id != 0 then
                commandsBegin 0
                addIdNow e id
                commandsEnd 0
            | none => apiDelete .world e
        | .remove => removeIdNow e cmd.id
        | .set => setIdMove e cmd.id (cmd.value.getD 0) true
        | .ensure =>
          setIdMove e cmd.id (cmd.value.getD 0) false
          if cmd.fromSet then bumpWrite e cmd.id
        | .modified => modifiedIdIf e cmd.id true
        | .addModified =>
          commandsBegin 0
          addIdNow e cmd.id
          commandsEnd 0
          modifiedIdIf e cmd.id true
        | .delete => apiDelete .world e
        | .clear => apiClear .world e
        | .onDeleteAction =>
          commandsBegin 0
          onDelete cmd.id (some cmd.action) false false
          commandsEnd 0
        | .skip => pure ()
      -- next:
      if dst != k then
        let dl ← stageCur dst
        if (← getCmds dst dl).queue.size != 0 then
          discard <| flush dst
      let sc ← stageCur k
      if (← getCmds k sc).queue.size != 0 then
        modCmds k commands (fun c => { c with cursor := i + 1 })
        commands := sc
        nested := true
        break
      i := i + 1
    if nested then
      entering := true
      continue
    -- end of this level
    if dst != k then commandsEnd dst
    setStageCur k commands
    modCmds k commands (fun c => { c with queue := #[], hasRemove := false })
    if commands != root then
      commands := commands - 1
      i := (← getCmds k commands).cursor
      continue
    return true
  fail .internalError "model" "flush did not terminate"

-- ### Cleanup (on_delete.c)

/-- `flecs_marked_id_push` (on_delete.c 8-25) -/
partial def markedPush (id : Id) (action : Option Policy) (deleteId : Bool) : M Unit := do
  let some c ← crGet id | fail .internalError "on_delete.c 14" "mark: no record"
  crSet { c with marked := true, refcount := c.refcount + 1 }
  modify fun w => { w with marked := w.marked.push { id, action, deleteId } }

/-- delete action for one table (`flecs_get_delete_action`, on_delete.c
    111-152): the policies of the table's pairs matching `id`, in type order,
    folded by `deleteAction`. -/
partial def deleteActionFor (x : Table) (id : Id) (action : Option Policy) (deleteTarget : Bool) : M (Option Policy) := do
  match action with
  | some a => return some a
  | none =>
    if !deleteTarget then return none
    let mut ps : List Policy := []
    for i in x.type do
      if idMatch i id then ps := ps ++ [← policyOf (pairFirst i)]
    return deleteAction ps

/-- `flecs_target_mark_for_delete` (on_delete.c 51-84) -/
partial def targetMarkForDelete (e : UInt64) : M Unit := do
  let r ← getRec e
  if !hasFlag r.flags FIsId && !hasFlag r.flags FIsTarget then return
  if hasFlag r.flags FIsId then
    if let some _ ← crGet e then componentMarkForDelete e none true
    if let some _ ← crGet (mkPair e EcsWildcard) then componentMarkForDelete (mkPair e EcsWildcard) none true
  if hasFlag r.flags FIsTarget then
    if let some _ ← crGet (mkPair EcsWildcard e) then
      componentMarkForDelete (mkPair EcsWildcard e) none true

/-- `flecs_component_mark_for_delete` (on_delete.c 346-430) -/
partial def componentMarkForDelete (id : Id) (action : Option Policy) (deleteId : Bool) : M Unit := do
  let some c ← crGet id | return
  if c.marked then return
  markedPush id action deleteId
  let deleteTarget := action.isNone && isPair id && pairFirst id == EcsWildcard
  let some c ← crGet id | return
  for t in c.cache do
    let x ← tbl t
    if x.count == 0 then continue
    if x.marked then continue
    let cur ← deleteActionFor x id action deleteTarget
    if cur == some .delete then
      modTbl t (fun x => { x with marked := true })
      for i in [0:x.count] do
        targetMarkForDelete (x.ents.getD i 0)
    else if cur == some .panic then
      fail .constraintViolated "on_delete.c 395-397" "(OnDelete, Panic) constraint violated"
  let some c ← crGet id | return
  for t in c.cache do
    let x ← tbl t
    if x.count == 0 then modTbl t (fun x => { x with marked := true })
  if isWildcard id && isPair id then
    for ch in (← crChildren id) do
      if let some cc ← crGet ch then crSet { cc with marked := true }

/-- `flecs_on_delete_mark` (on_delete.c 432-463) -/
partial def onDeleteMark (id : Id) (action : Option Policy) (deleteId : Bool) : M Unit := do
  let some _ ← crGet id | return
  let mut action := action
  if action.isNone then
    if !isPair id || pairSecond id == EcsWildcard then
      action := none  -- ECS_ID_ON_DELETE: components/relationships default Remove
  componentMarkForDelete id action deleteId

/-- `flecs_remove_from_table` (on_delete.c 465-556) -/
partial def removeFromTable (t : Nat) : M Unit := do
  let x ← tbl t
  if x.type.isEmpty then return
  let ms := (← get).marked
  let mut rm : Array Id := #[]
  for m in ms do
    for i in x.type do
      if idMatch i m.id && !rm.contains i then rm := rm.push i
  if rm.isEmpty then return
  let dstType := x.type.filter (fun i => !rm.contains i)
  let removed := x.type.filter (fun i => rm.contains i)
  let d ← tableEnsure dstType
  if d == t then fail .internalError "on_delete.c 525" "dst == src"
  let x ← tbl t
  if x.count != 0 then emit .onRemove removed t 0 x.count none none (some d)
  tableMerge d t

/-- `flecs_table_merge` (table.c 2103-2205) -/
partial def tableMerge (d s : Nat) : M Unit := do
  let sx ← tbl s
  let dx ← tbl d
  if sx.lock != 0 || dx.lock != 0 then fail .lockedStorage "storage/table.c 2108-2111" "merge on locked table"
  if sx.count == 0 then return
  for i in [0:sx.count] do
    let e := sx.ents.getD i 0
    discard <| getRec e
    modRec e (fun r => { r with table := some d, row := dx.count + i })
  let mut dx := dx
  for i in [0:sx.count] do
    let e := sx.ents.getD i 0
    dx := { dx with ents := if dx.count + i < dx.ents.size then dx.ents.set! (dx.count + i) e else dx.ents.push e }
  let cols := dx.colIds.mapIdx (fun ci cid =>
    let base := (dx.cols.getD ci #[]).extract 0 dx.count
    let srcCol := match colIndex sx cid with
      | some sc => (sx.cols.getD sc #[]).extract 0 sx.count
      | none => Array.replicate sx.count 0
    base ++ srcCol)
  -- table.c 2121: the source's traversable count, read before the merge
  let srcTrav ← hasTraversable s
  setTbl d { dx with cols, count := dx.count + sx.count }
  setTbl s { sx with count := 0 }
  -- table.c 2202-2203
  if srcTrav then propagateInvalidate d dx.count sx.count
  -- table.c 2167 (each dst column shared with src) and 2183; the source's
  -- dirty state is not marked
  for ci in [0:dx.colIds.size] do
    if (colIndex sx (dx.colIds.getD ci 0)).isSome then markTableDirty d (ci + 1)
  markTableDirty d 0
  bumpMember d
  bumpMember s

/-- `flecs_table_fini_data(world, table, true, false)` = clear entities
    (table.c 1141-1226, 1070-1133) -/
partial def tableClearEntities (t : Nat) : M Unit := do
  let x ← tbl t
  if x.lock != 0 then fail .lockedStorage "storage/table.c 1147" "table data cleanup while locked"
  if x.count != 0 then
    emit .onRemove x.type t 0 x.count none
  let x ← tbl t
  let count := x.count
  if count == 0 then return
  let ents := x.ents.extract 0 count
  if (← hasDtors x) then
    for c in x.colIds do
      if let some acts := (← hooksOf c).onRemove then
        invokeHook t ents 0 c .onRemove acts none
  -- table.c 1097-1101
  if (← hasTraversable t) then propagateInvalidate t 0 count
  for e in ents do
    if !(← isValid e) then fail .internalError "storage/table.c 1112-1113" "entity being cleared is not valid"
    let ix ← liftE ((← getIx).remove e)
    setIx ix
  modTbl t (fun x => { x with count := 0 })

/-- `flecs_on_delete_clear_entities` (on_delete.c 558-668) -/
partial def onDeleteClearEntities : M Unit := do
  let mut last := (← get).marked.size
  let mut first := 0
  for _ in [0:64] do
    let mut i := last
    while i > first do
      i := i - 1
      let m := (← get).marked.getD i default
      let some c ← crGet m.id | continue
      -- iterate a snapshot of the cache (flecs_table_cache_iter takes the
      -- array pointer and count at the start, table_cache.c 255-269)
      for t in c.cache do
        let w ← get
        let some x := w.tables[t]? | continue
        if !x.live || x.count == 0 then continue
        if m.action == some .remove || !x.marked then removeFromTable t
        else tableClearEntities t
    let newLast := (← get).marked.size
    if newLast != last then
      first := last
      last := newLast
    else break

/-- `flecs_on_delete_clear_ids` (on_delete.c 688-768) -/
partial def onDeleteClearIds : M Unit := do
  for pass in [0:2] do
    for m in (← get).marked do
      let wc := isWildcard m.id
      if pass == 0 && wc then continue
      if pass == 1 && !wc then continue
      let some c ← crGet m.id | continue
      -- flecs_component_release_tables (component_index.c 753-776)
      let mut remaining := false
      for t in c.cache do
        let x ← tbl t
        if x.count != 0 then remaining := true
        else tableFini t
      if remaining then
        if let some c ← crGet m.id then crSet { c with marked := false }
        discard <| crRelease m.id
      else
        let rc ← crRelease m.id
        if rc != 0 then
          if m.deleteId then discard <| crRelease m.id
          else if let some c ← crGet m.id then crSet { c with marked := false }

/-- `flecs_on_delete` (on_delete.c 786-827) -/
partial def onDelete (id : Id) (action : Option Policy) (deleteId : Bool) (force : Bool) : M Unit := do
  let _ := force
  let count := (← get).marked.size
  onDeleteMark id action deleteId
  if count == 0 && (← get).marked.size != 0 then
    onDeleteClearEntities
    onDeleteClearIds
    modify fun w => { w with marked := #[] }

-- ### Public API (entity.c)

/-- `ecs_new` (entity.c 701-712) -/
partial def apiNew (tg : Tgt) : M UInt64 := do
  let _ := tg
  if (← get).mt then fail .invalidOperation "entity.c 117-118" "cannot create entities in multithreaded mode"
  let (ix, e) ← liftE ((← getIx).newId)
  setIx ix
  let r ← getRec e
  if r.table.isSome then fail .internalError "entity.c 660" "new: record already has a table"
  let row ← appendRaw 0 e
  modRec e (fun r => { r with table := some 0, row := row })
  return e

/-- `ecs_add_id` / `flecs_add_id` (entity.c 1409-1420, 437-450) -/
partial def apiAdd (tg : Tgt) (e : UInt64) (id : Id) : M Unit := do
  checkAlive e "add"
  match tg with
  | .stage k =>
    discard <| cmdNewBatched k e { kind := .add, id, entity := e }
  | .world =>
    commandsBegin 0
    addIdNow e id
    commandsEnd 0

/-- `ecs_remove_id` / `flecs_remove_id` (entity.c 1422-1442, 467-480, commands.c 308-333) -/
partial def apiRemove (tg : Tgt) (e : UInt64) (id : Id) : M Unit := do
  checkAlive e "remove"
  match tg with
  | .stage k =>
    let (_, er) ← cmdNewBatched k e { kind := .remove, id, entity := e }
    let lvl ← stageCur k
    modCmds k lvl (fun c =>
      let ent := (getEntry c er).getD {}
      let rem := if (ent.removed == 0 || ent.removed == id) && !isWildcard id then id else REMOVED_MANY
      { (putEntry c er { ent with removed := rem }) with hasRemove := true })
  | .world =>
    commandsBegin 0
    removeIdNow e id
    commandsEnd 0

/-- `ecs_set_id` (entity.c 1981-2033); staged: `flecs_defer_set_impl`
    (commands.c 629-712). -/
partial def apiSet (tg : Tgt) (e : UInt64) (id : Id) (v : Nat) : M Unit := do
  checkAlive e "set"
  if !hasTypeInfo id then fail .invalidParameter "commands.c 657-658" "provided component is not a type"
  match tg with
  | .stage k =>
    discard <| getRec e
    let mut p ← getMut e id
    if p.isNone && (← crGet id).isNone && !(← get).mt then
      discard <| crEnsure id
    let (_, p') ← deferSkipRemoved k e id p
    p := p'
    let (idx, _) ← cmdNewBatched k e { kind := .add, id, entity := e }
    let lvl ← stageCur k
    if (← get).stages.size != 1 then p := none
    let setCmd := fun (kind : CK) (val : Option Nat) =>
      modCmds k lvl (fun c => { c with queue := c.queue.modify idx (fun cm => { cm with kind := kind, value := val }) })
    if id < HI && !(← nonTrivialSet id) then
      match p with
      | none =>
        setCmd .ensure (some v)
        modCmds k lvl (fun c => { c with queue := c.queue.modify idx (fun cm => { cm with fromSet := true }) })
      | some ptr =>
        setCmd .add none
        writePtr ptr v
        bumpWrite e id
      return
    match p with
    | none => setCmd .set (some v)
    | some ptr =>
      setCmd .addModified none
      let r ← getRec e
      let t := r.table.getD 0
      lockT t
      writePtr ptr v
      unlockT t
  | .world =>
    commandsBegin 0
    let some p ← ensureNow e id | fail .invalidParameter "entity.c 2016" "set: ensure returned NULL"
    if id < HI && !(← nonTrivialSet id) then
      writePtr p v
      bumpWrite e id
    else
      -- flecs_copy_id (entity.c 810-840)
      let r ← getRec e
      let t := r.table.getD 0
      lockT t
      writePtr p v
      unlockT t
      markDirty t id
      bumpWrite e id
      let r ← getRec e
      notifyOnSet (r.table.getD 0) r.row id true (some p)
    commandsEnd 0

/-- `ecs_ensure_id` followed by a write through the returned pointer
    (entity.c 1722-1759; staged: commands.c 547-627). -/
partial def apiEnsureWrite (tg : Tgt) (e : UInt64) (id : Id) (v : Nat) : M Unit := do
  checkAlive e "ensure"
  if !hasTypeInfo id then fail .invalidParameter "commands.c 562-563" "provided component is not a type"
  match tg with
  | .stage k =>
    discard <| getRec e
    let mut p ← getMut e id
    if p.isNone && (← crGet id).isNone && !(← get).mt then
      discard <| crEnsure id
    let (removed, p') ← deferSkipRemoved k e id p
    p := p'
    let lvl ← stageCur k
    if p.isNone then
      if let some idx ← deferFindCmdValue k e id then
        modCmds k lvl (fun c => { c with queue := c.queue.modify idx (fun cm => { cm with value := some v }) })
        return
    let (idx, _) ← cmdNewBatched k e { kind := .add, id, entity := e }
    match p with
    | none =>
      -- commands.c 590-611: the command's value starts as the inherited
      -- value: through the table's override ref when the component was
      -- removed in this batch (flecs_table_get_override refreshes the
      -- cache), else flecs_get_base_component.  The program then writes
      -- the whole value, so only the cache refresh is observable.
      if removed then
        if let some t := (← getRec e).table then
          if hasIsA (← tbl t) then discard <| getOverride t id
      modCmds k lvl (fun c => { c with queue := c.queue.modify idx (fun cm => { cm with kind := .ensure, value := some v }) })
    | some ptr => writePtr ptr v
  | .world =>
    commandsBegin 0
    let some p ← ensureNow e id
      | fail .invalidOperation "entity.c 1748-1752" "component ensured on entity was removed during the operation"
    commandsEnd 0
    writePtr p v

/-- `ecs_modified_id` (entity.c 1889-1929) -/
partial def apiModified (tg : Tgt) (e : UInt64) (id : Id) : M Unit := do
  checkAlive e "modified"
  if id < HI && !(← nonTrivialSet id) then return
  match tg with
  | .stage k => discard <| cmdNew k { kind := .modified, id, entity := e }
  | .world =>
    commandsBegin 0
    let r ← getRec e
    let some t := r.table | fail .internalError "entity.c 1917" "no table"
    if !tableHas (← tbl t) id then
      fail .invalidParameter "entity.c 1912-1915" "modified(): entity does not have component"
    notifyOnSet t r.row id true none
    -- entity.c 1925
    markDirty t id
    bumpWrite e id
    commandsEnd 0

/-- `ecs_clear` (entity.c 1293-1325) -/
partial def apiClear (tg : Tgt) (e : UInt64) : M Unit := do
  if !(← isValid e) then fail .invalidParameter "entity.c 1298" "clear: invalid entity"
  match tg with
  | .stage k =>
    let (_, er) ← cmdNewBatched k e { kind := .clear, entity := e }
    let lvl ← stageCur k
    modCmds k lvl (fun c =>
      let ent := (getEntry c er).getD {}
      { (putEntry c er { ent with removed := REMOVED_MANY }) with hasRemove := true })
  | .world =>
    commandsBegin 0
    let r ← getRec e
    let some t := r.table | fail .internalError "entity.c 1309" "no table"
    let x ← tbl t
    if x.type.size != 0 then commit e 0 { removed := x.type }
    commandsEnd 0

/-- `ecs_delete` (entity.c 1327-1407) -/
partial def apiDelete (tg : Tgt) (e : UInt64) : M Unit := do
  if e == 0 then fail .invalidParameter "entity.c 1332" "delete: entity is 0"
  match tg with
  | .stage k =>
    discard <| cmdNewBatched k e { kind := .delete, entity := e }
  | .world =>
    commandsBegin 0
    match (← getIx).tryGet e with
    | none => pure ()
    | some r =>
      let panicExpected ← panicHolders e
      let flags := r.flags
      if flags != 0 then
        if hasFlag flags FIsTarget then
          onDelete (mkPair EcsWildcard e) none true true
        if hasFlag flags FIsId then
          onDelete e none true true
          onDelete (mkPair e EcsWildcard) none true true
        commandsEnd 0
        commandsBegin 0
      -- `table = r->table` on the record pointer: NULL when the entity was
      -- cleaned up as a result of a cycle (entity.c 1380-1382)
      let r ← rawRec e
      match r.table with
      | some t =>
        let x ← tbl t
        -- flecs_actions_move_remove (entity.c 1387-1388)
        if x.type.size != 0 && (← hasTraversable t) then propagateInvalidate t r.row 1
        if x.type.size != 0 then emit .onRemove x.type t r.row 1 none
        let r ← rawRec e
        tableDelete t r.row true
      | none => pure ()
      setIx (← liftE ((← getIx).remove e))
      if !panicExpected.isEmpty then
        modify fun w => { w with viol := w.viol.push s!"deleting {e} did not panic although {panicExpected} hold a pair with a (OnDeleteTarget, Panic) relationship to it" }
    commandsEnd 0

/-- `ecs_delete_with` / `ecs_remove_all` (on_delete.c 829-871) -/
partial def apiOnDeleteAction (tg : Tgt) (id : Id) (action : Policy) : M Unit := do
  match tg with
  | .stage k => discard <| cmdNew k { kind := .onDeleteAction, id, action }
  | .world =>
    commandsBegin 0
    onDelete id (some action) false false
    commandsEnd 0

end

/-- `ecs_merge` (stage.c 358-366) -/
def merge (k : Nat) : M Unit := do
  discard <| flush k

/-- `ecs_readonly_begin` (stage.c 289-312) -/
def readonlyBegin (mt : Bool) : M Unit := modify fun w => { w with readonly := true, mt := mt }

/-- `ecs_readonly_end` (stage.c 314-330) -/
def readonlyEnd : M Unit := do
  if !(← get).readonly then fail .invalidOperation "stage.c 318-319" "world is not in readonly mode"
  modify fun w => { w with readonly := false, mt := false }
  for k in [0:(← get).stages.size] do
    discard <| flush k

/-! ### Reads used by properties -/

def has (e : UInt64) (id : Id) : M Bool := do
  let r ← getRec e
  match r.table with
  | some t => return (typeWithout (← tbl t).type id).isSome
  | none => return false

def getVal (e : UInt64) (id : Id) : M (Option Nat) := do
  let r ← getRec e
  match r.table with
  | some t =>
    let x ← tbl t
    match colIndex x id with
    | some c => return (x.cols.getD c #[])[r.row]?
    | none => return none
  | none => return none

end W
end Flecs
