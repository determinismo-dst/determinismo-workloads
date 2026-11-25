/-
  The world: tables, component records, hooks, observers, stages and the
  command queue, transcribed from flecs v4.2.0 (paths under src/).

  Model universe: two data components C0, C1 (low ids, 8 bytes, values are
  Nat), and user entities created with ecs_new.  Relationships are user
  entities with an OnDeleteTarget policy and Exclusive flag kept in `World`.
  Not modelled: IsA/prefabs, sparse/DontFragment, Parent (non-fragmenting
  ChildOf), names, toggles, With, emplace, clone, bulk ops, custom events.
-/
import FlecsLean.EntityIndex

namespace Flecs
open Std

def C0 : Id := 60
def C1 : Id := 61
def isDataComp (id : Id) : Bool := id == C0 || id == C1
/-- Ids with a column: the data components, and pairs whose first element is
    a data component (type info from the relationship,
    component_index.c 278-319). -/
def hasTypeInfo (id : Id) : Bool :=
  isDataComp id || (isPair id && !isWildcard id && isDataComp (pairFirst id))

inductive Policy | remove | delete | panic
  deriving Repr, BEq, Inhabited, DecidableEq

/-- The loop of `flecs_get_delete_action` over the OnDeleteTarget policies of
    the pairs `(R, tgt)` in a table, in type order: the last one wins unless
    one is Delete. -/
def deleteAction : List Policy → Option Policy
  | [] => none
  | [p] => if p = .delete then some .delete else some p
  | p :: q :: qs => if p = .delete then some .delete else deleteAction (q :: qs)

/-! ### Hook and observer bodies -/

inductive Via | world | stage
  deriving Repr, BEq, Inhabited, DecidableEq
inductive Who | self | slot (i : Nat)
  deriving Repr, BEq, Inhabited, DecidableEq
inductive IdRef | id (x : Id) | pair (r : Id) (t : Who)
  deriving Repr, BEq, Inhabited, DecidableEq
inductive Act where
  | add (v : Via) (w : Who) (x : IdRef)
  | remove (v : Via) (w : Who) (x : IdRef)
  | set (v : Via) (w : Who) (x : IdRef) (val : Nat)
  | delete (v : Via) (w : Who)
  | whenVal (val : Nat) (a : Act)
  deriving Repr, BEq, Inhabited

inductive Ev | onAdd | onSet | onRemove
  deriving Repr, BEq, Inhabited, DecidableEq

/-- Where an observer's term finds its component (round 2): on the entity
    (self), on an ancestor through ChildOf (up), or either (self|up). -/
inductive OSrc | self | up | selfUp
  deriving Repr, BEq, Inhabited, DecidableEq

structure Obs where
  event : Ev
  pattern : Id
  acts : List Act := []
  src : OSrc := .self
  /-- a monitor (`EcsMonitor`): OnAdd when an entity starts matching the
      term, OnRemove when it stops (observer.c 654-773) -/
  monitor : Bool := false
  deriving Repr, Inhabited

structure Hooks where
  onAdd : Option (List Act) := none
  onSet : Option (List Act) := none
  onRemove : Option (List Act) := none
  deriving Repr, Inhabited

structure LogEv where
  hook : Bool
  ev : Ev
  entity : UInt64
  id : Id
  val : Option Nat
  deriving Repr, BEq, Inhabited

/-! ### Storage -/

structure Table where
  type : Array Id
  ents : Array UInt64 := #[]
  count : Nat := 0
  colIds : Array Id := #[]
  cols : Array (Array Nat) := #[]
  lock : Int := 0
  live : Bool := true
  marked : Bool := false
  /-- `table->dirty_state` (table.c 1380-1450): per column + 1 counters,
      allocated on first use by change detection (all 1), NULL before -/
  dirty : Option (Array Int) := none
  deriving Inhabited

structure CR where
  id : Id
  cache : Array Nat := #[]
  refcount : Int := 1
  marked : Bool := false
  deriving Inhabited

/-! ### Commands (commands.h 10-58) -/

inductive CK | add | remove | set | ensure | modified | addModified | delete
  | clear | onDeleteAction | skip
  deriving Repr, BEq, Inhabited, DecidableEq

inductive ERef | inl0 | inl1 | sp (k : UInt64)
  deriving Repr, BEq, Inhabited, DecidableEq

structure Entry where
  first : Int := -1
  last : Nat := 0
  removed : Id := 0
  deriving Repr, Inhabited

structure Cmd where
  kind : CK
  next : Int := 0
  id : Id := 0
  entry : Option ERef := none
  entity : UInt64 := 0
  value : Option Nat := none
  action : Policy := .remove
  /-- oracle only: the command's value came from ecs_set (not ecs_ensure) -/
  fromSet : Bool := false
  deriving Repr, Inhabited

structure Cmds where
  queue : Array Cmd := #[]
  entity : UInt64 := 0
  entry : Entry := {}
  second : UInt64 := 0
  secondEntry : Entry := {}
  lastEntity : UInt64 := 0
  lastEntry : Option ERef := none
  entries : HashMap UInt64 Entry := {}
  hasRemove : Bool := false
  cursor : Nat := 0
  deriving Inhabited

structure Stage where
  levels : Array Cmds := #[{}]
  cur : Nat := 0
  deriving Inhabited

/-- `FLECS_CMD_REMOVED_MANY` (commands.c 8) -/
def REMOVED_MANY : Id := 0xFFFFFFFFFFFFFFFF

structure Marked where
  id : Id
  action : Option Policy
  deleteId : Bool
  deriving Inhabited

/-! ### Queries (query/cache/*.c) -/

inductive QSrc
  /-- `$this`, self -/
  | self
  /-- `$this`, up(ChildOf) -/
  | up
  /-- a fixed source: slot `k` of the program -/
  | fixed (k : Nat)
  deriving Repr, BEq, Inhabited, DecidableEq

inductive QOper | and | not | optional
  deriving Repr, BEq, Inhabited, DecidableEq

inductive QIO | default_ | in_ | out | inout | none
  deriving Repr, BEq, Inhabited, DecidableEq

structure QTerm where
  id : Id
  src : QSrc := .self
  oper : QOper := .and
  io : QIO := .default_
  deriving Repr, BEq, Inhabited

/-- `ecs_query_cache_match_t`: one cached table. -/
structure QMatch where
  table : Nat
  /-- per cache field: column in the table or -1 -/
  columns : Array Int := #[]
  /-- per cache field: 0 ($this) or the source entity -/
  sources : Array UInt64 := #[]
  setFields : Array Bool := #[]
  /-- `_monitor`: [0] for the table, [f+1] per field, -1 untracked -/
  monitor : Option (Array Int) := none
  deriving Repr, Inhabited

/-- `ecs_query_cache_group_t` -/
structure QGroup where
  id : UInt64
  tables : Array QMatch := #[]
  deriving Repr, Inhabited

structure QCache where
  terms : Array QTerm
  detect : Bool := false
  orderBy : Bool := false
  /-- group_by with the default action on this relationship (cache.c 155-172) -/
  groupBy : Option UInt64 := none
  /-- groups in list order (`first_group`, `next`) -/
  groups : Array QGroup := #[]
  matchCount : Int := 0
  prevMatchCount : Int := -1
  /-- `EcsQueryHasChangeDetection` -/
  hasCD : Bool := false
  /-- `impl->monitor` for fixed-source fields; `none` entries were never
      written (flecs_alloc_n does not zero) -/
  fixedMonitor : Option (Array (Option Int)) := none
  /-- `table_slices` for order_by: (table, offset, count) -/
  slices : Array (Nat × Nat × Nat) := #[]
  deriving Inhabited

structure World where
  ix : EIndex := {}
  tables : Array Table := #[{ type := #[] }]
  byType : HashMap (List Id) Nat := {}
  crs : HashMap Id CR := {}
  crOrder : Array Id := #[]
  stages : Array Stage := #[{}]
  readonly : Bool := false
  mt : Bool := false
  hooks : HashMap Id Hooks := {}
  obs : Array Obs := #[]
  nonTrivialSet : HashSet Id := {}
  odt : HashMap UInt64 Policy := {}
  exclusive : HashSet UInt64 := {}
  slots : Array UInt64 := #[]
  log : Array LogEv := #[]
  marked : Array Marked := #[]
  ensureAdd : Option (UInt64 × Array Id) := none
  /-- reads of table storage past the row count (stale memory) -/
  staleReads : Array String := #[]
  /-- oracle violations seen while running -/
  viol : Array String := #[]
  /-- run every queued command on its own (no batching) -/
  noBatch : Bool := false
  /-- handles returned by ecs_entity_range_new, in order -/
  rangeHandles : Array Nat := #[]
  /-- check `has(e, c)` inside on_add hooks -/
  checkHookView : Bool := true
  fuel : Nat := 400
  /-- `world->has_dirty_state` -/
  hasDirty : Bool := false
  /-- query caches (round 2) -/
  queries : Array QCache := #[]
  /-- table events not yet delivered to the query caches: (created?, table) -/
  tableEvents : Array (Bool × Nat) := #[]
  /-- revalidations enqueued by the rematch observers: (query, table) -/
  revalidate : Array (Nat × Nat) := #[]
  /-- oracle (not flecs): per entity and component, a count of the
      documented detectable writes (set, modified, out-iteration) -/
  wver : HashMap (UInt64 × Id) Nat := {}
  /-- oracle: per table, a count of entities added or removed -/
  mver : HashMap Nat Nat := {}
  /-- oracle: what a query read from a table when it last synced it -/
  osnap : HashMap (Nat × Nat) String := {}
  /-- oracle: what a query's fixed-source fields read at the last update of
      its fixed monitor -/
  ofixed : HashMap Nat String := {}
  /-- monitor and up-observer invocations: (observer index, event, entity,
      source) -/
  obsLog : Array (Nat × Ev × UInt64 × UInt64) := #[]
  /-- oracle: per monitor, the entities it has reported as matching -/
  monBelief : HashMap (Nat × UInt64) Bool := {}
  /-- `world->stages[0]->base` (observable.c 1210-1228): set while a prefab
      is instantiated, so instantiation does not recurse through flecs_emit -/
  instantiating : Bool := false
  deriving Inhabited

abbrev M := StateT World (Except Fail)

def fail {α} (c : Code) (site msg : String) : M α := throw ⟨c, site, msg⟩

namespace W

def tick : M Unit := do
  let w ← get
  if w.fuel == 0 then fail .internalError "model" "fuel exhausted (unbounded hook recursion)"
  set { w with fuel := w.fuel - 1 }

def getIx : M EIndex := return (← get).ix
def setIx (ix : EIndex) : M Unit := modify fun w => { w with ix := ix }
def liftE {α} (x : Except Fail α) : M α := match x with
  | .ok a => pure a
  | .error e => throw e

def getRec (e : UInt64) : M Rec := do liftE ((← getIx).get e)
def modRec (e : UInt64) (f : Rec → Rec) : M Unit := do setIx ((← getIx).modRec e f)
def isAlive (e : UInt64) : M Bool := return (← getIx).isAlive e
def isValid (e : UInt64) : M Bool := return (← getIx).isValid e
def getAlive (e : UInt64) : M UInt64 := return (← getIx).getAlive e

def tbl (t : Nat) : M Table := do
  let w ← get
  match w.tables[t]? with
  | some x => if x.live then return x else fail .useAfterFree "storage/table.c" s!"table {t} used after free"
  | none => fail .segfault "storage/table.c" s!"no table {t}"
def setTbl (t : Nat) (x : Table) : M Unit := modify fun w => { w with tables := w.tables.set! t x }
def modTbl (t : Nat) (f : Table → Table) : M Unit := do setTbl t (f (← tbl t))

def tableHas (x : Table) (id : Id) : Bool := x.type.contains id
def colIndex (x : Table) (id : Id) : Option Nat := x.colIds.findIdx? (· == id)

/-! ### Hooks configuration helpers -/

def hooksOf (id : Id) : M Hooks := do
  let w ← get
  let key := if isPair id then pairFirst id else id
  return (w.hooks[key]?).getD {}
def colHasOnAdd (id : Id) : M Bool := return (← hooksOf id).onAdd.isSome
def colHasOnRemove (id : Id) : M Bool := return (← hooksOf id).onRemove.isSome
/-- EcsTableIsComplex: some column has ctor/on_add (HasCtors) or dtor/on_remove
    (HasDtors) hooks (table.c 98-128, api_flags.h 275-276). -/
def isComplex (x : Table) : M Bool := do
  for c in x.colIds do
    if (← colHasOnAdd c) || (← colHasOnRemove c) then return true
  return false
def hasDtors (x : Table) : M Bool := do
  for c in x.colIds do
    if (← colHasOnRemove c) then return true
  return false

def nonTrivialSet (id : Id) : M Bool := return (← get).nonTrivialSet.contains id

def policyOf (rel : UInt64) : M Policy := do
  if rel == EcsChildOf then return .delete
  return ((← get).odt[rel]?).getD .remove
def isExclusive (rel : UInt64) : M Bool := do
  if rel == EcsChildOf then return true
  return (← get).exclusive.contains rel

/-! ### Component records (storage/component_index.c) -/

def crGet (id : Id) : M (Option CR) := return (← get).crs[id]?
def crSet (c : CR) : M Unit := modify fun w => { w with crs := w.crs.insert c.id c }

def addFlag (e : UInt64) (f : Nat) : M Unit := do
  let ix ← getIx
  discard <| liftE (ix.getAny e)
  setIx (ix.modRec e (fun r => { r with flags := r.flags ||| f }))

/-- `flecs_component_new` (component_index.c 401-587), the parts the model
    observes: wildcard records, the alive check of the target, and the
    IsTarget/IsId row flags. -/
partial def crEnsure (id : Id) : M CR := do
  if let some c ← crGet id then return c
  if isPair id then
    let rel := pairFirst id
    let tgt := pairSecond id
    if !isWildcard id then
      discard <| crEnsure (mkPair rel EcsWildcard)
      discard <| crEnsure (mkPair EcsWildcard tgt)
    if tgt != 0 then
      let alive ← getAlive tgt
      if alive == 0 then
        fail .invalidParameter "storage/component_index.c 462-465" s!"target {tgt} of pair is not alive"
      if alive != EcsWildcard then
        addFlag alive FIsTarget
        if rel == EcsChildOf then addFlag alive FIsTraversable
    if rel != EcsWildcard && rel != EcsChildOf then
      let r ← getAlive rel
      addFlag r FIsId
  else
    addFlag (id &&& COMPONENT_MASK) FIsId
  let c : CR := { id }
  crSet c
  modify fun w => { w with crOrder := w.crOrder.push id }
  return c

/-- non-wildcard pair records linked under a wildcard record, in creation
    order (`flecs_component_first_next` / `second_next`). -/
def crChildren (wc : Id) : M (Array Id) := do
  let w ← get
  let f := pairFirst wc
  let s := pairSecond wc
  return w.crOrder.filter fun i =>
    w.crs.contains i && isPair i && !isWildcard i &&
      (if f == EcsWildcard then pairSecond i == s else pairFirst i == f)

/-- `flecs_component_release` + `flecs_component_free` (component_index.c 597-751) -/
partial def crRelease (id : Id) : M Int := do
  let some c ← crGet id | fail .internalError "storage/component_index.c 741" s!"release of freed record {id}"
  let rc := c.refcount - 1
  if rc < 0 then fail .internalError "storage/component_index.c 741-742" "negative refcount"
  crSet { c with refcount := rc }
  if rc == 0 then
    if c.cache.size != 0 then
      fail .internalError "storage/component_index.c 589-595" s!"freeing record {id} with tables"
    if isWildcard id && isPair id then
      for ch in (← crChildren id) do
        discard <| crRelease ch
    modify fun w => { w with crs := w.crs.erase id, crOrder := w.crOrder.filter (· != id) }
  return rc

def crClaim (id : Id) : M Unit := do
  let some c ← crGet id | fail .internalError "storage/component_index.c 729" "claim of missing record"
  crSet { c with refcount := c.refcount + 1 }

/-! ### Tables (storage/table.c, storage/table_graph.c) -/

/-- Records a table registers with (table.c 691-790): its ids, (R, *) per
    relationship and (*, T) per pair. -/
def recordIds (type : Array Id) : Array Id := _root_.Id.run do
  let mut out := #[]
  for i in type do
    out := out.push i
  let mut lastRel : UInt64 := 0
  for i in type do
    if isPair i then
      let r := pairFirst i
      if r != lastRel then
        out := out.push (mkPair r EcsWildcard)
        lastRel := r
      let wt := mkPair EcsWildcard (pairSecond i)
      if !out.contains wt then out := out.push wt
  return out

/-- `flecs_table_ensure` / `flecs_table_new` / `flecs_table_init`. -/
partial def tableEnsure (type : Array Id) : M Nat := do
  if type.size == 0 then return 0
  if let some t := (← get).byType[type.toList]? then return t
  if (← get).readonly then fail .internalError "storage/table_graph.c 523" "table created in readonly mode"
  for i in type do
    discard <| crEnsure i
  let recs := recordIds type
  for i in recs do
    discard <| crEnsure i
  let w ← get
  let t := w.tables.size
  let colIds := type.filter hasTypeInfo
  set { w with tables := w.tables.push { type, colIds, cols := colIds.map (fun _ => #[]) },
               byType := w.byType.insert type.toList t }
  for i in recs do
    let some c ← crGet i | fail .internalError "table.c 812" "missing record"
    crSet { c with cache := c.cache.push t, refcount := c.refcount + 1 }
  -- EcsOnTableCreate (delivered to the query caches, cache.c 552-565)
  modify fun w => { w with tableEvents := w.tableEvents.push (true, t) }
  return t

/-- `flecs_table_fini` (table.c 1268-1344) for an empty table. -/
partial def tableFini (t : Nat) : M Unit := do
  let x ← tbl t
  if x.lock != 0 then fail .lockedStorage "storage/table.c 1277" "table deletion while locked"
  modify fun w => { w with byType := w.byType.erase x.type.toList }
  -- EcsOnTableDelete (cache.c 585-589)
  modify fun w => { w with tableEvents := w.tableEvents.push (false, t) }
  setTbl t { x with live := false }
  for i in recordIds x.type do
    let some c ← crGet i | fail .internalError "storage/table.c 901-923" "record missing on unregister"
    crSet { c with cache := c.cache.filter (· != t) }
    discard <| crRelease i

/-! ### Dirty state (table.c 1380-1450) -/

/-- `flecs_table_mark_table_dirty` (table.c 1382-1394) -/
def markTableDirty (t : Nat) (index : Nat) : M Unit := do
  let w ← get
  match w.tables[t]? with
  | some x =>
    if let some d := x.dirty then
      setTbl t { x with dirty := some (d.modify index (· + 1)) }
  | none => pure ()

/-- oracle: an entity entered or left table `t` -/
def bumpMember (t : Nat) : M Unit := modify fun w =>
  { w with mver := w.mver.insert t ((w.mver[t]?).getD 0 + 1) }

/-- oracle: a detectable write of `id` on `e` -/
def bumpWrite (e : UInt64) (id : Id) : M Unit := modify fun w =>
  { w with wver := w.wver.insert (e, id) ((w.wver[(e, id)]?).getD 0 + 1) }

/-- `flecs_table_mark_dirty` (table.c 1397-1429) -/
def markDirty (t : Nat) (id : Id) : M Unit := do
  let w ← get
  match w.tables[t]? with
  | some x =>
    if let some d := x.dirty then
      match colIndex x id with
      | some c => setTbl t { x with dirty := some (d.modify (c + 1) (· + 1)) }
      | none => pure ()
  | none => pure ()

/-- `flecs_table_get_dirty_state` (table.c 1432-1450) -/
def getDirty (t : Nat) : M (Array Int) := do
  let x ← tbl t
  match x.dirty with
  | some d => return d
  | none =>
    let d := Array.replicate (x.colIds.size + 1) (1 : Int)
    setTbl t { x with dirty := some d }
    modify fun w => { w with hasDirty := true }
    return d

def lockT (t : Nat) : M Unit := do
  if !(← get).readonly then modTbl t fun x => { x with lock := x.lock + 1 }
def unlockT (t : Nat) : M Unit := do
  if !(← get).readonly then modTbl t fun x => { x with lock := x.lock - 1 }

/-- read entity `i` of a table, flagging reads past `count` -/
def tableEnt (t : Nat) (i : Nat) : M UInt64 := do
  let x ← tbl t
  if i >= x.count then
    modify fun w => { w with staleReads := w.staleReads.push s!"entity slot {i} of table {t} (count {x.count})" }
  return x.ents.getD i 0

/-- A component pointer: table, column, row (the C code passes `void*`). -/
structure Ptr where
  t : Nat
  col : Nat
  row : Nat
  deriving Repr, Inhabited, BEq

def readPtr (p : Ptr) : M Nat := do
  let w ← get
  match w.tables[p.t]? with
  | none => fail .segfault "ptr" "bad table"
  | some x =>
    if !x.live then fail .useAfterFree "component pointer" s!"read through pointer into freed table {p.t}"
    if p.row >= x.count then
      modify fun w => { w with staleReads := w.staleReads.push s!"value row {p.row} of table {p.t} (count {x.count})" }
    return (x.cols.getD p.col #[]).getD p.row 0

def writePtr (p : Ptr) (v : Nat) : M Unit := do
  let w ← get
  match w.tables[p.t]? with
  | none => fail .segfault "ptr" "bad table"
  | some x =>
    if !x.live then fail .useAfterFree "component pointer" s!"write through pointer into freed table {p.t}"
    let col := x.cols.getD p.col #[]
    let col := if p.row < col.size then col.set! p.row v else col
    setTbl p.t { x with cols := x.cols.set! p.col col }

end W
end Flecs
