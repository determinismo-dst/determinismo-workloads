/-
  The entity index, transcribed from flecs v4.2.0
  src/storage/entity_index.c (whole file) and src/addons/entity_ranges.c
  (whole file; FLECS_ENTITY_RANGES is on in the default build, flecs.h 231).

  Pages are modelled as a set of allocated page numbers plus a map of records;
  a record that is absent from the map on an allocated page is the zeroed
  record `{dense := 0, table := none, row := 0}` (calloc, entity_index.c 22).
-/
import Std.Data.HashMap
import Std.Data.HashSet
import FlecsLean.Ids

namespace Flecs

/-- Which assert fired.  `INVALID_PARAMETER`/`INVALID_OPERATION` asserts are
    the library rejecting a call; the rest are internal (a bug when reached by
    a call the docs allow). -/
inductive Code where
  | invalidParameter | invalidOperation | internalError | outOfRange
  | constraintViolated | lockedStorage | useAfterFree | segfault
  | alreadyInUse
  deriving Repr, BEq, Inhabited, DecidableEq

structure Fail where
  code : Code
  site : String
  msg : String
  deriving Repr, Inhabited

instance : ToString Fail := ⟨fun f => s!"{repr f.code} at {f.site}: {f.msg}"⟩

/-- `ecs_record_t`.  `row` and the row flags are packed in one uint32 in C
    (api_defines.h 324-329); they are kept apart here. -/
structure Rec where
  dense : Nat := 0
  table : Option Nat := none
  row : Nat := 0
  flags : Nat := 0
  deriving Repr, BEq, Inhabited

/-- Row flags, api_flags.h 42-45 (as small bits). -/
def FIsId : Nat := 1
def FIsTarget : Nat := 2
def FIsTraversable : Nat := 4
def FIsBase : Nat := 8
def hasFlag (fs f : Nat) : Bool := (fs &&& f) != 0

/-- `ecs_entity_range_t` (entity_ranges.h). -/
structure ERange where
  min : UInt64
  max : UInt64
  cur : UInt64
  recycled : Array UInt64 := #[]
  deriving Repr, Inhabited

def PAGE_BITS : UInt64 := 10   -- flecs.h 315

structure EIndex where
  dense : Array UInt64 := #[0]
  recs : Std.HashMap UInt64 Rec := {}
  pages : Std.HashSet UInt64 := {}
  alive : Nat := 1
  maxId : UInt64 := 0
  ranges : Array ERange := #[]   -- by handle (pointer identity)
  sorted : Array Nat := #[]      -- handles sorted by min (index->ranges)
  active : Option Nat := none
  deriving Inhabited

namespace EIndex

def recOf (ix : EIndex) (id : UInt64) : Rec := (ix.recs[lo32 id]?).getD {}
def setRec (ix : EIndex) (id : UInt64) (r : Rec) : EIndex :=
  { ix with recs := ix.recs.insert (lo32 id) r }
def modRec (ix : EIndex) (id : UInt64) (f : Rec → Rec) : EIndex :=
  ix.setRec id (f (ix.recOf id))
def denseAt (ix : EIndex) (i : Nat) : UInt64 := ix.dense.getD i 0
def setDense (ix : EIndex) (i : Nat) (v : UInt64) : EIndex :=
  { ix with dense := ix.dense.set! i v }

/-- entity_index.c 8-27 -/
def ensurePage (ix : EIndex) (id : UInt64) : EIndex :=
  { ix with pages := ix.pages.insert ((lo32 id) >>> PAGE_BITS) }

def hasPage (ix : EIndex) (id : UInt64) : Bool :=
  ix.pages.contains ((lo32 id) >>> PAGE_BITS)

/-- entity_index.c 101-123 -/
def tryGetAny (ix : EIndex) (e : UInt64) : Option Rec :=
  if !ix.hasPage e then none
  else
    let r := ix.recOf e
    if r.dense == 0 then none else some r

/-- entity_index.c 67-79: dereferences the page without checking it. -/
def getAny (ix : EIndex) (e : UInt64) : Except Fail Rec :=
  if !ix.hasPage e then
    .error ⟨.segfault, "storage/entity_index.c 73-75", "page of entity not allocated"⟩
  else
    let r := ix.recOf e
    if r.dense == 0 then
      .error ⟨.invalidParameter, "storage/entity_index.c 76-77", s!"entity {lo32 e} does not exist"⟩
    else .ok r

/-- entity_index.c 125-137 -/
def tryGet (ix : EIndex) (e : UInt64) : Option Rec :=
  match ix.tryGetAny e with
  | none => none
  | some r => if r.dense >= ix.alive || ix.denseAt r.dense != e then none else some r

/-- entity_index.c 81-91 -/
def get (ix : EIndex) (e : UInt64) : Except Fail Rec := do
  let r ← ix.getAny e
  if r.dense >= ix.alive then
    throw ⟨.invalidParameter, "storage/entity_index.c 86-87", "entity is not alive"⟩
  if ix.denseAt r.dense != e then
    throw ⟨.invalidParameter, "storage/entity_index.c 88-89", "mismatching liveness generation for entity"⟩
  return r

def isAlive (ix : EIndex) (e : UInt64) : Bool := (ix.tryGet e).isSome
/-- entity_index.c 249-256 -/
def isValid (ix : EIndex) (e : UInt64) : Bool :=
  match ix.tryGetAny (lo32 e) with
  | none => true
  | some r => r.dense < ix.alive
def exists_ (ix : EIndex) (e : UInt64) : Bool := (ix.tryGetAny e).isSome

/-- entity_index.c 230-240 -/
def getAlive (ix : EIndex) (e : UInt64) : UInt64 :=
  match ix.tryGetAny e with
  | some r => if r.dense < ix.alive then ix.denseAt r.dense else 0
  | none => 0

/-- entity_index.c 220-228 -/
def makeAlive (ix : EIndex) (e : UInt64) : EIndex :=
  match ix.tryGetAny e with
  | some r => ix.setDense r.dense e
  | none => ix

/-! ### Ranges (addons/entity_ranges.c) -/

def rangeContains (r : ERange) (id : UInt64) : Bool :=
  id >= r.min && (r.max == 0 || id <= r.max)

/-- entity_ranges.c 17-37 (binary search over `sorted`). -/
def findRange (ix : EIndex) (id : UInt64) : Option Nat := _root_.Id.run do
  let mut lo : Int := 0
  let mut hi : Int := (ix.sorted.size : Int) - 1
  for _ in [0:64] do
    if lo > hi then return none
    let mid := (lo + hi) / 2
    let h := ix.sorted.getD mid.toNat 0
    let r := ix.ranges.getD h default
    if id < r.min then hi := mid - 1
    else if r.max != 0 && id > r.max then lo := mid + 1
    else return some h
  return none

def activeRange (ix : EIndex) : Option ERange := ix.active.map (fun h => ix.ranges.getD h default)

def modRange (ix : EIndex) (h : Nat) (f : ERange → ERange) : EIndex :=
  { ix with ranges := ix.ranges.modify h f }

/-- entity_ranges.c 39-53 -/
def rangesOnEnsure (ix : EIndex) (id : UInt64) : EIndex :=
  match ix.activeRange with
  | none => { ix with maxId := if id > ix.maxId then id else ix.maxId }
  | some a =>
    if rangeContains a id then { ix with maxId := if id > ix.maxId then id else ix.maxId }
    else match ix.findRange id with
      | some h => ix.modRange h (fun r => { r with cur := if id > r.cur then id else r.cur })
      | none => ix

/-- entity_ranges.c 55-83.  `r` is the (already updated) record of `entity`. -/
def rangesOnDelete (ix : EIndex) (entity : UInt64) : Except Fail EIndex := do
  let id := lo32 entity
  match ix.activeRange with
  | none => return ix
  | some a =>
    if rangeContains a id then return ix
    let last := ix.dense.size - 1
    let rDense := (ix.recOf entity).dense
    let idsLast := ix.denseAt last
    let rl ← ix.getAny idsLast
    let ix := ix.setRec idsLast { rl with dense := rDense }
    let ix := ix.setDense rDense idsLast
    let ix := { ix with dense := ix.dense.extract 0 last }
    let ix := ix.modRec entity (fun r => { r with dense := 0 })
    match ix.findRange id with
    | some h => return ix.modRange h (fun r => { r with recycled := r.recycled.push (genInc entity) })
    | none => return ix

/-- entity_index.c 139-186 -/
def ensure (ix : EIndex) (entity : UInt64) : Except Fail EIndex := do
  let id := lo32 entity
  let mut ix := ix.ensurePage id
  let r := ix.recOf id
  let mut dense := r.dense
  if dense != 0 then
    if dense < ix.alive then
      if ix.denseAt dense != entity then
        throw ⟨.internalError, "storage/entity_index.c 152-154", "alive entity has different generation"⟩
      return ix
  else
    ix := { ix with dense := ix.dense.push entity }
    dense := ix.dense.size - 1
    ix := ix.modRec id (fun r => { r with dense := dense })
    ix := ix.rangesOnEnsure id
  if dense == 0 then throw ⟨.internalError, "storage/entity_index.c 168", "dense is 0"⟩
  -- swap with the first not-alive element
  if ix.alive >= ix.dense.size then
    throw ⟨.useAfterFree, "storage/entity_index.c 172", "read past dense array"⟩
  let eSwap := ix.denseAt ix.alive
  let rSwap ← ix.getAny eSwap
  if rSwap.dense != ix.alive then
    throw ⟨.internalError, "storage/entity_index.c 174-175", "r_swap->dense != alive_count"⟩
  ix := ix.modRec eSwap (fun r => { r with dense := dense })
  ix := ix.modRec id (fun r => { r with dense := ix.alive })
  ix := ix.setDense dense eSwap
  ix := ix.setDense ix.alive entity
  ix := { ix with alive := ix.alive + 1 }
  if !ix.isAlive entity then
    throw ⟨.internalError, "storage/entity_index.c 182-183", "entity not alive after ensure"⟩
  return ix

/-- entity_index.c 188-218 -/
def remove (ix : EIndex) (entity : UInt64) : Except Fail EIndex := do
  match ix.tryGet entity with
  | none => return ix
  | some r =>
    let dense := r.dense
    let iSwap := ix.alive - 1
    let mut ix := { ix with alive := iSwap }
    let eSwap := ix.denseAt iSwap
    let rSwap ← ix.getAny eSwap
    if rSwap.dense != iSwap then
      throw ⟨.internalError, "storage/entity_index.c 203", "r_swap->dense != i_swap"⟩
    ix := ix.modRec eSwap (fun r => { r with dense := dense })
    ix := ix.modRec entity (fun r => { r with table := none, row := 0, flags := 0, dense := iSwap })
    ix := ix.setDense dense eSwap
    ix := ix.setDense iSwap (genInc entity)
    if ix.isAlive entity then
      throw ⟨.internalError, "storage/entity_index.c 212-213", "entity alive after remove"⟩
    ix.rangesOnDelete entity

/-- entity_index.c 265-289 -/
def newIdIntern (ix : EIndex) (dense : Nat) : Except Fail (EIndex × UInt64) := do
  if ix.maxId >= 0xFFFFFFFF then
    throw ⟨.invalidOperation, "storage/entity_index.c 269-271", "entity id overflow"⟩
  let id := ix.maxId + 1
  let ix := { ix with maxId := id }
  if ix.exists_ id then
    throw ⟨.invalidOperation, "storage/entity_index.c 277-279", s!"new entity {id} id already in use"⟩
  match ix.activeRange with
  | some a => if a.max != 0 && id > a.max then
      throw ⟨.outOfRange, "storage/entity_index.c 280-281", s!"new id {id} past active range max {a.max}"⟩
  | none => pure ()
  let ix := ix.setDense dense id
  let ix := (ix.ensurePage id).modRec id (fun r => { r with dense := dense })
  return (ix, id)

/-- entity_index.c 291-302 -/
def newId (ix : EIndex) : Except Fail (EIndex × UInt64) := do
  if ix.alive != ix.dense.size then
    let e := ix.denseAt ix.alive
    return ({ ix with alive := ix.alive + 1 }, e)
  let ix := { ix with dense := ix.dense.push 0 }
  let d := ix.alive
  let ix := { ix with alive := ix.alive + 1 }
  newIdIntern ix d

/-- entity_ranges.c 89-137 -/
def setRange (ix : EIndex) (h : Nat) : Except Fail EIndex := do
  let range := ix.ranges.getD h default
  if ix.findRange range.min != some h then
    throw ⟨.invalidParameter, "addons/entity_ranges.c 85-87", "range was not created with ecs_entity_range_new"⟩
  let alive := ix.alive
  let denseCount := ix.dense.size
  let mut ix := ix
  match ix.active with
  | some p =>
    let saved := ix.dense.extract alive denseCount
    ix := ix.modRange p (fun r => { r with recycled := saved, cur := ix.maxId })
  | none => pure ()
  for i in [alive:denseCount] do
    let e := ix.denseAt i
    discard <| ix.getAny e
    ix := ix.modRec e (fun r => { r with dense := 0 })
  let recycled := (ix.ranges.getD h default).recycled
  ix := { ix with dense := (ix.dense.extract 0 alive) ++ recycled }
  for i in [0:recycled.size] do
    let id := lo32 (recycled.getD i 0)
    ix := ix.ensurePage id
    let r := ix.recOf id
    if r.table.isSome then
      throw ⟨.internalError, "addons/entity_ranges.c 129", s!"recycled id {id} of range is in a table (alive)"⟩
    ix := ix.setRec id { r with dense := alive + i }
  ix := ix.modRange h (fun r => { r with recycled := #[] })
  ix := { ix with maxId := (ix.ranges.getD h default).cur, active := some h }
  return ix

def notAliveCount (ix : EIndex) : Nat := ix.dense.size - ix.alive

/-- entity_ranges.c 175-200: overlap check, registration, sorted insert. -/
def rangeAdd (ix : EIndex) (min max : UInt64) : Except Fail (EIndex × Nat) := do
  for h in ix.sorted do
    let r := ix.ranges.getD h default
    if !(!rangeContains r min && (r.min < min || (max != 0 && r.min > max))) then
      throw ⟨.invalidParameter, "addons/entity_ranges.c 180-184", s!"range [{min}, {max}] overlaps [{r.min}, {r.max}]"⟩
  let h := ix.ranges.size
  let ix := { ix with ranges := ix.ranges.push { min, max, cur := min - 1 } }
  let before := ix.sorted.filter (fun k => (ix.ranges.getD k default).min <= min)
  let after := ix.sorted.filter (fun k => (ix.ranges.getD k default).min > min)
  return ({ ix with sorted := before ++ #[h] ++ after }, h)

/-- entity_ranges.c 139-212.  Returns the new range handle.  The recursive
    call for the default `[1, min - 1]` range (168-173) is unfolded: that call
    has `min = 1`, so it does not recurse again. -/
def rangeNew (ix : EIndex) (min max : UInt64) : Except Fail (EIndex × Nat) := do
  if min == 0 then throw ⟨.invalidParameter, "addons/entity_ranges.c 145", "min must be > 0"⟩
  if !(max == 0 || max >= min) then
    throw ⟨.invalidParameter, "addons/entity_ranges.c 146-147", "max must be >= min or 0"⟩
  if ix.notAliveCount != 0 then
    throw ⟨.invalidOperation, "addons/entity_ranges.c 151-153", "cannot create entity range after entities have been deleted"⟩
  let firstRange := ix.sorted.size == 0
  if firstRange && min == 1 then
    if !(max == 0 || max >= ix.maxId) then
      throw ⟨.invalidOperation, "addons/entity_ranges.c 160-162", "range cannot be below last alive entity id"⟩
  let mut ix := ix
  if firstRange && min > 1 then
    -- ecs_entity_range_new(world, 1, min - 1): first range, min == 1
    if !(min - 1 >= 1) then throw ⟨.invalidParameter, "addons/entity_ranges.c 146-147", "max must be >= min or 0"⟩
    -- (the min == 1 coverage check of the nested call: max = min - 1 >= max_id)
    if !(min - 1 >= ix.maxId) then
      throw ⟨.invalidOperation, "addons/entity_ranges.c 160-162 (nested default range)", "range cannot be below last alive entity id"⟩
    let (ix', dh) ← ix.rangeAdd 1 (min - 1)
    let ix' := ix'.modRange dh (fun r => { r with cur := ix'.maxId })
    let ix'' ← ix'.setRange dh
    -- outer call: 168-173 then sets cur again and activates (already active)
    let ix'' := ix''.modRange dh (fun r => { r with cur := ix.maxId })
    ix ← ix''.setRange dh
  let (ix', h) ← ix.rangeAdd min max
  ix := ix'
  if firstRange && min == 1 then
    ix := ix.modRange h (fun r => { r with cur := ix.maxId })
    ix ← ix.setRange h
  return (ix, h)

end EIndex
end Flecs
