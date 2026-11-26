/-
  Cached queries, their table matching, grouping, sorting and change
  detection, transcribed from flecs v4.2.0 src/query/cache/{cache.c,
  match.c, group.c, order_by.c, change_detection.c, cache_iter.c} and the
  iterator glue in src/query/engine/eval_iter.c 217-680.

  Query shapes: `$this` terms with self source (And, Not, Optional), `$this`
  terms with up(ChildOf) source (And), and terms with a fixed source (And),
  which are not cached and are evaluated before the cached terms
  (query/compiler/compiler.c 1116-1117).  Every query is created with
  `cache_kind = EcsQueryCacheAuto`.  Options: `EcsQueryDetectChanges`,
  `order_by` on C0 with a callback comparing values, `group_by` a
  relationship with the default action.

  Fields: the cached terms come first in the term list, so cache field `f` is
  query field `f` (an identity `field_map`); fixed terms follow.
-/
import FlecsLean.Ops

namespace Flecs
open Std

namespace W

def qSet (qi : Nat) (q : QCache) : M Unit := modify fun w => { w with queries := w.queries.set! qi q }

def isData (id : Id) : Bool := hasTypeInfo id

/-- `EcsQueryTrivialCache` (cache.c 755-778): only self terms with And, Not
    or Optional, no fixed terms, no order_by/group_by/DetectChanges. -/
def isTrivial (q : QCache) : Bool :=
  !q.detect && !q.orderBy && q.groupBy.isNone && q.terms.all (fun t => t.src == .self)

/-- `ecs_search_relation` with `up(ChildOf)` (no self): the first ancestor
    whose table has `id` (search.c, trav_up_cache.c). -/
partial def upSrc (t : Nat) (id : Id) (depth : Nat := 0) : M (Option UInt64) := do
  if depth > 64 then fail .internalError "model" "ChildOf cycle"
  let x ← tbl t
  match x.type.find? (fun i => isPair i && pairFirst i == EcsChildOf) with
  | none => return none
  | some pr =>
    let p ← getAlive (pairSecond pr)
    if p == 0 then return none
    match ((← getIx).recOf p).table with
    | none => return none
    | some pt =>
      let px ← tbl pt
      if px.type.contains id then return some p
      upSrc pt id (depth + 1)

/-- Evaluate the cache query on a table (the uncached query the cache uses
    to populate itself, cache.c 211-256): the fields of the match, or none.
    Round 4: a self term for a wildcard pair `(R, *)` yields one result per
    matching pair of the table, in type order (match.c 174-208); the first
    is the match, the others its `wildcard_matches`. -/
def evalMatch (q : QCache) (t : Nat) : M (Option QMatch) := do
  let x ← tbl t
  let mut cols : Array Int := #[]
  let mut srcs : Array UInt64 := #[]
  let mut sets : Array Bool := #[]
  let mut pairs : Array Id := #[]
  for term in cachedTerms q do
    if isPair term.id && isWildcard term.id && term.src == .self && term.oper == .and then
      pairs := x.type.filter (fun i => idMatch i term.id)
      if pairs.isEmpty then return none
      cols := cols.push (-1); srcs := srcs.push 0; sets := sets.push true
      continue
    let has := x.type.contains term.id
    match term.src, term.oper with
    | .self, .and =>
      if !has then return none
      cols := cols.push (match colIndex x term.id with | some c => (c : Int) | none => -1)
      srcs := srcs.push 0
      sets := sets.push true
    | .self, .not =>
      if has then return none
      cols := cols.push (-1); srcs := srcs.push 0; sets := sets.push false
    | .self, .optional =>
      cols := cols.push (if has then (match colIndex x term.id with | some c => (c : Int) | none => -1) else -1)
      srcs := srcs.push 0
      sets := sets.push has
    | .up, .optional =>
      -- round 5: `?C(up)` (the cascade term of flecs's Cascade tests)
      match (← upSrc t term.id) with
      | none => cols := cols.push (-1); srcs := srcs.push 0; sets := sets.push false
      | some p => cols := cols.push (-1); srcs := srcs.push p; sets := sets.push true
    | .up, _ =>
      match (← upSrc t term.id) with
      | none => return none
      | some p =>
        cols := cols.push (-1); srcs := srcs.push p; sets := sets.push true
    | .fixed _, _ => pure ()
  return some { table := t, columns := cols, sources := srcs, setFields := sets,
                pair := pairs.getD 0 0, wildPairs := pairs.extract 1 pairs.size }

/-- A new `wildcard_matches` vector (flecs_alloc_t + ecs_vec_init,
    match.c 200-203 and 271-275). -/
def newVec : M Nat := do
  let w ← get
  set { w with vecNext := w.vecNext + 1 }
  return w.vecNext

/-- `flecs_free_t(a, ecs_vec_t, wildcard_matches)` (match.c 63-64, 256-257). -/
def freeVec (v : Nat) : M Unit := do
  if v == 0 then return
  modify fun w => { w with vecFreed := w.vecFreed.push v }

/-! ### Groups (group.c) -/

/-- The ChildOf depth of a table (`flecs_relation_depth`, search.c 517-553:
    the `depth` of its `(ChildOf, P)` record, which is P's depth + 1,
    component_index.c 1188-1231; 0 for a root). -/
partial def childOfDepth (t : Nat) (fuel : Nat := 64) : M Nat := do
  if fuel == 0 then fail .internalError "model" "ChildOf cycle"
  let x ← tbl t
  match x.type.find? (fun i => isPair i && pairFirst i == EcsChildOf) with
  | none => return 0
  | some pr =>
    let p ← getAlive (pairSecond pr)
    if p == 0 then return 0
    match ((← getIx).recOf p).table with
    | none => return 1
    | some pt => return (← childOfDepth pt (fuel - 1)) + 1

/-- default group_by action (cache.c 159-177): target of the first
    (R, *) pair in the table type; round 5: the cascade action
    (cache.c 179-191) -/
def groupIdOf (q : QCache) (t : Nat) : M UInt64 := do
  if q.cascade then return (← childOfDepth t).toUInt64
  match q.groupBy with
  | none => return 0
  | some r =>
    let x ← tbl t
    match x.type.find? (fun i => isPair i && pairFirst i == r) with
    | some pr => return (← getAlive (pairSecond pr))
    | none => return 0

def findTable (q : QCache) (t : Nat) : Option (Nat × Nat) := Id.run do
  for gi in [0:q.groups.size] do
    let g := q.groups.getD gi default
    for mi in [0:g.tables.size] do
      if (g.tables.getD mi default).table == t then return some (gi, mi)
  return none

/-- `flecs_query_cache_ensure_group` + `flecs_query_cache_group_insert`
    (group.c 37-82): a new group goes to the head of the list unless the
    query is ordered (cascade): then before the first group with a larger
    id.  Round 5: a new non-default group is a new allocation (a new
    identity); the default group is `&cache->default_group` (identity 0),
    re-initialized and inserted again after it was removed (59-79). -/
def ensureGroup (q : QCache) (gid : UInt64) : M (QCache × Nat) := do
  for gi in [0:q.groups.size] do
    if (q.groups.getD gi default).id == gid then return (q, gi)
  let uid ← if gid == 0 then pure 0 else newVec
  let g : QGroup := { id := gid, uid }
  if q.cascade then
    -- round 6: descending order (group.c 41-48) for EcsDesc
    let pos := (q.groups.findIdx? (fun h => if q.cascadeDesc then h.id < gid else h.id > gid)).getD q.groups.size
    return ({ q with groups := (q.groups.extract 0 pos).push g ++ q.groups.extract pos q.groups.size }, pos)
  return ({ q with groups := #[g] ++ q.groups }, 0)

def nextPow2 (n : Nat) : Nat := Id.run do
  let mut k := 1
  for _ in [0:40] do
    if k ≥ n then return k
    k := 2 * k
  return k

/-- `ecs_vec_append` on a group's `tables` (group.c 157-158; vec.c
    366-379, 179-215): when the array is full it is reallocated
    (`flecs_brealloc` frees the old chunk, block_allocator.c 287-326). -/
def pushMatch (g : QGroup) (m : QMatch) : M QGroup := do
  if g.tables.size == g.cap then
    let cap := max 2 (nextPow2 (g.tables.size + 1))
    freeVec g.arr
    let arr ← newVec
    return { g with tables := g.tables.push m, cap, arr }
  return { g with tables := g.tables.push m }

/-- `flecs_query_cache_add_table` (group.c 216-245) -/
def addTable (qi : Nat) (m : QMatch) : M Unit := do
  let m ← if m.wildPairs.isEmpty then pure m else do pure { m with wildVec := (← newVec) }
  let q ← qGet qi
  let gid ← groupIdOf q m.table
  let (q, gi) ← ensureGroup q gid
  let g ← pushMatch (q.groups.getD gi default) m
  let q := { q with groups := q.groups.set! gi g, matchCount := q.matchCount + 1 }
  qSet qi q

/-- `flecs_query_cache_remove_table_from_group` (group.c 176-213): the last
    table moves into the hole (ecs_vec_remove); an empty group is removed
    (`flecs_query_cache_remove_group`, 118-130: unlinked, its array freed
    by ecs_vec_fini, and a non-default group freed by
    ecs_map_remove_free). -/
def removeFromGroup (q : QCache) (gi mi : Nat) : M QCache := do
  let q := { q with matchCount := q.matchCount + 1 }
  let g := q.groups.getD gi default
  let n := g.tables.size
  let ts := if mi + 1 == n then g.tables.pop else (g.tables.set! mi (g.tables.getD (n - 1) default)).pop
  if ts.isEmpty then
    freeVec g.arr
    return { q with groups := q.groups.eraseIdx! gi }
  return { q with groups := q.groups.set! gi { g with tables := ts } }

/-- `flecs_query_cache_remove_table` (group.c 302-329) -/
def removeTable (qi : Nat) (t : Nat) : M Unit := do
  let q ← qGet qi
  match findTable q t with
  | none => pure ()
  | some (gi, mi) =>
    -- flecs_query_cache_match_fini (match.c 48-67) frees wildcard_matches
    freeVec ((q.groups.getD gi default).tables.getD mi default).wildVec
    qSet qi (← removeFromGroup q gi mi)

/-- `flecs_query_cache_ensure_table` + rematch overwrite (group.c 277-299,
    match.c 212-286): the match keeps its monitor. -/
def rematchTable (qi : Nat) (m : QMatch) : M Unit := do
  let q ← qGet qi
  match findTable q m.table with
  | none => addTable qi m
  | some (gi, mi) =>
    let old := (q.groups.getD gi default).tables.getD mi default
    -- flecs_query_cache_rematch_next (match.c 212-286): existing entries
    -- are overwritten; superfluous ones are freed, and the vector itself
    -- when no further result remains (255-258); a missing vector is
    -- allocated (271-275)
    let vec ← if m.wildPairs.isEmpty then do freeVec old.wildVec; pure 0
      else if old.wildVec == 0 then newVec else pure old.wildVec
    let m := { m with monitor := old.monitor, wildVec := vec }
    let gid ← groupIdOf q m.table
    if gid == (q.groups.getD gi default).id then
      qSet qi { q with groups := q.groups.modify gi (fun g => { g with tables := g.tables.set! mi m }) }
    else
      -- flecs_query_cache_move_table_to_group (group.c 249-274): append to
      -- the destination group, then remove from the source group
      let srcUid := (q.groups.getD gi default).uid
      let (q2, gdst) ← ensureGroup q gid
      let g ← pushMatch (q2.groups.getD gdst default) m
      let q2 := { q2 with groups := q2.groups.set! gdst g, matchCount := q2.matchCount + 1 }
      let gsrc := (q2.groups.findIdx? (fun h => h.uid == srcUid && h.id == (q.groups.getD gi default).id)).getD gi
      qSet qi (← removeFromGroup q2 gsrc mi)

/-- `flecs_query_revalidate_table` (match.c 328-365) -/
def revalidateTable (qi : Nat) (t : Nat) : M Unit := do
  let w ← get
  match w.tables[t]? with
  | none => pure ()
  | some x =>
    if !x.live then return
    let q ← qGet qi
    qSet qi { q with matchCount := q.matchCount + 1 }
    -- flecs_query_rematch_table (match.c 288-326)
    match (← evalMatch (← qGet qi) t) with
    | none => removeTable qi t
    | some m => rematchTable qi m

/-- Deliver pending table events and revalidations to the caches
    (cache.c 547-606 on_event; the revalidate events are enqueued on stage 0
    and run when the command queue is flushed). -/
def drainQueryEvents : M Unit := do
  for _ in [0:1000] do
    let w ← get
    if w.tableEvents.isEmpty && w.revalidate.isEmpty then return
    let evs := w.tableEvents
    let revs := w.revalidate
    set { w with tableEvents := #[], revalidate := #[] }
    for (created, t) in evs do
      for qi in [0:(← get).queries.size] do
        if created then
          let q ← qGet qi
          let live := ((← get).tables.getD t default).live
          if !live then
            -- created and freed within the same call: flecs matched it at
            -- creation and removed it at deletion (two match_count bumps);
            -- the model evaluates it on its type as it was
            let w0 ← get
            setTbl t { (w0.tables.getD t default) with live := true }
            let r ← evalMatch q t
            setTbl t { ((← get).tables.getD t default) with live := false }
            if r.isSome then qSet qi { q with matchCount := q.matchCount + 2 }
          else if (findTable q t).isNone then
            if let some m ← evalMatch q t then addTable qi m
        else removeTable qi t
    for (qi, t) in revs do revalidateTable qi t

/-- Read fields with a fixed source (`q->read_fields & q->fixed_fields`). -/
def fixedReadFields (q : QCache) : Array (Nat × QTerm × Nat) := Id.run do
  let mut out := #[]
  for f in [0:q.terms.size] do
    let t := q.terms.getD f default
    match t.src with
    | .fixed k =>
      if t.io != .out && t.io != .none && t.oper != .not && isData t.id then out := out.push (f, t, k)
    | _ => pure ()
  return out

/-! ### The oracle for change detection (not flecs)

Queries.md "Change Detection": detected are adding or removing components
(entities entering or leaving a table), deleting entities, `set`,
`modified`, and iterating with `out`/`inout` terms without skipping; not
detected are writes through `ensure` without `modified`.  "A query with
change detection enabled will only report a change for the components it
matched with, or when an entity got added/removed to a matched table."  "When
a change occurred in a table matching a query, the query state for that table
will remain changed until the table is iterated by the query."

So the state a query depends on for a table is: the entities that entered or
left it, and the detected writes of each component the query reads, on the
table's entities or on the source entity of a field (up or fixed source).
The oracle records that state when the query syncs the table and compares. -/

def readIO (io : QIO) : Bool := io == .in_ || io == .inout || io == .default_

def readSelf (t : QTerm) : Bool := t.src == .self && readIO t.io && isData t.id && t.oper != .not

def oracleState (qi t : Nat) : M String := do
  let q ← qGet qi
  let w ← get
  let x ← tbl t
  let ents := x.ents.extract 0 x.count
  let mut parts : Array String := #[s!"m{(w.mver[t]?).getD 0}"]
  for term in cachedTerms q do
    if readSelf term then
      for e in ents do parts := parts.push s!"{e}/{term.id}:{(w.wver[(e, term.id)]?).getD 0}"
    else if term.src == .up && readIO term.io && isData term.id then
      match (← upSrc t term.id) with
      | some p => parts := parts.push s!"up {p}/{term.id}:{(w.wver[(p, term.id)]?).getD 0}"
      | none => parts := parts.push "up none"
  return ",".intercalate parts.toList

def oracleFixedState (qi : Nat) : M String := do
  let q ← qGet qi
  let w ← get
  let mut parts : Array String := #[]
  for (_, term, k) in fixedReadFields q do
    let src := w.slots.getD k 0
    if (← has src term.id) then
      parts := parts.push s!"{src}/{term.id}:{(w.wver[(src, term.id)]?).getD 0}"
  return ",".intercalate parts.toList

def oracleSync (qi t : Nat) : M Unit := do
  if (← get).iterQuiet then return
  let s ← oracleState qi t
  modify fun w => { w with osnap := w.osnap.insert (qi, t) s }

def oracleFixedSync (qi : Nat) : M Unit := do
  if (← get).iterQuiet then return
  let s ← oracleFixedState qi
  modify fun w => { w with ofixed := w.ofixed.insert qi s }

/-- Expected ecs_iter_changed for a table: never synced, or the state
    differs (the fixed part is checked separately). -/
def oracleChanged (qi t : Nat) : M Bool := do
  let s ← oracleState qi t
  match (← get).osnap[(qi, t)]? with
  | none => return true
  | some s0 => return s0 != s

def oracleFixedChanged (qi : Nat) : M Bool := do
  match (← get).ofixed[qi]? with
  | none => return false
  | some s0 => return s0 != (← oracleFixedState qi)

def noteViol (msg : String) : M Unit := modify fun w => { w with viol := w.viol.push msg }

/-! ### Change detection (change_detection.c) -/

def setMatch (qi : Nat) (t : Nat) (f : QMatch → QMatch) : M Unit := do
  let q ← qGet qi
  match findTable q t with
  | none => pure ()
  | some (gi, mi) =>
    qSet qi { q with groups := q.groups.modify gi (fun g => { g with tables := g.tables.modify mi f }) }

def getMatch (qi t : Nat) : M (Option QMatch) := do
  let q ← qGet qi
  match findTable q t with
  | none => return none
  | some (gi, mi) => return some ((q.groups.getD gi default).tables.getD mi default)

/-- `flecs_query_get_column_for_field` (change_detection.c 30-75) -/
def columnForField (q : QCache) (m : QMatch) (f : Nat) : M (Option (Nat × Int)) := do
  let col := m.columns.getD f (-1)
  if col != -1 then return some (m.table, col)
  let src := m.sources.getD f 0
  if src == 0 then return none
  let r := (← getIx).recOf src
  match r.table with
  | none => return none
  | some st =>
    let x ← tbl st
    let id := ((cachedTerms q).getD f default).id
    if !x.type.contains id then return none
    return some (st, match colIndex x id with | some c => (c : Int) | none => -1)

/-- `flecs_query_get_match_monitor` (change_detection.c 79-138): returns
    true when it created the monitor. -/
def getMatchMonitor (qi t : Nat) : M Bool := do
  let q ← qGet qi
  if isTrivial q then
    fail .invalidOperation "change_detection.c 87-89" "query was not created with change detection enabled"
  let some m ← getMatch qi t | return false
  if m.monitor.isSome then return false
  let ts := cachedTerms q
  let mut mon : Array Int := #[0]
  for f in [0:ts.size] do
    let term := ts.getD f default
    let mut v : Int := -1
    if readIO term.io && m.setFields.getD f false then
      match (← columnForField q m f) with
      | some (_, c) => if c != -1 then v := 0
      | none => pure ()
    mon := mon.push v
  setMatch qi t (fun m => { m with monitor := some mon })
  qSet qi { (← qGet qi) with hasCD := true }
  return true

/-- `flecs_query_check_match_monitor` (change_detection.c 329-419) -/
def checkMatchMonitor (qi t : Nat) : M Bool := do
  if (← getMatchMonitor qi t) then return true
  let q ← qGet qi
  let some m ← getMatch qi t | return false
  let some mon := m.monitor | return false
  let dirty ← getDirty t
  if mon.getD 0 0 != dirty.getD 0 0 then return true
  for f in [0:(cachedTerms q).size] do
    let mv := mon.getD (f + 1) (-1)
    if mv == -1 then continue
    if !m.setFields.getD f false then continue
    let col := m.columns.getD f (-1)
    let src := m.sources.getD f 0
    if src == 0 then
      if col >= 0 then
        if mv != dirty.getD (col.toNat + 1) 0 then return true
      continue
    match (← columnForField q m f) with
    | none => continue
    | some (st, c) =>
      if c < 0 then continue
      let sd ← getDirty st
      if mv != sd.getD (c.toNat + 1) 0 then return true
  return false

/-- `flecs_query_check_match_monitor_term` (change_detection.c 218-259);
    `field` 0 is the table, `f + 1` field `f`. -/
def checkMatchMonitorTerm (qi t field : Nat) : M Bool := do
  if (← getMatchMonitor qi t) then return true
  let q ← qGet qi
  let some m ← getMatch qi t | return false
  let some mon := m.monitor | return false
  let state := mon.getD field (-1)
  if state == -1 then return false
  let dirty ← getDirty t
  if field == 0 then return mon.getD 0 0 != dirty.getD 0 0
  match (← columnForField q m (field - 1)) with
  | none => fail .internalError "change_detection.c 251" "cur.column != -1"
  | some (st, c) =>
    let sd ← getDirty st
    return state != sd.getD (c.toNat + 1) 0

/-- `flecs_query_sync_match_monitor` (change_detection.c 581-633) -/
def syncMatchMonitor (qi t : Nat) : M Unit := do
  let some m ← getMatch qi t | return
  if m.monitor.isNone then
    if (← qGet qi).hasCD then discard <| getMatchMonitor qi t
    else return
  let q ← qGet qi
  let some m ← getMatch qi t | return
  let some mon := m.monitor | return
  let dirty ← getDirty t
  let mut mon := mon.set! 0 (dirty.getD 0 0)
  for f in [0:(cachedTerms q).size] do
    if mon.getD (f + 1) (-1) == -1 then continue
    match (← columnForField q m f) with
    | none => continue
    | some (st, c) =>
      let sd ← getDirty st
      mon := mon.set! (f + 1) (sd.getD ((c + 1).toNat) 0)
  setMatch qi t (fun m => { m with monitor := some mon })
  let q ← qGet qi
  qSet qi { q with prevMatchCount := q.matchCount }

/-- `flecs_query_get_fixed_monitor` (change_detection.c 142-201).  A field
    the loop skips is never written: reading it later is a read of
    uninitialized memory (recorded as a violation, the model answers
    "changed"). -/
def getFixedMonitor (qi : Nat) (check : Bool) : M Bool := do
  let q ← qGet qi
  let mut check := check
  let mut mon := match q.fixedMonitor with
    | some mo => mo
    | none => Array.replicate q.terms.size none
  if q.fixedMonitor.isNone then check := false
  let slots := (← get).slots
  for (f, term, k) in fixedReadFields q do
    let src := slots.getD k 0
    let r := (← getIx).recOf src
    let some st := r.table | continue
    if (← crGet term.id).isNone then continue
    let x ← tbl st
    if !x.type.contains term.id then continue
    let d ← getDirty st
    let c := match colIndex x term.id with | some c => c + 1 | none => 0
    if !check then mon := mon.set! f (some (d.getD c 0))
    else
      match mon.getD f none with
      | none =>
        modify fun w => { w with viol := w.viol.push s!"uninit: query {qi} compares the fixed-source monitor of field {f}, which was never written (change_detection.c 184, 194)" }
        qSet qi { (← qGet qi) with fixedMonitor := some mon }
        return true
      | some v => if v != d.getD c 0 then
          qSet qi { (← qGet qi) with fixedMonitor := some mon }
          return true
  qSet qi { (← qGet qi) with fixedMonitor := some mon }
  return !check

/-- `flecs_query_check_cache_monitor` (change_detection.c 262-298) -/
def checkCacheMonitor (qi : Nat) : M Bool := do
  let q ← qGet qi
  if q.matchCount != q.prevMatchCount then return true
  for g in q.groups do
    for m in g.tables do
      if (← checkMatchMonitor qi m.table) then return true
  return false

/-- `ecs_query_changed` (change_detection.c 636-673) -/
def queryChanged (qi : Nat) : M Bool := do
  let q ← qGet qi
  if !(fixedReadFields q).isEmpty then
    if q.fixedMonitor.isNone then
      discard <| getFixedMonitor qi false
      oracleFixedSync qi
  if (← qGet qi).fixedMonitor.isSome then
    if (← getFixedMonitor qi true) then return true
  if !(← qGet qi).hasCD then
    for g in (← qGet qi).groups do
      for m in g.tables do discard <| getMatchMonitor qi m.table
  checkCacheMonitor qi

/-- Write fields (query/validator.c 1167-1182: data fields with inout != In,
    not Not). -/
def isWriteField (t : QTerm) : Bool :=
  isData t.id && t.oper != .not && t.io != .in_ && t.io != .none

/-- `flecs_query_mark_fields_dirty` (change_detection.c 464-527) for one
    result; the oracle counts the write. -/
def markFieldsDirty (qi : Nat) (t : Nat) (m : QMatch) (ents : Array UInt64) : M Unit := do
  -- change_detection.c 478-480: nothing is marked for EcsIterNoData
  if (← get).iterNoData then return
  let q ← qGet qi
  let ts := cachedTerms q
  let hasDirty := (← get).hasDirty
  for f in [0:ts.size] do
    let term := ts.getD f default
    if !isWriteField term || !m.setFields.getD f false then continue
    let src := m.sources.getD f 0
    if src == 0 then
      for e in ents do bumpWrite e term.id
      if hasDirty then
        let x ← tbl t
        if let some c := colIndex x term.id then
          if x.dirty.isSome then markTableDirty t (c + 1)
    else
      -- shared fields that aren't marked explicitly as out/inout are readonly
      if term.io == .default_ then continue
      bumpWrite src term.id
      if hasDirty then
        match ((← getIx).recOf src).table with
        | none => pure ()
        | some st =>
          let x ← tbl st
          if let some c := colIndex x term.id then
            if x.dirty.isSome then markTableDirty st (c + 1)

/-- `flecs_query_mark_fixed_fields_dirty` (change_detection.c 530-578) -/
def markFixedFieldsDirty (qi : Nat) : M Unit := do
  let q ← qGet qi
  let slots := (← get).slots
  for f in [0:q.terms.size] do
    let term := q.terms.getD f default
    match term.src with
    | .fixed k =>
      if !isWriteField term then continue
      let src := slots.getD k 0
      if (← has src term.id) then bumpWrite src term.id
      if !(← get).hasDirty then continue
      match ((← getIx).recOf src).table with
      | none => pure ()
      | some st =>
        let x ← tbl st
        if let some c := colIndex x term.id then
          if x.dirty.isSome then markTableDirty st (c + 1)
    | _ => pure ()

/-! ### Sorting (order_by.c) -/

def valOf (t : Nat) (row : Nat) : M Nat := do
  let x ← tbl t
  match colIndex x C0 with
  | some c => return (x.cols.getD c #[]).getD row 0
  | none => return 0

/-- `flecs_table_swap` (table.c 2018-2090) -/
def tableSwap (t : Nat) (r1 r2 : Nat) : M Unit := do
  let x ← tbl t
  if x.lock != 0 then fail .lockedStorage "storage/table.c 2025" "table swap on locked table"
  if r1 == r2 then return
  markTableDirty t 0
  let x ← tbl t
  let e1 := x.ents.getD r1 0
  let e2 := x.ents.getD r2 0
  modRec e1 (fun r => { r with row := r2 })
  modRec e2 (fun r => { r with row := r1 })
  let ents := (x.ents.set! r1 e2).set! r2 e1
  let cols := x.cols.map (fun c => (c.set! r1 (c.getD r2 0)).set! r2 (c.getD r1 0))
  setTbl t { x with ents, cols }

def cmp (a b : Nat) : Int := if a < b then -1 else if a > b then 1 else 0

/-- `ECS_SORT_TABLE_WITH_COMPARE` partition (flecs_c.h 795-835): Hoare
    partition with the pivot followed across swaps. -/
partial def partition (t : Nat) (lo hi : Nat) : M Nat := do
  let p := (hi + lo) / 2
  let mut pivotRow := p
  let mut i : Int := lo - 1
  let mut j : Int := hi + 1
  for _ in [0:10000] do
    repeat
      i := i + 1
      if cmp (← valOf t i.toNat) (← valOf t pivotRow) >= 0 then break
    repeat
      j := j - 1
      if cmp (← valOf t j.toNat) (← valOf t pivotRow) <= 0 then break
    if i >= j then return j.toNat
    tableSwap t i.toNat j.toNat
    if p == i.toNat then pivotRow := j.toNat
    else if p == j.toNat then pivotRow := i.toNat
  fail .internalError "model" "partition did not terminate"

partial def quicksort (t : Nat) (lo hi : Nat) : M Unit := do
  if hi ≤ lo then return
  let p ← partition t lo hi
  quicksort t lo p
  quicksort t (p + 1) hi

/-- `flecs_query_cache_build_sorted_table_range` + `build_sorted_tables`
    (order_by.c 81-226): merge the sorted tables into slices. -/
def buildSlices (qi : Nat) : M Unit := do
  let q ← qGet qi
  let mut slices : Array (Nat × Nat × Nat) := #[]
  for g in q.groups do
    -- helpers for non-empty tables, in group order
    let mut hs : Array (Nat × Nat × Nat) := #[]   -- (table, row, count)
    for m in g.tables do
      let x ← tbl m.table
      if x.count != 0 then hs := hs.push (m.table, 0, x.count)
    if hs.isEmpty then continue
    let mut cur : Option Nat := none   -- index into slices of the open slice
    let mut curTable : Option Nat := none
    for _ in [0:100000] do
      let mut minI : Option Nat := none
      for k in [0:hs.size] do
        let (t, row, cnt) := hs.getD k default
        if row >= cnt then continue
        match minI with
        | none => minI := some k
        | some mk =>
          let (mt, mrow, _) := hs.getD mk default
          if cmp (← valOf mt mrow) (← valOf t row) > 0 then minI := some k
      match minI with
      | none => break
      | some mk =>
        let (t, row, cnt) := hs.getD mk default
        if curTable == some t then
          let ci := cur.getD 0
          slices := slices.modify ci (fun (a, b, c) => (a, b, c + 1))
        else
          slices := slices.push (t, row, 1)
          cur := some (slices.size - 1)
          curTable := some t
        hs := hs.set! mk (t, row + 1, cnt)
  qSet qi { (← qGet qi) with slices }

/-- `flecs_query_cache_sort_tables` (order_by.c 228-319) -/
def sortTables (qi : Nat) : M Unit := do
  let q ← qGet qi
  let mut tablesSorted := false
  let field := ((cachedTerms q).findIdx? (fun t => t.id == C0 && t.oper == .and)).getD 0
  for g in q.groups do
    for m in g.tables do
      let t := m.table
      let mut dirty := false
      if (← checkMatchMonitorTerm qi t 0) then
        tablesSorted := true
        dirty := true
        if (← tbl t).count == 0 then
          syncMatchMonitor qi t
          oracleSync qi t
      if (← checkMatchMonitorTerm qi t (field + 1)) then dirty := true
      if dirty then
        let x ← tbl t
        if (colIndex x C0).isNone then
          dirty := false
          tablesSorted := true
      if !dirty then continue
      let x ← tbl t
      if x.count ≥ 2 then quicksort t 0 (x.count - 1)
      tablesSorted := true
  let q ← qGet qi
  if tablesSorted || q.matchCount != q.prevMatchCount then
    buildSlices qi
    qSet qi { (← qGet qi) with matchCount := (← qGet qi).matchCount + 1 }

/-! ### Iteration (cache_iter.c, eval_iter.c 454-680) -/

/-- One yielded result: table, rows, entities, the value of each field per
    entity (none for fields without data), and what ecs_iter_changed said. -/
structure QResult where
  table : Nat
  offset : Nat
  count : Nat
  ents : Array UInt64
  vals : Array (Array (Option Nat))
  changed : Bool
  deriving Repr, Inhabited, BEq

inductive IterMode | full | skipAll | first
  deriving Repr, BEq, Inhabited, DecidableEq

def fieldVals (q : QCache) (m : QMatch) (row cnt : Nat) : M (Array (Array (Option Nat))) := do
  let ts := q.terms
  let x ← tbl m.table
  let slots := (← get).slots
  let mut out := #[]
  for i in [0:cnt] do
    let mut vs := #[]
    for f in [0:ts.size] do
      let term := ts.getD f default
      if !isData term.id then vs := vs.push none; continue
      match term.src with
      | .self =>
        match colIndex x term.id with
        | some c => vs := vs.push ((x.cols.getD c #[])[row + i]?)
        | none => vs := vs.push none
      | .up =>
        let src := m.sources.getD f 0
        vs := vs.push (← getVal src term.id)
      | .fixed k => vs := vs.push (← getVal (slots.getD k 0) term.id)
    out := out.push vs
  return out

/-- Run an iterator to the end (or after the first result), as
    `ecs_query_iter` + `ecs_query_next` loop.  `skip` calls ecs_iter_skip on
    every result; `askChanged` calls ecs_iter_changed on every result. -/
def iterate (qi : Nat) (mode : IterMode) (ask : Bool) : M (Array QResult) := do
  -- flecs_query_cache_iter_init (cache_iter.c 11-37)
  if (← qGet qi).orderBy then sortTables qi
  let q ← qGet qi
  qSet qi { q with prevMatchCount := q.matchCount }
  let q ← qGet qi
  -- round 3 oracle: a user iteration (any mode) sees the cache's tables
  if !(← get).iterQuiet then
    let ts := q.groups.foldl (fun acc g => acc ++ g.tables.toList.map (·.table)) []
    modify fun w => { w with ouser := w.ouser.insert qi ts }
  -- fixed-source terms are evaluated first; if one fails nothing is yielded
  let slots := (← get).slots
  let mut fixedOk := true
  for t in q.terms do
    match t.src with
    | .fixed k =>
      let src := slots.getD k 0
      if t.oper == .and && !(← has src t.id) then fixedOk := false
    | _ => pure ()
  let mut out : Array QResult := #[]
  if fixedOk then
    -- the iteration order: slices for order_by, else groups' table arrays
    let order : Array (Nat × Nat × Option Nat) ←
      if q.orderBy then pure (q.slices.map (fun (t, o, c) => (t, o, some c)))
      else pure (q.groups.foldl (fun acc g => acc ++ g.tables.foldl (fun a m =>
        -- round 4: a table matched through a wildcard yields one result per
        -- match (cache_iter.c 106-113)
        a ++ (List.replicate (1 + m.wildPairs.size) (m.table, 0, none)).toArray) #[]) #[])
    let mut fixedComputed : Option Bool := none
    for (t, off, cntO) in order do
      let some m ← getMatch qi t | continue
      let x ← tbl t
      let cnt := cntO.getD x.count
      if x.count == 0 then
        if (← qGet qi).hasCD then
          syncMatchMonitor qi t
          oracleSync qi t
        continue
      -- ecs_iter_changed (change_detection.c 676-712)
      let mut ch := false
      if ask && !(fixedReadFields (← qGet qi)).isEmpty then
        match fixedComputed with
        | some b => ch := b
        | none =>
          let b ← if (← qGet qi).fixedMonitor.isSome then getFixedMonitor qi true else pure false
          fixedComputed := some b
          ch := b
      let expected ← oracleChanged qi t
      let expectedFixed ← oracleFixedChanged qi
      if ask && !ch then ch ← checkMatchMonitor qi t
      if ask && (expected || expectedFixed) && !ch then
        noteViol s!"P-CD1 ecs_iter_changed: query {qi} table {t} returned false, but since the query last iterated the table its data changed (oracle state {(← get).osnap[(qi, t)]?} -> {← oracleState qi t})"
      let m ← (do return (← getMatch qi t).getD m)
      let ents := (x.ents.extract off (off + cnt))
      let vals ← fieldVals (← qGet qi) m off cnt
      out := out.push { table := t, offset := off, count := cnt, ents, vals, changed := ch }
      -- the next ecs_query_next (or ecs_iter_fini for `first`) runs change
      -- detection on this result unless it was skipped
      if mode != .skipAll then
        markFieldsDirty qi t m ents
        if (← qGet qi).hasCD then syncMatchMonitor qi t
        oracleSync qi t
      if mode == .first then return out
    -- "Done iterating" (eval_iter.c 597-605)
    markFixedFieldsDirty qi
    if (← qGet qi).fixedMonitor.isSome then
      discard <| getFixedMonitor qi false
      oracleFixedSync qi
  else
    markFixedFieldsDirty qi
    if (← qGet qi).fixedMonitor.isSome then
      discard <| getFixedMonitor qi false
      oracleFixedSync qi
  return out


/-! ### Round 4: the cache iterator, one result at a time (cache_iter.c 11-123)

`qit->group` is held by group id, `qit->tables` is the group's table vector
or a `wildcard_matches` vector (by identity), `qit->cur`, `qit->all_cur`,
and `qit->elem` (the slot of the last result).  Calls may run between two
`ecs_query_next`, so the vectors can change under the cursor. -/

structure QCursor where
  /-- `qit->group`: round 5, by identity (`QGroup.uid`) -/
  group : Option Nat := none
  wildVec : Option Nat := none
  cur : Nat := 0
  allCur : Nat := 0
  /-- `qit->elem`: (group identity, slot, the group array's identity) or
      (vector, index) of the last result -/
  elem : Option (Option Nat × Option Nat × Nat × Nat) := none
  /-- the last result's table and entities (`it->table`, `it->entities`) -/
  lastT : Option Nat := none
  lastEnts : Array UInt64 := #[]
  done : Bool := false
  /-- round 5: an order_by query iterates `cache->table_slices`
      (cache_iter.c 27-34) -/
  slice : Bool := false
  deriving Inhabited

/-- `flecs_query_cache_iter_init` (cache_iter.c 11-37) -/
def cursorInit (qi : Nat) : M QCursor := do
  -- round 5: order_by: sort and build the slices first (cache_iter.c
  -- 27-34, order_by.c 230-319)
  if (← qGet qi).orderBy then sortTables qi
  let q ← qGet qi
  qSet qi { q with prevMatchCount := q.matchCount }
  -- the change oracle: a user iteration sees the cache's tables
  if !(← get).iterQuiet then
    let ts := q.groups.foldl (fun acc g => acc ++ g.tables.toList.map (·.table)) []
    modify fun w => { w with ouser := w.ouser.insert qi ts }
  if q.orderBy then return { slice := true }
  match q.groups[0]? with
  | none => return { done := true }
  | some g => return { group := some g.uid }

/-- The match that owns a wildcard vector. -/
def vecOwner (q : QCache) (v : Nat) : Option QMatch := Id.run do
  for g in q.groups do
    for m in g.tables do
      if m.wildVec == v then return some m
  return none

/-- Change detection on the previous result at the start of
    `ecs_query_next` (eval_iter.c 217-234, 492-500): through `qit->elem`,
    which is a pointer into the vector, so it is whatever match is at that
    slot now.  `qit->elem` is read only when the query has change detection
    (`EcsQueryHasChangeDetection`, eval_iter.c 225-230). -/
def cursorSyncElem (qi : Nat) (c : QCursor) : M Unit := do
  let some (gid, vec, slot, arr) := c.elem | return
  -- flecs_query_mark_fields_dirty uses the iterator's own table and rows
  if let some t := c.lastT then
    if let some m ← getMatch qi t then markFieldsDirty qi t m c.lastEnts
  let hasCD := (← qGet qi).hasCD
  let q ← qGet qi
  match vec with
  | some v =>
    if (← get).vecFreed.contains v then
      if hasCD then
        noteViol s!"P1 use after free: ecs_query_next syncs the monitor of a wildcard match (qit->elem) in the wildcard_matches vector {v}, which a rematch freed (match.c 247-258 / 48-67)"
    else if let some m := vecOwner q v then
      oracleSync qi m.table
  | none =>
    -- round 5: the group's table array was reallocated or finalized; only
    -- a query with change detection reads it (the change oracle still
    -- records what the user was given)
    if hasCD && (← get).vecFreed.contains arr then
      noteViol s!"P1 use after free: ecs_query_next syncs the monitor of qit->elem (eval_iter.c 225-230, change_detection.c 581-633), a pointer into table array {arr} of group {gid}, which was freed: an ecs_vec_append that grew the array (group.c 157-158, vec.c 373-375, block_allocator.c 314) or ecs_vec_fini when the group was removed (group.c 103)"
      return
    match q.groups.findIdx? (fun g => some g.uid == gid) with
    | none => pure ()
    | some gi =>
      let g := q.groups.getD gi default
      match g.tables[slot]? with
      | none =>
        if hasCD then
          modify fun w => { w with staleReads := w.staleReads.push s!"qit->elem slot {slot} of group {gid} (count {g.tables.size})" }
      | some m =>
        if hasCD then syncMatchMonitor qi m.table
        oracleSync qi m.table

/-- `flecs_query_cache_next` (cache_iter.c 41-123), preceded by the change
    detection of the previous result.  Returns the table and the matched
    pair of the next result. -/
partial def cursorNext (qi : Nat) (c : QCursor) (fuel : Nat := 1000) : M (QCursor × Option (Nat × Id × Option (Nat × Nat))) := do
  if fuel == 0 then fail .internalError "model" "cursor loop"
  if c.done then return (c, none)
  let q ← qGet qi
  if c.slice then
    -- round 5: a slice is a copy of a match with a row range (order_by.c
    -- 195-209); the iterator returns that range (cache_iter.c 356-378 sets
    -- the range of $this), skipping slices whose table is empty now (82-98)
    match q.slices[c.cur]? with
    | none => return ({ c with done := true }, none)
    | some (t, off, cnt) =>
      -- a table deleted during the iteration: its struct stays in the
      -- table store with count 0 (flecs_table_fini_data, storage/table.c
      -- 1205; the store keeps the memory, 1333-1336), so the slice is
      -- skipped (the model does not follow a reuse of the slot)
      let x := (← get).tables.getD t default
      -- round 6 (model error corrected): an order_by query has change
      -- detection from its first sort on (flecs_query_check_table_monitor
      -- creates the monitors and sets EcsQueryHasChangeDetection,
      -- change_detection.c 79-138), so the skip first syncs the slice's
      -- monitor (cache_iter.c 84-87): for a freed table that is the block
      -- flecs_query_cache_match_fini freed (match.c 41-43)
      if !x.live then
        noteViol s!"P1 use after free: the iterator skips a slice of table {t}, which was freed during the iteration, after syncing the slice's copy of its monitor (cache_iter.c 84-87, change_detection.c 581-633), a block flecs_query_cache_match_fini freed (match.c 41-43)"
      if !x.live || x.count == 0 then return (← cursorNext qi { c with cur := c.cur + 1 } (fuel - 1))
      let c := { c with cur := c.cur + 1, lastT := some t, lastEnts := x.ents.extract off (off + cnt), elem := none }
      return (c, some (t, 0, some (off, cnt)))
  match c.wildVec with
  | some v =>
    if (← get).vecFreed.contains v then
      noteViol s!"P1 use after free: the iterator reads the wildcard_matches vector {v} of the table it is iterating (qit->tables, cache_iter.c 49 and 77-78), which a rematch freed (match.c 247-258) or a table removal freed (group.c 321, match.c 48-67)"
      return ({ c with done := true }, none)
    match vecOwner q v with
    | none => return ({ c with done := true }, none)
    | some owner =>
      if c.cur ≥ owner.wildPairs.size then
        cursorNext qi { c with wildVec := none, cur := c.allCur } (fuel - 1)
      else
        let pair := owner.wildPairs.getD c.cur 0
        let x ← tbl owner.table
        let c := { c with elem := some (none, some v, c.cur, 0), cur := c.cur + 1,
                          lastT := some owner.table, lastEnts := x.ents.extract 0 x.count }
        return (c, some (owner.table, pair, none))
  | none =>
    match q.groups.findIdx? (fun g => some g.uid == c.group) with
    | none =>
      -- the group left the list: the default group's vector was finalized
      -- and its `next` cleared (group.c 117-130); another group was freed
      if c.group != some 0 then
        noteViol s!"P1 use after free: the iterator's group (identity {c.group}) was freed while it was iterated: the next ecs_query_next reads its tables and next (cache_iter.c 49-62) after flecs_query_cache_remove_group freed it (group.c 118-130, 109 ecs_map_remove_free)"
      return ({ c with done := true }, none)
    | some gi =>
      let g := q.groups.getD gi default
      if c.cur ≥ g.tables.size then
        match q.groups[gi + 1]? with
        | none => return ({ c with done := true }, none)
        | some g2 => cursorNext qi { c with group := some g2.uid, cur := 0 } (fuel - 1)
      else
        let m := g.tables.getD c.cur default
        let x ← tbl m.table
        if x.count == 0 then
          if (← qGet qi).hasCD then
            syncMatchMonitor qi m.table
            oracleSync qi m.table
          cursorNext qi { c with cur := c.cur + 1 } (fuel - 1)
        else
          let elem := some (c.group, (none : Option Nat), c.cur, g.arr)
          let c := { c with lastT := some m.table, lastEnts := x.ents.extract 0 x.count }
          let c := if m.wildVec != 0 then { c with wildVec := some m.wildVec, allCur := c.cur + 1, cur := 0, elem }
            else { c with cur := c.cur + 1, elem }
          return (c, some (m.table, m.pair, none))

/-- `ecs_query_init` with a cache (cache.c 700-911) -/
def createQuery (q : QCache) : M Nat := do
  let qi := (← get).queries.size
  modify fun w => { w with queries := w.queries.push q }
  -- EcsQueryDetectChanges / order_by: non_trivial_set (cache.c 781-810)
  if q.detect then
    for t in q.terms do
      if t.id < HI then modify fun w => { w with nonTrivialSet := w.nonTrivialSet.insert t.id }
  if q.orderBy then modify fun w => { w with nonTrivialSet := w.nonTrivialSet.insert C0 }
  -- fixed-source terms (validator.c 1188-1199)
  for t in q.terms do
    match t.src with
    | .fixed _ => if t.id < HI then modify fun w => { w with nonTrivialSet := w.nonTrivialSet.insert t.id }
    | _ => pure ()
  -- flecs_query_cache_match_tables (cache.c 195-208): every live table
  let w ← get
  for t in [0:w.tables.size] do
    let x := w.tables.getD t default
    if !x.live || t == 0 then continue
    if let some m ← evalMatch (← qGet qi) t then addTable qi m
  if q.orderBy then
    sortTables qi
  -- `result->prev_match_count = -1` then match: changed until iterated
  return qi

end W

end Flecs
