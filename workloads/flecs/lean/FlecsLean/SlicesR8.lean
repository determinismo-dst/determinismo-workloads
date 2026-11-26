/-
  Round 8: order_by slices across iterators, the query cache's match
  counters, its monitor allocator, and the dirty state a skipped stale slice
  plants, transcribed from flecs v4.2.0.  It corrects round 7's F55 and
  finds F56.

  The F55 correction.  A new table is set up by `flecs_init_table`
  (storage/table_graph.c 418-430), which sets `table->dirty_state = NULL`
  (424) before `flecs_table_init`.  Round 7 read only `flecs_table_new`
  (433-494) and `flecs_table_init` and missed that line.  So the 1-int dirty
  state that the skip of a freed table's slice plants in the zeroed slot
  (cache_iter.c 81-99 -> `flecs_query_sync_match_monitor`,
  change_detection.c 581-633 -> `flecs_table_get_dirty_state`,
  storage/table.c 1432-1450) is never written past: the next table created
  in the slot drops the pointer.  Nothing frees the block: a dead slot is
  never finalized, and the new table forgets it.  It leaks
  (`FLECS_SANITIZE`: `flecs_ballocator_fini`, block_allocator.c 96-115,
  "Leak detected!" and `ecs_abort(ECS_LEAK_DETECTED)`).

  The same skip writes the slice's monitor, which `flecs_query_cache_match_
  fini` returned to `cache->allocators.monitors` (match.c 41-43).  With the
  default allocator (no `FLECS_USE_OS_ALLOC`, no `FLECS_SANITIZE`) a freed
  chunk's first 8 bytes are its free-list link (`flecs_bfree_w_dbg_info`,
  block_allocator.c 274: `chunk->next = ba->head`).  The monitor of a
  one-field query is 8 bytes (cache.c 620-621): `monitor[0] = dirty_state[0]`
  (change_detection.c 606) overwrites the link's low half with 1, and,
  because `monitor[1]` (the link's high half) is not -1, the term loop reads
  the freed `base.columns` (whose first bytes are that allocator's link: a
  column that is a multiple of 16, never -1, `flecs_query_get_column_for_
  field`, 30-75) and stores `dirty_state[column + 1]`, read past the 1-int
  block, into `monitor[1]` (627-628).  The link becomes a wild pointer.  The
  next monitor allocated for the query pops that chunk; the one after it
  pops the wild pointer (`flecs_balloc_w_dbg_info`, 150-190:
  `ba->head = ba->head->next`): a crash, or a monitor at a wild address.
  With `FLECS_SANITIZE` the link sits before the data (16-byte header) and
  is not hit; with `FLECS_USE_OS_ALLOC` and the round-7 test's wrapper
  freed blocks are never reused.

  F56.  `flecs_query_sync_match_monitor` ends with `cache->prev_match_count
  = cache->match_count` (change_detection.c 632), and every
  `ecs_query_next` after a result syncs that result's monitor
  (eval_iter.c 494-502 -> `flecs_query_change_detection`, 217-232).  So a
  matched table deleted during an iteration (`flecs_query_cache_remove_
  table_from_group`, group.c 176-181: `match_count++`) is forgotten by the
  next sync.  The next iterator's `flecs_query_cache_sort_tables`
  (order_by.c 228-321) rebuilds the slices only when a match's monitor
  reports a change or `match_count != prev_match_count` (315): the deleted
  table's slice stays in `cache->table_slices` for later iterators too,
  until a matched table changes.  A table created after the iteration in
  the freed slot is then returned by a new iterator.

  The model: the order_by query `P` (in, cached, order_by P) and tags with
  an OnDelete policy (round 6's `Slices` world), plus per table its
  `dirty_state[0]` (bumped when rows are added or removed:
  storage/table.c 1558, 1586, 1689), per match its monitor chunk and
  `monitor[0]`, the counters, the slices, and the monitor free list.
  Phases: iterations (with calls after chosen results, the result's table
  locked as the C++ `each` locks it) and calls between them.  Properties:
  - P1 (Manual.md "Error handling"): no use of freed memory, no crash;
  - P-IT3 (Queries.md "Iteration"): results match the query;
  - P-L1 (new): every block flecs allocates is freed by `ecs_fini`
    (flecs.h `FLECS_SANITIZE`: "Enables expensive checks that can detect
    issues early. Recommended for running tests"; its leak check aborts).
-/
import FlecsLean.Slices

namespace Flecs.Slices8
open Flecs.Slices (showOp isort)
abbrev Op := Flecs.Slices.Op

/-- `block`: the default build (block allocators, free-list links in freed
    chunks).  `os`: `FLECS_USE_OS_ALLOC` with the round-7 test's wrapper
    (freed blocks kept and never reused).  `sanitize`: `FLECS_SANITIZE`
    (block allocators with a 16-byte header before the data). -/
inductive Alloc | block | os | sanitize
  deriving Repr, BEq, Inhabited, DecidableEq

def Alloc.show : Alloc → String
  | .block => "default allocator" | .os => "FLECS_USE_OS_ALLOC" | .sanitize => "FLECS_SANITIZE"

structure T where
  hasP : Bool
  tags : List Nat
  /-- the entity column, row order -/
  rows : Array Nat := #[]
  slot : Nat
  live : Bool := true
  /-- `dirty_state[0]` -/
  ver : Nat := 1
  /-- the iteration (1-based) during which the table was freed, 0 outside -/
  freedIn : Nat := 0
  deriving Repr, Inhabited

/-- A cache match: its table and monitor chunk with `monitor[0]`. -/
structure M where
  t : Nat
  mon : Option Nat := none
  mver : Nat := 0
  deriving Repr, Inhabited

/-- A slice: a struct copy of a match (order_by.c 195-205). -/
structure S where
  t : Nat
  mon : Option Nat
  off : Nat
  cnt : Nat
  deriving Repr, Inhabited, BEq

structure W where
  alloc : Alloc
  tabs : Array T := #[]
  /-- (table, value, alive) -/
  ents : Array (Nat × Nat × Bool) := #[]
  free : List Nat := []
  nextSlot : Nat := 0
  /-- the dirty-state block a zeroed slot points to, planted by a skip -/
  slotDirty : List (Nat × Nat) := []
  /-- planted blocks: never freed -/
  planted : Nat := 0
  ms : List M := []
  matchCount : Nat := 0
  prevCount : Nat := 0
  slices : List S := []
  /-- the iteration that built the slices -/
  slicesBuilt : Nat := 0
  nchunks : Nat := 0
  chunkFreed : List Nat := []
  chunkBad : List Nat := []
  monFree : List Nat := []
  /-- the monitor free list's head is a wild pointer -/
  wild : Bool := false
  delPolicy : Array Bool := #[]
  deadTags : List Nat := []
  out : List (String × String) := []
  crashed : Bool := false
  deriving Inhabited

def tab (w : W) (t : Nat) : T := w.tabs.getD t default

def report (w : W) (p d : String) : W :=
  if w.out.any (·.2 == d) then w else { w with out := w.out ++ [(p, d)] }

/-- The live table in memory slot `s`. -/
def occupant (w : W) (s : Nat) : Option Nat :=
  (List.range w.tabs.size).find? (fun t => (tab w t).live && (tab w t).slot == s)

def findTable (w : W) (hasP : Bool) (tags : List Nat) : Option Nat :=
  (List.range w.tabs.size).find? (fun t =>
    let x := tab w t
    x.live && x.hasP == hasP && x.tags == tags)

/-- `flecs_table_new` + `flecs_init_table` (table_graph.c 418-494): the slot
    freed last; `dirty_state = NULL` (424) drops a planted block; the query
    cache matches a table with P (`EcsOnTableCreate`, cache.c 569-581;
    group.c 150-172: `match_count++`). -/
def ensureTable (w : W) (hasP : Bool) (tags : List Nat) : W × Nat :=
  match findTable w hasP tags with
  | some t => (w, t)
  | none =>
    let (slot, free, next) := if !hasP && tags.isEmpty then (1000000, w.free, w.nextSlot) else
      match w.free with
      | s :: rest => (s, rest, w.nextSlot)
      | [] => (w.nextSlot, [], w.nextSlot + 1)
    let t := w.tabs.size
    let w := { w with tabs := w.tabs.push { hasP, tags, slot }, free, nextSlot := next,
                      slotDirty := w.slotDirty.filter (·.1 != slot) }
    let w := if hasP then { w with ms := w.ms ++ [{ t }], matchCount := w.matchCount + 1 } else w
    (w, t)

def appendRow (w : W) (t e : Nat) : W :=
  let x := tab w t
  { w with tabs := w.tabs.set! t { x with rows := x.rows.push e, ver := x.ver + 1 },
           ents := w.ents.modify e (fun (_, v, a) => (t, v, a)) }

/-- `flecs_table_delete`: the last row moves into the removed one. -/
def removeRow (w : W) (e : Nat) : W := Id.run do
  let (t, _, _) := w.ents.getD e (0, 0, false)
  let x := tab w t
  let some r := (List.range x.rows.size).find? (fun i => x.rows.getD i 0 == e) | return w
  let last := x.rows.size - 1
  let rows := (x.rows.set! r (x.rows.getD last 0)).pop
  { w with tabs := w.tabs.set! t { x with rows, ver := x.ver + 1 } }

/-- Free monitor chunk `c` (match.c 41-43). -/
def freeChunk (w : W) (c : Nat) : W :=
  { w with chunkFreed := c :: w.chunkFreed,
           monFree := if w.alloc == .os then w.monFree else c :: w.monFree }

/-- `flecs_table_fini` of table t during iteration `it` (0 outside): the
    cache drops its match (group.c 176-181: `match_count++`) and frees the
    monitor; the slot is zeroed (sparse.c 391-393) and freed last. -/
def freeTable (w : W) (t : Nat) (it : Nat) : W := Id.run do
  let x := tab w t
  let mut w := { w with tabs := w.tabs.set! t { x with live := false, freedIn := it, rows := #[] },
                        free := x.slot :: w.free,
                        slotDirty := w.slotDirty.filter (·.1 != x.slot) }
  match w.ms.find? (·.t == t) with
  | none => return w
  | some m =>
    w := { w with ms := w.ms.filter (·.t != t), matchCount := w.matchCount + 1 }
    if let some c := m.mon then w := freeChunk w c
    return w

def newEnt (w : W) (hasP : Bool) (tags : List Nat) (v : Nat) : W :=
  let (w, t) := ensureTable w hasP tags
  let e := w.ents.size
  appendRow { w with ents := w.ents.push (t, v, true) } t e

/-- One call, with table `locked` locked, during iteration `it`; none when
    flecs would assert on the lock or on a dead tag (the program is
    skipped). -/
def runOp (w : W) (locked : Option Nat) (it : Nat) (op : Op) : Option W := Id.run do
  match op with
  | .newEnt p ts v =>
    if ts.any (fun k => w.deadTags.contains k) then return none
    let (w', t) := ensureTable w p ts
    if locked == some t then return none
    return some (newEnt w' p ts v)
  | .deleteEnt e =>
    let (t, _, alive) := w.ents.getD e (0, 0, false)
    if e ≥ w.ents.size || !alive then return some w
    if locked == some t then return none
    let w := removeRow w e
    return some { w with ents := w.ents.modify e (fun (t, v, _) => (t, v, false)) }
  | .deleteTag k =>
    if w.deadTags.contains k then return some w
    let w := { w with deadTags := k :: w.deadTags }
    let doomed := (List.range w.tabs.size).filter (fun t =>
      let x := tab w t
      x.live && x.tags.contains k)
    if doomed.any (fun t => locked == some t) then return none
    let mut w := w
    for t in doomed do
      let x := tab w t
      for e in x.rows.toList do
        if w.delPolicy.getD k false then
          w := { w with ents := w.ents.modify e (fun (t, v, _) => (t, v, false)) }
        else
          let (w', t') := ensureTable w x.hasP (x.tags.filter (· != k))
          if locked == some t' then return none
          w := appendRow w' t' e
      let x := tab w t
      w := { w with tabs := w.tabs.set! t { x with rows := #[], ver := x.ver + 1 } }
    for t in doomed do
      w := freeTable w t it
    return some w

/-- A monitor for a match (`flecs_query_get_match_monitor`,
    change_detection.c 79-138: `flecs_balloc`).  With a wild free-list head
    the allocation dereferences it. -/
def allocChunk (w : W) : W × Nat :=
  if w.crashed then (w, 0) else
  if w.alloc != .os && w.wild then
    let w := report w "P1 no use after free"
      "crash: the query's monitor allocator hands out a wild pointer: its free-list link was overwritten by the skip of a freed table's slice (change_detection.c 581-633 wrote monitor[0] and monitor[1] of the freed chunk, block_allocator.c 168, 274)"
    ({ w with crashed := true }, 0)
  else
  match w.alloc, w.monFree with
  | .os, _ | _, [] => ({ w with nchunks := w.nchunks + 1 }, w.nchunks)
  | _, c :: rest =>
    -- popping a chunk whose link was overwritten makes the head wild; the
    -- rest of the list is unreachable
    let bad := w.chunkBad.contains c
    ({ w with monFree := if bad then [] else rest, chunkFreed := w.chunkFreed.erase c,
              wild := bad, chunkBad := w.chunkBad.erase c }, c)

/-- The sync of a slice whose match is gone (its table freed): the write of
    the freed monitor, and the dirty state planted in a zeroed slot.
    `it` is the iteration, `why` what the iterator saw there. -/
def staleSync (w : W) (s : S) (it : Nat) (why : String) : W := Id.run do
  let x := tab w s.t
  let later := x.freedIn < it
  let lead := if later then
      s!"F56 later iterator: iterator {it} still has the slice of table {s.t}, freed during iterator {x.freedIn} (the next sync set prev_match_count = match_count, change_detection.c 632, so flecs_query_cache_sort_tables did not rebuild the slices, order_by.c 315)"
    else s!"skip: iterator {it} reaches the slice of table {s.t}, freed during this iteration"
  let mut w := report w "P1 no use after free" s!"{lead}; {why}; the iterator syncs the slice's monitor, a chunk flecs_query_cache_match_fini freed (cache_iter.c 81-99, change_detection.c 581-633, match.c 41-43)"
  if let some c := s.mon then
    if w.alloc == .block && w.chunkFreed.contains c && !w.chunkBad.contains c then
      w := { w with chunkBad := c :: w.chunkBad }
  -- the zeroed slot: flecs_table_get_dirty_state plants a 1-int block
  if occupant w x.slot == none && !(w.slotDirty.any (·.1 == x.slot)) then
    w := { w with slotDirty := (x.slot, w.planted) :: w.slotDirty, planted := w.planted + 1 }
  return { w with prevCount := w.matchCount }

/-- The sync of a live match after its result (eval_iter.c 217-232). -/
def liveSync (w : W) (t : Nat) : W :=
  let x := tab w t
  { w with ms := w.ms.map (fun m => if m.t == t then { m with mver := x.ver } else m),
           prevCount := w.matchCount }

/-- `flecs_query_cache_sort_tables` and `build_sorted_table_range`
    (order_by.c 81-321), at iterator creation (cache_iter.c 11-37). -/
def sortTables (w : W) (it : Nat) : W := Id.run do
  let mut w := w
  let mut sorted := false
  for m in w.ms do
    let x := tab w m.t
    match m.mon with
    | none =>
      let (w', c) := allocChunk w
      w := { w' with ms := w'.ms.map (fun m' => if m'.t == m.t then { m' with mon := some c } else m') }
      if w.crashed then return w
      sorted := true
      if x.rows.size == 0 then w := liveSync w m.t
    | some _ =>
      if m.mver != x.ver then
        sorted := true
        if x.rows.size == 0 then w := liveSync w m.t
  if sorted || w.matchCount != w.prevCount then
    -- build the slices: tables sorted by value, merged
    let matched := w.ms.filter (fun m => (tab w m.t).rows.size > 0)
    for m in matched do
      let x := tab w m.t
      let rows := isort (fun a b => (w.ents.getD a (0, 0, false)).2.1 ≤ (w.ents.getD b (0, 0, false)).2.1) x.rows.toList
      w := { w with tabs := w.tabs.set! m.t { x with rows := rows.toArray } }
    let mut pos : List (M × Nat) := matched.map (fun m => (m, 0))
    let mut out : Array S := #[]
    for _ in [0:64] do
      let cands := pos.filter (fun (m, r) => r < (tab w m.t).rows.size)
      let val := fun (m : M) (r : Nat) => (w.ents.getD ((tab w m.t).rows.getD r 0) (0, 0, false)).2.1
      let best := cands.foldl (fun (acc : Option (M × Nat)) (m, r) =>
        match acc with
        | none => some (m, r)
        | some (m0, r0) => if val m r < val m0 r0 then some (m, r) else acc) none
      match best with
      | none => break
      | some (m, r) =>
        let m := (w.ms.find? (·.t == m.t)).getD m
        out := match out.back? with
          | some s => if s.t == m.t then out.pop.push { s with cnt := s.cnt + 1 } else out.push { t := m.t, mon := m.mon, off := r, cnt := 1 }
          | none => out.push { t := m.t, mon := m.mon, off := r, cnt := 1 }
        pos := pos.map (fun (m', r') => if m'.t == m.t then (m', r' + 1) else (m', r'))
    w := { w with slices := out.toList, slicesBuilt := it, matchCount := w.matchCount + 1 }
  return { w with prevCount := w.matchCount }

/-- One iteration (`it`, 1-based) with calls after chosen results. -/
def iterate (w : W) (it : Nat) (calls : List (Nat × Op)) : Option W := Id.run do
  let mut w := sortTables w it
  if w.crashed then return some w
  let mut n := 0
  for s in w.slices do
    let x := tab w s.t
    let occ := if x.live then some s.t else occupant w x.slot
    let cnt := match occ with | some o => (tab w o).rows.size | none => 0
    if cnt == 0 then
      -- cache_iter.c 81-99: skipped, after the sync
      if x.live then w := liveSync w s.t
      else w := staleSync w s it (match occ with
        | none => "its memory was zeroed: count 0"
        | some o => s!"its memory now holds table {o}, which is empty")
      if w.crashed then return some w
      continue
    let o := occ.getD s.t
    let y := tab w o
    n := n + 1
    if o != s.t then
      let later := x.freedIn < it
      let lead := if later then s!"F56 later iterator: iterator {it} still has the slice of table {s.t}, freed during iterator {x.freedIn} (prev_match_count was synced, change_detection.c 632; no rebuild, order_by.c 315)"
        else s!"result {n} of iterator {it}: the slice of table {s.t}, freed during this iteration"
      w := report w "P1 no use after free" s!"{lead}, names table {o}'s memory (count {cnt}); the iterator returns that table with the slice's freed _trs and columns (cache_iter.c 326-377); a debug build aborts in flecs_iter_assert_columns (eval_iter.c 253-273)"
      for i in [s.off:s.off + s.cnt] do
        if i < cnt && !y.hasP then
          let e := y.rows.getD i 0
          w := report w "P-IT3 results match the query" s!"{if later then "F56 later iterator" else "same iteration"}: iterator {it} returns e{e}, which does not have P (its table [{y.tags.map (fun k => s!"T{k}")}] took the memory of table {s.t})"
    -- the calls after this result, with its table locked
    for (k, op) in calls do
      if k == n then
        match runOp w (some o) it op with
        | some w' => w := w'
        | none => return none
    -- the next ecs_query_next syncs this result's monitor
    let x := tab w s.t
    if x.live then w := liveSync w s.t
    else w := staleSync w s it "after its result"
    if w.crashed then return some w
  return some w

inductive Phase
  /-- an iteration with calls after the k-th result -/
  | iter (calls : List (Nat × Op))
  /-- a call outside any iteration -/
  | call (op : Op)
  deriving Repr, BEq, Inhabited

def showPhase : Phase → String
  | .iter cs => s!"iterate{if cs.isEmpty then "" else s!" ({cs.map (fun (k, o) => s!"after result {k}: {showOp o}")})"}"
  | .call o => showOp o

structure Prog where
  alloc : Alloc
  ntags : Nat
  delPolicy : Array Bool
  init : List Op
  phases : List Phase
  deriving Inhabited

instance : Repr Prog := ⟨fun p _ => .text s!"{p.alloc.show}; tags {p.ntags} (OnDelete Delete: {(List.range p.ntags).filter (fun k => p.delPolicy.getD k false)}); before: {p.init.map showOp}; then {p.phases.map showPhase}"⟩

/-- Run the program to `ecs_fini`; the final world, or none if skipped. -/
def run (p : Prog) : Option W := Id.run do
  let mut w : W := { alloc := p.alloc, delPolicy := p.delPolicy }
  for op in p.init do
    match runOp w none 0 op with
    | some w' => w := w'
    | none => return none
  let mut it := 0
  for ph in p.phases do
    if w.crashed then break
    match ph with
    | .iter cs =>
      it := it + 1
      match iterate w it cs with
      | some w' => w := w'
      | none => return none
    | .call op =>
      match runOp w none 0 op with
      | some w' => w := w'
      | none => return none
  return some w

def check (p : Prog) : List (String × String) :=
  match run p with
  | none => []
  | some w =>
    let leak := if w.planted > 0 && !w.crashed then
      [("P-L1 no leak at ecs_fini", s!"leak: {w.planted} dirty-state block(s) planted by the skip of a freed table's slice (flecs_table_get_dirty_state on the zeroed slot, storage/table.c 1432-1450) are never freed: flecs_init_table resets dirty_state of the next table in the slot (table_graph.c 424), and a dead slot is never finalized ({p.alloc.show}{if p.alloc == .sanitize then ": flecs_ballocator_fini aborts, \"Leak detected!\", block_allocator.c 96-115" else ""})")]
      else []
    w.out ++ leak

section
variable {m : Type → Type} [Monad m] [Pick m]

def genType (ntags : Nat) : m (Bool × List Nat) := do
  let hasP := (← Pick.pick "s8.hasP" 2) == 0
  let mask ← Pick.pick "s8.tags" (2 ^ ntags)
  return (hasP, (List.range ntags).filter (fun k => (mask >>> k) % 2 == 1))

def genOp (ntags nents : Nat) : m Op := do
  match (← Pick.pick "s8.call" 3) with
  | 0 => let (p, ts) ← genType ntags; return .newEnt p ts (← pickOf "s8.v" #[1, 3, 5])
  | 1 => return .deleteEnt (← Pick.pick "s8.e" nents)
  | _ => return .deleteTag (← Pick.pick "s8.k" ntags)

/-- `nphases` phases; an iteration has at most one call. -/
def genProg (alloc : Alloc) (ntags ninit nphases : Nat) : m Prog := do
  let mut pol := #[]
  for _ in [0:ntags] do pol := pol.push ((← Pick.pick "s8.policy" 2) == 1)
  let mut init := []
  for i in [0:ninit] do
    let (p, ts) ← genType ntags
    init := init ++ [Flecs.Slices.Op.newEnt p ts (2 * i + 2)]
  let mut phases := []
  for _ in [0:nphases] do
    match (← Pick.pick "s8.phase" 3) with
    | 0 => phases := phases ++ [Phase.iter []]
    | 1 =>
      let k := (← Pick.pick "s8.after" 3) + 1
      phases := phases ++ [Phase.iter [(k, ← genOp ntags (ninit + nphases))]]
    | _ => phases := phases ++ [Phase.call (← genOp ntags (ninit + nphases))]
  return { alloc, ntags, delPolicy := pol, init, phases }

end

def shrink (p : Prog) : List Prog :=
  (List.range p.phases.length).map (fun i => { p with phases := p.phases.eraseIdx i }) ++
  (List.range p.init.length).map (fun i => { p with init := p.init.eraseIdx i })

/-- The setup of the C tests: T0 = Tag (OnDelete Delete), T1 = Velocity's
    stand-in (a table without P).  [P]: e0 (2), e2 (6); [P, T0]: e1 (4).
    Slices: [P] row 0, [P, T0] row 0, [P] row 1. -/
def base : List Op := [.newEnt true [] 2, .newEnt true [0] 4, .newEnt true [] 6]

def cases : List (String × Prog) := [
  ("F55 corrected, query_order_by_skip_leaks_dirty_state (OS allocator): delete T0 after result 1; after the iteration ecs_new [T1], ecs_new [P, T1]",
    { alloc := .os, ntags := 2, delPolicy := #[true, false], init := base,
      phases := [.iter [(1, .deleteTag 0)], .call (.newEnt false [1] 0), .call (.newEnt true [1] 9)] }),
  ("F55 corrected, the same with FLECS_SANITIZE",
    { alloc := .sanitize, ntags := 2, delPolicy := #[true, false], init := base,
      phases := [.iter [(1, .deleteTag 0)], .call (.newEnt false [1] 0), .call (.newEnt true [1] 9)] }),
  ("F55 corrected, query_order_by_skip_corrupts_monitor_allocator (default allocator): delete T0 after result 1; then two new tables with P; iterate",
    { alloc := .block, ntags := 3, delPolicy := #[true, false, false], init := base,
      phases := [.iter [(1, .deleteTag 0)], .call (.newEnt true [1] 7), .call (.newEnt true [2] 8), .iter []] }),
  ("control: the delete outside the iteration (default allocator)",
    { alloc := .block, ntags := 3, delPolicy := #[true, false, false], init := base,
      phases := [.iter [], .call (.deleteTag 0), .call (.newEnt true [1] 7), .call (.newEnt true [2] 8), .iter []] }),
  ("F56, query_order_by_stale_slice_next_iterator: delete T0 after result 3 (the last); after the iteration ecs_new [T1]; a new iterator",
    { alloc := .block, ntags := 2, delPolicy := #[true, false], init := base,
      phases := [.iter [(3, .deleteTag 0)], .call (.newEnt false [1] 0), .iter []] }),
  ("control: the delete before the first iterator",
    { alloc := .block, ntags := 2, delPolicy := #[true, false], init := base,
      phases := [.call (.deleteTag 0), .iter [], .call (.newEnt false [1] 0), .iter []] }),
  ("control: delete T0 after result 3, then a row added to [P] before the new iterator",
    { alloc := .block, ntags := 2, delPolicy := #[true, false], init := base,
      phases := [.iter [(3, .deleteTag 0)], .call (.newEnt false [1] 0), .call (.newEnt true [] 8), .iter []] }) ]

end Flecs.Slices8
