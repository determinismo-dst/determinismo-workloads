/-
  Round 6: order_by slices against the reuse of a deleted table's slot,
  transcribed from flecs v4.2.0.

  - Tables live in `world->store.tables`, a sparse set of `ecs_table_t`
    (table_graph.c 443: `flecs_sparse_add_t`; storage/table.c 1333-1336:
    `flecs_sparse_remove_w_gen_t` on free).  A removed element's memory is
    zeroed (sparse.c 391-393) and its dense index moves to the first unused
    position (380-389), which `flecs_sparse_new_index` hands out first
    (137-150): the next table created takes the memory of the table freed
    last.
  - A table is freed when a component in its type is deleted: the cleanup
    deletes or moves the table's entities (on_delete.c 558-668, by the
    component's OnDelete policy), then releases the tables
    (`flecs_on_delete_clear_ids`, 688-768).  The query cache drops the
    table's match (`EcsOnTableDelete`, cache.c 601-604;
    `flecs_query_cache_remove_table`, group.c 302-326), whose arrays
    (`base.columns`, `_trs`, `_ids`, `_sources`) `flecs_query_cache_match_
    fini` frees (match.c 18-67).
  - An order_by query iterates `cache->table_slices` (cache_iter.c 27-34),
    built when an iterator is created: each slice is a struct copy of a
    match, with its table pointer and array pointers, and a row range
    (order_by.c 195-205).  The iterator skips a slice whose table has count
    0 (cache_iter.c 81-99, `ecs_table_count(qm->base.table)`), else returns
    its range of that table (`flecs_query_is_cache_search`, 192-222: the
    slice's `_trs`, `columns`, `_ids`, `_sources` become the iterator's).

  The model: a component P (the order_by component) and tags; each tag has
  an OnDelete policy (Remove, the default, or Delete).  The query is
  `P`, cached, order_by P.  The iteration runs with calls made after chosen
  results, with the iterated table locked as the C++ `each` locks it
  (Queries.md "Iteration"); a program whose call would move or delete rows
  of the locked table, or delete it, is skipped (flecs asserts there).
  Properties:
  - P1 (iteration): no read or write of memory freed by the cache (Manual.md
    "Error handling"); an order_by query always has change detection
    (`flecs_query_check_table_monitor` creates the monitors when the slices
    are built and sets `EcsQueryHasChangeDetection`, change_detection.c
    79-138), so a skipped slice's monitor is synced (cache_iter.c 81-99);
  - P-IT2 (round 5): a result covers only rows below its table's count;
  - P-IT3: every entity a result returns matches the query (Queries.md
    "Iteration": the iterator returns the matching tables).
-/
import FlecsLean.Search2

namespace Flecs.Slices

structure Tbl where
  hasP : Bool
  tags : List Nat
  /-- the column of entities, including rows past the count (stale copies) -/
  mem : Array Nat := #[]
  count : Nat := 0
  /-- the memory of the `ecs_table_t` in the store -/
  slot : Nat
  live : Bool := true
  deriving Repr, Inhabited

structure Ent where
  table : Nat
  val : Nat
  alive : Bool := true
  deriving Repr, Inhabited

structure W where
  tables : Array Tbl := #[]
  ents : Array Ent := #[]
  /-- freed slots, the most recently freed first -/
  free : List Nat := []
  nextSlot : Nat := 0
  /-- OnDelete Delete per tag (else Remove) -/
  delPolicy : Array Bool := #[]
  /-- tags deleted so far (a deleted id cannot be added again) -/
  deadTags : List Nat := []
  deriving Inhabited

def findTable (w : W) (hasP : Bool) (tags : List Nat) : Option Nat :=
  (List.range w.tables.size).find? (fun t =>
    let x := w.tables.getD t default
    x.live && x.hasP == hasP && x.tags == tags)

/-- `flecs_table_find_or_create`: a new table takes the slot freed last. -/
def ensureTable (w : W) (hasP : Bool) (tags : List Nat) : W × Nat :=
  match findTable w hasP tags with
  | some t => (w, t)
  | none =>
    -- the empty type is the root table (`world->store.root`), which is not
    -- in the store: it never takes a freed slot
    let (slot, free, next) := if !hasP && tags.isEmpty then (1000000, w.free, w.nextSlot) else
      match w.free with
      | s :: rest => (s, rest, w.nextSlot)
      | [] => (w.nextSlot, [], w.nextSlot + 1)
    ({ w with tables := w.tables.push { hasP, tags, slot }, free, nextSlot := next }, w.tables.size)

def appendRow (w : W) (t e : Nat) : W :=
  let x := w.tables.getD t default
  let mem := if x.count < x.mem.size then x.mem.set! x.count e else x.mem.push e
  { w with tables := w.tables.set! t { x with mem, count := x.count + 1 },
           ents := w.ents.modify e (fun en => { en with table := t }) }

/-- `flecs_table_delete` (storage/table.c 1653-1704): the last row moves
    into the removed one; its old slot keeps the entity id. -/
def removeRow (w : W) (e : Nat) : W := Id.run do
  let en := w.ents.getD e default
  let t := en.table
  let x := w.tables.getD t default
  let some r := (List.range x.count).find? (fun i => x.mem.getD i 0 == e) | return w
  let last := x.count - 1
  let le := x.mem.getD last 0
  let mem := x.mem.set! r le
  { w with tables := w.tables.set! t { x with mem, count := last } }

def newEnt (w : W) (hasP : Bool) (tags : List Nat) (v : Nat) : W :=
  let (w, t) := ensureTable w hasP tags
  let e := w.ents.size
  appendRow { w with ents := w.ents.push { table := t, val := v } } t e

inductive Op
  /-- `ecs_new` with the type (P and the tags), P = v -/
  | newEnt (hasP : Bool) (tags : List Nat) (v : Nat)
  /-- `ecs_delete(world, e)` -/
  | deleteEnt (e : Nat)
  /-- `ecs_delete(world, Tag_k)`: the cleanup by Tag_k's OnDelete policy -/
  | deleteTag (k : Nat)
  deriving Repr, BEq, Inhabited

def showOp : Op → String
  | .newEnt p ts v => s!"ecs_new [{if p then "P, " else ""}{ts.map (fun k => s!"T{k}")}]{if p then s!" P={v}" else ""}"
  | .deleteEnt e => s!"ecs_delete(e{e})"
  | .deleteTag k => s!"ecs_delete(T{k})"

/-- Run a call with table `locked` locked: none when flecs would assert on
    the lock (the program is skipped). -/
def runOp (w : W) (locked : Option Nat) (op : Op) : Option W := Id.run do
  match op with
  | .newEnt p ts v =>
    -- a deleted tag is not alive: flecs asserts when it is added (the
    -- program is skipped)
    if ts.any (fun k => w.deadTags.contains k) then return none
    let (w', t) := ensureTable w p ts
    if locked == some t then return none
    return some (newEnt w' p ts v)
  | .deleteEnt e =>
    let en := w.ents.getD e default
    if e ≥ w.ents.size || !en.alive then return some w
    if locked == some en.table then return none
    let w := removeRow w e
    return some { w with ents := w.ents.modify e (fun x => { x with alive := false }) }
  | .deleteTag k =>
    if w.deadTags.contains k then return some w
    let w := { w with deadTags := k :: w.deadTags }
    let doomed := (List.range w.tables.size).filter (fun t =>
      let x := w.tables.getD t default
      x.live && x.tags.contains k)
    if doomed.any (fun t => locked == some t) then return none
    let mut w := w
    -- on_delete.c 558-668: delete or move the entities
    for t in doomed do
      let x := w.tables.getD t default
      for i in [0:x.count] do
        let e := x.mem.getD i 0
        if w.delPolicy.getD k false then
          w := { w with ents := w.ents.modify e (fun x => { x with alive := false }) }
        else
          let (w', t') := ensureTable w x.hasP (x.tags.filter (· != k))
          if locked == some t' then return none
          w := appendRow w' t' e
      let x := w.tables.getD t default
      w := { w with tables := w.tables.set! t { x with count := 0 } }
    -- 688-768: release the tables; each freed slot is reused first
    for t in doomed do
      let x := w.tables.getD t default
      w := { w with tables := w.tables.set! t { x with live := false, mem := #[] }, free := x.slot :: w.free }
    return some w

/-- A structural insertion sort (the kernel can evaluate it; `mergeSort`
    is well-founded recursion). -/
def insertBy (le : Nat → Nat → Bool) (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if le x y then x :: y :: ys else y :: insertBy le x ys

def isort (le : Nat → Nat → Bool) : List Nat → List Nat
  | [] => []
  | x :: xs => insertBy le x (isort le xs)

/-- `flecs_query_cache_sort_tables` and `flecs_query_cache_build_sorted_
    table_range` (order_by.c 81-321): sort each matched table, then merge
    the tables into slices (table, offset, count) by picking the smallest
    value; a slice ends when the next value comes from another table. -/
def buildSlices (w : W) : W × List (Nat × Nat × Nat) := Id.run do
  let mut w := w
  let matched := (List.range w.tables.size).filter (fun t =>
    let x := w.tables.getD t default
    x.live && x.hasP && x.count > 0)
  for t in matched do
    let x := w.tables.getD t default
    let rows := isort (fun a b => (w.ents.getD a default).val ≤ (w.ents.getD b default).val) (x.mem.extract 0 x.count).toList
    w := { w with tables := w.tables.set! t { x with mem := rows.toArray ++ x.mem.extract x.count x.mem.size } }
  let mut pos : List (Nat × Nat) := matched.map (fun t => (t, 0))
  let mut out : Array (Nat × Nat × Nat) := #[]
  for _ in [0:64] do
    let cands := pos.filter (fun (t, r) => r < (w.tables.getD t default).count)
    let best := cands.foldl (fun (acc : Option (Nat × Nat)) (t, r) =>
      let v := (w.ents.getD ((w.tables.getD t default).mem.getD r 0) default).val
      match acc with
      | none => some (t, r)
      | some (t0, r0) =>
        let v0 := (w.ents.getD ((w.tables.getD t0 default).mem.getD r0 0) default).val
        if v < v0 then some (t, r) else acc) none
    match best with
    | none => break
    | some (t, r) =>
      out := match out.back? with
        | some (t0, o, c) => if t0 == t then out.pop.push (t, o, c + 1) else out.push (t, r, 1)
        | none => out.push (t, r, 1)
      pos := pos.map (fun (t', r') => if t' == t then (t', r' + 1) else (t', r'))
  return (w, out.toList)

structure Prog where
  ntags : Nat
  delPolicy : Array Bool
  /-- the entities before the iteration -/
  init : List Op
  /-- calls made after the k-th result (1-based), with that result's table
      locked -/
  calls : List (Nat × Op)
  deriving Inhabited

instance : Repr Prog := ⟨fun p _ => .text s!"tags {p.ntags} (OnDelete Delete: {(List.range p.ntags).filter (fun k => p.delPolicy.getD k false)}); before: {p.init.map showOp}; during the iteration: {p.calls.map (fun (k, o) => s!"after result {k}: {showOp o}")}"⟩

/-- Iterate; the broken properties.  Returns none when the program is
    skipped. -/
def check (p : Prog) : List (String × String) := Id.run do
  let mut w : W := { delPolicy := p.delPolicy }
  for op in p.init do
    match runOp w none op with
    | some w' => w := w'
    | none => return []
  let (w1, slices) := buildSlices w
  w := w1
  let mut n := 0
  let mut out := []
  for (t, off, cnt) in slices do
    let x := w.tables.getD t default
    -- the memory the slice's table pointer names now
    let occ := if x.live then some t else
      (List.range w.tables.size).find? (fun t' =>
        let y := w.tables.getD t' default
        y.live && y.slot == x.slot)
    -- an order_by query has change detection (flecs_query_check_table_
    -- monitor gets each match a monitor and sets EcsQueryHasChangeDetection,
    -- change_detection.c 79-138, 217-231): a skipped slice's monitor is
    -- synced (cache_iter.c 81-99)
    let skippedFreed := fun (what : String) =>
      ("P1 no use after free", s!"a slice of table {t}, which ecs_delete freed during the iteration, is skipped ({what}), but the iterator first syncs its monitor (cache_iter.c 84-87, flecs_query_sync_match_monitor, change_detection.c 581-633): it writes monitor[0] into the slice's copy of _monitor, which flecs_query_cache_match_fini freed (match.c 41-43; the write lands on the block allocator's free-list link), and allocates a dirty state for the zeroed table memory (storage/table.c 1432-1450)")
    let some o := occ | do
      out := out ++ [skippedFreed "its memory was zeroed: count 0"]
      return out.eraseDups
    let y := w.tables.getD o default
    if y.count == 0 then
      if o != t then
        out := out ++ [skippedFreed s!"its memory now holds table {o}, which is empty"]
        return out.eraseDups
      continue
    n := n + 1
    if o != t then
      out := out ++ [("P1 no use after free", s!"result {n}: a slice of table {t}, which ecs_delete freed during the iteration, names its memory, now table {o} [{if y.hasP then "P, " else ""}{y.tags.map (fun k => s!"T{k}")}] with count {y.count} (the store hands out the slot freed last: sparse.c 137-150, 380-393); the iterator returns it and copies the slice's _trs, columns, _ids and _sources (cache_iter.c 192-222), which flecs_query_cache_match_fini freed (match.c 18-46); a debug build aborts there, in flecs_iter_assert_columns (eval_iter.c 251-271, called at 585: the freed columns and _trs disagree), before the result reaches the caller")]
    for i in [off:off + cnt] do
      let e := y.mem.getD i 0
      if i ≥ y.count then
        out := out ++ [("P-IT2 rows within the table", s!"result {n} covers row {i} of table {o}, whose count is {y.count}")]
      else if !y.hasP then
        out := out ++ [("P-IT3 results match the query", s!"result {n} returns e{e}, which does not have P (its table [{y.tags.map (fun k => s!"T{k}")}] took the memory of table {t}, freed during the iteration)")]
    if !out.isEmpty then return out.eraseDups
    -- the calls after this result, with its table locked
    for (k, op) in p.calls do
      if k == n then
        match runOp w (some o) op with
        | some w' => w := w'
        | none => return []
  return out

section
variable {m : Type → Type} [Monad m] [Pick m]

def genType (ntags : Nat) : m (Bool × List Nat) := do
  let hasP := (← Pick.pick "sl.hasP" 2) == 0
  let mask ← Pick.pick "sl.tags" (2 ^ ntags)
  return (hasP, (List.range ntags).filter (fun k => (mask >>> k) % 2 == 1))

def genOp (ntags nents : Nat) : m Op := do
  match (← Pick.pick "sl.call" 3) with
  | 0 => let (p, ts) ← genType ntags; return .newEnt p ts (← pickOf "sl.v" #[1, 3, 5])
  | 1 => return .deleteEnt (← Pick.pick "sl.e" nents)
  | _ => return .deleteTag (← Pick.pick "sl.k" ntags)

def genProg (ntags ninit ncalls : Nat) : m Prog := do
  let mut pol := #[]
  for _ in [0:ntags] do pol := pol.push ((← Pick.pick "sl.policy" 2) == 1)
  let mut init := []
  for i in [0:ninit] do
    let (p, ts) ← genType ntags
    init := init ++ [Op.newEnt p ts (2 * i + 2)]
  let mut calls := []
  for _ in [0:ncalls] do
    let k := (← Pick.pick "sl.k" 3) + 1
    calls := calls ++ [(k, ← genOp ntags (ninit + ncalls))]
  return { ntags, delPolicy := pol, init, calls }

end

def shrink (p : Prog) : List Prog :=
  (List.range p.calls.length).map (fun i => { p with calls := p.calls.eraseIdx i })

/-- The C test's program: T0 = Tag with OnDelete Delete, T1 = TagB.
    [P]: e0 (2), e2 (6); [P, T0]: e1 (4).  Slices: [P] row 0, [P, T0] row
    0, [P] row 1.  After the first result: delete T0 (deletes e1 and its
    table), then create an entity with only T1: its table takes the freed
    memory. -/
def cases : List (String × Prog) := [
  ("query_order_by_reused_table_slot",
    { ntags := 2, delPolicy := #[true, false],
      init := [.newEnt true [] 2, .newEnt true [0] 4, .newEnt true [] 6],
      calls := [(1, .deleteTag 0), (1, .newEnt false [1] 0)] }),
  ("no new table after the delete: the slice is skipped after its freed monitor is synced",
    { ntags := 2, delPolicy := #[true, false],
      init := [.newEnt true [] 2, .newEnt true [0] 4, .newEnt true [] 6],
      calls := [(1, .deleteTag 0)] }),
  ("the new table has P: its entity is returned from the stale slice",
    { ntags := 2, delPolicy := #[true, false],
      init := [.newEnt true [] 2, .newEnt true [0] 4, .newEnt true [] 6],
      calls := [(1, .deleteTag 0), (1, .newEnt true [1] 9)] }) ]

/-! ### Round 7: the dirty state planted in a zeroed table slot

  The skip of a slice whose table was freed calls
  `flecs_query_sync_match_monitor` (cache_iter.c 84-87), which calls
  `flecs_table_get_dirty_state` (storage/table.c 1432-1450) on the slice's
  table pointer: the store's zeroed memory.  Its `dirty_state` is NULL, so
  a block of `column_count + 1` = 1 int32 is allocated and its pointer
  written into the zeroed slot.  `flecs_table_new` (table_graph.c 433-470)
  takes the slot with `flecs_sparse_add_t`, which does not zero it
  (sparse.c 258-269), and neither it nor `flecs_table_init` sets
  `dirty_state`: the next table created there starts with the 1-int block.
  `flecs_table_mark_dirty` (storage/table.c 1397-1429), on every `ecs_set`
  and `ecs_modified` of a column of that table, increments
  `dirty_state[column]` with column >= 1; query monitors read
  `dirty_state[tc.column + 1]` (change_detection.c 581-633).  The block
  is freed with the new table's size (storage/table.c 1318:
  `flecs_wfree_n(world, int32_t, table->column_count + 1, ...)`).

  The model continues the iteration after the skip (round 6's `check`
  stops at the first violation), then runs calls after it.  Property P1:
  no write or read past an allocation.  The freed monitor written by the
  same skip is round 6's F46 (P1, use after free), not counted again. -/

inductive Post
  /-- `ecs_new` with the type, after the iteration -/
  | newEnt (hasP : Bool) (tags : List Nat)
  /-- `ecs_set(world, e, P, ...)` on the k-th entity created after the
      iteration -/
  | setP (k : Nat)
  deriving Repr, BEq, Inhabited

def showPost : Post → String
  | .newEnt p ts => s!"ecs_new [{if p then "P, " else ""}{ts.map (fun k => s!"T{k}")}]"
  | .setP k => s!"ecs_set(n{k}, P)"

structure Prog7 where
  base : Prog
  post : List Post
  deriving Inhabited

instance : Repr Prog7 := ⟨fun p _ => .text s!"{repr p.base}; after the iteration: {p.post.map showPost}"⟩

/-- The slots holding a planted dirty state after the iteration (and the
    round-6 P1 of the same skip, as a flag). -/
def iterateLeaks (p : Prog) : Option (W × List Nat × Bool) := Id.run do
  let mut w : W := { delPolicy := p.delPolicy }
  for op in p.init do
    match runOp w none op with
    | some w' => w := w'
    | none => return none
  let (w1, slices) := buildSlices w
  w := w1
  let mut n := 0
  let mut leaks : List Nat := []
  let mut uaf := false
  for (t, off, cnt) in slices do
    let x := w.tables.getD t default
    let occ := if x.live then some t else
      (List.range w.tables.size).find? (fun t' =>
        let y := w.tables.getD t' default
        y.live && y.slot == x.slot)
    match occ with
    | none =>
      -- the zeroed slot: count 0, skipped; the sync plants a dirty state
      uaf := true
      if !leaks.contains x.slot then leaks := x.slot :: leaks
      continue
    | some o =>
      let y := w.tables.getD o default
      if y.count == 0 then
        if o != t then uaf := true
        continue
      if o != t then return none  -- round 6's P-IT3/P1 forms: not this model
      n := n + 1
      let _ := off + cnt
      for (k, op) in p.calls do
        if k == n then
          match runOp w (some o) op with
          | some w' => w := w'
          | none => return none
  return some (w, leaks, uaf)

def check7 (p : Prog7) : List (String × String) := Id.run do
  let some (w0, leaks, _) := iterateLeaks p.base | return []
  if leaks.isEmpty then return []
  let mut w := w0
  -- the planted block per live table: a table created in a planted slot
  let mut planted : List Nat := []   -- table indices
  let mut created : Array Nat := #[] -- entity ids created after the iteration
  let mut leaksLeft := leaks
  for op in p.post do
    match op with
    | .newEnt hp ts =>
      if ts.any (fun k => w.deadTags.contains k) then return []
      let before := w.tables.size
      let (w', t) := ensureTable w hp ts
      w := w'
      if w.tables.size > before then
        let slot := (w.tables.getD t default).slot
        if leaksLeft.contains slot then
          planted := t :: planted
          leaksLeft := leaksLeft.erase slot
      w := newEnt w hp ts 0
      created := created.push (w.ents.size - 1)
    | .setP k =>
      let some e := created[k]? | continue
      let t := (w.ents.getD e default).table
      let x := w.tables.getD t default
      if !x.hasP then continue
      if planted.contains t then
        return [("P1 no write past an allocation", s!"ecs_set(P) on an entity of table {t} [P{String.join (x.tags.map (fun k => s!", T{k}"))}], created after the iteration in the slot of a table freed during it: the skip of that table's slice allocated a 1-element dirty state into the zeroed slot (cache_iter.c 84-87, change_detection.c 600-606, storage/table.c 1432-1450), which flecs_table_new keeps (table_graph.c 443, sparse.c 258-269); flecs_table_mark_dirty writes dirty_state[1] (storage/table.c 1397-1429), past the block")]
  return []

section
variable {m : Type → Type} [Monad m] [Pick m]

def genPost (ntags : Nat) (len : Nat) : m (List Post) := do
  let mut out := []
  for _ in [0:len] do
    match (← Pick.pick "sl7.post" 2) with
    | 0 => let (hp, ts) ← genType ntags; out := out ++ [Post.newEnt hp ts]
    | _ => out := out ++ [Post.setP (← Pick.pick "sl7.k" 2)]
  return out

def genProg7 (ntags ninit ncalls npost : Nat) : m Prog7 := do
  let b ← genProg ntags ninit ncalls
  return { base := b, post := ← genPost ntags npost }

end

def shrink7 (p : Prog7) : List Prog7 :=
  (shrink p.base).map (fun b => { p with base := b }) ++
  (List.range p.post.length).map (fun i => { p with post := p.post.eraseIdx i })

def cases7 : List (String × Prog7) := [
  ("query_order_by_freed_slot_dirty_state: after the iteration, ecs_new [P, T1], then ecs_set P",
    { base := { ntags := 2, delPolicy := #[true, false],
                init := [.newEnt true [] 2, .newEnt true [0] 4, .newEnt true [] 6],
                calls := [(1, .deleteTag 0)] },
      post := [.newEnt true [1], .setP 0] }),
  ("control: no delete during the iteration",
    { base := { ntags := 2, delPolicy := #[true, false],
                init := [.newEnt true [] 2, .newEnt true [0] 4, .newEnt true [] 6],
                calls := [] },
      post := [.newEnt true [1], .setP 0] }),
  ("control: the delete before the iterator is created",
    { base := { ntags := 2, delPolicy := #[true, false],
                init := [.newEnt true [] 2, .newEnt true [0] 4, .newEnt true [] 6, .deleteTag 0],
                calls := [] },
      post := [.newEnt true [1], .setP 0] }) ]

end Flecs.Slices
