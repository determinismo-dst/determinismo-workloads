/-
  Round 6: allocations and writes of the worker threads outside the table
  walk: the iterator each worker creates for a multi-threaded system whose
  query has order_by.  Transcribed from flecs v4.2.0:
  - every stage that runs a multi-threaded system creates its own iterator
    over the system's query (`flecs_run_intern`, addons/system/system.c
    80-81, then `ecs_worker_iter`, 99-101); the main thread runs stage 0
    while the workers run the others (pipeline.c 627-645, worker.c 34-60);
  - `ecs_query_iter` -> `flecs_query_iter` (eval_iter.c 782-860) ->
    `flecs_query_cache_iter_init` (cache_iter.c 11-37): for an order_by
    query `flecs_query_cache_sort_tables` (order_by.c 228-321) first;
  - that checks each match's monitor (`flecs_query_check_table_monitor`,
    change_detection.c 441-459): a match without one gets it
    (`flecs_query_get_match_monitor`, 79-138: `flecs_balloc` from the
    cache's monitor allocator) and counts as changed; a changed table is
    sorted in place (`flecs_query_cache_sort_table`, order_by.c 12-45: the
    quicksort of `ECS_SORT_TABLE_WITH_COMPARE`, flecs_c.h 795-860, swaps
    rows with `flecs_table_swap`, storage/table.c 2014-2090: entity ids,
    records, every column);
  - then the slices are rebuilt (`flecs_query_cache_build_sorted_tables`,
    order_by.c 215-225: `ecs_vec_clear` and `ecs_vec_append_t(NULL, ...)`,
    an OS realloc) and `cache->match_count` incremented (319-320);
  - the monitor is synced only when the iteration moves past the table
    (eval_iter.c 217-234), so until then every other stage that creates its
    iterator sees the table as changed too.
  Nothing takes a lock.  The sort's swap is three steps here: read the two
  rows, write the first, write the second (entities[row_1] = e2;
  entities[row_2] = e1, table.c 2050-2052).

  The model: `threads` stages, one table of `rows` entities in reverse
  order, no monitor yet.  Each stage: check the monitor (allocate it when
  missing), sort the table with a selection sort made of swaps (the
  quicksort's swap is the same three steps), rebuild the slices, increment
  match_count.  Properties:
  - PW5 (round 4): no data race;
  - PW6: a sort leaves the table a permutation of its entities, each
    record pointing at its row (Systems.md "Threading": staging "makes it
    safe for multiple threads to iterate the same world without taking
    locks").
-/
import FlecsLean.Search

namespace Flecs.WSort
open Determinismo

inductive Loc
  | monitor | monHead | row (i : Nat) | slices | matchCount | dirty
  deriving Repr, BEq, Inhabited

def Loc.show : Loc → String
  | .monitor => "match->_monitor"
  | .monHead => "cache->allocators.monitors.head"
  | .row i => s!"table->data.entities[{i}] (and the record and columns of that row)"
  | .slices => "cache->table_slices"
  | .matchCount => "cache->match_count"
  | .dirty => "table->dirty_state[0] and the match monitor's copy of it"

/-- A stage's program counter: phase and registers. -/
structure PC where
  s : Nat := 0
  /-- selection sort: the outer index, the inner index, the min so far -/
  i : Nat := 0
  j : Nat := 0
  mn : Nat := 0
  /-- the two rows read for a swap -/
  a : Nat := 0
  b : Nat := 0
  reg : Nat := 0
  deriving Repr, BEq, Inhabited

structure Mem where
  rows : Array Nat
  monitor : Nat := 0
  /-- the monitor equals the table's dirty state (a sync happened after the
      last swap) -/
  synced : Bool := false
  monHead : Nat := 1
  matchCount : Nat := 0
  acc : Array (Loc × Nat × Bool) := #[]
  deriving Inhabited

abbrev WM := ProcessM Mem PC

def mem : WM Mem := return (← get).memory
def modMem (f : Mem → Mem) : WM Unit := modify fun p => { p with memory := f p.memory }

/-- `races`: 0 none, 1 every location, 2 only the table's rows and the
    slices (the sort itself; the monitor race is F33's). -/
def access (races : Nat) (t : Nat) (l : Loc) (w : Bool) : WM Unit := do
  if races == 0 then return
  if races == 2 then
    match l with
    | .row _ | .slices => pure ()
    | _ => return
  let m ← mem
  for (l', t', w') in m.acc do
    if l' == l && t' != t && (w || w') then
      violate "PW5 no data race" s!"stages {t'} and {t} access {l.show} ({if w' then "write" else "read"}, then {if w then "write" else "read"}) with no synchronization: both create an iterator over the order_by system's query (system.c 80-81) and both sort the table in place (order_by.c 228-321, flecs_table_swap)"
  modMem fun m => { m with acc := m.acc.push (l, t, w) }

/-- Steps:
    0 read monitor; 1 read monitor head; 2 write head; 3 write monitor
    (then the table is "changed": sort);
    10 outer loop; 11 inner compare (read row j and row mn); 12 swap read
    rows; 13 write row i; 14 write row mn;
    20 rebuild slices; 21 read match_count; 22 write match_count; done. -/
def step (races : Nat) (th : Nat) (pc : PC) : WM (StepResult PC) := do
  let m ← mem
  let n := m.rows.size
  let acc := access races th
  match pc.s with
  | 0 =>
    acc .monitor false
    -- flecs_query_check_table_monitor: a missing monitor is allocated (and
    -- the table counts as changed); an existing one is compared with the
    -- table's dirty state
    if m.monitor != 0 then
      acc .dirty false
      if m.synced then return .ran { pc with s := 30 }
      return .ran { pc with s := 10, i := 0 }
    return .ran { pc with s := 1 }
  | 1 => acc .monHead false; return .ran { pc with s := 2, reg := m.monHead }
  | 2 => acc .monHead true; modMem (fun m => { m with monHead := pc.reg + 1 }); return .ran { pc with s := 3 }
  | 3 => acc .monitor true; modMem (fun m => { m with monitor := pc.reg }); return .ran { pc with s := 10, i := 0 }
  | 10 =>
    if pc.i + 1 ≥ n then return .ran { pc with s := 20 }
    return .ran { pc with s := 11, j := pc.i + 1, mn := pc.i }
  | 11 =>
    if pc.j ≥ n then return .ran { pc with s := 12 }
    acc (.row pc.j) false
    acc (.row pc.mn) false
    let mn := if m.rows.getD pc.j 0 < m.rows.getD pc.mn 0 then pc.j else pc.mn
    return .ran { pc with j := pc.j + 1, mn }
  | 12 =>
    if pc.mn == pc.i then return .ran { pc with s := 10, i := pc.i + 1 }
    acc (.row pc.i) false
    acc (.row pc.mn) false
    return .ran { pc with s := 13, a := m.rows.getD pc.i 0, b := m.rows.getD pc.mn 0 }
  | 13 =>
    acc (.row pc.i) true
    -- flecs_table_swap marks the table dirty (storage/table.c 2034)
    acc .dirty true
    modMem (fun m => { m with rows := m.rows.set! pc.i pc.b, synced := false })
    return .ran { pc with s := 14 }
  | 14 =>
    acc (.row pc.mn) true
    modMem (fun m => { m with rows := m.rows.set! pc.mn pc.a })
    return .ran { pc with s := 10, i := pc.i + 1 }
  | 20 => acc .slices true; return .ran { pc with s := 21 }
  | 21 => acc .matchCount false; return .ran { pc with s := 22, reg := m.matchCount }
  | 22 =>
    acc .matchCount true
    modMem (fun m => { m with matchCount := pc.reg + 1 })
    return .ran { pc with s := 30 }
  | 30 =>
    -- the iteration moves past the table: flecs_query_sync_match_monitor
    -- (eval_iter.c 217-234; change_detection.c 581-633)
    acc .dirty true
    modMem (fun m => { m with synced := true })
    return .ran { pc with s := 99 }
  | _ => return .done

structure Cfg where
  threads : Nat := 2
  rows : Nat := 3
  races : Nat := 1
  maxSteps : Nat := 400
  deriving Repr, Inhabited

def timeline (cfg : Cfg) (src : Source) : Ended := Id.run do
  let start : Process Mem PC :=
    { memory := { rows := (List.range cfg.rows).reverse.toArray },
      threads := Array.replicate cfg.threads (some {}) }
  let body : WM Unit := do
    interleave { step := step cfg.races } cfg.maxSteps
    -- PW6: the table is still a permutation of its entities
    let m ← mem
    let want := List.range cfg.rows
    let got := m.rows.toList
    if got.mergeSort (· ≤ ·) != want then
      violate "PW6 sorting keeps the entities" s!"after the stages sorted the table at once, its entity column is {got}: some entities appear twice and others are gone (two flecs_table_swap calls interleaved on the same rows)"
    let _ := m.matchCount
  let (r, p) := runProcess start body src
  match r with
  | .error (.violation prop detail) =>
    return { taken := p.decisions.taken, violation := some (prop, detail) }
  | _ => return { taken := p.decisions.taken, violation := none }

end Flecs.WSort
