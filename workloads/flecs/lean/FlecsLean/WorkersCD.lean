/-
  Round 4: what the worker threads of a multi-threaded system write when
  its query has change detection, at the granularity of single loads and
  stores, transcribed from flecs v4.2.0:
  - every worker iterates the whole query (`ecs_worker_next`, iter.c
    1036-1095, calls `ecs_iter_next` on the chained query iterator for every
    table and takes a slice of its rows);
  - each `ecs_query_next` first runs change detection on the previous
    result (eval_iter.c 217-234, 492-500): `flecs_query_sync_match_monitor`
    (change_detection.c 581-633);
  - that allocates the match's monitor when it has none
    (`flecs_query_get_match_monitor`, 79-138: `flecs_balloc` from
    `cache->allocators.monitors`, then `match->_monitor = monitor`), and the
    table's dirty state when it has none (`flecs_table_get_dirty_state`,
    storage/table.c 1432-1450: `flecs_alloc_n(&world->allocator, ...)` then
    `table->dirty_state = ...`), and writes `cache->prev_match_count`
    (change_detection.c 632);
  - `flecs_balloc` (datastructures/block_allocator.c 141-187) takes the head
    of a free list: `result = ba->head; ba->head = ba->head->next`.
  No lock is taken by any of these: the worker threads run the op's systems
  in parallel between two sync points (worker.c, Systems.md "Threading").

  The model: `threads` stages, each iterating tables 0..n-1 of the system's
  cache.  Tables start without a dirty state and their matches without a
  monitor (tables matched since the query last ran on the main thread).
  Each step is one load or store.  Properties:
  - PW3: an allocator never gives the same chunk to two allocations (a
    free-list race; the chunk then backs two arrays);
  - PW4: no allocation is lost (written to a pointer that another thread
    overwrites);
  - PW5: no data race: two threads access the same location, one of them
    writing, without synchronization (C11 5.1.2.4: undefined behavior).
-/
import FlecsLean.Search

namespace Flecs.WCD
open Determinismo

/-- Locations. -/
inductive Loc
  | monHead | dirtyHead | prevMatchCount
  | monitor (t : Nat) | dirty (t : Nat)
  deriving Repr, BEq, Inhabited

def Loc.show : Loc → String
  | .monHead => "cache->allocators.monitors.head"
  | .dirtyHead => "world->allocator (dirty-state size class).head"
  | .prevMatchCount => "cache->prev_match_count"
  | .monitor t => s!"match(table {t})->_monitor"
  | .dirty t => s!"table {t}->dirty_state"

/-- Program counter of a worker: table `t`, step `s`, and a register. -/
structure PC where
  t : Nat := 0
  s : Nat := 0
  reg : Nat := 0
  deriving Repr, BEq, Inhabited

structure Mem where
  ntables : Nat
  /-- free lists: next chunk ids (chunks are numbered; 0 = NULL) -/
  monHead : Nat
  dirtyHead : Nat
  monitor : Array Nat
  dirty : Array Nat
  /-- chunks handed out: (allocator, chunk, thread, table) -/
  given : Array (String × Nat × Nat × Nat) := #[]
  /-- accesses: (location, thread, write?) since the op began -/
  acc : Array (Loc × Nat × Bool) := #[]
  deriving Inhabited

abbrev WM := ProcessM Mem PC

def mem : WM Mem := return (← get).memory
def modMem (f : Mem → Mem) : WM Unit := modify fun p => { p with memory := f p.memory }

/-- PW5: record an access and report a race with another thread's access. -/
def access (t : Nat) (l : Loc) (w : Bool) : WM Unit := do
  let m ← mem
  for (l', t', w') in m.acc do
    if l' == l && t' != t && (w || w') then
      violate "PW5 no data race" s!"threads {t'} and {t} access {l.show} ({if w' then "write" else "read"}, then {if w then "write" else "read"}) with no synchronization between them"
  modMem fun m => { m with acc := m.acc.push (l, t, w) }

/-- Record an allocation, checking PW3. -/
def give (alloc : String) (chunk thread table : Nat) : WM Unit := do
  let m ← mem
  for (a, c, th, tb) in m.given do
    if a == alloc && c == chunk then
      violate "PW3 one chunk per allocation" s!"{alloc} gave chunk {chunk} to thread {th} (table {tb}) and to thread {thread} (table {table}): both read the free-list head before either stored the next one (block_allocator.c 172-173)"
  modMem fun m => { m with given := m.given.push (alloc, chunk, thread, table) }

/-- One step of worker `th`.  The steps per table (after its result):
    0 read match->_monitor; 1 read monitors head; 2 write monitors head;
    3 write match->_monitor; 4 read table->dirty_state; 5 read dirty head;
    6 write dirty head; 7 write table->dirty_state; 8 write
    prev_match_count. -/
def step (races : Bool) (th : Nat) (pc : PC) : WM (StepResult PC) := do
  let m ← mem
  if pc.t ≥ m.ntables then return .done
  let t := pc.t
  let acc := fun l w => if races then access th l w else pure ()
  match pc.s with
  | 0 =>
    acc (.monitor t) false
    if m.monitor.getD t 0 != 0 then return .ran { pc with s := 4 }
    return .ran { pc with s := 1 }
  | 1 => acc .monHead false; return .ran { pc with s := 2, reg := m.monHead }
  | 2 =>
    acc .monHead true
    -- chunks are consecutive: the next free chunk is reg + 1
    modMem fun m => { m with monHead := pc.reg + 1 }
    give "monitors" pc.reg th t
    return .ran { pc with s := 3 }
  | 3 =>
    acc (.monitor t) true
    let old := m.monitor.getD t 0
    if old != 0 then
      violate "PW4 no lost allocation" s!"thread {th} stores monitor chunk {pc.reg} into match(table {t})->_monitor over chunk {old}, which another thread stored after both saw NULL (change_detection.c 90-92, 134): chunk {old} leaks"
    modMem fun m => { m with monitor := m.monitor.set! t pc.reg }
    return .ran { pc with s := 4 }
  | 4 =>
    acc (.dirty t) false
    if m.dirty.getD t 0 != 0 then return .ran { pc with s := 8 }
    return .ran { pc with s := 5 }
  | 5 => acc .dirtyHead false; return .ran { pc with s := 6, reg := m.dirtyHead }
  | 6 =>
    acc .dirtyHead true
    modMem fun m => { m with dirtyHead := pc.reg + 1 }
    give "world allocator" pc.reg th t
    return .ran { pc with s := 7 }
  | 7 =>
    acc (.dirty t) true
    let old := m.dirty.getD t 0
    if old != 0 then
      violate "PW4 no lost allocation" s!"thread {th} stores dirty-state chunk {pc.reg} into table {t}->dirty_state over chunk {old}, which another thread stored after both saw NULL (table.c 1438-1442): chunk {old} leaks, and the counts written to it are lost"
    modMem fun m => { m with dirty := m.dirty.set! t pc.reg }
    return .ran { pc with s := 8 }
  | _ =>
    acc .prevMatchCount true
    return .ran { t := t + 1, s := 0, reg := 0 }

structure Cfg where
  threads : Nat := 2
  tables : Nat := 1
  /-- report data races (PW5); off: look only for PW3 and PW4 -/
  races : Bool := true
  maxSteps : Nat := 200
  deriving Repr, Inhabited

def timeline (cfg : Cfg) (src : Source) : Ended := Id.run do
  let start : Process Mem PC :=
    { memory := { ntables := cfg.tables, monHead := 1, dirtyHead := 1,
                  monitor := Array.replicate cfg.tables 0, dirty := Array.replicate cfg.tables 0 },
      threads := Array.replicate cfg.threads (some {}) }
  let body : WM Unit := interleave { step := step cfg.races } cfg.maxSteps
  let (r, p) := runProcess start body src
  match r with
  | .error (.violation prop detail) =>
    return { taken := p.decisions.taken, violation := some (prop, detail) }
  | _ => return { taken := p.decisions.taken, violation := none }

end Flecs.WCD
