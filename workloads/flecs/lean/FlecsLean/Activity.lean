/-
  Round 3: system activity (the `EcsEmpty` tag) and the pipeline, from
  flecs v4.2.0:
  - `ecs_run_aperiodic(world, EcsAperiodicEmptyQueries)` (world.c 1338-1365):
    every query whose `ecs_query_is_true` is false gets `EcsEmpty`;
  - query creation (cache.c 885-903): a cache with no matched table gets
    `EcsEmpty`; tables are matched when created, empty or not
    (cache.c 195-208, 547-565);
  - `flecs_query_cache_add_table` (group.c 216-245): the only place
    `EcsEmpty` is removed, when the first table joins an empty cache;
  - `flecs_query_cache_remove_table` (group.c 302-329), reached through
    `ecs_delete_empty_tables` (world.c 1367-...): a table leaves the cache;
  - the pipeline schedules only systems without `EcsEmpty`
    (pipeline.c 295-296, 357-376).

  A system is reduced to which table kinds its query matches.  Tables are
  created empty; entities are added to and removed from them.  `progress`
  runs the systems the pipeline schedules.

  PA1 (Systems.md "Pipelines": "A pipeline is a list of systems that is
  executed when the ecs_progress/world::progress function is invoked", and
  "Sync points": a system is inactive when "it doesn't match any
  entities"): an enabled system whose query matches an entity when
  `ecs_progress` starts runs in that frame.
-/
import FlecsLean.Search

namespace Flecs.Activity
open Determinismo

structure Tbl where
  kind : Nat
  count : Nat := 0
  live : Bool := true
  deriving Repr, Inhabited

structure Sys where
  /-- table kinds the query matches -/
  kinds : List Nat
  created : Bool := false
  cache : List Nat := []
  empty : Bool := false
  deriving Repr, Inhabited

structure St where
  tables : Array Tbl := #[]
  sys : Array Sys
  log : Array String := #[]
  deriving Inhabited

inductive AOp
  /-- the first entity of a new table kind creates the table (or adds to it) -/
  | addEntity (kind : Nat)
  | removeEntity (kind : Nat)
  | createSystem (k : Nat)
  | emptyQueries
  /-- `ecs_delete_empty_tables` with zero thresholds -/
  | deleteEmpty
  | progress
  deriving Repr, BEq, Inhabited

def tableOf (st : St) (kind : Nat) : Option Nat := Id.run do
  for i in [0:st.tables.size] do
    let t := st.tables.getD i default
    if t.live && t.kind == kind then return some i
  return none

/-- `flecs_query_cache_add_table` (group.c 216-245) -/
def addToCache (st : St) (k t : Nat) : St :=
  let s := st.sys.getD k default
  let wasEmpty := s.cache.isEmpty
  let s := { s with cache := s.cache ++ [t] }
  let s := if wasEmpty then { s with empty := false } else s
  { st with sys := st.sys.set! k s }

/-- `ecs_query_is_true` (api.c 706-713) for a cache: some matched table has
    an entity. -/
def isTrue (st : St) (s : Sys) : Bool :=
  s.cache.any (fun t => (st.tables.getD t default).count > 0)

def apply (st : St) (op : AOp) : St × List (String × String) := Id.run do
  let mut st := st
  let mut out : List (String × String) := []
  match op with
  | .addEntity kind =>
    match tableOf st kind with
    | some t =>
      st := { st with tables := st.tables.modify t (fun x => { x with count := x.count + 1 }) }
    | none =>
      -- a new table: every query matching it adds it (OnTableCreate)
      let t := st.tables.size
      st := { st with tables := st.tables.push { kind, count := 1 } }
      for k in [0:st.sys.size] do
        let s := st.sys.getD k default
        if s.created && s.kinds.contains kind then st := addToCache st k t
  | .removeEntity kind =>
    if let some t := tableOf st kind then
      st := { st with tables := st.tables.modify t (fun x => { x with count := x.count - 1 }) }
  | .createSystem k =>
    let s := st.sys.getD k default
    if !s.created then
      let mut s := { s with created := true }
      for t in [0:st.tables.size] do
        let x := st.tables.getD t default
        if x.live && s.kinds.contains x.kind then s := { s with cache := s.cache ++ [t] }
      -- cache.c 900-903
      if s.cache.isEmpty then s := { s with empty := true }
      st := { st with sys := st.sys.set! k s }
  | .emptyQueries =>
    for k in [0:st.sys.size] do
      let s := st.sys.getD k default
      if s.created && !isTrue st s then
        st := { st with sys := st.sys.set! k { s with empty := true } }
  | .deleteEmpty =>
    for t in [0:st.tables.size] do
      let x := st.tables.getD t default
      if x.live && x.count == 0 then
        st := { st with tables := st.tables.set! t { x with live := false } }
        for k in [0:st.sys.size] do
          let s := st.sys.getD k default
          st := { st with sys := st.sys.set! k { s with cache := s.cache.erase t } }
  | .progress =>
    for k in [0:st.sys.size] do
      let s := st.sys.getD k default
      if !s.created then continue
      let hasMatch := isTrue st s
      let runs := !s.empty
      if hasMatch && !runs then
        out := out ++ [("PA1 active systems run", s!"system {k} matches {(s.cache.filter (fun t => (st.tables.getD t default).count > 0)).length} non-empty table(s) but has EcsEmpty, so ecs_progress does not run it")]
  st := { st with log := st.log.push s!"{repr op}" }
  return (st, out)

def run (nsys : Nat) (kinds : Array (List Nat)) (ops : List AOp) : List (String × String) × St := Id.run do
  let mut st : St := { sys := (List.range nsys).toArray.map (fun k => { kinds := kinds.getD k [] }) }
  for op in ops do
    let (st', vs) := apply st op
    st := st'
    if !vs.isEmpty then return (vs, st)
  return ([], st)

structure AProg where
  kinds : Array (List Nat)
  ops : List AOp
  deriving Repr, Inhabited

def check (p : AProg) : List (String × String) := (run p.kinds.size p.kinds p.ops).1

section
variable {m : Type → Type} [Monad m] [Pick m]

def genAOp (nsys nkinds : Nat) : m AOp := do
  match (← Pick.pick "act.call" 6) with
  | 0 => return .addEntity (← Pick.pick "act.kind" nkinds)
  | 1 => return .removeEntity (← Pick.pick "act.kind" nkinds)
  | 2 => return .createSystem (← Pick.pick "act.sys" nsys)
  | 3 => return .emptyQueries
  | 4 => return .deleteEmpty
  | _ => return .progress

/-- Two systems over two table kinds: system 0 matches kind 0, system 1
    kinds 0 and 1 (or only 1). -/
def genAProg (len : Nat) : m AProg := do
  let k1 ← pickOf "act.sys1.kinds" #[[1], [0, 1]]
  let mut ops := []
  for _ in [0:len] do ops := ops ++ [← genAOp 2 2]
  return { kinds := #[[0], k1], ops := ops ++ [.progress] }

end

def shrinkA (p : AProg) : List AProg :=
  (List.range p.ops.length).map (fun i => { p with ops := p.ops.eraseIdx i })

end Flecs.Activity
