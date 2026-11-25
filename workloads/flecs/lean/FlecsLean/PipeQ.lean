/-
  Round 4: when the pipeline rebuilds its schedule, transcribed from
  flecs v4.2.0:
  - `flecs_pipeline_build` (addons/pipeline/pipeline.c 263-473) rebuilds only
    when `ecs_query_match_count(pq->query)` (query/api.c 717-728: the cache's
    `match_count`) differs from the count it recorded (269-274).  It records
    the count at 465, after the schedule is built; when the schedule is
    empty it returns at 390-392 without recording it;
  - the cache's `match_count` goes up when a table is added to or removed
    from the cache (group.c 169, 181), when a table is revalidated
    (match.c 356, whatever the result), and when an iteration of a sorted
    query finds a table whose entities changed
    (order_by.c 312-315; every pipeline query is sorted, pipeline.c 800-801);
  - revalidation is requested by the rematch observers for terms with `up`
    traversal (cache.c 334-430), except for a table with the `Parent`
    component and a ChildOf term (cache.c 268-273): such tables are filtered
    per entity when the query is iterated (compiler.c 632-727, the
    `has_childof_trav` filter);
  - terms that are not cached (a fixed source; a DontFragment component,
    validator.c 837-859) are evaluated when the query is iterated, so a
    change of what they match changes no table of the cache.

  The world: systems, a module entity M, one phase P, a `Game` entity and a
  tag `Running`, a DontFragment tag `Foo`.  Each system is a child of M
  through `(ChildOf, M)` or through the `Parent` component, or has no
  parent.  The pipeline is the builtin one (`System, Phase(cascade
  DependsOn), !Disabled(up DependsOn), !Disabled(up ChildOf)`, pipeline.c
  979-990) or a custom one: `System, Running(Game)` or `System, Foo`.
  Calls happen between frames; a frame runs the schedule.
-/
import FlecsLean.Search2

namespace Flecs.PipeQ

inductive ParentKind | none | childOf | parentComp
  deriving Repr, BEq, Inhabited, DecidableEq

inductive PipeKind | builtin | fixedSrc | dontFragment
  deriving Repr, BEq, Inhabited, DecidableEq

structure SysE where
  parent : ParentKind
  disabled : Bool := false
  foo : Bool := false
  deriving Repr, BEq, Inhabited

structure St where
  kind : PipeKind
  sys : Array SysE
  moduleDisabled : Bool := false
  phaseDisabled : Bool := false
  running : Bool := false
  /-- the cache: (table key, its system entities); a table key is
      (parent kind, Foo? (no: DontFragment), disabled) -/
  cacheTables : List ParentKind := []
  matchCount : Nat := 0
  /-- `pq->match_count`: none is -1 -/
  pqCount : Option Nat := none
  schedule : List Nat := []
  frames : Nat := 0
  deriving Inhabited

/-- The table a system lives in: its parent storage (with M for ChildOf) and
    the Disabled tag; Foo is DontFragment and does not change the table. -/
def tableKey (s : SysE) : ParentKind × Bool := (s.parent, s.disabled)

/-- Does the cache (table level) hold the table of `key`?  Disabled tables
    are not matched (observer.c 253-273, match.c 304-310).  The up terms:
    `!Disabled(up DependsOn)` on the phase; `!Disabled(up ChildOf)` on M for
    a `(ChildOf, M)` table; a `Parent` table passes at table level (it is
    filtered per entity). -/
def cacheMatches (st : St) (key : ParentKind × Bool) : Bool :=
  let (pk, dis) := key
  if dis then false
  else match st.kind with
    | .builtin =>
      !st.phaseDisabled && !(pk == .childOf && st.moduleDisabled)
    | _ => true

/-- What the whole query matches, per system (the reference). -/
def queryMatches (st : St) (k : Nat) : Bool :=
  let s := st.sys.getD k default
  if s.disabled then false
  else match st.kind with
    | .builtin => !st.phaseDisabled && !(s.parent != .none && st.moduleDisabled)
    | .fixedSrc => st.running
    | .dontFragment => s.foo

def keysNow (st : St) : List (ParentKind × Bool) :=
  (st.sys.toList.map tableKey).eraseDups

/-- Bring the cache up to date after a call: tables that start or stop
    matching through a cached term are added or removed (match_count + 1);
    `revalidated` tables bump the count too (match.c 356). -/
def syncCache (st : St) (revalidated : List ParentKind) (moved : Bool) : St := Id.run do
  let mut st := st
  let want := (keysNow st).filter (cacheMatches st) |>.map (·.1)
  let mut n := st.matchCount
  for t in st.cacheTables do
    if !want.contains t then n := n + 1
  for t in want do
    if !st.cacheTables.contains t then n := n + 1
  for t in revalidated do
    if st.cacheTables.contains t || want.contains t then n := n + 1
  -- order_by.c 312-315: a cached table whose entities changed
  if moved then n := n + 1
  st := { st with cacheTables := want, matchCount := n }
  return st

inductive Op
  | disableModule | enableModule
  | disablePhase | enablePhase
  | disableSys (k : Nat) | enableSys (k : Nat)
  | addRunning | removeRunning
  | addFoo (k : Nat) | removeFoo (k : Nat)
  | progress
  deriving Repr, BEq, Inhabited

/-- `flecs_pipeline_update` at the start of a frame: rebuild if the count
    changed; record it only for a non-empty schedule (pipeline.c 390-392,
    465). -/
def update (st : St) : St := Id.run do
  if st.pqCount == some st.matchCount then return st
  let sched := (List.range st.sys.size).filter (fun k =>
    let s := st.sys.getD k default
    -- iterate the cache's tables, then the uncached filters
    st.cacheTables.contains (tableKey s).1 && !s.disabled && queryMatches st k)
  if sched.isEmpty then return { st with schedule := [] }
  return { st with schedule := sched, pqCount := some st.matchCount }

def step (st : St) (op : Op) : St × List (String × String) := Id.run do
  match op with
  | .progress =>
    let st := update st
    let expected := (List.range st.sys.size).filter (queryMatches st)
    let mut out := []
    if st.schedule != expected then
      out := [("PA2 the pipeline runs what its query matches",
        s!"frame {st.frames}: the pipeline ({repr st.kind}) runs systems {st.schedule}, its query matches {expected} (systems {st.sys.toList.map (fun s => repr s.parent)}, module disabled {st.moduleDisabled}, phase disabled {st.phaseDisabled}, Running {st.running}, Foo {st.sys.toList.map (·.foo)}; cache match_count {st.matchCount}, recorded {repr st.pqCount})")]
    return ({ st with frames := st.frames + 1 }, out)
  | .disableModule | .enableModule =>
    let v := op == .disableModule
    if st.moduleDisabled == v then return (st, [])
    let st := { st with moduleDisabled := v }
    -- rematch observers of `Disabled(up ChildOf)`: every child table, except
    -- those with the Parent component (cache.c 268-273)
    let reval := (keysNow st).map (·.1) |>.filter (· == .childOf)
    return (syncCache st reval false, [])
  | .disablePhase | .enablePhase =>
    let v := op == .disablePhase
    if st.phaseDisabled == v then return (st, [])
    let st := { st with phaseDisabled := v }
    if st.kind != .builtin then return (st, [])
    let reval := (keysNow st).map (·.1)
    return (syncCache st reval false, [])
  | .disableSys k | .enableSys k =>
    if k ≥ st.sys.size then return (st, [])
    let v := op == .disableSys k
    if (st.sys.getD k default).disabled == v then return (st, [])
    let st := { st with sys := st.sys.modify k (fun s => { s with disabled := v }) }
    return (syncCache st [] true, [])
  | .addRunning | .removeRunning =>
    -- Game is not a system: no table of the cache changes
    return ({ st with running := op == .addRunning }, [])
  | .addFoo k | .removeFoo k =>
    if k ≥ st.sys.size then return (st, [])
    -- DontFragment: the system stays in its table
    return ({ st with sys := st.sys.modify k (fun s => { s with foo := op == .addFoo k }) }, [])

structure Prog where
  kind : PipeKind
  parents : Array ParentKind
  running0 : Bool
  foo0 : Bool
  ops : List Op
  deriving Inhabited

def run (p : Prog) : List (String × String) := Id.run do
  let st0 : St := { kind := p.kind, sys := p.parents.map (fun pk => { parent := pk, foo := p.foo0 }),
                    running := p.running0 }
  -- tables are created and matched when the systems are created
  let mut st := syncCache st0 [] false
  for op in p.ops do
    let (st', vs) := step st op
    st := st'
    if !vs.isEmpty then return vs
  return []

def check (p : Prog) : List (String × String) := run p

section
variable {m : Type → Type} [Monad m] [Pick m]

def genProg (nsys len : Nat) : m Prog := do
  let kind ← pickOf "pq.kind" #[PipeKind.builtin, .fixedSrc, .dontFragment]
  let mut ps := #[]
  for _ in [0:nsys] do ps := ps.push (← pickOf "pq.parent" #[ParentKind.none, .childOf, .parentComp])
  let running0 := (← Pick.pick "pq.running0" 2) == 1
  let foo0 := (← Pick.pick "pq.foo0" 2) == 1
  let mut ops := []
  for _ in [0:len] do
    let o ← match (← Pick.pick "pq.call" 8) with
      | 0 => pickOf "pq.module" #[Op.disableModule, .enableModule]
      | 1 => pickOf "pq.phase" #[Op.disablePhase, .enablePhase]
      | 2 => do pure (Op.disableSys (← Pick.pick "pq.sys" nsys))
      | 3 => do pure (Op.enableSys (← Pick.pick "pq.sys" nsys))
      | 4 => pickOf "pq.running" #[Op.addRunning, .removeRunning]
      | 5 => do pure (Op.addFoo (← Pick.pick "pq.sys" nsys))
      | 6 => do pure (Op.removeFoo (← Pick.pick "pq.sys" nsys))
      | _ => pure Op.progress
    ops := ops ++ [o]
  return { kind, parents := ps, running0, foo0, ops := [.progress] ++ ops ++ [.progress] }

end

def shrink (p : Prog) : List Prog :=
  (List.range p.ops.length).map (fun i => { p with ops := p.ops.eraseIdx i })

instance : Repr Prog := ⟨fun p _ => .text s!"pipeline {repr p.kind}; systems' parents {p.parents.toList.map (fun x => repr x)}; Game has Running {p.running0}; systems have Foo {p.foo0}; calls {p.ops.map (fun o => toString (repr o))}"⟩

/-- The C tests' programs. -/
def cases : List (String × Prog) := [
  ("pipeline_parent_module_disabled (Parent hierarchy)",
    { kind := .builtin, parents := #[.parentComp], running0 := false, foo0 := false,
      ops := [.progress, .disableModule, .progress] }),
  ("pipeline_parent_module_disabled (ChildOf control)",
    { kind := .builtin, parents := #[.childOf], running0 := false, foo0 := false,
      ops := [.progress, .disableModule, .progress] }),
  ("pipeline_custom_uncached_term (Running(Game))",
    { kind := .fixedSrc, parents := #[.none], running0 := true, foo0 := true,
      ops := [.progress, .removeRunning, .progress, .progress] }),
  ("pipeline_custom_uncached_term (Foo, DontFragment)",
    { kind := .dontFragment, parents := #[.none], running0 := true, foo0 := true,
      ops := [.progress, .removeFoo 0, .progress, .progress] }),
  ("empty schedule: the count is not recorded, so it rebuilds (no failure)",
    { kind := .fixedSrc, parents := #[.none], running0 := false, foo0 := false,
      ops := [.progress, .addRunning, .progress] }) ]

end Flecs.PipeQ
