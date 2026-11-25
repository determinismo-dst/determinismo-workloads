/-
  The pipeline: how it decides sync points and how it runs a frame,
  transcribed from flecs v4.2.0 src/addons/pipeline/pipeline.c and the parts
  of src/addons/system/system.c and src/query/validator.c that feed it.

  A system is reduced to what the pipeline reads from it: the terms of its
  query after validation (id, source, operator, access modifier), whether it
  is active (its query matches something: no `EcsEmpty` tag), its
  `multi_threaded` and `immediate` flags, and, for the frame simulation, what
  its commands do to the pipeline's own query when they are merged (disable
  or delete a system, enable one, make one active).

  The pipeline query is the builtin one: systems in a single phase ordered by
  entity id (pipeline.c 978-991, `flecs_entity_compare`).  It rebuilds when
  its match count changes (pipeline.c 269-274).  Because it is sorted, every
  change of a matched table, an entity moving in or out of it, bumps the match
  count (query/cache/order_by.c 309-312), so any change to the set of enabled
  active systems causes a rebuild.  That is how the model decides rebuilds.
-/
import FlecsLean.Ids
import FlecsLean.Gen
import FlecsLean.World

namespace Flecs.Pipe
open Flecs

/-- Where a term's component comes from (`ecs_term_ref_t src`). -/
inductive Src
  /-- `$this`, `self` (the default for a plain term) -/
  | thisSelf
  /-- `$this`, `up` only -/
  | thisUp
  /-- `$this`, `self|up` -/
  | thisSelfUp
  /-- no source: `X()`, `src.id = EcsIsEntity` with id 0 -/
  | zero
  /-- a fixed entity: `X(Game)` -/
  | fixed
  deriving Repr, BEq, Inhabited, DecidableEq

inductive Oper | and | not | optional
  deriving Repr, BEq, Inhabited, DecidableEq

inductive InOut | default_ | none | filter | in_ | out | inout
  deriving Repr, BEq, Inhabited, DecidableEq

structure Term where
  id : Id
  src : Src := .thisSelf
  oper : Oper := .and
  inout : InOut := .default_
  deriving Repr, BEq, Inhabited

/-- What a system's commands do to the pipeline when they are merged. -/
inductive Effect
  | none
  /-- `ecs_enable(it->world, it->system, false)` or `ecs_delete` of itself -/
  | disableSelf
  /-- disable system `k` (pipeline order index in the program) -/
  | disable (k : Nat)
  /-- enable system `k` -/
  | enable (k : Nat)
  /-- system `k` starts matching an entity (loses `EcsEmpty`) -/
  | activate (k : Nat)
  deriving Repr, BEq, Inhabited

structure Sys where
  terms : List Term
  active : Bool := true
  enabled : Bool := true
  mt : Bool := false
  immediate : Bool := false
  effect : Effect := .none
  deriving Repr, Inhabited

/-- `flecs_term_finalize` (query/validator.c 1113-1126): a Not term and a
    term for `*` or `(*, *)` default to `InOutNone`. -/
def finalize (t : Term) : Term :=
  if t.inout == .default_ && (t.oper == .not || t.id == EcsWildcard ||
      t.id == mkPair EcsWildcard EcsWildcard) then { t with inout := .none }
  else t

def isThis (s : Src) : Bool := s == .thisSelf || s == .thisUp || s == .thisSelfUp
def hasSelf (s : Src) : Bool := s == .thisSelf || s == .thisSelfUp

/-! ### Write state (pipeline.c 49-133) -/

structure WS where
  barrier : Bool := false
  ids : List Id := []
  wild : List Id := []
  deriving Repr, Inhabited, BEq

/-- `flecs_pipeline_get_write_state` (pipeline.c 61-105): true is
    `WriteStateToStage`. -/
def getWS (ws : WS) (id : Id) : Bool := Id.run do
  if ws.barrier then return true
  if id == EcsWildcard then
    if !ws.ids.isEmpty || !ws.wild.isEmpty then return true
  let mut result := false
  if !isWildcard id then
    if ws.ids.contains id then result := true
  else
    for k in ws.ids do
      if idMatch k id then return true
  for k in ws.wild do
    if idMatch id k then return true
  return result

/-- `flecs_pipeline_set_write_state` (pipeline.c 107-125) -/
def setWS (ws : WS) (id : Id) : WS :=
  if id == EcsWildcard then { ws with barrier := true }
  else if isWildcard id then
    if ws.wild.contains id then ws else { ws with wild := ws.wild ++ [id] }
  else if ws.ids.contains id then ws else { ws with ids := ws.ids ++ [id] }

/-- `flecs_pipeline_check_term` (pipeline.c 135-220) -/
def checkTerm (t : Term) (isActive : Bool) (ws : WS) : Bool × WS := Id.run do
  if t.inout == .filter then return (false, ws)
  let mut fromAny := t.src == .zero
  let fromThis := isThis t.src
  let isShared := !fromAny && (!fromThis || !hasSelf t.src)
  let isFixed := !fromAny && !fromThis
  let w := getWS ws t.id
  if fromThis && w then return (true, ws)
  let mut io := t.inout
  if io == .default_ then
    if fromAny then return (false, ws)
    else if isShared then io := .in_
    else io := .inout
  if t.oper == .not && io == .out then fromAny := true
  let mut ws := ws
  if fromAny || isFixed then
    if (io == .out || io == .inout) && isActive then ws := setWS ws t.id
    if (io == .in_ || io == .inout) && w then return (true, ws)
  return (false, ws)

/-- `flecs_pipeline_check_terms` (pipeline.c 222-250): `$this` terms first. -/
def checkTerms (ts : List Term) (isActive : Bool) (ws : WS) : Bool × WS := Id.run do
  let mut nm := false
  let mut ws := ws
  for t in ts do
    if isThis t.src then
      let (b, ws') := checkTerm t isActive ws
      nm := nm || b
      ws := ws'
  for t in ts do
    if !isThis t.src then
      let (b, ws') := checkTerm t isActive ws
      nm := nm || b
      ws := ws'
  return (nm, ws)

/-! ### Building the schedule (pipeline.c 263-473) -/

structure Op where
  offset : Nat
  count : Nat := 0
  mt : Bool := false
  immediate : Bool := false
  deriving Repr, Inhabited, BEq

structure Schedule where
  ops : Array Op := #[]
  /-- program indices of the systems in the schedule, in order -/
  systems : Array Nat := #[]
  deriving Repr, Inhabited

/-- `flecs_pipeline_build` (pipeline.c 263-394), the part that builds the ops.
    `sys` is the pipeline query's result in order: program index and system.
    Fails with the assert of pipeline.c 354. -/
def buildOps (sys : Array (Nat × Sys)) : Except String Schedule := do
  let mut ws : WS := {}
  let mut ops : Array Op := #[]
  let mut systems : Array Nat := #[]
  let mut op : Option Nat := none
  let mut mt := false
  let mut imm := false
  let mut first := true
  for (k, s) in sys do
    let ts := s.terms.map finalize
    let (nm0, ws1) := checkTerms ts s.active ws
    let mut nm := nm0
    ws := ws1
    if s.active then
      if first then
        mt := s.mt
        imm := s.immediate
        first := false
      if s.mt != mt then
        nm := true
        mt := s.mt
      if s.immediate != imm then
        nm := true
        imm := s.immediate
    if imm then nm := true
    if nm then
      ws := {}
      if let some o := op then
        if (ops.getD o default).count != 0 then op := none
      let mut nm2 := false
      if s.active then
        let (b, ws2) := checkTerms ts true ws
        nm2 := b
        ws := ws2
      if nm2 then
        throw s!"pipeline.c 354: ecs_assert(needs_merge == false, ECS_INTERNAL_ERROR) for system {k}"
    if op.isNone then
      ops := ops.push { offset := systems.size }
      op := some (ops.size - 1)
    if s.active then
      systems := systems.push k
      let o := op.getD 0
      let cur := ops.getD o default
      let cur := if cur.count == 0 then { cur with mt := mt, immediate := imm } else cur
      ops := ops.set! o { cur with count := cur.count + 1 }
  if let some o := op then
    if (ops.getD o default).count == 0 && ops.size > 1 then ops := ops.pop
  return { ops, systems }

/-- The op a system index of the schedule runs in. -/
def opOf (sc : Schedule) (i : Nat) : Nat := Id.run do
  for j in [0:sc.ops.size] do
    let o := sc.ops.getD j default
    if o.offset ≤ i && i < o.offset + o.count then return j
  return sc.ops.size

/-! ### Running a frame (pipeline.c 395-473, 475-675) -/

structure RunSt where
  sys : Array Sys
  sched : Schedule := {}
  /-- the enabled-and-active set the schedule was built from -/
  builtFrom : Option (List Nat) := none
  curOp : Option Nat := none
  curI : Nat := 0
  lastFrame : Array Nat
  frame : Nat := 1
  /-- systems that ran this frame, in order, with the op they ran in -/
  ran : Array (Nat × Nat) := #[]
  /-- (op, stage count) of each executed op -/
  executed : Array Op := #[]
  deriving Inhabited

def inPipeline (st : RunSt) : List Nat :=
  (List.range st.sys.size).filter (fun k => (st.sys.getD k default).enabled)

/-- the pipeline query's results (enabled systems, by entity id = program
    index), with each system's activity -/
def queryResult (st : RunSt) : Array (Nat × Sys) :=
  (inPipeline st).toArray.map (fun k => (k, st.sys.getD k default))

def activeKey (st : RunSt) : List Nat :=
  (inPipeline st).filter (fun k => (st.sys.getD k default).active)

/-- `flecs_pipeline_build` (pipeline.c 263-473), including the resume logic
    of 450-458: after a rebuild, `cur_op`/`cur_i` point at the last system in
    the new order that already ran this frame; if none did they keep their
    old values (an op index and a system index into the old schedule). -/
def build (st : RunSt) : Except String (RunSt × Bool) := do
  let key := (inPipeline st).map (fun k => (k, (st.sys.getD k default).active))
  let keyList := key.map (fun (k, a) => if a then k + 1000 else k)
  if st.builtFrom == some keyList then return (st, false)
  let sched ← buildOps (queryResult st)
  let mut st := { st with sched, builtFrom := some keyList }
  let mut opIndex := 0
  let mut ranSinceMerge := 0
  for i in [0:sched.systems.size] do
    let k := sched.systems.getD i 0
    ranSinceMerge := ranSinceMerge + 1
    if ranSinceMerge == (sched.ops.getD opIndex default).count then
      ranSinceMerge := 0
      opIndex := opIndex + 1
    if st.lastFrame.getD k 0 == st.frame then
      if opIndex < sched.ops.size then
        st := { st with curOp := some opIndex, curI := i }
      else
        st := { st with curOp := none, curI := 0 }
  if sched.ops.size != 0 then
    if let some c := st.curOp then
      if c ≥ sched.ops.size then
        throw s!"pipeline.c 467-470: ecs_assert(pq->cur_op <= ecs_vec_last(&pq->ops), ECS_INTERNAL_ERROR) (cur_op {c}, {sched.ops.size} ops)"
  return (st, true)

/-- `flecs_pipeline_next_system` (pipeline.c 475-489) -/
def nextSystem (st : RunSt) : RunSt :=
  match st.curOp with
  | none => st
  | some c =>
    let i := st.curI + 1
    let o := st.sched.ops.getD c default
    if i ≥ o.offset + o.count then
      let c' := c + 1
      { st with curI := i, curOp := if c' ≥ st.sched.ops.size then none else some c' }
    else { st with curI := i }

/-- `flecs_pipeline_update` (pipeline.c 491-519) -/
def update (st : RunSt) (startOfFrame : Bool) : Except String RunSt := do
  let (st, _) ← build st
  if startOfFrame then
    return { st with curOp := if st.sched.ops.size == 0 then none else some 0, curI := 0 }
  else return nextSystem st

/-- Apply the merged commands of the systems that ran in an op. -/
def applyEffects (st : RunSt) (ks : List Nat) : RunSt := Id.run do
  let mut sys := st.sys
  for k in ks do
    match (sys.getD k default).effect with
    | .none => pure ()
    | .disableSelf => sys := sys.modify k (fun s => { s with enabled := false })
    | .disable j => sys := sys.modify j (fun s => { s with enabled := false })
    | .enable j => sys := sys.modify j (fun s => { s with enabled := true })
    | .activate j => sys := sys.modify j (fun s => { s with active := true })
  return { st with sys }

/-- `flecs_run_pipeline` (pipeline.c 581-675) for one frame. -/
def runFrame (st : RunSt) : Except String RunSt := do
  let mut st ← update st true
  for _ in [0:64] do
    match st.curOp with
    | none => return st
    | some c =>
      if st.curI == st.sched.systems.size then
        st ← update st false
        continue
      let o := st.sched.ops.getD c default
      st := { st with executed := st.executed.push o }
      -- flecs_run_pipeline_ops (pipeline.c 545-579)
      let mut ranHere : List Nat := []
      let fin := o.offset + o.count
      let mut i := st.curI
      while i < fin do
        let k := st.sched.systems.getD i 0
        st := { st with lastFrame := st.lastFrame.set! k st.frame, ran := st.ran.push (k, c) }
        ranHere := ranHere ++ [k]
        i := i + 1
      -- readonly_end / commands_end: the op's commands are merged
      st := applyEffects st ranHere
      -- `return i - 1` (pipeline.c 578): i is max(cur_i, end) after the loop
      st := { st with curI := (max st.curI fin) - 1 }
      st ← update st false
  throw "model: frame did not terminate"

/-! ### Properties -/

/-- What a term pattern means (Queries.md "Wildcards", "Any"): `Any` stands
    for any id at its position, like `Wildcard`. -/
def semMatch (id pattern : Id) : Bool :=
  let fix := fun (x : UInt64) => if x == EcsAny then EcsWildcard else x
  let p := if isPair pattern then mkPair (fix (pairFirst pattern)) (fix (pairSecond pattern))
    else fix pattern
  idMatch id p

def overlap (u : List Id) (a b : Id) : Bool := u.any (fun c => semMatch c a && semMatch c b)

/-- Ids a system may enqueue commands for (Systems.md "Sync points": `out`
    on a term matched on no entity; the code also counts fixed sources and
    `[out] !X`). -/
def writes (s : Sys) : List Id :=
  (s.terms.map finalize).filterMap fun t =>
    let fromAny := t.src == .zero
    let fromThis := isThis t.src
    let isFixed := !fromAny && !fromThis
    let w := t.inout == .out || t.inout == .inout
    if t.inout != .filter && w && (fromAny || isFixed || (t.oper == .not && t.inout == .out)) then some t.id
    else none

/-- Ids a system reads, for sync purposes: every `$this` term (the system
    matches on the main storage), and `in`/`inout` (or shared default)
    terms matched on no entity or a fixed entity. -/
def reads (s : Sys) : List Id :=
  (s.terms.map finalize).filterMap fun t =>
    if t.inout == .filter then none
    else if isThis t.src then some t.id
    else
      let io := if t.inout == .default_ then (if t.src == .zero then InOut.none else .in_) else t.inout
      if io == .in_ || io == .inout then some t.id else none

structure Prog where
  sys : Array Sys
  threads : Bool := true
  deriving Inhabited

def showIdP (id : Id) : String :=
  let e := fun (x : UInt64) => if x == EcsWildcard then "*" else if x == EcsAny then "_" else toString x
  if isPair id then s!"({e (pairFirst id)}, {e (pairSecond id)})" else e id

/-- PP1 no internal assert; PP2 sync: a read of an id for which an earlier
    active system could have enqueued commands comes after a merge
    (Systems.md "Sync points"); PP3 immediate systems are single threaded
    (Systems.md "Immediate systems"); PP4 every system that is enabled and
    active for the whole frame runs exactly once (Systems.md "Pipelines": "A
    pipeline is a list of systems that is executed when ecs_progress is
    invoked"). -/
def checkProg (u : List Id) (p : Prog) : List (String × String) := Id.run do
  let mut out : List (String × String) := []
  -- schedule at the start of the frame
  let st0 : RunSt := { sys := p.sys, lastFrame := Array.replicate p.sys.size 0 }
  match buildOps (queryResult st0) with
  | .error e => return [("PP1 no-crash", e)]
  | .ok sc =>
    -- PP2
    let act := sc.systems
    for a in [0:act.size] do
      for b in [a+1:act.size] do
        let ka := act.getD a 0
        let kb := act.getD b 0
        let sa := p.sys.getD ka default
        let sb := p.sys.getD kb default
        if opOf sc a == opOf sc b then
          for w in writes sa do
            for r in reads sb do
              if overlap u w r then
                out := out ++ [("PP2 sync point", s!"system {ka} may enqueue commands for {showIdP w}, system {kb} reads {showIdP r}; they run in the same op without a merge")]
    -- PP3
    if p.threads then
      for o in sc.ops do
        if o.immediate && o.mt then
          out := out ++ [("PP3 immediate single-threaded", s!"op at {o.offset} (count {o.count}) is immediate and multi-threaded: its systems run on the worker threads, outside readonly mode")]
  -- PP4: run one frame
  match runFrame st0 with
  | .error e => out := out ++ [("PP1 no-crash", e)]
  | .ok st =>
    -- systems enabled and active at the start and never disabled during the
    -- frame
    -- round 4 correction: also not disabled in the middle of the frame (a
    -- system that ran and disabled it); round 2 compared only the start
    -- and the end of the frame
    let ranK := st.ran.toList.map (·.1)
    let disabledMid := fun (k : Nat) => ranK.any fun j =>
      match (p.sys.getD j default).effect with
      | .disable x => x == k
      | .disableSelf => j == k
      | _ => false
    let stable := (List.range p.sys.size).filter fun k =>
      let s := p.sys.getD k default
      s.enabled && s.active && (st.sys.getD k default).enabled && !disabledMid k
    for k in stable do
      let n := (st.ran.filter (·.1 == k)).size
      if n != 1 then
        out := out ++ [("PP4 every system runs", s!"system {k} was enabled and active for the whole frame but ran {n} times (ran: {st.ran.toList.map (·.1)})")]
        break
  return out

/-! ### Generators -/

section
variable {m : Type → Type} [Monad m] [Pick m]

def genPId (ids : Array Id) : m Id := pickOf "pipe.id" ids

def genTerm (ids : Array Id) : m Term := do
  let id ← genPId ids
  let src ← pickOf "pipe.src" #[Src.thisSelf, .zero, .thisUp, .fixed, .thisSelfUp]
  let oper ← pickOf "pipe.oper" #[Oper.and, .not, .optional]
  let io ← pickOf "pipe.inout" #[InOut.default_, .in_, .out, .inout, .none, .filter]
  return { id := id, src := src, oper := oper, inout := io }

def genEffect (n : Nat) : m Effect := do
  match (← Pick.pick "pipe.effect" 5) with
  | 0 => return .none
  | 1 => return .disableSelf
  | 2 => return .disable (← Pick.pick "pipe.effect.sys" n)
  | 3 => return .enable (← Pick.pick "pipe.effect.sys" n)
  | _ => return .activate (← Pick.pick "pipe.effect.sys" n)

def genSys (ids : Array Id) (n maxTerms : Nat) : m Sys := do
  let nt := (← Pick.pick "pipe.terms" maxTerms) + 1
  let mut ts := []
  for _ in [0:nt] do ts := ts ++ [← genTerm ids]
  let active := (← Pick.pick "pipe.active" 4) != 0
  let enabled := (← Pick.pick "pipe.enabled" 4) != 0
  let mt := (← Pick.pick "pipe.mt" 3) == 0
  let immediate := (← Pick.pick "pipe.immediate" 3) == 0
  let effect ← genEffect n
  return { terms := ts, active, enabled, mt, immediate, effect }

def genProg (ids : Array Id) (n maxTerms : Nat) : m Prog := do
  let mut sys := #[]
  for _ in [0:n] do sys := sys.push (← genSys ids n maxTerms)
  return { sys }

/-- A small menu for exhaustive enumeration of sync-point decisions: every
    system active and enabled, single-threaded, no effects. -/
def genSysSmall (ids : Array Id) (maxTerms : Nat) : m Sys := do
  let nt := (← Pick.pick "pipe.terms" maxTerms) + 1
  let mut ts := []
  for _ in [0:nt] do
    let id ← genPId ids
    let src ← pickOf "pipe.src" #[Src.thisSelf, .zero, .fixed]
    let oper ← pickOf "pipe.oper" #[Oper.and, .not]
    let io ← pickOf "pipe.inout" #[InOut.default_, .in_, .out, .inout]
    ts := ts ++ [({ id := id, src := src, oper := oper, inout := io } : Term)]
  return { terms := ts }

def genProgSmall (ids : Array Id) (n maxTerms : Nat) : m Prog := do
  let mut sys := #[]
  for _ in [0:n] do sys := sys.push (← genSysSmall ids maxTerms)
  return { sys }

/-- Frames: systems separated by sync points or mode switches, whose merged
    commands disable, enable or activate systems. -/
def genSysFrame (n : Nat) : m Sys := do
  let w := mkPair EcsWildcard EcsWildcard
  let _ := w
  let ts ← pickOf "pipe.frame.terms" #[([] : List Term),
    [{ id := C0, src := .zero, inout := .out }],
    [{ id := C0 }],
    [{ id := C0 }, { id := C0, src := .zero, inout := .out }]]
  let active := (← Pick.pick "pipe.active" 2) == 0
  let enabled := (← Pick.pick "pipe.enabled" 2) == 0
  let immediate := (← Pick.pick "pipe.immediate" 2) == 1
  let effect ← genEffect n
  return { terms := ts, active, enabled, immediate, effect }

def genProgFrame (n : Nat) : m Prog := do
  let mut sys := #[]
  for _ in [0:n] do sys := sys.push (← genSysFrame n)
  return { sys }

end

/-! ### The id menu -/

def R : Id := 400
def S : Id := 401
def T1 : Id := 402
def T2 : Id := 403

/-- Ids terms are drawn from: components, a pair, wildcard and Any pairs. -/
def idMenu : Array Id := #[C0, C1, mkPair R T1, mkPair R EcsWildcard,
  mkPair EcsWildcard T1, mkPair R EcsAny, mkPair EcsWildcard EcsWildcard, EcsWildcard]

/-- Concrete ids overlaps are decided over. -/
def concrete : List Id := [C0, C1, mkPair R T1, mkPair R T2, mkPair S T1, mkPair S T2]

/-- Drop one system, or one term of a system, or reset a flag. -/
def shrinkCands (p : Prog) : List Prog := Id.run do
  let mut out := []
  for i in [0:p.sys.size] do
    -- removing a system shifts later indices: only remove when no effect
    -- names a system
    out := out ++ [{ p with sys := p.sys.eraseIdx! i |>.map (fun s => { s with effect := match s.effect with
      | .disable j => if j == i then .none else .disable (if j > i then j - 1 else j)
      | .enable j => if j == i then .none else .enable (if j > i then j - 1 else j)
      | .activate j => if j == i then .none else .activate (if j > i then j - 1 else j)
      | e => e }) }]
  for i in [0:p.sys.size] do
    let s := p.sys.getD i default
    for j in [0:s.terms.length] do
      out := out ++ [{ p with sys := p.sys.set! i { s with terms := s.terms.eraseIdx j } }]
    if s.effect != .none then out := out ++ [{ p with sys := p.sys.set! i { s with effect := .none } }]
    if s.mt then out := out ++ [{ p with sys := p.sys.set! i { s with mt := false } }]
    if s.immediate then out := out ++ [{ p with sys := p.sys.set! i { s with immediate := false } }]
    if !s.active then out := out ++ [{ p with sys := p.sys.set! i { s with active := true } }]
    if !s.enabled then out := out ++ [{ p with sys := p.sys.set! i { s with enabled := true } }]
    for j in [0:s.terms.length] do
      let t := s.terms.getD j default
      if t.inout != .default_ then
        out := out ++ [{ p with sys := p.sys.set! i { s with terms := s.terms.set j { t with inout := .default_ } } }]
      if t.oper != .and then
        out := out ++ [{ p with sys := p.sys.set! i { s with terms := s.terms.set j { t with oper := .and } } }]
  return out

def showEnt (x : UInt64) : String :=
  if x == EcsWildcard then "*" else if x == EcsAny then "_" else if x == R then "R"
  else if x == S then "S" else if x == T1 then "T1" else if x == T2 then "T2"
  else if x == C0 then "C0" else if x == C1 then "C1" else toString x

def showId (id : Id) : String :=
  if isPair id then s!"({showEnt (pairFirst id)}, {showEnt (pairSecond id)})" else showEnt id

def showTerm (t : Term) : String :=
  let io := match t.inout with
    | .default_ => "" | .none => "[none] " | .filter => "[filter] " | .in_ => "[in] "
    | .out => "[out] " | .inout => "[inout] "
  let op := match t.oper with | .and => "" | .not => "!" | .optional => "?"
  let src := match t.src with
    | .thisSelf => "" | .thisUp => "(up)" | .thisSelfUp => "(self|up)" | .zero => "()" | .fixed => "(Game)"
  s!"{io}{op}{showId t.id}{src}"

def showSys (k : Nat) (s : Sys) : String :=
  let ts := ", ".intercalate (s.terms.map showTerm)
  let fl := (if s.active then [] else ["inactive"]) ++ (if s.enabled then [] else ["disabled"]) ++
    (if s.mt then ["multi_threaded"] else []) ++ (if s.immediate then ["immediate"] else []) ++
    (match s.effect with
      | .none => [] | .disableSelf => ["disables itself"] | .disable j => [s!"disables S{j}"]
      | .enable j => [s!"enables S{j}"] | .activate j => [s!"activates S{j}"])
  s!"S{k}: [{ts}] {", ".intercalate fl}"

def showProg (p : Prog) : String :=
  "; ".intercalate ((List.range p.sys.size).map (fun k => showSys k (p.sys.getD k default)))

instance : Repr Prog := ⟨fun p _ => .text (showProg p)⟩

def check (p : Prog) : List (String × String) := checkProg concrete p

/-! ### Round 4: the builtin systems of `ecs_init()`

`ecs_init()` imports FlecsScript (world.c 987-989), whose async addon creates
`ProgressTasks` (addons/script/eval/async.c 1428-1433): an immediate system
without terms in `EcsPreUpdate`, so it is always active.  Systems in
`EcsOnUpdate` and later phases run after it; systems in `EcsOnLoad` and
`EcsPostLoad` run before it (the cascade on DependsOn, pipeline.c 935-985).
Round 2's frame model had only the program's systems. -/

def progressTasks : Sys := { terms := [], immediate := true }

def shiftEffect (d : Nat) : Effect → Effect
  | .disable j => .disable (j + d)
  | .enable j => .enable (j + d)
  | .activate j => .activate (j + d)
  | e => e

/-- The program in a world made by `ecs_init()`: `ProgressTasks` runs before
    the program's systems (`front`, phases from OnUpdate on) or after them
    (OnLoad, PostLoad). -/
def withBuiltin (p : Prog) (front : Bool) : Prog :=
  if front then { p with sys := #[progressTasks] ++ p.sys.map (fun s => { s with effect := shiftEffect 1 s.effect }) }
  else { p with sys := p.sys.push progressTasks }

/-- The systems that ran in one frame, in order, or the assert. -/
def frameRuns (p : Prog) : Except String (List Nat) := do
  let st0 : RunSt := { sys := p.sys, lastFrame := Array.replicate p.sys.size 0 }
  let st ← runFrame st0
  return st.ran.toList.map (·.1)

end Flecs.Pipe
