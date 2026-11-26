/-
  Round 5: the query compiler and the query VM for cached queries whose
  uncached part is Sparse terms, transcribed from flecs v4.2.0:
  - `flecs_query_compile` (query/compiler/compiler.c 1047-1340): the
    `SetIds` op (1093-1110), the cache op of
    `flecs_query_insert_cache_search` (632-747: every cacheable term is
    marked compiled, one `EcsQueryCache` op writes `$this`), the order in
    which the remaining terms are compiled (1126-1190), and the `Yield`;
  - `flecs_query_compile_term` (compiler_term.c 1147-1563) for a `$this`
    self term: `is_or`/`first_or`/`last_or` (1173-1180), the Or-chain write
    state (1218-1222, 1290-1295), the conditional-evaluation block
    (1349-1353, 152-240), Not/Optional/Or blocks (1361-1368, 117-155,
    245-280), `flecs_query_mark_last_or_op` (1016-1021) and
    `flecs_query_end_block_or` (282-360);
  - `flecs_query_op_insert` (compiler_term.c 98-115);
  - the VM: `flecs_query_run_until` (engine/eval.c 1733-1785) with
    `flecs_query_dispatch` (1656-1731) for SetIds (1193-1214), Cache
    (532-546, cache_iter.c 356-378), And on a written `$this`
    (`flecs_query_with`, eval.c 150-252), Or with a written source
    (`flecs_query_with_or`, 1510-1524), Not (1553-1563), Optional
    (1565-1590), IfVar (1592-1625), End (1647-1654), `flecs_query_run_block`
    (1327-1349) and `flecs_query_reset_after_block` (1264-1325);
  - `ecs_query_next` for the VM (eval_iter.c 573-586): `qit->op` is the op
    before the Yield.

  Terms are `$this` self terms on three components, each a table component
  or a fragmenting Sparse component (DontFragment terms compile to other ops
  and are not cached, so their chains stay consistent; round 4).  The cache
  is round 4's `Val` transcription; the cache's own query is all table
  terms and is evaluated as documented.  Paths the model does not
  transcribe (`select` ops on an unwritten `$this`, a cache test) make the
  program "unmodelled"; the search counts them.
-/
import FlecsLean.Validator

namespace Flecs.OrVM
open Flecs.Val

inductive Kind | setIds | cache | and_ | or_ | not_ | optional | end_ | yield | ifVar | all
  deriving Repr, BEq, Inhabited, DecidableEq

/-- `ecs_query_op_t`: kind, labels, the term's component; `wr` is bit 0
    (`$this`) of `op->written`. -/
structure QOp where
  kind : Kind
  prev : Int := 0
  next : Int := 0
  comp : Nat := 0
  wr : Bool := false
  /-- an Or op's source is the `$this` variable (begin_block_or 268-275) -/
  srcVar : Bool := false
  deriving Repr, Inhabited, BEq

/-- `FlecsRuleOrMarker` (compiler_term.c 64) -/
def orMarker : Int := -2

/-- The compile context (`ecs_query_compile_ctx_t`), bit 0 (`$this`) of its
    write masks, and `ctrlflow[0]`. -/
structure CCtx where
  ops : Array QOp := #[]
  written : Bool := false
  condWritten : Bool := false
  writtenOr : Bool := false
  condWrittenOr : Bool := false
  inOr : Bool := false
  lblBegin : Int := -1
  lblQuery : Int := -1
  lblCondEval : Int := 0
  /-- accesses outside the op array -/
  oob : Array String := #[]
  unmodelled : Option String := none
  deriving Inhabited

abbrev CM := StateM CCtx

def opAt (c : CCtx) (i : Int) : QOp := if i < 0 then default else c.ops.getD i.toNat default

def setOp (i : Int) (f : QOp → QOp) : CM Unit :=
  modify fun c => if i < 0 then c else { c with ops := c.ops.modify i.toNat f }

/-- `flecs_query_op_insert` (compiler_term.c 98-115) -/
def insert (op : QOp) : CM Int := do
  let c ← get
  let count := c.ops.size + 1
  let mut op := { op with next := (count : Int), prev := (count : Int) - 2 }
  if count > 1 && c.lblBegin == -1 then
    -- "Variables written by previous instruction can't be written by this
    -- instruction, except when this is part of an OR chain"
    if (c.ops.getD (c.ops.size - 1) default).wr then op := { op with wr := false }
  set { c with ops := c.ops.push op }
  return (count : Int) - 1

/-- `flecs_query_begin_block` (117-127) -/
def beginBlock (k : Kind) (srcVar : Bool := false) : CM Unit := do
  let i ← insert { kind := k, srcVar }
  modify fun c => { c with lblBegin := i }

/-- `flecs_query_end_block` (129-155), `reset = true` -/
def endBlock : CM Unit := do
  let e ← insert { kind := .end_ }
  let c ← get
  setOp c.lblBegin (fun o => { o with next := e })
  setOp e (fun o => { o with prev := c.lblBegin })
  modify fun c => { c with lblBegin := -1 }

/-- `flecs_query_end_block_or` (282-360) -/
def endBlockOr : CM Unit := do
  let e ← insert { kind := .end_ }
  let c ← get
  let lb := c.lblBegin
  let mut prevOr : Int := lb + 1
  for k in [0:(e - (lb + 1)).toNat] do
    let i : Int := lb + 1 + k
    if (opAt (← get) i).next == orMarker then
      if i == e - 1 then setOp prevOr (fun o => { o with prev := lb })
      else setOp prevOr (fun o => { o with prev := i + 1 })
      setOp i (fun o => { o with next := e })
      prevOr := i + 1
  let mut srcIsVar := false
  if lb < 0 then
    -- `ecs_query_op_t *first = &ops[ctx->cur->lbl_begin]` with lbl_begin -1
    modify fun c => { c with oob := c.oob.push "compiler_term.c 306-309: flecs_query_end_block_or reads ops[-1].flags and ops[-1].src and writes ops[-1].next (lbl_begin is -1: the chain's first term was compiled into the cache, so no Or block was begun)" }
  else
    srcIsVar := (opAt (← get) lb).srcVar
    setOp lb (fun o => { o with next := e })
  setOp e (fun o => { o with prev := lb })
  setOp (e - 1) (fun o => { o with prev := lb })
  modify fun c => { c with inOr := false, lblBegin := -1 }
  if srcIsVar then modify fun c => { c with written := true }
  modify fun c => { c with written := c.written || c.condWritten }

/-- `flecs_query_begin_block_cond_eval` (157-217): an IfVar op when `$this`
    was conditionally written. -/
def beginCondEval (condWriteState : Bool) : CM Unit := do
  let c ← get
  let cws := if c.inOr then c.condWrittenOr else condWriteState
  if cws then
    modify fun c => { c with lblCondEval := (c.ops.size : Int) }
    discard <| insert { kind := .ifVar }
  else modify fun c => { c with lblCondEval := -1 }

/-- `flecs_query_end_block_cond_eval` (219-240) -/
def endCondEval : CM Unit := do
  let c ← get
  if c.lblCondEval == -1 then return
  let e ← insert { kind := .end_ }
  let c ← get
  setOp c.lblCondEval (fun o => { o with next := e })
  setOp e (fun o => { o with prev := c.lblCondEval })

/-- `flecs_query_compile_term` for an uncached `$this` self term. -/
def compileTerm (ts : Array VTerm) (i : Nat) : CM Unit := do
  let t := ts.getD i default
  let prevOr := i > 0 && (ts.getD (i - 1) default).oper == .or
  let isOr := t.oper == .or || prevOr
  let firstOr := isOr && !prevOr
  let lastOr := isOr && t.oper != .or
  let condWrite := t.oper == .optional || isOr
  -- 1218-1222
  if firstOr then modify fun c => { c with condWrittenOr := c.condWritten, inOr := true }
  else if isOr then modify fun c => { c with written := c.writtenOr }
  let isNot := t.oper == .not
  let isOpt := t.oper == .optional
  let condWriteState := (← get).condWritten
  let srcWritten := (← get).written
  -- 1290-1295
  if firstOr then modify fun c => { c with writtenOr := c.written }
  -- 1297-1302: flecs_query_select_all for Not/Optional on an unwritten source
  if !srcWritten && (isNot || isOpt) then
    -- round 7: flecs_query_select_all (compiler_term.c 787-826): an All op
    -- that writes $this (816) and `flecs_query_write_ctx(src, ctx, false)`
    discard <| insert { kind := .all, wr := true }
    modify fun c => { c with written := true }
  -- 1349-1353
  if (← get).condWritten && (!isOr || firstOr) then beginCondEval condWriteState
  -- 1361-1368
  if isNot then beginBlock .not_
  else if isOpt then beginBlock .optional
  else if firstOr then beginBlock .or_ (srcVar := true)
  -- 1458-1461: the source is written (conditionally for Or/Optional)
  let w0 := (← get).written
  modify fun c => { c with written := true, condWritten := c.condWritten || (!w0 && condWrite) }
  let idx ← insert { kind := .and_, comp := t.comp, wr := true }
  modify fun c => { c with lblQuery := idx }
  if isOr then setOp idx (fun o => { o with next := orMarker })
  if isNot || isOpt then endBlock
  if lastOr then endBlockOr
  -- 1540-1544
  let c ← get
  if c.lblCondEval != 0 && (!isOr || lastOr) then endCondEval

/-- `flecs_query_compile` for a query with a cache (cache kind Auto): which
    terms are cached is the validator's decision (round 4). -/
def compile (q : FQuery) (ts : Array VTerm) : CCtx := Id.run do
  let prog : CM Unit := do
    -- 1093-1110: SetIds (the terms have fixed ids)
    discard <| insert { kind := .setIds }
    -- 632-747: the cache op writes $this (flecs_query_write_ctx(0, false))
    discard <| insert { kind := .cache, wr := true }
    modify fun c => { c with written := true }
    let n := ts.size
    let mut compiled : Array Bool := q.terms.map (·.cacheable)
    -- 1133-1137
    let mut startTerm := 0
    for _ in [0:n] do
      if startTerm < n && (ts.getD startTerm default).oper == .optional then startTerm := startTerm + 1
      else break
    let mut pass := startTerm
    for _ in [0:2] do
      for i in [pass:n] do
        if compiled.getD i true then continue
        if (ts.getD i default).oper == .optional && pass != 0 then break
        compileTerm ts i
        compiled := compiled.set! i true
      if pass != 0 then pass := 0 else break
    -- Yield (1309-1312)
    discard <| insert { kind := .yield }
  let ((), c) := prog.run {}
  return c

/-! ### The VM -/

structure OpCtx where
  /-- `ecs_query_ctrl_ctx_t::op_index` -/
  opIndex : Int := 0
  /-- `ecs_query_and_ctx_t::remaining` -/
  remaining : Nat := 0
  /-- round 7: the table iterator of a select (`op_ctx->it`) or an All
      (`op_ctx->cur`): the next table index to look at -/
  tcur : Nat := 0
  deriving Inhabited

structure VM where
  ops : Array QOp
  /-- the cache's tables in cache order (non-empty and empty), as indices
      into `types` -/
  cache : Array Nat
  types : Array (List Nat)
  counts : Array Nat
  opIndex : Int := 0
  written : Array Bool
  opCtx : Array OpCtx
  cacheCur : Nat := 0
  /-- `vars[0].range.table` -/
  this : Option Nat := none
  /-- `vars[0].entity == EcsWildcard` (eval_iter.c 882; the cache op only
      sets the range, cache_iter.c 373-375) -/
  thisEntityUnset : Bool := true
  unmodelled : Option String := none
  markerReached : Bool := false
  deriving Inhabited

abbrev VMM := StateM VM

def vop (i : Int) : VMM QOp := do
  let v ← get
  return if i < 0 then default else v.ops.getD i.toNat default

def wrAt (i : Int) : VMM Bool := do
  let v ← get
  return if i < 0 then false else v.written.getD i.toNat false

def setWr (i : Int) (b : Bool) : VMM Unit :=
  modify fun v => if i < 0 then v else { v with written := v.written.set! i.toNat b }

def ctxAt (i : Int) : VMM OpCtx := do
  let v ← get
  return if i < 0 then default else v.opCtx.getD i.toNat default

def setCtx (i : Int) (f : OpCtx → OpCtx) : VMM Unit :=
  modify fun v => if i < 0 then v else { v with opCtx := v.opCtx.modify i.toNat f }

def unmod (s : String) : VMM Unit := modify fun v => { v with unmodelled := v.unmodelled <|> some s }

/-- Round 7: a select's table walk (`flecs_table_cache_iter` with
    `EcsTableNotEmpty`, then `flecs_query_var_set_range(op, src, table, 0,
    0)`, which sets `vars[0].entity = 0`, eval_utils.c 163-183). -/
def selectTables (me : Int) (sel : List Nat → Bool) (redo : Bool) : VMM Bool := do
  let v ← get
  let oc ← ctxAt me
  let start := if redo then oc.tcur else 0
  let mut cur := start
  while cur < v.types.size do
    if sel (v.types.getD cur []) && v.counts.getD cur 0 != 0 then
      setCtx me (fun c => { c with tcur := cur + 1 })
      modify fun v => { v with this := some cur, thisEntityUnset := false }
      return true
    cur := cur + 1
  setCtx me (fun c => { c with tcur := cur })
  return false

/-- `flecs_query_last_op_for_or_cond` (eval.c 1351-1364) -/
def lastOpForOrCond (ops : Array QOp) (cur last : Int) : Int := Id.run do
  let mut c := cur
  for _ in [0:ops.size + 1] do
    let o := if c < 0 then default else ops.getD c.toNat default
    let atLast := c == last
    c := c + 1
    if o.next == last || atLast then return c
  return c

mutual

/-- `flecs_query_run_until` (eval.c 1733-1785) -/
partial def runUntil (redo0 : Bool) (first cur last : Int) (fuel : Nat) : VMM Bool := do
  if fuel == 0 then unmod "fuel"; return false
  modify fun v => { v with opIndex := cur }
  let mut redo := redo0
  for _ in [0:500] do
    let i := (← get).opIndex
    let op ← vop i
    let result ← dispatch op redo (fuel - 1)
    let cur' := if result then op.next else op.prev
    if cur' == orMarker then modify fun v => { v with markerReached := true }
    -- ctx->op_index may have been moved by a nested run_until
    let oi := (← get).opIndex
    redo := cur' < oi
    if !redo then setWr cur' ((← wrAt cur') || (← wrAt oi) || op.wr)
    modify fun v => { v with opIndex := cur' }
    if cur' ≤ first then return false
    if !(cur' < last) then return true
    if (← get).unmodelled.isSome then return false
  unmod "loop bound"
  return false

/-- `flecs_query_run_block` (1327-1349) -/
partial def runBlock (redo : Bool) (fuel : Nat) : VMM Bool := do
  let me := (← get).opIndex
  if !redo then setCtx me (fun c => { c with opIndex := me + 1 })
  else
    let oc ← ctxAt me
    if (← vop oc.opIndex).kind == .end_ then return false
  setWr (me + 1) (← wrAt me)
  let op ← vop me
  let oc ← ctxAt me
  let r ← runUntil redo me oc.opIndex op.next fuel
  let after := (← get).opIndex
  setCtx me (fun c => { c with opIndex := after - 1 })
  return r

/-- `flecs_query_reset_after_block` (1264-1325): the End's field is the
    term's (end_block copies it), so a failed block moves `op_index` to the
    End. -/
partial def resetAfterBlock (me : Int) (result : Bool) : VMM Unit := do
  let start ← vop me
  let endI := start.next
  if result then return
  let oi := (← get).opIndex
  setWr endI (← wrAt oi)
  modify fun v => { v with opIndex := endI }
  setCtx me (fun c => { c with opIndex := endI })

partial def dispatch (op : QOp) (redo : Bool) (fuel : Nat) : VMM Bool := do
  let me := (← get).opIndex
  match op.kind with
  | .setIds => return !redo
  | .yield => return false
  | .end_ => return !redo
  | .cache =>
    let w ← wrAt me
    setWr (me + 1) true
    if w then unmod "cache test (cache_iter.c 381-393)"; return false
    if !redo then modify fun v => { v with cacheCur := 0 }
    -- flecs_query_cache_next: skip empty tables
    let v ← get
    let mut cur := v.cacheCur
    while cur < v.cache.size do
      let t := v.cache.getD cur 0
      if v.counts.getD t 0 != 0 then
        modify fun v => { v with cacheCur := cur + 1, this := some t }
        return true
      cur := cur + 1
    modify fun v => { v with cacheCur := cur }
    return false
  | .all =>
    -- flecs_query_all (eval.c 254-315): written $this: once
    if (← wrAt me) then return !redo
    selectTables me (fun _ => true) redo
  | .and_ =>
    if !(← wrAt me) then
      -- round 7: flecs_query_select (eval.c 136-148) ->
      -- flecs_query_select_w_id (52-134): the non-empty tables of the
      -- component's table cache, one result per table (the component is
      -- in a type once: `remaining` is 0)
      return (← selectTables me (fun ty => ty.contains op.comp) redo)
    -- flecs_query_with on the written table
    let v ← get
    let some t := v.this | return false
    if !redo then
      if (v.types.getD t []).contains op.comp then
        setCtx me (fun c => { c with remaining := 1 })
        return true
      return false
    let oc ← ctxAt me
    let rem := oc.remaining - 1
    setCtx me (fun c => { c with remaining := rem })
    return rem > 0
  | .or_ =>
    if op.srcVar && !(← wrAt me) then return (← selectOr op me redo fuel)
    -- flecs_query_with_or
    let r ← runBlock redo fuel
    if r then setCtx me (fun c => { c with opIndex := op.next })
    return r
  | .not_ =>
    if redo then return false
    let r ← runBlock false fuel
    resetAfterBlock me r
    return !r
  | .optional =>
    let r ← runBlock redo fuel
    resetAfterBlock me r
    if !redo then return true
    -- same table range as before: no second yield
    return r
  | .ifVar =>
    if !redo then
      if (← get).thisEntityUnset then
        resetAfterBlock me false
        return true
    runBlock redo fuel

/-- Round 7: `flecs_query_select_or` (eval.c 1390-1508), with
    `flecs_query_run_until_for_select_or` (1366-1388). -/
partial def selectOr (op : QOp) (me : Int) (redo0 : Bool) (fuel : Nat) : VMM Bool := do
  let first := me + 1
  let mut redo := redo0
  if !redo then setCtx me (fun c => { c with opIndex := first })
  let ops := (← get).ops
  let firstOp ← vop (first - 1)
  let last := firstOp.next
  let mut curOp := (← ctxAt me).opIndex
  let mut result := false
  for _ in [0:64] do
    let cur := (← ctxAt me).opIndex
    modify fun v => { v with opIndex := cur }
    -- 1414: ctx->written[cur] = ctx->written[first - 1] | op->written
    setWr cur ((← wrAt (first - 1)) || op.wr)
    -- run_until_for_select_or
    let lfc := lastOpForOrCond ops cur last
    let start := if redo then lfc - 1 else cur
    discard <| runUntil redo (first - 1) start lfc fuel
    result := (← get).opIndex == last
    if result then
      if first == cur then break
      -- 1426-1480: is an earlier term of the chain true for this result?
      setWr first (← wrAt last)
      let saved ← ctxAt first
      setCtx first (fun _ => {})
      discard <| runUntil false (first - 1) first cur fuel
      setCtx first (fun _ => saved)
      if (← get).opIndex == last then
        -- a duplicate: find the next result (`continue` tests cur_op)
        redo := true
        if curOp == last then break
        continue
      break
    -- 1499-1504: no result, the next term of the chain
    let ni := lastOpForOrCond ops (← ctxAt me).opIndex last
    setCtx me (fun c => { c with opIndex := ni })
    curOp := ni
    redo := false
    if curOp == last then break
  return result

end

/-- `ecs_query_next` until it returns false: the tables yielded, in order. -/
def iterate (ops : Array QOp) (cache : Array Nat) (types : Array (List Nat)) (counts : Array Nat) :
    List Nat × VM := Id.run do
  let n := ops.size
  let v0 : VM := { ops, cache, types, counts, written := Array.replicate (n + 1) false,
                   opCtx := Array.replicate (n + 1) {} }
  let prog : VMM (List Nat) := do
    let mut out : List Nat := []
    let mut qop : Int := 0
    let mut redo := false
    for _ in [0:64] do
      let r ← runUntil redo (-1) qop ((n : Int) - 1) 400
      if !r then break
      if (← get).unmodelled.isSome then break
      match (← get).this with
      | some t => out := out ++ [t]
      | none => unmod "yield without a table"; break
      qop := (← get).opIndex - 1
      redo := true
    return out
  let (out, v) := prog.run v0
  return (out, v)

/-! ### Documented semantics -/

/-- Queries.md "Or", "Not", "Optional": a table matches when every chain
    has a term that matches (Or), every And term's component is in the
    table, no Not term's component is. -/
def matchesDoc (ts : Array VTerm) (ty : List Nat) : Bool := Id.run do
  for c in chains ts do
    let terms := c.map (fun i => ts.getD i default)
    if c.length > 1 then
      if !terms.any (fun t => ty.contains t.comp) then return false
    else
      let t := terms.headD default
      match t.oper with
      | .and | .or => if !ty.contains t.comp then return false
      | .not => if ty.contains t.comp then return false
      | .optional => pure ()
  return true

structure Prog where
  storage : Array Storage
  terms : Array VTerm
  /-- the tables in creation order, after the query: component lists -/
  tables : Array (List Nat)
  deriving Inhabited

def showProg (p : Prog) : String :=
  s!"{showV { storage := p.storage, terms := p.terms }}; tables (in creation order) {p.tables.toList}"

instance : Repr Prog := ⟨fun p _ => .text (showProg p)⟩

def showOps (ops : Array QOp) : String :=
  ", ".intercalate ((List.range ops.size).map fun i =>
    let o := ops.getD i default
    let k := match o.kind with
      | .setIds => "SetIds" | .cache => "Cache" | .and_ => s!"And(C{o.comp})" | .or_ => "Or"
      | .not_ => "Not" | .optional => "Optional" | .end_ => "End" | .yield => "Yield" | .ifVar => "IfVar"
      | .all => "All"
    s!"{i}:{k}[prev {o.prev}, next {o.next}]")

inductive Outcome
  | skipped (why : String)
  | unmodelled (why : String)
  | ran (ops : Array QOp) (got : List Nat) (want : List Nat) (oob : Array String) (marker : Bool)
  deriving Inhabited

def run (p : Prog) : Outcome :=
  -- a table is identified by its type: two tables never have the same one
  if p.tables.toList.eraseDups.length != p.tables.size then .skipped "duplicate table types" else
  match createQuery p.storage p.terms .auto false false with
  | .crash _ => .skipped "F29: the query crashes when it is created"
  | .rejected e => .skipped s!"rejected: {e}"
  | .created .auto cts _ _ =>
    match finalizeTerms p.storage p.terms with
    | .error e => .skipped e
    | .ok q =>
      let c := compile q p.terms
      match c.unmodelled with
      | some u => .unmodelled u
      | none =>
        -- the cache: tables matching the cache's query, in creation order
        let cache := (List.range p.tables.size).filter (fun t => matchesDoc cts (p.tables.getD t [])) |>.toArray
        let counts := p.tables.map (fun _ => 1)
        let (got, vm) := iterate c.ops cache p.tables counts
        match vm.unmodelled with
        | some u => .unmodelled u
        | none =>
          let want := (List.range p.tables.size).filter (fun t => matchesDoc p.terms (p.tables.getD t []))
          .ran c.ops got want c.oob vm.markerReached
  | .created _ _ _ _ => .skipped "not a partially cached query"

/-- Properties:
  - PQ-OR1: a query's results are the tables that match its terms, each
    once (Queries.md "Or" operator, "Iteration"; ComponentTraits.md
    "Sparse trait": "ECS operations and queries work as expected with
    sparse components");
  - P1: no access outside the compiler's op array. -/
def check (p : Prog) : List (String × String) := Id.run do
  match run p with
  | .ran ops got want oob marker =>
    let mut out := []
    for o in oob do out := out ++ [("P1 no-crash", o)]
    let g := got.mergeSort (· ≤ ·)
    if g != want then
      out := out ++ [("PQ-OR1 results", s!"the cached query yields tables {got} but the tables {want} match its terms (ops: {showOps ops}{if marker then "; an op jumped to the Or marker label -2" else ""})")]
    return out
  | _ => return []

/-! ### Round 7: uncached queries (select, select_or, All) -/

/-- `flecs_query_compile` (compiler.c 1047-1190) for an uncached query: no
    cache op, the terms in order (leading Optional terms last). -/
def compileUncached (ts : Array VTerm) : CCtx := Id.run do
  let prog : CM Unit := do
    discard <| insert { kind := .setIds }
    let n := ts.size
    let mut startTerm := 0
    for _ in [0:n] do
      if startTerm < n && (ts.getD startTerm default).oper == .optional then startTerm := startTerm + 1
      else break
    let mut compiled : Array Bool := Array.replicate n false
    let mut pass := startTerm
    for _ in [0:2] do
      for i in [pass:n] do
        if compiled.getD i true then continue
        if (ts.getD i default).oper == .optional && pass != 0 then break
        compileTerm ts i
        compiled := compiled.set! i true
      if pass != 0 then pass := 0 else break
    discard <| insert { kind := .yield }
  let ((), c) := prog.run {}
  return c

/-- Run an uncached query (cache kind None). -/
def runUncached (p : Prog) : Outcome :=
  if p.tables.toList.eraseDups.length != p.tables.size then .skipped "duplicate table types" else
  match finalizeTerms p.storage p.terms with
  | .error e => .skipped e
  | .ok _ =>
    if p.storage.any (· == .dontFragment) then .skipped "DontFragment" else
    let c := compileUncached p.terms
    match c.unmodelled with
    | some u => .unmodelled u
    | none =>
      let counts := p.tables.map (fun _ => 1)
      let (got, vm) := iterate c.ops #[] p.tables counts
      match vm.unmodelled with
      | some u => .unmodelled u
      | none =>
        let want := (List.range p.tables.size).filter (fun t => matchesDoc p.terms (p.tables.getD t []))
        .ran c.ops got want c.oob vm.markerReached

/-- PQ-OR1 and P1 for the uncached query. -/
def checkU (p : Prog) : List (String × String) := Id.run do
  match runUncached p with
  | .ran ops got want oob marker =>
    let mut out := []
    for o in oob do out := out ++ [("P1 no-crash", o)]
    let g := got.mergeSort (· ≤ ·)
    if g != want then
      let kind := if got.length != got.eraseDups.length then "a table twice" else if g.all (want.contains ·) then "a table missing" else "a table that does not match"
      out := out ++ [("PQ-OR1 results", s!"uncached: {kind}: the query yields tables {got} but the tables {want} match its terms (ops: {showOps ops}{if marker then "; an op jumped to the Or marker label -2" else ""})")]
    return out
  | _ => return []

def outcomeKindU (p : Prog) : String :=
  match runUncached p with
  | .skipped w => if (w.splitOn "duplicate").length > 1 then "skipped: duplicate table types" else s!"skipped: rejected"
  | .unmodelled u => s!"unmodelled: {u}"
  | .ran ops got want oob _ =>
    let sel := ops.any (fun o => o.kind == .or_) && ops.size > 0
    let wrong := got.mergeSort (· ≤ ·) != want
    s!"ran{if sel then " (Or chain)" else ""}: {if !oob.isEmpty then "out of bounds" else if wrong then "wrong results" else "right"}"

/-! ### Generator -/

section
variable {m : Type → Type} [Monad m] [Pick m]

/-- `ncomp` components (table or Sparse), `len` terms, `ntab` tables. -/
def genProg (ncomp len ntab : Nat) : m Prog := do
  let mut st := #[]
  for _ in [0:ncomp] do st := st.push (← pickOf "or.storage" #[Storage.table, .sparse])
  let mut ts := #[]
  for _ in [0:len] do
    let comp ← Pick.pick "or.comp" ncomp
    let oper ← pickOf "or.oper" #[TOper.and, .or, .not, .optional]
    ts := ts.push { comp, oper }
  let mut tabs := #[]
  for _ in [0:ntab] do
    let mask := (← Pick.pick "or.table" ((2 ^ ncomp) - 1)) + 1
    tabs := tabs.push ((List.range ncomp).filter (fun c => (mask >>> c) % 2 == 1))
  return { storage := st, terms := ts, tables := tabs }

end

def shrink (p : Prog) : List Prog := Id.run do
  let mut out := []
  for i in [0:p.tables.size] do out := out ++ [{ p with tables := p.tables.eraseIdx! i }]
  for i in [0:p.terms.size] do out := out ++ [{ p with terms := p.terms.eraseIdx! i }]
  for i in [0:p.storage.size] do
    if p.storage.getD i .table != .table then out := out ++ [{ p with storage := p.storage.set! i .table }]
  return out

/-- Counts of what a run did, for the search report. -/
def outcomeKind (p : Prog) : String :=
  match run p with
  | .skipped w =>
    if (w.splitOn "F29").length > 1 then "skipped: F29 crash"
    else if (w.splitOn "duplicate").length > 1 then "skipped: duplicate table types"
    else "skipped: not partially cached / rejected"
  | .unmodelled u => s!"unmodelled: {u}"
  | .ran ops got want oob _ =>
    let wrong := got.mergeSort (· ≤ ·) != want
    let tag := if !oob.isEmpty && wrong then "ran: out of bounds and wrong results"
      else if !oob.isEmpty then "ran: out of bounds, results right"
      else if wrong then "ran: wrong results, no out-of-bounds access"
      else "ran: right"
    let _ := ops
    tag

/-- The C test's programs. C0 = TagA, C1 = Position (Sparse), C2 = TagC. -/
def cases : List (String × Prog) := [
  ("query_or_sparse_term_after_chain: TagA || Position(Sparse), TagC; tables [TagA, Position], [TagA, TagC], [Position, TagC]",
    { storage := #[.table, .sparse, .table],
      terms := #[{ comp := 0, oper := .or }, { comp := 1 }, { comp := 2 }],
      tables := #[[0, 1], [0, 2], [1, 2]] }),
  ("the same, first table [TagA] (no Position): nothing is returned",
    { storage := #[.table, .sparse, .table],
      terms := #[{ comp := 0, oper := .or }, { comp := 1 }, { comp := 2 }],
      tables := #[[0], [0, 2], [1, 2]] }),
  ("Position(Sparse) || TagA, TagC (sparse first: the validator makes the whole chain uncached, control)",
    { storage := #[.table, .sparse, .table],
      terms := #[{ comp := 1, oper := .or }, { comp := 0 }, { comp := 2 }],
      tables := #[[0, 2], [1, 2]] }),
  ("TagA || Position(Sparse) || TagB, TagC: TagB loses its cache flag after Position; the chain's End and the TagB op get prev -1",
    { storage := #[.table, .sparse, .table, .table],
      terms := #[{ comp := 0, oper := .or }, { comp := 1, oper := .or }, { comp := 3 }, { comp := 2 }],
      tables := #[[0, 2], [1, 2], [3, 2]] }),
  ("control: TagA, Position(Sparse) (no Or chain)",
    { storage := #[.table, .sparse],
      terms := #[{ comp := 0 }, { comp := 1 }],
      tables := #[[0, 1], [0], [1]] }) ]

end Flecs.OrVM
