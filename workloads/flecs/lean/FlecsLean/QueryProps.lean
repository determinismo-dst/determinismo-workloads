/-
  Query programs, their runner and the properties checked on them.

  A program creates entities, then queries, then runs world/stage calls
  (round 1's `Op`), iterations and `ecs_query_changed` checks.  After every
  call the pending table events and revalidations reach the query caches
  (flecs delivers them before the call returns).

  Properties (sources in Queries.md):
  - P-Q1 results: a full iteration yields exactly the entities whose
    components match the terms in the current world, with the current
    values ("Iteration", "Source", "Relationship Traversal").
  - P-Q2 order: an order_by query yields values in order ("Sorting"), when
    no undetected write (`ensure` without `modified`) happened.
  - P-Q3 groups: tables of one group are iterated together ("Grouping":
    "Grouped tables are iterated together").
  - P-CD1 changed: `ecs_query_changed` and `ecs_iter_changed` report every
    documented change since the query last iterated ("Change Detection").
  - P1 no crash, no read of uninitialized memory.
-/
import FlecsLean.Query
import FlecsLean.Gen
import FlecsLean.Search2

namespace Flecs
open Std

inductive QOp
  | op (o : Op)
  | iter (q : Nat) (mode : W.IterMode) (ask : Bool)
  | changed (q : Nat)
  /-- round 3: `ecs_query_is_true` (api.c 706-713, iter.c 511-526) -/
  | isTrue (q : Nat)
  /-- round 3: `ecs_query_count` (api.c 667-704) -/
  | count (q : Nat)
  /-- round 4: iterate `q` one result at a time; after the `k`-th result run
      `body` on the world, with the result's table locked as the C++ `each`
      does (Queries.md "Iteration"), then finish the iteration -/
  | iterBody (q : Nat) (k : Nat) (body : Op)
  deriving Repr, BEq, Inhabited

structure QProg where
  nEnts : Nat := 3
  queries : Array QCache := #[]
  ops : List QOp := []
  deriving Inhabited

instance : Repr QTerm := ⟨fun t _ => .text s!"{repr t.io} {repr t.oper} {t.id} {repr t.src}"⟩

instance : Repr QProg := ⟨fun p _ =>
  let qs := p.queries.toList.map (fun q =>
    s!"query[{", ".intercalate (q.terms.toList.map (fun t => s!"{repr t.io} {repr t.oper} {t.id} {repr t.src}"))}] detect={q.detect} order_by={q.orderBy} group_by={repr q.groupBy}")
  .text s!"ents={p.nEnts}\n    " ++ .text ("\n    ".intercalate qs) ++ .text "\n    " ++
    .text ("\n    ".intercalate (p.ops.map (fun o => toString (repr o))))⟩

namespace W

/-- Reference evaluation of a query over the world (not the cache): every
    entity of every live non-root table that matches, with its values. -/
def refResults (q : QCache) : M (List (UInt64 × Array (Option Nat))) := do
  let slots := (← get).slots
  for t in q.terms do
    match t.src with
    | .fixed k => if t.oper == .and && !(← has (slots.getD k 0) t.id) then return []
    | _ => pure ()
  let w ← get
  let mut out := []
  for t in [1:w.tables.size] do
    let x := w.tables.getD t default
    if !x.live || x.count == 0 then continue
    match (← evalMatch q t) with
    | none => pure ()
    | some m =>
      let vals ← fieldVals q m 0 x.count
      for _ in [0:1 + m.wildPairs.size] do
        for i in [0:x.count] do
          out := out ++ [(x.ents.getD i 0, vals.getD i #[])]
  return out

/-- Round 4: what the query matches, as (entity, matched pair) pairs (the
    pair is 0 without a wildcard term), and where each slot entity is. -/
def refPairs (q : QCache) : M (List (UInt64 × Id)) := do
  let slots := (← get).slots
  for t in q.terms do
    match t.src with
    | .fixed k => if t.oper == .and && !(← has (slots.getD k 0) t.id) then return []
    | _ => pure ()
  let w ← get
  let mut out := []
  for t in [1:w.tables.size] do
    let x := w.tables.getD t default
    if !x.live || x.count == 0 then continue
    match (← evalMatch q t) with
    | none => pure ()
    | some m =>
      for p in #[m.pair] ++ m.wildPairs do
        for i in [0:x.count] do
          out := out ++ [(x.ents.getD i 0, p)]
  return out

end W

/-- the fixed sources of a query are alive (a deleted cascade can take one) -/
def fixedAlive (q : QCache) : M Bool := do
  let slots := (← get).slots
  for t in q.terms do
    match t.src with
    | .fixed k => if !(← W.isAlive (slots.getD k 0)) then return false
    | _ => pure ()
  return true

structure QOutcome where
  fail : Option Fail
  viol : Array String

def sortKey (x : UInt64 × Array (Option Nat)) : String := s!"{x.1}:{repr x.2}"

def runQProg (p : QProg) : QOutcome := Id.run do
  let s : Scenario := { ops := [] }
  match W.initWorld s false with
  | .error f => return { fail := some f, viol := #[] }
  | .ok (w0, rs) =>
    let mut w := w0
    let mut viol : Array String := #[]
    let hasEnsure := p.ops.any (fun o => match o with
      | .op (.ensure _ _ .c0 _) => true
      | _ => false)
    let step : M Unit := do
      for _ in [0:p.nEnts] do W.runOp rs .new
      for q in p.queries do discard <| W.createQuery q
      W.drainQueryEvents
    match step.run w with
    | .error f => return { fail := some f, viol := #[] }
    | .ok ((), w') => w := w'
    for o in p.ops do
      let act : M Unit := match o with
        | .op op => do
          let ok ← W.allowed rs op
          if !ok then return
          -- the fixed source of a query stays alive (a query whose fixed
          -- source was deleted is not used)
          if let .delete _ e := op then
            if p.queries.any (fun q => q.terms.any (fun t => t.src == .fixed e)) then return
          -- hierarchies are trees (HierarchiesManual.md): a parent is a
          -- lower slot (no ChildOf cycle, also across staged commands)
          if let .add _ e (.pair .childOf t) := op then
            if t ≥ e then return
            let slots := (← get).slots
            let mut cur := slots.getD t 0
            for _ in [0:16] do
              if cur == slots.getD e 0 then return
              let r := (← W.getIx).recOf cur
              match r.table with
              | none => break
              | some ct =>
                match ((← get).tables.getD ct default).type.find? (fun i => isPair i && pairFirst i == EcsChildOf) with
                | some pr => cur ← W.getAlive (pairSecond pr)
                | none => break
          if op == .readonlyBegin || op == .readonlyEnd then return
          W.runOp rs op
          W.drainQueryEvents
        | .iter qi mode ask => do
          if qi ≥ (← get).queries.size then return
          let q ← W.qGet qi
          if !(← fixedAlive q) then return
          -- ecs_iter_changed only on queries created with change detection
          let ask := ask && q.detect
          let rs ← W.iterate qi mode ask
          if mode == .full then
            let ref ← W.refResults (← W.qGet qi)
            let got := rs.toList.flatMap (fun r => (List.range r.count).map (fun i =>
              (r.ents.getD i 0, r.vals.getD i #[])))
            let a := (got.map sortKey).mergeSort (· ≤ ·)
            let b := (ref.map sortKey).mergeSort (· ≤ ·)
            if a != b then
              W.noteViol s!"P-Q1 results: query {qi} yielded {a} but the world has {b}"
            -- P-Q2
            if q.orderBy && !hasEnsure then
              let vs := got.map (fun (_, v) => (v.getD 0 none).getD 0)
              let groups ← rs.toList.mapM (fun r => W.groupIdOf q r.table)
              let _ := groups
              if q.groupBy.isNone && vs != vs.mergeSort (· ≤ ·) then
                W.noteViol s!"P-Q2 order: query {qi} yielded values {vs} out of order"
            -- P-Q3
            if q.groupBy.isSome then
              let gids ← rs.toList.mapM (fun r => W.groupIdOf q r.table)
              let mut seen : List UInt64 := []
              let mut last : Option UInt64 := none
              for g in gids do
                if last != some g then
                  if seen.contains g then
                    W.noteViol s!"P-Q3 groups: query {qi} returned to group {g} after leaving it ({gids})"
                  seen := seen ++ [g]
                  last := some g
        | .iterBody qi k body => do
          if qi ≥ (← get).queries.size then return
          let q ← W.qGet qi
          if !(← fixedAlive q) then return
          -- only world calls on other entities, as the C++ each allows
          let isWorld := match body with
            | .add .world _ _ | .remove .world _ _ | .set .world _ _ _ | .delete .world _
            | .clear .world _ | .modified .world _ _ => true
            | _ => false
          if !isWorld then return
          if !(← W.allowed rs body) then return
          -- the cursor transcribes the group/wildcard iteration and (round
          -- 5) order_by slices; no fixed-source terms
          if q.terms.any (fun t => match t.src with | .fixed _ => true | _ => false) then return
          -- a fixed source of another query stays alive (as for `.op`)
          if let .delete _ e := body then
            if p.queries.any (fun q => q.terms.any (fun t => t.src == .fixed e)) then return
          -- hierarchies are trees: a parent is a lower slot (as for `.op`)
          if let .add _ e (.pair .childOf t) := body then
            if t ≥ e then return
          let before ← W.refPairs q
          let w0 ← get
          let recsBefore := w0.slots.map (fun e => (w0.ix.recOf e).table)
          let mut c ← W.cursorInit qi
          let mut got : List (UInt64 × Id) := []
          let mut n := 0
          let mut bodyRan := false
          for _ in [0:200] do
            W.cursorSyncElem qi c
            let (c', r) ← W.cursorNext qi c
            c := c'
            match r with
            | none => break
            | some (t, pair, rng) =>
              let x ← W.tbl t
              match rng with
              | none => for i in [0:x.count] do got := got ++ [(x.ents.getD i 0, pair)]
              | some (off, cnt) =>
                for i in [off:off + cnt] do
                  got := got ++ [(x.ents.getD i 0, pair)]
                  if i ≥ x.count then
                    W.noteViol s!"P-IT2 rows within the table: query {qi} returned row {i} of table {t}, whose count is {x.count}: an order_by slice (order_by.c 195-209) built before the call covers rows the call removed (the entity id and values there are stale copies)"
              n := n + 1
              if n == k then
                -- the body, with the iterated table locked
                W.lockT t
                W.runOp rs body
                W.drainQueryEvents
                W.unlockT t
                bodyRan := true
          if !bodyRan then return
          -- "Done iterating": nothing more to check here
          let after ← W.refPairs (← W.qGet qi)
          let w1 ← get
          let recsAfter := w1.slots.map (fun e => (w1.ix.recOf e).table)
          let slots := (← get).slots
          let moved := (List.range slots.size).filterMap (fun i =>
            if recsBefore.getD i none != recsAfter.getD i none then some (slots.getD i 0) else none)
          let stable := before.filter (fun x => after.contains x && !moved.contains x.1)
          for x in stable.eraseDups do
            let cnt := (got.filter (· == x)).length
            if cnt != 1 then
              W.noteViol s!"P-IT1 iteration: query {qi}: entity {x.1} (pair {x.2}) matched before and after the call made after result {k}, and the call did not move it, but the iteration returned it {cnt} times (returned {got}, matched before {before}, after {after})"
        | .isTrue qi | .count qi => do
          if qi ≥ (← get).queries.size then return
          if !(← fixedAlive (← W.qGet qi)) then return
          -- an iterator with EcsIterNoData: is_true takes the first result
          -- and finishes the iterator (its fini runs change detection on
          -- that result, eval_iter.c 670-686); count skips every result
          modify fun w => { w with iterNoData := true, iterQuiet := true }
          let mode := match o with | .isTrue _ => W.IterMode.first | _ => .skipAll
          discard <| W.iterate qi mode false
          modify fun w => { w with iterNoData := false, iterQuiet := false }
        | .changed qi => do
          if qi ≥ (← get).queries.size then return
          if !(← W.qGet qi).detect then return
          if !(← fixedAlive (← W.qGet qi)) then return
          -- expected: a table the query matches now changed since it was
          -- last iterated (or was never iterated), or a fixed source changed
          let q ← W.qGet qi
          let mut expected ← W.oracleFixedChanged qi
          for g in q.groups do
            for m in g.tables do
              if (← W.oracleChanged qi m.table) then expected := true
          -- flecs.h 4797-4810: true after tables "have been matched or
          -- unmatched": a table the user last iterated is no longer matched
          let now := q.groups.foldl (fun acc g => acc ++ g.tables.toList.map (·.table)) []
          let unmatched := (((← get).ouser[qi]?).getD []).filter (fun t => !now.contains t)
          if !unmatched.isEmpty then expected := true
          let got ← W.queryChanged qi
          if expected && !got then
            let mut why := ""
            for g in q.groups do
              for m in g.tables do
                if (← W.oracleChanged qi m.table) then
                  why := why ++ s!" table {m.table}: {(← get).osnap[(qi, m.table)]?} -> {← W.oracleState qi m.table};"
            if (← W.oracleFixedChanged qi) then
              why := why ++ s!" fixed: {(← get).ofixed[qi]?} -> {← W.oracleFixedState qi}"
            if !unmatched.isEmpty then
              why := why ++ s!" unmatched since the last iteration: tables {unmatched}"
            W.noteViol s!"P-CD1 ecs_query_changed: query {qi} returned false after a documented change:{why}"
      match act.run w with
      | .error f => return { fail := some f, viol := viol ++ w.viol }
      | .ok ((), w') => w := w'
    return { fail := none, viol := viol ++ w.viol }

/-- Debug trace of a program: after each op, each query's matches (table,
    monitor, sources), the dirty states and oracle snapshots. -/
def traceQProg (p : QProg) : List String := Id.run do
  let s : Scenario := { ops := [] }
  match W.initWorld s false with
  | .error f => return [s!"init failed {f}"]
  | .ok (w0, rs) =>
    let mut w := w0
    let mut out := []
    let step : M Unit := do
      for _ in [0:p.nEnts] do W.runOp rs .new
      for q in p.queries do discard <| W.createQuery q
      W.drainQueryEvents
    match step.run w with
    | .error f => return [s!"setup failed {f}"]
    | .ok ((), w') => w := w'
    for o in p.ops do
      let act : M String := match o with
        | .op op => do W.runOp rs op; W.drainQueryEvents; return ""
        | .iter qi md a => do
          let r ← W.iterate qi md a
          return s!"results {repr (r.toList.map (fun x => (x.table, x.ents, x.changed)))}"
        | .changed qi => do return s!"changed = {← W.queryChanged qi}"
        | .iterBody qi k body => do
          let mut c ← W.cursorInit qi
          let mut msg := ""
          let mut n := 0
          for _ in [0:200] do
            W.cursorSyncElem qi c
            let (c', r) ← W.cursorNext qi c
            c := c'
            match r with
            | none => break
            | some (t, pair, _) =>
              n := n + 1
              msg := msg ++ s!" result {n}: table {t} pair {pair} ents {((← W.tbl t).ents.extract 0 (← W.tbl t).count)};"
              if n == k then
                W.lockT t; W.runOp rs body; W.drainQueryEvents; W.unlockT t
                msg := msg ++ s!" [body {repr body}]"
          return msg
        | .isTrue qi | .count qi => do
          modify fun w => { w with iterNoData := true, iterQuiet := true }
          let r ← W.iterate qi (match o with | .isTrue _ => W.IterMode.first | _ => .skipAll) false
          modify fun w => { w with iterNoData := false, iterQuiet := false }
          return s!"probe results {r.size}"
      match act.run w with
      | .error f => out := out ++ [s!"{repr o}: FAIL {f}"]; return out
      | .ok (msg, w') =>
        w := w'
        let mut line := s!"{repr o}: {msg}"
        for qi in [0:w.queries.size] do
          let q := w.queries.getD qi default
          for g in q.groups do
            for m in g.tables do
              let d := (w.tables.getD m.table default).dirty
              line := line ++ s!"\n     q{qi} t{m.table} mon={repr m.monitor} src={m.sources} dirty={repr d} osnap={(w.osnap[(qi, m.table)]?)}"
          line := line ++ s!"\n     q{qi} matchCount={q.matchCount} prev={q.prevMatchCount} fixedMon={repr q.fixedMonitor} ofixed={w.ofixed[qi]?}"
        for t in [1:w.tables.size] do
          let x := w.tables.getD t default
          if x.live then line := line ++ s!"\n     table {t} type={x.type} ents={x.ents.extract 0 x.count} dirty={repr x.dirty}"
        out := out ++ [line]
    return out

def checkQ (p : QProg) : List (String × String) := Id.run do
  let o := runQProg p
  let mut out : List (String × String) := []
  if let some f := o.fail then
    if !allowedFail f then out := out ++ [("P1 no-crash", toString f)]
  for v in o.viol do
    let prop := if v.startsWith "P-" then (v.splitOn ":").headD v
      else if v.startsWith "uninit" then "P1 uninitialized read"
      else if v.startsWith "P1 " then "P1 no-crash" else "P2 oracle"
    out := out ++ [(prop, v)]
  return out

/-! ### Generators -/

section
variable {m : Type → Type} [Monad m] [Pick m]

/-- Query menu (C0, C1 data components; ChildOf and the plain
    relationship `rRemove` = entity 386 for group_by). -/
def queryMenu (k : Nat) (fixedSlot : Nat) : QCache :=
  match k with
  | 0 => { terms := #[{ id := C0, io := .in_ }], detect := true }
  | 1 => { terms := #[{ id := C1, io := .in_ }, { id := C0, src := .fixed fixedSlot, io := .in_ }], detect := true }
  | 2 => { terms := #[{ id := C1, io := .in_ }, { id := C0, src := .up, io := .in_ }], detect := true }
  | 3 => { terms := #[{ id := C0, io := .in_ }], orderBy := true }
  | 4 => { terms := #[{ id := C0, io := .in_ }], groupBy := some 387, detect := true }
  | 5 => { terms := #[{ id := C0 }] }
  | 6 => { terms := #[{ id := C0, io := .in_ }, { id := C1, oper := .not }], detect := true }
  | 7 => { terms := #[{ id := C0, io := .in_ }, { id := C1, oper := .optional, io := .in_ }], detect := true }
  | 8 => { terms := #[{ id := C0, src := .up, io := .in_ }], detect := true }
  | 9 => { terms := #[{ id := C0, io := .in_ }], orderBy := true, groupBy := some 387 }
  | 10 => { terms := #[{ id := C0 }, { id := C1, src := .fixed fixedSlot }] }
  -- round 4: a wildcard term on the Remove relationship (387), with and
  -- without an up term, and grouped by the Delete relationship
  | 11 => { terms := #[{ id := mkPair 387 EcsWildcard }, { id := C0, src := .up, io := .in_ }], detect := true }
  | 12 => { terms := #[{ id := mkPair 387 EcsWildcard }, { id := C1, io := .in_ }], detect := true }
  | _ => { terms := #[{ id := C0, io := .in_ }, { id := C1, src := .up, io := .in_ }], groupBy := some 388, detect := true }

def queryMenuSize : Nat := 14

def genQOp (ents : Nat) (nq : Nat) : m QOp := do
  match (← Pick.pick "q.kind" 6) with
  | 5 =>
    let qi ← Pick.pick "q.query" nq
    let k := (← Pick.pick "q.k" 2) + 1
    let e ← Pick.pick "flecs.entity" ents
    let x ← pickOf "flecs.id" #[IdS.c0, .c1, .tag, .pair .childOf 0, .pair .childOf 1, .pair .remove 0, .pair .remove 1, .pair .delete 0]
    let body ← match (← Pick.pick "q.body" 4) with
      | 0 => pure (Op.delete .world e)
      | 1 => pure (Op.add .world e x)
      | 2 => pure (Op.remove .world e x)
      | _ => pure (Op.set .world e .c0 9)
    return .iterBody qi k body
  | 4 => if (← Pick.pick "q.probe" 2) == 0 then return .isTrue (← Pick.pick "q.query" nq)
         else return .count (← Pick.pick "q.query" nq)
  | 0 =>
    let qi ← Pick.pick "q.query" nq
    let md ← pickOf "q.mode" #[W.IterMode.full, .skipAll, .first]
    let ask := (← Pick.pick "q.ask" 2) == 0
    return .iter qi md ask
  | 1 => return .changed (← Pick.pick "q.query" nq)
  | _ =>
    let e ← Pick.pick "flecs.entity" ents
    let tg : Tgt := if (← Pick.pick "flecs.target" 3) == 0 then .stage 0 else .world
    let x ← pickOf "flecs.id" #[IdS.c0, .c1, .tag, .pair .childOf 0, .pair .childOf 1, .pair .remove 0, .pair .remove 1]
    match (← Pick.pick "flecs.call" 8) with
    | 0 => return .op (.delete tg e)
    | 1 | 2 => return .op (.add tg e x)
    | 3 => return .op (.remove tg e x)
    | 4 => return .op (.set tg e (← pickOf "flecs.set.id" #[IdS.c0, .c1]) (← pickOf "flecs.value" #[1, 2, 3]))
    | 5 => return .op (.modified tg e (← pickOf "flecs.set.id" #[IdS.c0, .c1]))
    | 6 => return .op (.ensure tg e (← pickOf "flecs.set.id" #[IdS.c0, .c1]) (← pickOf "flecs.value" #[1, 2, 3]))
    | _ => return .op (.merge 0)

def genQProg (ents len : Nat) : m QProg := do
  let nq := (← Pick.pick "q.count" 2) + 1
  let mut qs := #[]
  for _ in [0:nq] do
    qs := qs.push (queryMenu (← Pick.pick "q.menu" queryMenuSize) (← Pick.pick "q.fixed" ents))
  let mut ops := []
  for _ in [0:len] do ops := ops ++ [← genQOp ents nq]
  ops := ops ++ [.op (.merge 0)]
  for i in [0:nq] do ops := ops ++ [.changed i, .iter i .full true]
  return { nEnts := ents, queries := qs, ops }

/-- Round 4: iteration programs for exhaustive search.  Four entities, each
    built as one of eight kinds (C0; C0+C1; C0+(R, e0); C1+ChildOf e0;
    C1+ChildOf e1; ChildOf e0 + (R, e1) + (R, e2); C0 alone as a parent;
    C0+(R, e0) then deleted, leaving an empty table); a query of four
    shapes; then one iteration with a call after result k. -/
def genIterProg : m QProg := do
  let shape ← Pick.pick "it.query" 4
  let q : QCache := match shape with
    | 0 => { terms := #[{ id := C0 }] }
    | 1 => { terms := #[{ id := C1, io := .in_ }, { id := C0, src := .up, io := .in_ }], detect := true }
    | 2 => { terms := #[{ id := mkPair 387 EcsWildcard }, { id := C0, src := .up, io := .in_ }], detect := true }
    | _ => { terms := #[{ id := mkPair 387 EcsWildcard }], detect := true }
  let mut ops : List QOp := []
  let mut later : List QOp := []
  for e in [0:4] do
    let k ← Pick.pick "it.kind" 8
    let add := fun (x : IdS) => QOp.op (.add .world e x)
    ops := ops ++ (match k with
      | 0 => [add .c0]
      | 1 => [add .c1, add .c0]
      | 2 => [add (.pair .remove 0), add .c0]
      | 3 => [add (.pair .childOf 0), add .c1]
      | 4 => [add (.pair .childOf 1), add .c1]
      | 5 => [add (.pair .childOf 0), add (.pair .remove 1), add (.pair .remove 2)]
      | 6 => [QOp.op (.set .world e .c0 1)]
      | _ => [add (.pair .remove 0), add .c0])
    if k == 7 then later := later ++ [QOp.op (.delete .world e)]
  let k := (← Pick.pick "it.k" 3) + 1
  let tgt ← Pick.pick "it.target" 4
  let body := match (← Pick.pick "it.body" 4) with
    | 0 => Op.delete .world tgt
    | 1 => Op.remove .world tgt .c0
    | 2 => Op.add .world tgt .c0
    | _ => Op.add .world tgt .c1
  return { nEnts := 4, queries := #[q], ops := ops ++ later ++ [.iterBody 0 k body] }

/-- Round 5: iteration programs for cascade queries and table arrays that
    grow during an iteration.  A query of four shapes (cascade
    `C0, ?C0(cascade)` with and without change detection, `[in] C0` with
    change detection, `[in] C0` grouped by the Delete relationship); five
    entities, each built as one of seven kinds (C0 root; C0 + ChildOf a
    lower entity; ChildOf a lower entity without C0; C0 + C1; C0 + tag;
    C0 + (Delete, e0); nothing); optionally `ecs_query_changed` (which turns
    change detection on); then one iteration with a call after result k:
    reparent, unparent, delete, or add C1/tag. -/
def genIterProg5 : m QProg := do
  let shape ← Pick.pick "it5.query" 5
  let casc : QCache := { terms := #[{ id := C0, io := .in_ }, { id := C0, src := .up, oper := .optional, io := .in_ }], cascade := true }
  let q : QCache := match shape with
    | 0 => casc
    | 1 => { casc with detect := true }
    | 2 => { terms := #[{ id := C0, io := .in_ }], detect := true }
    | 3 => { terms := #[{ id := C0, io := .in_ }], groupBy := some 388, detect := true }
    | _ => { terms := #[{ id := C0, io := .in_ }], orderBy := true }
  let n := 5
  let mut ops : List QOp := []
  for e in [0:n] do
    -- C0 is set with a value per entity, so order_by interleaves tables
    let add := fun (x : IdS) => if x == .c0 then QOp.op (.set .world e .c0 ((e * 3) % 5 + 1)) else QOp.op (.add .world e x)
    let k ← Pick.pick "it5.kind" (if e == 0 then 4 else 7)
    let kinds : Array (List QOp) := if e == 0 then
        #[[add .c0], [add .c1, add .c0], [add .tag, add .c0], []]
      else #[[add .c0], [add .c1, add .c0], [add .tag, add .c0], [], [], [], []]
    if e == 0 || k < 4 then
      ops := ops ++ kinds.getD k []
    else
      let j ← Pick.pick "it5.parent" e
      ops := ops ++ (match k with
        | 4 => [add (.pair .childOf j), add .c0]
        | 5 => [add (.pair .childOf j)]
        | _ => [add (.pair .delete 0), add .c0])
  if (← Pick.pick "it5.changed" 2) == 1 then ops := ops ++ [.changed 0]
  let k := (← Pick.pick "it5.k" 4) + 1
  let tgt ← Pick.pick "it5.target" n
  let body ← match (← Pick.pick "it5.body" 5) with
    | 0 => pure (Op.add .world tgt (.pair .childOf (← Pick.pick "it5.newparent" n)))
    | 1 => pure (Op.remove .world tgt (.pair .childOf (← Pick.pick "it5.newparent" n)))
    | 2 => pure (Op.delete .world tgt)
    | 3 => pure (Op.add .world tgt .c1)
    | _ => pure (Op.add .world tgt .tag)
  return { nEnts := n, queries := #[q], ops := ops ++ [.iterBody 0 k body] }

end

/-! ### Cases (the C tests' programs) -/

def wo (o : Op) : QOp := .op o

def qIn (id : Id) (src : QSrc := .self) : QTerm := { id := id, src := src, io := .in_ }

/-- `[in] C1, [in] C0(src)` with change detection -/
def qC1C0 (src : QSrc) : QCache := { terms := #[qIn C1, qIn C0 src], detect := true }

/-- change_detection_fixed_source_moved.c: the fixed source moves to a new
    table, then its component is set. -/
def qcaseFixedMoveSet : QProg :=
  { nEnts := 2,
    queries := #[qC1C0 (.fixed 0)],
    ops := [wo (.set .world 0 .c0 1), wo (.set .world 1 .c1 1),
          .changed 0, .iter 0 .full false, .changed 0,
          wo (.add .world 0 .tag), wo (.set .world 0 .c0 2), .changed 0] }

/-- change_detection_parent_moved.c: the same through up(ChildOf). -/
def qcaseUpMoveSet : QProg :=
  { nEnts := 2,
    queries := #[qC1C0 .up],
    ops := [wo (.set .world 0 .c0 1), wo (.add .world 1 (.pair .childOf 0)), wo (.set .world 1 .c1 1),
          .changed 0, .iter 0 .full false, .changed 0,
          wo (.add .world 0 .tag), wo (.set .world 0 .c0 2), .changed 0, .iter 0 .full true] }

/-- change_detection_fixed_source_removed.c: the fixed source loses the
    component the query reads from it. -/
def qcaseFixedRemoved : QProg :=
  { nEnts := 2,
    queries := #[qC1C0 (.fixed 0)],
    ops := [wo (.set .world 0 .c0 1), wo (.set .world 1 .c1 1),
          .changed 0, .iter 0 .full false, .changed 0,
          wo (.remove .world 0 .c0), .changed 0] }

/-- change_detection_fixed_source_added.c: the fixed source gains the
    component after the monitor was created (uninitialized slot). -/
def qcaseFixedAdded : QProg :=
  { nEnts := 2,
    queries := #[qC1C0 (.fixed 0)],
    ops := [wo (.set .world 1 .c1 1), .changed 0, .iter 0 .full false,
          wo (.set .world 0 .c0 1), .changed 0] }

/-- query_is_true_consumes_change.c (F27): ecs_query_is_true syncs the
    first result's monitor, so a set is no longer reported. -/
def qcaseIsTrueSet : QProg :=
  { nEnts := 1,
    queries := #[{ terms := #[qIn C0], detect := true }],
    ops := [wo (.set .world 0 .c0 1), .changed 0, .iter 0 .full false, .changed 0,
            wo (.set .world 0 .c0 2), .isTrue 0, .changed 0] }

/-- query_is_true_consumes_change.c, second part (F27): a table unmatched
    through up traversal, then ecs_query_is_true resets prev_match_count. -/
def qcaseIsTrueUnmatched : QProg :=
  { nEnts := 2,
    queries := #[qC1C0 .up],
    ops := [wo (.set .world 0 .c0 1), wo (.add .world 1 (.pair .childOf 0)), wo (.set .world 1 .c1 1),
            .changed 0, .iter 0 .full false, .changed 0,
            wo (.remove .world 0 .c0), .isTrue 0, .changed 0] }

/-- the same with ecs_query_count (F27) -/
def qcaseCountUnmatched : QProg :=
  { qcaseIsTrueUnmatched with ops := [wo (.set .world 0 .c0 1), wo (.add .world 1 (.pair .childOf 0)), wo (.set .world 1 .c1 1),
            .changed 0, .iter 0 .full false, .changed 0,
            wo (.remove .world 0 .c0), .count 0, .changed 0] }

/-- Round 4, F30: iterating `C0` (cached); after the first result the
    target of a relationship is deleted, which deletes an empty table
    earlier in the cache; the last table moves into its slot and is never
    returned. -/
def qcaseIterSkipDelete : QProg :=
  { nEnts := 4,
    queries := #[{ terms := #[{ id := C0 }] }],
    ops := [wo (.add .world 1 (.pair .remove 0)), wo (.add .world 1 .c0),
            wo (.add .world 2 .c0),
            wo (.add .world 3 .c1), wo (.add .world 3 .c0),
            wo (.delete .world 1),
            .iterBody 0 1 (.delete .world 0)] }

/-- Round 4, F30: `[in] C1, [in] C0(up)`; after the second result the first
    table's parent loses C0, its table is unmatched (a rematch), the last
    table moves into its slot and is never returned. -/
def qcaseIterSkipRematch : QProg :=
  { nEnts := 6,
    queries := #[{ terms := #[{ id := C1, io := .in_ }, { id := C0, src := .up, io := .in_ }], detect := true }],
    ops := [wo (.set .world 0 .c0 1), wo (.set .world 1 .c0 1), wo (.set .world 2 .c0 1),
            wo (.add .world 3 (.pair .childOf 0)), wo (.set .world 3 .c1 1),
            wo (.add .world 4 (.pair .childOf 1)), wo (.set .world 4 .c1 1),
            wo (.add .world 5 (.pair .childOf 2)), wo (.set .world 5 .c1 1),
            .iterBody 0 2 (.remove .world 0 .c0)] }

/-- Round 4, F30: `(R, *), [in] C0(up)`; an entity with (R, e0) and (R, e1)
    under a parent with C0.  After the first result (the first pair) the
    parent loses C0: the table is unmatched and its wildcard_matches vector
    freed while the iterator reads it. -/
def qcaseIterWildFreed : QProg :=
  { nEnts := 4,
    queries := #[{ terms := #[{ id := mkPair 387 EcsWildcard }, { id := C0, src := .up, io := .in_ }], detect := true }],
    ops := [wo (.set .world 0 .c0 1),
            wo (.add .world 3 (.pair .childOf 0)), wo (.add .world 3 (.pair .remove 1)),
            wo (.add .world 3 (.pair .remove 2)),
            .iterBody 0 1 (.remove .world 0 .c0)] }


/-- Round 5 cases (the C tests' programs).  The cascade query is
    `C0, ?C0(cascade)`, created before the entities. -/
def qCascade (detect : Bool := false) : QCache :=
  { terms := #[qIn C0, { id := C0, src := .up, oper := .optional, io := .in_ }], cascade := true, detect }

/-- query_cascade_table_twice.c: p2 (e0) and p1 (e2) are roots, c2 (e1) a
    child of p2, c1 (e3) a child of p1.  The iteration returns the roots,
    then c2's table, then c1's table (group 1, last).  Then p1 becomes a
    child of p2: c1's table moves to group 2, which comes after group 1. -/
def qcaseCascadeTwice : QProg :=
  { nEnts := 4, queries := #[qCascade],
    ops := [wo (.add .world 0 .c0), wo (.add .world 1 (.pair .childOf 0)), wo (.add .world 1 .c0),
            wo (.add .world 2 .c0), wo (.add .world 3 (.pair .childOf 2)), wo (.add .world 3 .c0),
            .iterBody 0 3 (.add .world 2 (.pair .childOf 0))] }

/-- query_cascade_group_freed.c: x (e0) a root without C0, m (e1) its child
    without C0, p1 (e2) a root with C0, c1 (e3) its child, g (e4) a child
    of m.  Groups: 0 [p1], 1 [c1's table], 2 [g's table].  After the
    second result (c1), p1 becomes a child of m: p1 moves into g's table,
    c1's table moves to the new group 3, and group 1, now empty, is freed
    while the iterator is in it. -/
def qcaseCascadeGroupFreed : QProg :=
  { nEnts := 5, queries := #[qCascade],
    ops := [wo (.add .world 1 (.pair .childOf 0)),
            wo (.add .world 2 .c0), wo (.add .world 3 (.pair .childOf 2)), wo (.add .world 3 .c0),
            wo (.add .world 4 (.pair .childOf 1)), wo (.add .world 4 .c0),
            .iterBody 0 2 (.add .world 2 (.pair .childOf 1))] }

/-- query_iter_table_array_realloc.c, in small: two tables fill the default
    group's array (capacity 2); with change detection on, a call after the
    first result gives C0 to an entity outside the cache (it has only the
    tag), which creates a third matching table: the array is reallocated
    under `qit->elem`. -/
def qcaseIterRealloc : QProg :=
  { nEnts := 3, queries := #[{ terms := #[qIn C0], detect := true }],
    ops := [wo (.add .world 0 .c0), wo (.add .world 1 .c1), wo (.add .world 1 .c0), wo (.add .world 2 .tag),
            .changed 0, .iterBody 0 1 (.add .world 2 .c0)] }

/-- query_order_by_stale_rows.c: order_by on C0's value.  e0 (1), e2 (3),
    e3 (4) in [C0]; e1 (2) in [C0, tag].  Slices: [C0] row 0, [C0, tag]
    row 0, [C0] rows 1-2.  After the second result, e2 is deleted: e3 moves
    to row 1, the table's count is 2, and the last slice still covers rows
    1-2. -/
def qcaseOrderByStale : QProg :=
  { nEnts := 4, queries := #[{ terms := #[qIn C0], orderBy := true }],
    ops := [wo (.set .world 0 .c0 1), wo (.add .world 1 .tag), wo (.set .world 1 .c0 2),
            wo (.set .world 2 .c0 3), wo (.set .world 3 .c0 4),
            .iterBody 0 2 (.delete .world 2)] }

def qcases : List (String × QProg) := [
  ("query_order_by_stale_rows", qcaseOrderByStale),
  ("query_cascade_table_twice", qcaseCascadeTwice),
  ("query_cascade_group_freed", qcaseCascadeGroupFreed),
  ("query_iter_table_array_realloc (small)", qcaseIterRealloc),
  ("query_is_true_consumes_change (set)", qcaseIsTrueSet),
  ("query_is_true_consumes_change (unmatched)", qcaseIsTrueUnmatched),
  ("query_count_consumes_change (unmatched)", qcaseCountUnmatched),
  ("change_detection_fixed_source_moved", qcaseFixedMoveSet),
  ("change_detection_parent_moved", qcaseUpMoveSet),
  ("change_detection_fixed_source_removed", qcaseFixedRemoved),
  ("change_detection_fixed_source_added", qcaseFixedAdded),
  ("iter_skip_after_table_delete", qcaseIterSkipDelete),
  ("iter_skip_after_rematch", qcaseIterSkipRematch),
  ("iter_wildcard_matches_freed", qcaseIterWildFreed) ]

def shrinkQ (p : QProg) : List QProg := Id.run do
  let mut out := []
  let ops := p.ops.toArray
  for i in [0:ops.size] do
    out := out ++ [{ p with ops := (ops.eraseIdx! i).toList }]
  if p.queries.size > 1 then
    for i in [0:p.queries.size] do
      -- dropping a query renumbers the later ones
      let rn := fun (qi : Nat) => if qi > i then qi - 1 else qi
      let ops' := p.ops.filterMap (fun o => match o with
        | .iter qi md a => if qi == i then none else some (.iter (rn qi) md a)
        | .changed qi => if qi == i then none else some (.changed (rn qi))
        | .isTrue qi => if qi == i then none else some (.isTrue (rn qi))
        | .count qi => if qi == i then none else some (.count (rn qi))
        | .iterBody qi k b => if qi == i then none else some (.iterBody (rn qi) k b)
        | o => some o)
      out := out ++ [{ p with queries := p.queries.eraseIdx! i, ops := ops' }]
  return out

end Flecs
