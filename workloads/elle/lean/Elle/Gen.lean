import Determinismo
import Elle.Basic

/-!
# The world: histories as decisions

Every choice that makes a history is a named decision (determinismo's `decide`): how many
transactions, each one's outcome (`:ok`, `:fail`, `:info`), thread, micro-ops, keys, what each
read returned, and how invocations and completions interleave in real time. A thread's process
crashes on `:info` and comes back as a fresh process, as Jepsen's do. Value 0 of a decision is
the plainer option, so a shrunk counterexample is a small one.
-/

namespace Elle.Gen

open Determinismo Elle

inductive Workload where
  | listAppend | register
  deriving Repr, BEq, Inhabited

/-- How a read's value is drawn. -/
inductive ReadMode where
  /-- Any list of distinct appended elements (list append), any written value or `nil`
  (register): the whole space, for exhaustive search. -/
  | any
  /-- A cut of a decided execution order: the read sees the transactions before the cut (and its
  own writes), with now and then an aborted one: closer to what databases return. -/
  | cuts
  deriving Repr, BEq, Inhabited

structure Bounds where
  workload : Workload := .listAppend
  minTxns : Nat := 1
  maxTxns : Nat := 3
  maxMops : Nat := 2
  keys : Nat := 2
  threads : Nat := 2
  fail : Bool := true
  info : Bool := true
  interleave : Bool := true
  readMode : ReadMode := .any
  /-- Longest read value considered in `.any` mode. -/
  maxRead : Nat := 3
  /-- A value nobody wrote may be read. -/
  garbage : Bool := false
  deriving Repr, Inhabited

abbrev W := EStateM Stop Decisions

def dec (name : String) (n : Nat) : W Nat := Determinismo.decide (σ := Decisions) name n

/-- Lists of distinct elements of `es`, by length, up to `maxLen`. -/
def seqs (es : List Int) (maxLen : Nat) : List (List Int) :=
  let rec go (n : Nat) : List (List Int) :=
    match n with
    | 0 => [[]]
    | n + 1 =>
      let shorter := go n
      shorter ++ (shorter.filter (·.length == n)).flatMap fun s =>
        (es.filter (!s.contains ·)).map fun e => s ++ [e]
  go maxLen

structure Txn where
  status : OpType
  thread : Nat
  mops : List Mop

/-- The transactions, with appends and writes given unique values per key. -/
def genTxns (b : Bounds) : W (List Txn) := do
  let n := b.minTxns + (← dec "txn.count" (b.maxTxns - b.minTxns + 1))
  let mut txs : List Txn := []
  let mut next : List (Nat × Int) := []
  for _ in List.range n do
    let weights := [8] ++ (if b.fail then [1] else [0]) ++ (if b.info then [1] else [0])
    let s ← decideWeighted (σ := Decisions) "txn.status" (if b.fail || b.info then weights else [1])
    let status := match s with | 1 => OpType.fail | 2 => .info | _ => .ok
    let thread ← dec "txn.thread" b.threads
    let m := 1 + (← dec "txn.mops" b.maxMops)
    let mut mops : List Mop := []
    for _ in List.range m do
      let f ← dec "mop.f" 2
      let k ← dec "mop.key" b.keys
      if f == 0 then mops := mops ++ [{ f := .r, k, v := .nil }]
      else
        let v := (next.lookup k).getD 1
        next := amPut next k (v + 1)
        mops := mops ++ [{ f := if b.workload == .listAppend then .append else .w, k, v := .int v }]
    txs := txs ++ [{ status, thread, mops }]
  return txs

def written (txs : List Txn) (k : Nat) : List Int :=
  txs.flatMap fun t => t.mops.filterMap fun m =>
    if m.k == k && (m.f == .append || m.f == .w) then (match m.v with | .int e => some e | _ => none) else none

/-- A permutation of `0..n-1` by successive picks. -/
def genPerm (name : String) (n : Nat) : W (List Nat) := do
  let mut left := List.range n
  let mut out : List Nat := []
  for _ in List.range n do
    let i ← dec name left.length
    out := out ++ [left.getD i 0]
    left := left.eraseIdx i
  return out

/-- Fill the reads of acknowledged transactions. -/
def genReads (b : Bounds) (txs : List Txn) : W (List Txn) := do
  let order ← if b.readMode == .cuts then genPerm "exec.order" txs.length else pure []
  let mut out : List Txn := []
  let mut i := 0
  for t in txs do
    if t.status != .ok then
      out := out ++ [t]; i := i + 1; continue
    let mut mops : List Mop := []
    let mut own : List (Nat × List Int) := []
    let mut seen : List (Nat × Val) := []
    for m in t.mops do
      match m.f with
      | .r =>
        let es := written txs m.k
        let ownK := (own.lookup m.k).getD []
        let v ← match b.readMode with
          | .any =>
            if b.workload == .listAppend then do
              let cands := seqs (es ++ (if b.garbage then [99] else [])) b.maxRead
              let j ← dec "read.value" cands.length
              pure (Val.list (cands.getD j []))
            else do
              let cands : List Val := [.nil] ++ (es ++ (if b.garbage then [99] else [])).map Val.int
              let j ← dec "read.value" cands.length
              pure (cands.getD j .nil)
          | .cuts => do
            -- a stale or fresh cut of the execution order, the transaction's own writes on top
            let repeat_ ← if (seen.lookup m.k).isSome then dec "read.repeat" 4 else pure 1
            if repeat_ == 0 then pure ((seen.lookup m.k).getD .nil) else
            let cut ← dec "read.cut" (txs.length + 1)
            let before := (order.take cut).filter (· != i)
            let dirty ← decideRare (σ := Decisions) "read.dirty" 1 10
            let vis := before.filter fun j => match txs[j]? with
              | some u => u.status != .fail || dirty
              | none => false
            let vals := vis.flatMap fun j => match txs[j]? with
              | some u => u.mops.filterMap fun mo =>
                  if mo.k == m.k && (mo.f == .append || mo.f == .w) then (match mo.v with | .int e => some e | _ => none) else none
              | none => []
            if b.workload == .listAppend then pure (Val.list (vals ++ ownK))
            else
              match ownK.getLast? with
              | some e => pure (Val.int e)
              | none => pure (match vals.getLast? with | some e => Val.int e | none => Val.nil)
        seen := amPut seen m.k v
        mops := mops ++ [{ m with v }]
      | _ =>
        let e := match m.v with | .int e => e | _ => 0
        own := amUpdate own m.k [] (· ++ [e])
        mops := mops ++ [m]
    out := out ++ [{ t with mops }]
    i := i + 1
  return out

/-- Invocations and completions, interleaved by decision; `:info` crashes a thread's process. -/
def genEvents (b : Bounds) (txs : List Txn) : W History := do
  let full := txs.zip (List.range txs.length)
  let mut queues : List (Nat × List Nat) := (List.range b.threads).map fun th =>
    (th, (full.filter (·.1.thread == th)).map (·.2))
  let mut running : List (Nat × Nat) := []   -- thread -> txn
  let mut crashes : List (Nat × Nat) := []
  let mut ops : Array Op := #[]
  let mut fuel := 4 * txs.length + 4
  while fuel > 0 do
    fuel := fuel - 1
    -- available: complete a running txn, or invoke a thread's next one
    let acts : List (Nat × Bool) := (List.range b.threads).filterMap fun th =>
      if (running.lookup th).isSome then some (th, true)
      else if ((queues.lookup th).getD []).isEmpty then none else some (th, false)
    if acts.isEmpty then break
    let a ← if b.interleave then do pure (acts.getD (← dec "event.next" acts.length) (0, false))
            else pure (acts.getD 0 (0, false))
    let th := a.1
    let proc := th + b.threads * ((crashes.lookup th).getD 0)
    if a.2 then
      let j := (running.lookup th).getD 0
      let t := txs.getD j { status := .ok, thread := 0, mops := [] }
      let invValue := t.mops.map fun m => if m.f == .r then { m with v := .nil } else m
      let value := if t.status == .ok then t.mops else invValue
      ops := ops.push { index := ops.size, type := t.status, process := proc, value }
      running := running.filter (·.1 != th)
      if t.status == .info then crashes := amUpdate crashes th 0 (· + 1)
    else
      let q := (queues.lookup th).getD []
      let j := q.headD 0
      queues := amPut queues th (q.drop 1)
      running := running ++ [(th, j)]
      let t := txs.getD j { status := .ok, thread := 0, mops := [] }
      let invValue := t.mops.map fun m => if m.f == .r then { m with v := .nil } else m
      ops := ops.push { index := ops.size, type := .invoke, process := proc, value := invValue }
  return ops

def genHistory (b : Bounds) : W History := do
  let txs ← genTxns b
  let txs ← genReads b txs
  genEvents b txs

/-- A permutation of a history's vertices, standing for Bifurcan's hash order. -/
def genRank (n : Nat) : W (Nat → Nat) := do
  let p ← genPerm "order.rank" n
  return fun v => (p.findIdx? (· == v)).getD v

end Elle.Gen
