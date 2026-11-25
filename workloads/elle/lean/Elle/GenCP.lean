import Elle.Gen
import Elle.ClosedPredicate

/-!
# Closed-predicate histories, as decisions (for the differential test against real Elle)

As `elle.closed-predicate/gen` (closed_predicate.clj:740) shapes them: an `:init` op creating
the keys of `:w` and `:delete` type (k mod 3 = 1, 2) with 0 or 1, then transactions of reads,
predicate reads and one mutation per key. A read sees the state at a decided cut of the
history's write order (sometimes any version, sometimes a value nobody wrote).
-/

namespace Elle.GenCP

open Determinismo Elle Elle.Gen

def keyType (k : Nat) : F := match k % 3 with | 0 => .insert | 1 => .w | _ => .delete

def genPred : W Pred := do
  match ← dec "pred" 3 with
  | 0 => pure (.eq (Int.ofNat (← dec "pred.value" 2)))
  | 1 => pure (.mod 2 (Int.ofNat (← dec "pred.value" 2)))
  | _ => pure .tru

def evalPred := ClosedPredicate.evalPred

def genHistory (keys : Nat) (maxTxns : Nat) (threads : Nat) : W History := do
  let initKs := (List.range keys).filter fun k => keyType k != .insert
  let mut initVals : List (Nat × Int) := []
  for k in initKs do initVals := initVals ++ [(k, Int.ofNat (← dec "init.value" 2))]
  -- transactions: (status, mops without read results)
  let n := 1 + (← dec "txn.count" maxTxns)
  let mut left := List.range keys
  let mut next : Int := 2
  let mut txs : List (OpType × List Mop) := []
  for _ in List.range n do
    let s ← decideWeighted (σ := Decisions) "txn.status" [8, 1, 1]
    let status := match s with | 1 => OpType.fail | 2 => .info | _ => .ok
    let m := 1 + (← dec "txn.mops" 3)
    let mut mops : List Mop := []
    for _ in List.range m do
      match ← dec "mop.f" 3 with
      | 0 => mops := mops ++ [{ f := .r, k := ← dec "mop.key" keys, v := .nil }]
      | 1 => mops := mops ++ [{ f := .rp, k := 0, v := .nil, pred := ← genPred }]
      | _ =>
        match left with
        | k :: rest =>
          left := rest
          match keyType k with
          | .delete => mops := mops ++ [{ f := .delete, k, v := .nil }]
          | f => mops := mops ++ [{ f, k, v := .int next }]; next := next + 1
        | [] => pure ()
    txs := txs ++ [(status, mops)]
  -- states after each prefix of the (serial) write order: init, then the non-failed txns
  let applyTxn (st : List (Nat × Val)) (ms : List Mop) : List (Nat × Val) :=
    ms.foldl (fun st m => match m.f with
      | .insert | .w => amPut st m.k m.v
      | .delete => amPut st m.k .dead
      | _ => st) st
  let init : List (Nat × Val) := initVals.map fun (k, v) => (k, .int v)
  let states : List (List (Nat × Val)) := (txs.filter (·.1 != .fail)).foldl
    (fun acc (_, ms) => acc ++ [applyTxn (acc.getLast?.getD init) ms]) [init]
  let mut filled : List (OpType × List Mop) := []
  for (status, ms) in txs do
    if status != .ok then filled := filled ++ [(status, ms)]; continue
    let mut out : List Mop := []
    for m in ms do
      match m.f with
      | .r =>
        let st := states.getD (← dec "read.cut" states.length) init
        let v := match st.lookup m.k with
          | some (.int i) => Val.int i
          | _ => Val.nil
        let garbage ← decideRare (σ := Decisions) "read.garbage" 1 12
        out := out ++ [{ m with v := if garbage then .int 99 else v }]
      | .rp =>
        let st := states.getD (← dec "read.cut" states.length) init
        let seen := st.filterMap fun (k, v) => if evalPred m.pred v then some (k, v) else none
        out := out ++ [{ m with v := .kmap seen }]
      | _ => out := out ++ [m]
    filled := filled ++ [(status, out)]
  -- events: init first, then transactions over threads, serially per thread
  let mut ops : Array Op := #[]
  let initMops := initVals.map fun (k, v) => ({ f := .w, k, v := .int v } : Mop)
  ops := ops.push { index := 0, type := .invoke, process := 0, f := .init, value := initMops }
  ops := ops.push { index := 1, type := .ok, process := 0, f := .init, value := initMops }
  let mut i := 0
  for (status, ms) in filled do
    let th ← dec "txn.thread" threads
    let inv := ms.map fun m => if m.f == .r || m.f == .rp then { m with v := .nil } else m
    ops := ops.push { index := ops.size, type := .invoke, process := th + 1 + threads * i, value := inv }
    ops := ops.push { index := ops.size, type := status, process := th + 1 + threads * i,
                      value := if status == .ok then ms else inv }
    i := i + 1
  return ops

def ednPred : Pred → String
  | .tru => ":true"
  | .eq n => s!"[:= {n}]"
  | .mod m t => s!"[:mod {m} {t}]"

partial def ednVal : Val → String
  | .nil => "nil"
  | .int i => toString i
  | .kmap l => "{" ++ ", ".intercalate (l.map fun (k, v) => s!"{k} {ednVal v}") ++ "}"
  | .dead => "nil"
  | .unborn => "nil"
  | .list l => "[" ++ " ".intercalate (l.map toString) ++ "]"

def ednMop (m : Mop) : String :=
  match m.f with
  | .r => s!"[:r {m.k} {ednVal m.v}]"
  | .rp => s!"[:rp {ednPred m.pred} {ednVal m.v}]"
  | .insert => s!"[:insert {m.k} {ednVal m.v}]"
  | .w => s!"[:w {m.k} {ednVal m.v}]"
  | .delete => s!"[:delete {m.k}]"
  | .append => s!"[:append {m.k} {ednVal m.v}]"

def ednOp (o : Op) : String :=
  let t := match o.type with | .invoke => ":invoke" | .ok => ":ok" | .fail => ":fail" | .info => ":info"
  if o.f == .init then
    s!"\{:process {o.process}, :type {t}, :f :init, :value \{{", ".intercalate (o.value.map fun m => s!"{m.k} {ednVal m.v}")}}}"
  else s!"\{:process {o.process}, :type {t}, :f :txn, :value [{" ".intercalate (o.value.map ednMop)}]}"

def ednHistory (h : History) : String := "[" ++ "\n ".intercalate (h.toList.map ednOp) ++ "]"

end Elle.GenCP
