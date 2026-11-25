import Elle.Core
import Elle.Gen
import Elle.Spec

/-!
# elle.core's monotonic-key checker, and its specification

`elle.core/check` with `monotonic-key-graph` (core.clj:259), alone or combined with
`realtime-graph` (core.clj:19-22: "verifies that not only must the values of each key
monotonically increase, but that those increases must be observed in real time"). An op's value
is a map of keys to integers (here `[:r k v]` mops).

Specification: valid iff some total order of the acknowledged ops (extending real-time
precedence, when combined) has every key's values non-decreasing.
-/

namespace Elle.Monotonic

open Determinismo Elle Elle.Gen

def vals (h : History) (i : Nat) : List (Nat × Int) :=
  match h[i]? with
  | some o => o.value.filterMap fun m => match m.v with | .int v => some (m.k, v) | _ => none
  | none => []

def check (h : History) (realtime : Bool) : Bool :=
  let a := monotonicKeyGraph h (vals h)
  let a := if realtime then combine [a, realtimeGraph h] else a
  coreCheck a

def spec (h : History) (realtime : Bool) : Bool :=
  let pairs := pairIndex h
  let okOps := (h.toList.filter Op.isOk).map (·.index)
  let inv (i : Nat) := ((pairs.lookup i).getD i)
  let before (a b : Nat) := a < inv b   -- a completed before b was invoked
  (Spec.perms okOps).any fun order =>
    let pos (x : Nat) := (order.findIdx? (· == x)).getD 0
    let rtOk := !realtime || okOps.all fun a => okOps.all fun b => a == b || !before a b || pos a < pos b
    let mono := order.all fun a => order.all fun b =>
      pos a ≥ pos b || (vals h a).all fun (k, va) => match (vals h b).lookup k with
        | some vb => va ≤ vb
        | none => true
    rtOk && mono

/-- Ops reading a few keys' values, interleaved by thread. -/
def genHistory (n keys vmax threads : Nat) : W History := do
  let count := 1 + (← dec "op.count" n)
  let mut txs : List Gen.Txn := []
  for _ in List.range count do
    let s ← decideWeighted (σ := Decisions) "op.status" [6, 1, 1]
    let status := match s with | 1 => OpType.fail | 2 => .info | _ => .ok
    let thread ← dec "op.thread" threads
    let mut mops : List Mop := []
    for k in List.range keys do
      if (← dec "op.has" 3) != 0 then
        mops := mops ++ [{ f := .r, k, v := .int (Int.ofNat (← dec "op.value" vmax)) }]
    txs := txs ++ [{ status, thread, mops }]
  let b : Bounds := { threads, interleave := true }
  genEvents b txs

def ednOp (o : Op) : String :=
  let t := match o.type with | .invoke => ":invoke" | .ok => ":ok" | .fail => ":fail" | .info => ":info"
  let v := if o.isOk then "{" ++ ", ".intercalate (o.value.filterMap fun m => match m.v with
      | .int i => some s!"{m.k} {i}" | _ => none) ++ "}" else "nil"
  s!"\{:process {o.process}, :type {t}, :f :read, :value {v}}"

end Elle.Monotonic
