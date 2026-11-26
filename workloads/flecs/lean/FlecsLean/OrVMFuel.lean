/-
  Round 6: the query VM of `OrVM.lean` as one fuel-indexed function, so
  that the kernel can evaluate it (`decide +kernel`).  The partial mutual
  functions `runUntil`, `runBlock` and `dispatch` become the three cases of
  `vmF`, each nested call taking one unit of fuel; `resetAfterBlock` is not
  recursive; the cache op's `while` becomes a bounded `for`.  The search
  mode `or agree` checks that `iterateF` and `iterate` give the same tables
  on every generated program.
-/
import FlecsLean.OrVM

namespace Flecs.OrVM
open Flecs.Val

inductive Call
  /-- `flecs_query_run_until` (eval.c 1733-1785) -/
  | runUntil (redo : Bool) (first cur last : Int)
  /-- `flecs_query_run_block` (1327-1349) -/
  | runBlock (redo : Bool)
  /-- `flecs_query_dispatch` (1656-1731) -/
  | dispatch (op : QOp) (redo : Bool)

/-- `flecs_query_reset_after_block` (1264-1325) -/
def resetAfterBlockF (me : Int) (result : Bool) : VMM Unit := do
  let start ← vop me
  let endI := start.next
  if result then return
  let oi := (← get).opIndex
  setWr endI (← wrAt oi)
  modify fun v => { v with opIndex := endI }
  setCtx me (fun c => { c with opIndex := endI })

def vmF : Nat → Call → VMM Bool
  | 0, _ => do unmod "fuel"; return false
  | fuel + 1, .runUntil redo0 first cur last => do
    modify fun v => { v with opIndex := cur }
    let mut redo := redo0
    for _ in [0:500] do
      let i := (← get).opIndex
      let op ← vop i
      let result ← vmF fuel (.dispatch op redo)
      let cur' := if result then op.next else op.prev
      if cur' == orMarker then modify fun v => { v with markerReached := true }
      let oi := (← get).opIndex
      redo := cur' < oi
      if !redo then setWr cur' ((← wrAt cur') || (← wrAt oi) || op.wr)
      modify fun v => { v with opIndex := cur' }
      if cur' ≤ first then return false
      if !(cur' < last) then return true
      if (← get).unmodelled.isSome then return false
    unmod "loop bound"
    return false
  | fuel + 1, .runBlock redo => do
    let me := (← get).opIndex
    if !redo then setCtx me (fun c => { c with opIndex := me + 1 })
    else
      let oc ← ctxAt me
      if (← vop oc.opIndex).kind == .end_ then return false
    setWr (me + 1) (← wrAt me)
    let op ← vop me
    let oc ← ctxAt me
    let r ← vmF fuel (.runUntil redo me oc.opIndex op.next)
    let after := (← get).opIndex
    setCtx me (fun c => { c with opIndex := after - 1 })
    return r
  | fuel + 1, .dispatch op redo => do
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
      let v ← get
      for cur in [v.cacheCur:v.cache.size] do
        let t := v.cache.getD cur 0
        if v.counts.getD t 0 != 0 then
          modify fun v => { v with cacheCur := cur + 1, this := some t }
          return true
      modify fun v => { v with cacheCur := v.cache.size }
      return false
    | .and_ =>
      if !(← wrAt me) then unmod "select on an unwritten $this (eval.c 136-148)"; return false
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
      if op.srcVar && !(← wrAt me) then unmod "select_or (eval.c 1390-1508)"; return false
      let r ← vmF fuel (.runBlock redo)
      if r then setCtx me (fun c => { c with opIndex := op.next })
      return r
    | .not_ =>
      if redo then return false
      let r ← vmF fuel (.runBlock false)
      resetAfterBlockF me r
      return !r
    | .optional =>
      let r ← vmF fuel (.runBlock redo)
      resetAfterBlockF me r
      if !redo then return true
      return r
    | .ifVar =>
      if !redo then
        if (← get).thisEntityUnset then
          resetAfterBlockF me false
          return true
      vmF fuel (.runBlock redo)

/-- `ecs_query_next` until it returns false, with the fuel VM. -/
def iterateF (ops : Array QOp) (cache : Array Nat) (types : Array (List Nat)) (counts : Array Nat) :
    List Nat × VM := Id.run do
  let n := ops.size
  let v0 : VM := { ops, cache, types, counts, written := Array.replicate (n + 1) false,
                   opCtx := Array.replicate (n + 1) {} }
  let prog : VMM (List Nat) := do
    let mut out : List Nat := []
    let mut qop : Int := 0
    let mut redo := false
    for _ in [0:64] do
      let r ← vmF 1200 (.runUntil redo (-1) qop ((n : Int) - 1))
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

/-- `run` with the fuel VM: (yielded tables, matching tables), or none when
    the program is skipped or unmodelled. -/
def runF (p : Prog) : Option (List Nat × List Nat) :=
  if p.tables.toList.eraseDups.length != p.tables.size then none else
  match createQuery p.storage p.terms .auto false false with
  | .created .auto cts _ _ =>
    match finalizeTerms p.storage p.terms with
    | .error _ => none
    | .ok q =>
      let c := compile q p.terms
      if c.unmodelled.isSome then none else
      let cache := (List.range p.tables.size).filter (fun t => matchesDoc cts (p.tables.getD t [])) |>.toArray
      let counts := p.tables.map (fun _ => 1)
      let (got, vm) := iterateF c.ops cache p.tables counts
      if vm.unmodelled.isSome then none else
      some (got, (List.range p.tables.size).filter (fun t => matchesDoc p.terms (p.tables.getD t [])))
  | _ => none

/-- The two VMs agree on a program (the search mode `or agree`). -/
def agree (p : Prog) : List (String × String) :=
  match run p, runF p with
  | .ran _ got want _ _, some (got', want') =>
    if got == got' && want == want' then []
    else [("VM agreement", s!"the partial VM yields {got}, the fuel VM {got'}")]
  | .ran _ got _ _ _, none => [("VM agreement", s!"the partial VM yields {got}, the fuel VM is unmodelled")]
  | _, some (got', _) => [("VM agreement", s!"the partial VM did not run, the fuel VM yields {got'}")]
  | _, none => []

end Flecs.OrVM
