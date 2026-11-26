import Jank.R6.Nrepl.Graph

/-!
# Round 6, nREPL: every schedule of T3, by a depth-first search with hash compaction

T3's state graph (two connections, four evals each) outgrows the memory a process may take here
(Graph.lean keeps every state: ≈3.8 KB each, and T3 has more than 733,454, the states ≤6
preemptions reach). For the question "what does ANY schedule reach" no edge needs keeping, only the
set of states seen: this search keeps, per state, a 64-bit hash of the whole state (every field,
derived `Hashable` instances below) and its cheap summary hash (StateEq.lean) — 16 bytes — and the
depth-first stack. It reports every final state's verdict, every step violation and every deadlock
it meets.

What this gives up: two different states with equal hash pairs would be merged, and the second
one's successors not visited (hash compaction; Holzmann's bitstate family). The derived hash is
not a proved injective function, so the result is a search, not a decision: with n states and a
uniform 64-bit hash, the chance of any collision is below n²/2⁶⁵. The derived `BEq` search
(Graph.lean) is exact and is used wherever memory allows (T7, T9).
-/

namespace Jank.R6.Nrepl

open Determinismo Jank.R3.Nrepl Jank.NreplServer Jank.Analyzer

def nvHash : NV → UInt64
  | .i a => mixHash 1 (hash a)
  | .d a => mixHash 2 (hash a.toBits)
  | .b a => mixHash 3 (hash a)
  | .cs a => mixHash 4 (hash a)

instance : Hashable NV := ⟨nvHash⟩

deriving instance Hashable for Jank.Analyzer.CT
deriving instance Hashable for Obj
deriving instance Hashable for SourcePosition
deriving instance Hashable for ReadSource
deriving instance Hashable for ExprPosition
deriving instance Hashable for ExprKind
deriving instance Hashable for LoopKind
deriving instance Hashable for ConversionPolicy
deriving instance Hashable for CppValueKind
deriving instance Hashable for Parameter
deriving instance Hashable for FunctionArity
deriving instance Hashable for ArityKey
deriving instance Hashable for FunctionContext
deriving instance Hashable for Catch
deriving instance Hashable for ExprData
deriving instance Hashable for Expr
deriving instance Hashable for FrameType
deriving instance Hashable for LocalBinding
deriving instance Hashable for LocalCapture
deriving instance Hashable for LocalFrame
deriving instance Hashable for Arena
deriving instance Hashable for Val
deriving instance Hashable for Closure
deriving instance Hashable for NsCell
deriving instance Hashable for Slot
deriving instance Hashable for ExObj
deriving instance Hashable for LazyMap
deriving instance Hashable for Heap
deriving instance Hashable for JW
deriving instance Hashable for Jank.R3.Nrepl.TB
deriving instance Hashable for JVal
deriving instance Hashable for Desc
deriving instance Hashable for Sock
deriving instance Hashable for TConfig
deriving instance Hashable for TReq
deriving instance Hashable for TSent
deriving instance Hashable for EvalRec
deriving instance Hashable for TMem
deriving instance Hashable for Jank.R3.Nrepl.Handle
deriving instance Hashable for EvalReq
deriving instance Hashable for Fail
deriving instance Hashable for EvalEnd
deriving instance Hashable for EvAfter
deriving instance Hashable for OutEv

def exceptHash : Except Fail (Option Obj) → UInt64
  | .ok a => mixHash 1 (hash a)
  | .error a => mixHash 2 (hash a)

instance : Hashable (Except Fail (Option Obj)) := ⟨exceptHash⟩

deriving instance Hashable for EvPhase
deriving instance Hashable for Jank.LexBytes.Locale
deriving instance Hashable for Jank.LexBytes.Dec
deriving instance Hashable for Jank.ReadValue.Val
deriving instance Hashable for Jank.Lex.P
deriving instance Hashable for Jank.Lex.Kind
deriving instance Hashable for Jank.Lex.Data
deriving instance Hashable for Jank.Lex.Token
deriving instance Hashable for Jank.Lex.Out
deriving instance Hashable for Jank.Read.Shorthand
deriving instance Hashable for Jank.Read.S
deriving instance Hashable for EvRun
deriving instance Hashable for TEval
deriving instance Hashable for TCI
deriving instance Hashable for TConn
deriving instance Hashable for TPhase
deriving instance Hashable for TClient
deriving instance Hashable for TTh

/-- The whole state's derived hash, paired with the cheap summary hash. -/
def fullHash (k : PKey) : UInt64 × UInt64 :=
  (k.threads.foldl (fun h t => mixHash h (hash t)) (hash k.mem), hash k)

end Jank.R6.Nrepl

namespace Jank.R6.Nrepl

open Determinismo Jank.R3.Nrepl Jank.NreplServer

structure HK where
  a : UInt64
  b : UInt64
  deriving BEq, Hashable

structure HOut where
  states : Nat := 0
  expanded : Nat := 0
  runs : Nat := 0
  finals : Nat := 0
  finalViol : Nat := 0
  stepViol : Nat := 0
  deadlocks : Nat := 0
  examples : List String := []
  maxStack : Nat := 0
  checked : Nat := 0
  checkFails : Nat := 0
  /-- Blocked steps that changed the state (World T's R1 hang marks itself; expected 0 elsewhere):
  followed like any other step. -/
  blockedMoves : Nat := 0
  stopped : Bool := false
  /-- Distinct final states (by hash pair). -/
  finalKeys : Std.HashSet HK := {}

/-- Every state any schedule reaches (the sdk's `interleave`: any live thread may step), depth first,
states kept as hash pairs. `canon`: logs ordered by client (Graph.lean); `check`: each step also
run from the state with its logs in the other order (Graph.lean `build`'s check). -/
def dfsReach (s : TScenario) (canon check noOut : Bool) (maxStates deadlineMs : Nat) (desc : Bool := false) :
    IO HOut := do
  let t0 ← IO.monoMsNow
  -- `desc`: the logs' normal form puts clients in decreasing order: the same states, hashed through a
  -- different serialization (a second run whose collisions, if any, fall elsewhere).
  let norm (k : PKey) : PKey := if canon then (if desc then altKey k else canonKey k) else k
  let k0 := norm (PKey.of (tInitial s.cfg s.scripts))
  let h0 := fullHash k0
  let mut seen : Std.HashSet HK := ({} : Std.HashSet HK).insert ⟨h0.1, h0.2⟩
  let mut stack : Array PKey := #[k0]
  let mut o : HOut := { states := 1 }
  while !stack.isEmpty do
    if o.expanded % 1024 == 0 then
      if (← IO.monoMsNow) - t0 > deadlineMs || o.states > maxStates then
        return { o with stopped := true }
      if o.expanded % 100000 == 0 && o.expanded > 0 then
        IO.println s!"    … {o.expanded} expanded, {o.states} seen, stack {stack.size} ({(← IO.monoMsNow) - t0} ms)"
        (← IO.getStdout).flush
    let k := stack.back!
    stack := stack.pop
    o := { o with expanded := o.expanded + 1 }
    let live := liveOf k
    if live.isEmpty then
      let h := fullHash k
      o := { o with finals := o.finals + 1, finalKeys := o.finalKeys.insert ⟨h.1, h.2⟩ }
      if let some (p, d) := judgeEnd s k.mem noOut then
        o := { o with finalViol := o.finalViol + 1, examples := o.examples ++ [s!"final: {p}: {d.take 300}"] }
      continue
    let mut moved := false
    for t in live do
      let some locals := k.threads.getD t none | continue
      let brs := branchesOf k t locals
      o := { o with runs := o.runs + brs.size }
      if check then
        let ka := altKey k
        if let some la := ka.threads.getD t none then
          let brs' := branchesOf ka t la
          let same := brs.size == brs'.size && (brs.zip brs').all fun ((ta, ra, qa), (tb, rb, qb)) =>
            ta.map (·.value) == tb.map (·.value) && ra.isSome == rb.isSome &&
            (match ra, rb with
              | .stop _, .stop _ => true
              | x, y => x == y) && canonKey qa == canonKey qb
          o := { o with checked := o.checked + 1, checkFails := o.checkFails + (if same then 0 else 1) }
      for (_, res, q) in brs do
        match res with
        | .stop (some (p, d)) =>
          moved := true
          o := { o with stepViol := o.stepViol + 1 }
          if o.examples.length < 5 then o := { o with examples := o.examples ++ [s!"step: {p}: {d.take 300}"] }
        | .stop none => moved := true
        | .blocked =>
          let q' := norm q
          if !(q' == k) then
            o := { o with blockedMoves := o.blockedMoves + 1 }
            let h := fullHash q'
            let hk : HK := ⟨h.1, h.2⟩
            if !seen.contains hk then
              seen := seen.insert hk
              o := { o with states := o.states + 1 }
              stack := stack.push q'
        | .ran | .done =>
          moved := true
          let q' := norm q
          let h := fullHash q'
          let hk : HK := ⟨h.1, h.2⟩
          if !seen.contains hk then
            seen := seen.insert hk
            o := { o with states := o.states + 1 }
            stack := stack.push q'
    if !moved then
      o := { o with deadlocks := o.deadlocks + 1 }
      if o.examples.length < 5 then
        o := { o with examples := o.examples ++ [s!"deadlock: {((tStuck (procOf k #[])).getD "").take 300}"] }
    o := { o with maxStack := max o.maxStack stack.size }
  return o

end Jank.R6.Nrepl
