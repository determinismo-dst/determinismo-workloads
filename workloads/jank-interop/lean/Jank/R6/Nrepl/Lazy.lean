import Jank.R6.Nrepl.Graph

/-!
# Round 6, nREPL: counting preemption-bounded timelines without the whole graph

`Graph.lean` builds every state any schedule reaches, then counts. When that graph is too large
(T3's), `countLazy` computes the same count at one budget b by running each (state, thread) step
only when a schedule with ≤ b preemptions takes it: the states it stores are those ≤ b preemptions
reach. The scheduler rule, the leaves, the eintr-0 count, the violations and the log ordering
(`canon`, with the same order check as `build`) are Graph.lean's (`countFrom`), so for the budgets
both can run the two give the same numbers (checked: Run/R6/Nrepl.lean `lazy` against `count`).
-/

namespace Jank.R6.Nrepl

open Determinismo Jank.R3.Nrepl Jank.NreplServer

structure LState where
  keys : Array PKey := #[]
  index : Std.HashMap PKey Nat := {}
  steps : Std.HashMap (Nat × Nat) (Array Branch) := {}
  finals : Std.HashMap Nat (Option (String × String)) := {}
  memo : Std.HashMap SKey Sum := {}
  runs : Nat := 0
  checked : Nat := 0
  checkFails : Nat := 0
  checkFirstDiffers : Nat := 0
  /-- Stopped: the time or state bound was reached; the count is not complete. -/
  stopped : Bool := false
  deriving Inhabited

structure LCfg where
  s : TScenario
  canon : Bool := false
  check : Bool := false
  noOut : Bool := false
  maxStates : Nat := 1000000
  deadline : Nat := 0

abbrev LM := StateT LState IO

def lIntern (k : PKey) : LM Nat := do
  let st ← get
  match st.index.get? k with
  | some i => pure i
  | none =>
    let i := st.keys.size
    set { st with keys := st.keys.push k, index := st.index.insert k i }
    pure i

def lNorm (c : LCfg) (k : PKey) : PKey := if c.canon then canonKey k else k

def lFinal (c : LCfg) (i : Nat) : LM (Option (String × String)) := do
  if let some v := (← get).finals.get? i then return v
  let k := (← get).keys[i]!
  let v := judgeEnd c.s k.mem c.noOut
  if c.check then
    let v' := judgeEnd c.s (altKey k).mem c.noOut
    modify fun st => { st with checked := st.checked + 1 }
    if v.isSome != v'.isSome then modify fun st => { st with checkFails := st.checkFails + 1 }
    else if (v.map (·.1)) != (v'.map (·.1)) then modify fun st => { st with checkFirstDiffers := st.checkFirstDiffers + 1 }
  modify fun st => { st with finals := st.finals.insert i v }
  return v

def lStep (c : LCfg) (i t : Nat) : LM (Array Branch) := do
  if let some bs := (← get).steps.get? (i, t) then return bs
  let k := (← get).keys[i]!
  let some locals := k.threads.getD t none | return #[]
  let brs := branchesOf k t locals
  if c.check then
    let ka := altKey k
    if let some la := ka.threads.getD t none then
      let brs' := branchesOf ka t la
      let same := brs.size == brs'.size && (brs.zip brs').all fun ((ta, ra, qa), (tb, rb, qb)) =>
        ta.map (·.value) == tb.map (·.value) && ra.isSome == rb.isSome &&
        (match ra, rb with
          | .stop _, .stop _ => true
          | x, y => x == y) && canonKey qa == canonKey qb
      modify fun st => { st with checked := st.checked + 1, checkFails := st.checkFails + (if same then 0 else 1) }
  let mut bs : Array Branch := #[]
  for (taken, res, q) in brs do
    let j ← lIntern (lNorm c q)
    bs := bs.push { taken, res, succ := j }
  modify fun st => { st with steps := st.steps.insert (i, t) bs, runs := st.runs + brs.size }
  return bs

/-- Graph.lean's `countFrom`, with the steps run on demand. -/
partial def lCount (c : LCfg) (i : Nat) (cur : Option Nat) (blocked : List Nat) (left : Nat) : LM Sum := do
  let key : SKey := (i, cur, blocked, left, none)
  if let some r := (← get).memo.get? key then return r
  if (← get).stopped then return {}
  let st ← get
  if st.keys.size > c.maxStates || (c.deadline > 0 && st.memo.size % 4096 == 0 && (← IO.monoMsNow) > c.deadline) then
    set { st with stopped := true }
    return {}
  let k := st.keys[i]!
  let live := liveOf k
  let r ← do
    if live.isEmpty then
      pure (leafSum i (← lFinal c i) false)
    else
      let ready := live.filter (!blocked.contains ·)
      if ready.isEmpty then
        let d := (tStuck (procOf k #[])).getD ""
        pure (leafSum i (some ("every request gets a done reply (no hang)", d)) false)
      else
        let choices : List (Nat × Nat × Nat) := match cur with
          | some c' =>
            if ready.contains c' then
              let others := ready.filter (· != c')
              if left > 0 && !others.isEmpty then
                (c', left, 1) :: others.map fun o => (o, left - 1, 1)
              else [(c', left, 0)]
            else [((ready.find? (· > c')).getD (ready.headD 0), left, 0)]
          | none => [(ready.headD 0, left, 0)]
        let mut acc : Sum := {}
        for (t, left', d0) in choices do
          let bs ← lStep c i t
          for b in bs do
            let ch ← match b.res with
              | .stop v => pure (leafSum b.succ v false)
              | .ran => lCount c b.succ (some t) [] left'
              | .done => lCount c b.succ (some t) [] left'
              | .blocked => lCount c b.succ (some t) (insertSorted t blocked) left'
            acc := acc.add ch (!b.eintr1) (d0 + b.taken.size)
        pure acc
  modify fun st => { st with memo := st.memo.insert key r }
  return r

def countLazy (c : LCfg) (budget : Nat) : IO (Sum × LState) := do
  let p0 := tInitial c.s.cfg c.s.scripts
  let (r, st) ← (do
    let i ← lIntern (lNorm c (PKey.of p0))
    lCount c i none [] budget).run {}
  pure (r, st)

end Jank.R6.Nrepl
