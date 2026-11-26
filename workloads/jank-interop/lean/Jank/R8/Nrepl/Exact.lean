import Jank.R8.Nrepl.Codec

/-!
# Round 8, nREPL: World T's exact state graph in compact form, and every budget counted at once

`exactGraph` builds the graph of every state any schedule reaches (the sdk's `interleave`: any live
thread may step next), as round 6's `build` (Graph.lean) does, on the same step (`branchesOf`, one
iteration of `interleavePB`'s loop after the choice) and with the same log ordering (`canonKey`), but
keeps each state as its code (Codec.lean): a few small indices into tables of distinct components.
Edges are packed into one `Nat` each (successor, thread, result, whether the branch drew
`net.read.eintr = 1`).

`comboGraph` and `countLayers` count round 3's `interleavePB` timelines exactly, for every budget
0 … B at once. A scheduler state ("combo") is a state with the scheduler's `cur` and `blocked`
(ThreadSearch.lean 26–60); its children are copied from round 6's `countFrom` (Graph.lean 344–389):
round robin after a block or an end, and, when the running thread is ready and another is, a
`thread.preempt` decision whose options other than 0 spend one unit of budget. Let f_L(c) be the
number of timelines from combo c with L preemptions left. A child reached without a preemption
is counted at layer L, one reached by a preemption at layer L − 1, and a leaf (a final state, a
step that threw, a deadlock) is one timeline. The combo graph is acyclic (a progress step goes to
a later state of the acyclic state graph, a blocked step adds a thread to `blocked`), so each layer
is one pass over the combos in post-order, from the layer below. f_b of the root (state 0, no `cur`,
nothing blocked) is the count at ≤ b, for each b ≤ B.
-/

namespace Jank.R8.Nrepl

open Determinismo Jank.R3.Nrepl Jank.R6.Nrepl Jank.NreplServer Jank.Analyzer

unsafe def ptrSameUnsafe {α : Type} (a b : α) : Bool := ptrAddrUnsafe a == ptrAddrUnsafe b

/-- Pointer identity at run time (Codec.lean: the fast path's premise). -/
@[implemented_by ptrSameUnsafe] opaque ptrSame {α : Type} (a b : α) : Bool

/-- Fast-path hints for a successor of the state with code `pc`: a component that is the very object
stored at the parent's index keeps that index. -/
def hintsFor (T : Tabs) (pc : Array Nat) (c : Comps) (fast : Bool) : Hints :=
  if !fast then {} else
  let hAt {α : Type} (t : Tab α) (j : Nat) (x : α) : Nat × Bool :=
    let i := pc.getD j 0
    match t.vals[i]? with
    | some y => (i, ptrSame y x)
    | none => (i, false)
  { jw := hAt T.jw 0 c.jw, fds := hAt T.fds 1 c.fds, temps := hAt T.temps 2 c.temps,
    socks := hAt T.socks 3 c.socks, misc := hAt T.misc 4 c.misc, replies := hAt T.replies 5 c.replies,
    logs := hAt T.logs 6 c.logs,
    th := c.threads.zipIdx.map fun (x, k) => if 7 + k < pc.size then hAt T.th (7 + k) x else (0, false) }

/-! ## Steps

`branchesOfP step` is round 6's `branchesOf` (Graph.lean 112–128) over a given step function;
with `tStep` (round 3's, the step of `tProg`) it is `branchesOf` itself. -/

abbrev StepFn := Nat → TTh → ProcessM TMem TTh (StepResult TTh)

def iterStepP (step : StepFn) (t : Nat) (locals : TTh) : ProcessM TMem TTh (StepResult TTh) := do
  let r ← step t locals
  match r with
  | .ran l => modify fun p => { p with threads := p.threads.set! t (some l), steps := p.steps + 1 }
  | .blocked => pure ()
  | .done => modify fun p => { p with threads := p.threads.set! t none, steps := p.steps + 1 }
  pure r

partial def branchesOfP (step : StepFn) (k : PKey) (t : Nat) (locals : TTh) : Array (Array Taken × Res × PKey) := Id.run do
  let mut out := #[]
  let mut path : Array Nat := #[]
  for _ in [0:100000] do
    let (taken, res, q) := match (iterStepP step t locals).run (procOf k path) with
      | .ok r p => (p.decisions.taken, (match r with
          | .ran _ => Res.ran
          | .blocked => Res.blocked
          | .done => Res.done), PKey.of p)
      | .error (.violation prop d) p => (p.decisions.taken, Res.stop (some (prop, d)), PKey.of p)
      | .error _ p => (p.decisions.taken, Res.stop none, PKey.of p)
    out := out.push (taken, res, q)
    match nextPath taken with
    | none => break
    | some p => path := p
  return out

/-! ## Edges -/

/-- Branch results: 0 ran, 1 blocked, 2 done, 3 stopped without a violation (limit), 4 a violation. -/
def resKind : Res → Nat
  | .ran => 0
  | .blocked => 1
  | .done => 2
  | .stop none => 3
  | .stop (some _) => 4

def packEdge (succ t kind e1 : Nat) : Nat := ((succ * 16 + t) * 8 + kind) * 2 + e1
def eE1 (e : Nat) : Nat := e % 2
def eKind (e : Nat) : Nat := (e / 2) % 8
def eT (e : Nat) : Nat := (e / 16) % 16
def eSucc (e : Nat) : Nat := e / 256

structure EG where
  codes : Array (Array Nat) := #[]
  index : Std.HashMap (Array Nat) Nat := {}
  /-- Per expanded state: where its edges start (`eoff[i]` … `eoff[i+1]`). -/
  eoff : Array Nat := #[]
  edges : Array Nat := #[]
  finals : Array Nat := #[]
  finalViol : Array (Nat × String × String) := #[]
  stepViol : Array (Nat × String × String) := #[]
  deadlocks : Array Nat := #[]
  runs : Nat := 0
  blockedMoves : Nat := 0
  progressSelf : Nat := 0
  fastHits : Nat := 0
  maxThreads : Nat := 0
  /-- Round 6's order check (Graph.lean `build … check`): each step and final verdict also computed
  from the state with its logs ordered the other way. -/
  checkOn : Bool := false
  checked : Nat := 0
  checkFails : Nat := 0
  checkFirstDiffers : Nat := 0
  deriving Inhabited

def EG.size (g : EG) : Nat := g.codes.size

def EG.intern (g : EG) (code : Array Nat) : EG × Nat × Bool :=
  match g.index.get? code with
  | some i => (g, i, false)
  | none =>
    let n := g.codes.size
    ({ g with codes := g.codes.push code, index := g.index.insert code n }, n, true)

def EG.decode (g : EG) (T : Tabs) (i : Nat) : Option PKey :=
  T.decode (g.codes.getD i #[]).toList

def countFast (h : Hints) : Nat :=
  let b (x : Nat × Bool) := if x.2 then 1 else 0
  b h.jw + b h.fds + b h.temps + b h.socks + b h.misc + b h.replies + b h.logs + (h.th.filter (·.2)).length

/-- Encodes a state (with the parent's code for the fast path) and interns its code. -/
def EG.add (g : EG) (T : Tabs) (q : PKey) (pc : Array Nat) (fast : Bool) : EG × Tabs × Nat :=
  let c := split q
  let h := hintsFor T pc c fast
  let (T, code) := T.encodeC c h
  let (g, j, _) := { g with fastHits := g.fastHits + countFast h }.intern code.toArray
  (g, T, j)

/-- Expands state `i`: every live thread's step under every value of its own decisions. -/
def EG.expand (g : EG) (T : Tabs) (step : StepFn) (s : TScenario) (i : Nat) (canon noOut fast : Bool) : EG × Tabs :=
  expandCore { g with eoff := g.eoff.push g.edges.size } T step s i canon noOut fast
where
  /-- Appends state `i`'s edges (the caller records where they start). -/
  expandCore (g : EG) (T : Tabs) (step : StepFn) (s : TScenario) (i : Nat) (canon noOut fast : Bool) : EG × Tabs := Id.run do
  let some k := g.decode T i | return (g, T)
  let mut T := T
  let pc := g.codes.getD i #[]
  let live := liveOf k
  let mut g := { g with maxThreads := max g.maxThreads k.threads.size }
  if live.isEmpty then
    let v := judgeEnd s k.mem noOut
    g := { g with finals := g.finals.push i }
    if let some (p, d) := v then g := { g with finalViol := g.finalViol.push (i, p, d) }
    if g.checkOn then
      let v' := judgeEnd s (altKey k).mem noOut
      g := { g with checked := g.checked + 1 }
      if v.isSome != v'.isSome then g := { g with checkFails := g.checkFails + 1 }
      else if (v.map (·.1)) != (v'.map (·.1)) then g := { g with checkFirstDiffers := g.checkFirstDiffers + 1 }
    return (g, T)
  let mut moved := false
  for t in live do
    let some locals := k.threads.getD t none | continue
    let brs := branchesOfP step k t locals
    if g.checkOn then
      let ka := altKey k
      if let some la := ka.threads.getD t none then
        let brs' := branchesOfP step ka t la
        let same := brs.size == brs'.size && (brs.zip brs').all fun ((ta, ra, qa), (tb, rb, qb)) =>
          ta.map (·.value) == tb.map (·.value) && ra.isSome == rb.isSome &&
          (match ra, rb with
            | .stop _, .stop _ => true
            | x, y => x == y) && canonKey qa == canonKey qb
        g := { g with checked := g.checked + 1, checkFails := g.checkFails + (if same then 0 else 1) }
    for (taken, res, q) in brs do
      let e1 := if taken.any (fun x => x.name == "net.read.eintr" && x.value != 0) then 1 else 0
      let kind := resKind res
      g := { g with runs := g.runs + 1 }
      match res with
      | .stop v =>
        moved := true
        if let some (p, d) := v then g := { g with stepViol := g.stepViol.push (i, p, d) }
        g := { g with edges := g.edges.push (packEdge i t kind e1) }
      | _ =>
        let q' := if canon then canonKey q else q
        let (g', T', j) := g.add T q' pc fast
        g := g'
        T := T'
        match res with
        | .blocked => if j != i then g := { g with blockedMoves := g.blockedMoves + 1 }
        | _ =>
          moved := true
          if j == i then g := { g with progressSelf := g.progressSelf + 1 }
        g := { g with edges := g.edges.push (packEdge j t kind e1) }
  if !moved then g := { g with deadlocks := g.deadlocks.push i }
  return (g, T)

/-- Every state any schedule reaches, breadth first (state ids in discovery order). -/
def exactGraph (s : TScenario) (canon noOut fast : Bool) (maxStates deadlineMs : Nat)
    (progress : Nat → Nat → IO Unit := fun _ _ => pure ()) (step : StepFn := tStep) (check : Bool := false) :
    IO (EG × Tabs × Bool) := do
  let t0 ← IO.monoMsNow
  let p0 := tInitial s.cfg s.scripts
  let k0 := if canon then canonKey (PKey.of p0) else PKey.of p0
  let (g, T, _) := ({ checkOn := check } : EG).add {} k0 #[] false
  let mut g := g
  let mut T := T
  let mut i := 0
  while i < g.size do
    if i % 1024 == 0 then
      if g.size > maxStates || (← IO.monoMsNow) - t0 > deadlineMs then return (g, T, false)
      if i % 100000 == 0 && i > 0 then progress i g.size
    let (g', T') := g.expand T step s i canon noOut fast
    g := g'
    T := T'
    i := i + 1
  return (g, T, true)

/-! ## The state graph's own checks: acyclic, the longest progress path -/

/-- Progress successors (ran/done to another state). -/
def EG.succs (g : EG) (i : Nat) : List Nat := Id.run do
  let a := g.eoff.getD i 0
  let b := g.eoff.getD (i + 1) g.edges.size
  let mut out := []
  for k in [a:b] do
    let e := g.edges[k]!
    let kd := eKind e
    if (kd == 0 || kd == 2 || (kd == 1 && eSucc e != i)) && eSucc e != i then out := eSucc e :: out
  return out.eraseDups

/-- Longest progress path from state 0 and whether the graph (without self-loops) is acyclic. -/
def EG.longest (g : EG) : Nat × Bool := Id.run do
  let n := g.size
  let mut color : ByteArray := ByteArray.mk (Array.replicate n 0)
  let mut len : Array Nat := Array.replicate n 0
  let mut acyclic := true
  let mut stack : Array (Nat × List Nat) := #[(0, g.succs 0)]
  color := color.set! 0 1
  while !stack.isEmpty do
    let (v, todo) := stack.back!
    match todo with
    | [] =>
      let l := (g.succs v).foldl (fun a w => max a (len[w]! + 1)) 0
      len := len.set! v l
      color := color.set! v 2
      stack := stack.pop
    | w :: more =>
      stack := stack.set! (stack.size - 1) (v, more)
      if color.get! w == 1 then acyclic := false
      else if color.get! w == 0 then
        color := color.set! w 1
        stack := stack.push (w, g.succs w)
  return (len.getD 0 0, acyclic)

/-! ## Scheduler states and the layered count -/

/-- Live threads of state `i` (those with edges), in increasing order. -/
def EG.live (g : EG) (i : Nat) : List Nat := Id.run do
  let a := g.eoff.getD i 0
  let b := g.eoff.getD (i + 1) g.edges.size
  let mut ts : List Nat := []
  for k in [a:b] do
    let t := eT g.edges[k]!
    if !ts.contains t then ts := ts ++ [t]
  return ts.mergeSort (· ≤ ·)

def EG.branches (g : EG) (i t : Nat) : List Nat := Id.run do
  let a := g.eoff.getD i 0
  let b := g.eoff.getD (i + 1) g.edges.size
  let mut out := #[]
  for k in [a:b] do
    let e := g.edges[k]!
    if eT e == t then out := out.push e
  return out.toList

def isFinalViol (g : EG) (i : Nat) : Bool := g.finalViol.any (·.1 == i)

/-- Combo key: the state in the low 27 bits; `cur + 1` (0: none) and the blocked mask above. -/
def comboKey (i : Nat) (cur : Option Nat) (blocked : Nat) : Nat :=
  ((match cur with | some c => c + 1 | none => 0) * 256 + blocked) * 134217728 + i

def keyState (k : Nat) : Nat := k % 134217728
def keyBlocked (k : Nat) : Nat := (k / 134217728) % 256
def keyCur (k : Nat) : Option Nat := let c := k / 134217728 / 256; if c == 0 then none else some (c - 1)

/-- Combo entries: (target * 4 + kind) * 2 + e1; kind 0 a combo, 1 a leaf, 2 a leaf with a violation. -/
def packC (target kind e1 : Nat) : Nat := (target * 4 + kind) * 2 + e1

structure CG where
  index : Std.HashMap Nat Nat := {}
  keys : Array Nat := #[]
  coff : Array Nat := #[]
  cmid : Array Nat := #[]
  cend : Array Nat := #[]
  ce : Array Nat := #[]
  order : Array Nat := #[]
  deriving Inhabited

def CG.id (cg : CG) (key : Nat) : CG × Nat × Bool :=
  match cg.index.get? key with
  | some c => (cg, c, false)
  | none =>
    let c := cg.keys.size
    ({ cg with index := cg.index.insert key c, keys := cg.keys.push key, coff := cg.coff.push 0,
               cmid := cg.cmid.push 0, cend := cg.cend.push 0 }, c, true)

/-- Children of combo c (round 6's `countFrom` choices), written into `ce`. -/
def CG.expand (cg : CG) (g : EG) (c : Nat) : CG := Id.run do
  let key := cg.keys[c]!
  let i := keyState key
  let blocked := keyBlocked key
  let cur := keyCur key
  let live := g.live i
  let mut cg := { cg with coff := cg.coff.set! c cg.ce.size }
  let leaf (v : Bool) : Nat := packC 0 (if v then 2 else 1) 0
  if live.isEmpty then
    cg := { cg with ce := cg.ce.push (leaf (isFinalViol g i)) }
    return { cg with cmid := cg.cmid.set! c cg.ce.size, cend := cg.cend.set! c cg.ce.size }
  let ready := live.filter fun t => (blocked >>> t) % 2 == 0
  if ready.isEmpty then
    cg := { cg with ce := cg.ce.push (leaf true) }
    return { cg with cmid := cg.cmid.set! c cg.ce.size, cend := cg.cend.set! c cg.ce.size }
  let (stay, others) : Nat × List Nat := match cur with
    | some t => if ready.contains t then (t, ready.filter (· != t)) else ((ready.find? (· > t)).getD (ready.headD 0), [])
    | none => (ready.headD 0, [])
  let mut cg' := cg
  let emit (cg : CG) (t : Nat) : CG := Id.run do
    let mut cg := cg
    for e in g.branches i t do
      let kd := eKind e
      let e1 := eE1 e
      if kd == 3 then cg := { cg with ce := cg.ce.push (packC 0 1 e1) }
      else if kd == 4 then cg := { cg with ce := cg.ce.push (packC 0 2 e1) }
      else
        let nb := if kd == 1 then blocked ||| (1 <<< t) else 0
        let (cg2, d, _) := cg.id (comboKey (eSucc e) (some t) nb)
        cg := { cg2 with ce := cg2.ce.push (packC d 0 e1) }
    return cg
  cg' := emit cg' stay
  cg' := { cg' with cmid := cg'.cmid.set! c cg'.ce.size }
  for o in others do cg' := emit cg' o
  return { cg' with cend := cg'.cend.set! c cg'.ce.size }

/-- The combo graph from the root, depth first; `order` is post-order (children first). -/
def comboGraph (g : EG) (maxCombos : Nat) (deadline : Nat) : IO (CG × Bool) := do
  let (cg, root, _) := ({} : CG).id (comboKey 0 none 0)
  let mut cg := cg.expand g root
  let mut color : ByteArray := ByteArray.mk #[1]
  let mut stack : Array (Nat × Nat) := #[(root, cg.coff[root]!)]
  let mut steps := 0
  while !stack.isEmpty do
    steps := steps + 1
    if steps % 65536 == 0 then
      if cg.keys.size > maxCombos || (← IO.monoMsNow) > deadline then return (cg, false)
    let (c, pos) := stack.back!
    if pos < cg.cend[c]! then
      stack := stack.set! (stack.size - 1) (c, pos + 1)
      let e := cg.ce[pos]!
      if (e / 2) % 4 == 0 then
        let d := e / 8
        while color.size ≤ d do color := color.push 0
        if color.get! d == 0 then
          color := color.set! d 1
          cg := cg.expand g d
          stack := stack.push (d, cg.coff[d]!)
    else
      stack := stack.pop
      color := color.set! c 2
      cg := { cg with order := cg.order.push c }
  return (cg, true)

/-- Per budget layer L: timelines, eintr-0 timelines, timelines with a violation, from the root. -/
structure LayerOut where
  n : Nat
  n0 : Nat
  v : Nat
  deriving Inhabited

/-- f_0 … f_B over the combo graph; the root's values per layer. Also the longest timeline (step
attempts) over every combo, an upper bound on every budget's. -/
def countLayers (cg : CG) (B : Nat) (onLayer : Nat → LayerOut → IO Unit := fun _ _ => pure ()) :
    IO (Array LayerOut × Nat) := do
  let m := cg.order.size
  let mut pn : Array Nat := Array.replicate m 0
  let mut p0 : Array Nat := Array.replicate m 0
  let mut pv : Array Nat := Array.replicate m 0
  let mut out : Array LayerOut := #[]
  -- longest timeline: entries counted as step attempts
  let mut len : Array Nat := Array.replicate m 0
  for c in cg.order do
    let mut l := 0
    for k in [cg.coff[c]!:cg.cend[c]!] do
      let e := cg.ce[k]!
      let x := if (e / 2) % 4 == 0 then len[e / 8]! + 1 else 1
      l := max l x
    len := len.set! c l
  let longest := len.getD 0 0
  len := #[]
  for L in [0:B + 1] do
    let mut cn : Array Nat := Array.replicate m 0
    let mut c0 : Array Nat := Array.replicate m 0
    let mut cv : Array Nat := Array.replicate m 0
    for c in cg.order do
      let mut sn := 0
      let mut s0 := 0
      let mut sv := 0
      let hi := if L > 0 then cg.cend[c]! else cg.cmid[c]!
      for k in [cg.coff[c]!:hi] do
        let e := cg.ce[k]!
        let e1 := e % 2
        let kd := (e / 2) % 4
        let lower := k ≥ cg.cmid[c]!
        if kd == 0 then
          let d := e / 8
          let (xn, x0, xv) := if lower then (pn[d]!, p0[d]!, pv[d]!) else (cn[d]!, c0[d]!, cv[d]!)
          sn := sn + xn
          if e1 == 0 then s0 := s0 + x0
          sv := sv + xv
        else
          sn := sn + 1
          if e1 == 0 then s0 := s0 + 1
          if kd == 2 then sv := sv + 1
      cn := cn.set! c sn
      c0 := c0.set! c s0
      cv := cv.set! c sv
    let o : LayerOut := { n := cn.getD 0 0, n0 := c0.getD 0 0, v := cv.getD 0 0 }
    onLayer L o
    out := out.push o
    pn := cn
    p0 := c0
    pv := cv
  return (out, longest)

/-! ## The sdk's own `interleave` walk

`interleave` (the sdk's Threads.lean 51-74) picks the next thread among the ready ones at every
iteration (`thread.next`, a decision when two or more are ready), keeps `blocked` across blocked steps
and clears it after a step that ran or ended. Its timelines from (state, blocked) are counted by
recursion with a memo on the pair: the number of runs the sdk's `exhaust` would make over round 3's
`runT` (Threads.lean 621-639), every schedule, no preemption bound. -/

partial def interFrom (g : EG) (i blocked : Nat) : StateM (Std.HashMap Nat Nat) Nat := do
  let key := blocked * 134217728 + i
  if let some r := (← get).get? key then return r
  let live := g.live i
  let r ← do
    if live.isEmpty then pure 1
    else
      let ready := live.filter fun t => (blocked >>> t) % 2 == 0
      if ready.isEmpty then pure 1
      else
        let mut acc := 0
        for t in ready do
          for e in g.branches i t do
            let kd := eKind e
            if kd == 3 || kd == 4 then acc := acc + 1
            else if kd == 1 then acc := acc + (← interFrom g (eSucc e) (blocked ||| (1 <<< t)))
            else acc := acc + (← interFrom g (eSucc e) 0)
        pure acc
  modify fun m => m.insert key r
  return r

/-- The number of timelines of the sdk's `interleave` from the initial state, and the memo's size. -/
def interCount (g : EG) : Nat × Nat :=
  let (r, m) := (interFrom g 0 0).run {}
  (r, m.size)

/-! ## Bounded budgets, states expanded on demand

For worlds whose every-schedule graph is too large (the unlocked T3u, T9u), the count at one budget b
explores only the scheduler states (state, cur, blocked, budget left) that schedules with at most b
preemptions reach, expanding a state (all its live threads, as `EG.expand`) the first time one of
them needs it: round 6's `countLazy` (Lazy.lean), with compact states and packed scheduler states. -/

def comboKeyL (i : Nat) (cur : Option Nat) (blocked left : Nat) : Nat :=
  (((left * 16 + (match cur with | some c => c + 1 | none => 0)) * 256) + blocked) * 134217728 + i

def keyLeft (k : Nat) : Nat := k / 134217728 / 256 / 16

def keyCurL (k : Nat) : Option Nat := let c := (k / 134217728 / 256) % 16; if c == 0 then none else some (c - 1)

/-- The explorer's states: the graph, the tables, each expanded state's edge span. -/
structure LB where
  g : EG := {}
  T : Tabs := {}
  sa : Array Nat := #[]
  sb : Array Nat := #[]
  deriving Inhabited

def liveIn (g : EG) (a b : Nat) : List Nat := Id.run do
  let mut ts : List Nat := []
  for k in [a:b] do
    let t := eT g.edges[k]!
    if !ts.contains t then ts := ts ++ [t]
  return ts.mergeSort (· ≤ ·)

def branchesIn (g : EG) (a b t : Nat) : List Nat := Id.run do
  let mut out := #[]
  for k in [a:b] do
    let e := g.edges[k]!
    if eT e == t then out := out.push e
  return out.toList

/-- A bounded scheduler state's children (round 6's `countFrom` choices, the budget in the key); its
state `i` is expanded, its edges at `a` … `b`. -/
def expandB (g : EG) (a b : Nat) (cg : CG) (c : Nat) : CG := Id.run do
  let key := cg.keys[c]!
  let i := keyState key
  let blocked := keyBlocked key
  let cur := keyCurL key
  let left := keyLeft key
  let live := liveIn g a b
  let mut cg := { cg with coff := cg.coff.set! c cg.ce.size }
  if live.isEmpty then
    cg := { cg with ce := cg.ce.push (packC 0 (if isFinalViol g i then 2 else 1) 0) }
    return { cg with cend := cg.cend.set! c cg.ce.size }
  let ready := live.filter fun t => (blocked >>> t) % 2 == 0
  if ready.isEmpty then
    cg := { cg with ce := cg.ce.push (packC 0 2 0) }
    return { cg with cend := cg.cend.set! c cg.ce.size }
  let choices : List (Nat × Nat) := match cur with
    | some t =>
      if ready.contains t then
        let others := ready.filter (· != t)
        if left > 0 && !others.isEmpty then (t, left) :: others.map fun o => (o, left - 1) else [(t, left)]
      else [((ready.find? (· > t)).getD (ready.headD 0), left)]
    | none => [(ready.headD 0, left)]
  for (t, l) in choices do
    for e in branchesIn g a b t do
      let kd := eKind e
      let e1 := eE1 e
      if kd == 3 then cg := { cg with ce := cg.ce.push (packC 0 1 e1) }
      else if kd == 4 then cg := { cg with ce := cg.ce.push (packC 0 2 e1) }
      else
        let nb := if kd == 1 then blocked ||| (1 <<< t) else 0
        let (cg2, d, _) := cg.id (comboKeyL (eSucc e) (some t) nb l)
        cg := { cg2 with ce := cg2.ce.push (packC d 0 e1) }
  return { cg with cend := cg.cend.set! c cg.ce.size }

/-- Pads the span arrays to the states found (term mode: nothing else holds them). -/
def padSpans (n : Nat) (sa sb : Array Nat) (done : ByteArray) : Array Nat × Array Nat × ByteArray := Id.run do
  let mut sa := sa
  let mut sb := sb
  let mut done := done
  for _ in [done.size:n] do
    sa := sa.push 0
    sb := sb.push 0
    done := done.push 0
  return (sa, sb, done)

/-- Expands state `i` if it is not yet (term mode, every value passed on owned). -/
def expandState (step : StepFn) (s : TScenario) (canon noOut fast : Bool) (i : Nat)
    (st : EG × Tabs × Array Nat × Array Nat × ByteArray) : EG × Tabs × Array Nat × Array Nat × ByteArray :=
  match st with
  | (g, T, sa, sb, done) =>
    -- Taken apart and rebuilt before any read (the dbgTraceIfShared, an identity that reports a shared
    -- array on stderr, keeps the compiler from folding the rebuild away): without it the edge array
    -- arrived shared here and every push in expandCore copied it (measured: T3 ≤4 99 s against 12 s).
    let g : EG := match g with
      | ⟨codes, index, eoff, edges, finals, finalViol, stepViol, deadlocks, runs, blockedMoves, progressSelf, fastHits, maxThreads,
         c1, c2, c3, c4⟩ =>
        ⟨codes, index, eoff, dbgTraceIfShared "edges at entry" edges, finals, finalViol, stepViol, deadlocks, runs,
         blockedMoves, progressSelf, fastHits, maxThreads, c1, c2, c3, c4⟩
    let n := g.size
    let (sa, sb, done) := padSpans n sa sb done
    if done.get! i == 1 then (g, T, sa, sb, done) else
    let a := g.edges.size
    -- (and again here, for the same reason; both measured: with one of the two, T3 ≤3 and ≤4 take 120 s)
    let g : EG := match g with
      | ⟨codes, index, eoff, edges, finals, finalViol, stepViol, deadlocks, runs, blockedMoves, progressSelf, fastHits, maxThreads,
         c1, c2, c3, c4⟩ =>
        ⟨dbgTraceIfShared "codes" codes, dbgTraceIfShared "index" index, eoff, dbgTraceIfShared "edges" edges, finals,
         finalViol, stepViol, deadlocks, runs, blockedMoves, progressSelf, fastHits, maxThreads, c1, c2, c3, c4⟩
    let (g, T) := EG.expand.expandCore g T step s i canon noOut fast
    let b := g.edges.size
    let n := g.size
    let (sa, sb, done) := padSpans n (sa.set! i a) (sb.set! i b) (done.set! i 1)
    (g, T, sa, sb, done)

/-- The count at budget `b` with states expanded on demand: (timelines, eintr-0, with a violation),
the explorer's states, the scheduler states, and whether it completed. -/
def countBounded (s : TScenario) (b : Nat) (canon noOut fast : Bool) (maxStates maxCombos deadline : Nat)
    (step : StepFn := tStep) : IO (LayerOut × LB × Nat × Bool) := do
  let p0 := tInitial s.cfg s.scripts
  let k0 := if canon then canonKey (PKey.of p0) else PKey.of p0
  let (g0, T0, _) := ({} : EG).add {} k0 #[] false
  let mut g := g0
  let mut T := T0
  let mut sa : Array Nat := #[]
  let mut sb : Array Nat := #[]
  let mut done : ByteArray := ByteArray.empty
  let (cg0, root, _) := ({} : CG).id (comboKeyL 0 none 0 b)
  let mut cg := cg0
  let mut color : ByteArray := ByteArray.empty
  let mut stack : Array (Nat × Nat) := #[]
  let mut todo : Option Nat := some root
  let mut steps := 0
  while todo.isSome || !stack.isEmpty do
    steps := steps + 1
    if steps % 16384 == 0 then
      if cg.keys.size > maxCombos || g.size > maxStates || (← IO.monoMsNow) > deadline then
        return ({ n := 0, n0 := 0, v := 0 }, { g, T, sa, sb }, cg.keys.size, false)
    match todo with
    | some d =>
      -- expand combo d (and its state, the first time)
      todo := none
      let i := keyState cg.keys[d]!
      let (g', T', sa', sb', done') := expandState step s canon noOut fast i (g, T, sa, sb, done)
      g := g'
      T := T'
      sa := sa'
      sb := sb'
      done := done'
      cg := expandB g sa[i]! sb[i]! cg d
      while color.size ≤ d do color := color.push 0
      color := color.set! d 1
      stack := stack.push (d, cg.coff[d]!)
    | none =>
      let (c, pos) := stack.back!
      if pos < cg.cend[c]! then
        stack := stack.set! (stack.size - 1) (c, pos + 1)
        let e := cg.ce[pos]!
        if (e / 2) % 4 == 0 then
          let d := e / 8
          while color.size ≤ d do color := color.push 0
          if color.get! d == 0 then todo := some d
      else
        stack := stack.pop
        color := color.set! c 2
        cg := { cg with order := cg.order.push c }
  -- one pass in post-order: every child's budget is in its key
  let m := cg.keys.size
  let mut fn : Array Nat := Array.replicate m 0
  let mut f0 : Array Nat := Array.replicate m 0
  let mut fv : Array Nat := Array.replicate m 0
  for c in cg.order do
    let mut sn := 0
    let mut s0 := 0
    let mut sv := 0
    for k in [cg.coff[c]!:cg.cend[c]!] do
      let e := cg.ce[k]!
      let e1 := e % 2
      let kd := (e / 2) % 4
      if kd == 0 then
        let d := e / 8
        sn := sn + fn[d]!
        if e1 == 0 then s0 := s0 + f0[d]!
        sv := sv + fv[d]!
      else
        sn := sn + 1
        if e1 == 0 then s0 := s0 + 1
        if kd == 2 then sv := sv + 1
    fn := fn.set! c sn
    f0 := f0.set! c s0
    fv := fv.set! c sv
  return ({ n := fn.getD root 0, n0 := f0.getD root 0, v := fv.getD root 0 }, { g, T, sa, sb }, m, true)

end Jank.R8.Nrepl
