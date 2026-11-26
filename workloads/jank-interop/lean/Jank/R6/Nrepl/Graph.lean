import Jank.R6.Nrepl.StateEq

/-!
# Round 6, nREPL: World T as a state graph, and exact counts of its preemption-bounded timelines

## Why

Rounds 3–5 walked World T's timelines one by one (`censusRun`, R5's `walk`). Two schedules that
reach the same state run the rest twice; a world whose steps commute (a client's step and the other
connection's step) has astronomically many timelines but few states. T7 (estimated at ≈3.2·10¹¹
timelines at ≤1 preemption by round 4; in fact 1.25·10⁸¹, counted below) and T3/T9 (two clients)
stopped there.

## What

1. `build`: every process state reachable from a scenario's initial state under ANY schedule (the
   sdk's `interleave`: any live thread may step next), states merged only when equal (`PKey`, exact
   structural equality, StateEq.lean). For each state and each live thread, the step is run under
   every value of the decisions it draws itself (`net.read.split`, `net.read.len`,
   `net.read.eintr`), enumerated with the sdk's own `nextPath`. Each run is one scheduler
   iteration exactly as `interleavePB`'s loop body does it after choosing the thread (the step, then
   the thread's locals set or removed), on the same `tProg`.
2. `count`: the number of timelines of round 3's `interleavePB` at ≤ b preemptions, computed on the
   graph by dynamic programming over (state, the scheduler's `cur`, its `blocked` set, the budget
   left): the scheduler's choice rule is copied from ThreadSearch.lean (round robin after a block or
   end; `thread.preempt` with `others.length + 1` options when the running thread is ready, another
   is ready and budget is left). A timeline is a leaf of the decision tree: the count is what a
   complete depth-first walk (`nextPath` from the all-zero path) would run. Violations are counted
   per property, as each timeline's first one (the judge, the deadlock rule and the model bound as
   `runTWith` applies them). It also counts the timelines whose `net.read.eintr` draws are all 0
   (round 5's `whole0` walk), and the longest timeline's loop iterations and decisions (to check
   the 6,000-round and 100,000-decision bounds are never reached).

Soundness rests on: `PKey` equality is the states' identity (derived `BEq`); a step's result is a
function of `PKey`, the thread index and the values of its own decisions (Threads.lean reads only
memory and threads; `Process.note` only appends to the log; Theorems.lean `eintr_draw_unused`
for the one draw whose value is unused); the DP's choice rule is
`interleavePB`'s. The last is checked by reproducing rounds 3–5's complete walk counts exactly
(results/r6-nrepl-validate.txt: 17 timeline counts and 4 violation counts, T1–T10 and T7).
-/

namespace Jank.R6.Nrepl

open Determinismo Jank.R3.Nrepl Jank.NreplServer Jank.Analyzer

/-- One iteration of `interleavePB`'s loop after it chose thread `t` (ThreadSearch.lean 50–60). -/
def iterStep (t : Nat) (locals : TTh) : ProcessM TMem TTh (StepResult TTh) := do
  let r ← tProg.step t locals
  match r with
  | .ran l => modify fun p => { p with threads := p.threads.set! t (some l), steps := p.steps + 1 }
  | .blocked => pure ()
  | .done => modify fun p => { p with threads := p.threads.set! t none, steps := p.steps + 1 }
  pure r

inductive Res where
  | ran
  | blocked
  | done
  /-- The step threw: a violation, or `.limit`/`.nodeDown` (`none`: an end, not a failure). -/
  | stop (v : Option (String × String))
  deriving Inhabited, BEq

def Res.isSome : Res → Bool
  | .stop (some _) => true
  | _ => false

/-- One value sequence of a step's own decisions, and where it leads. -/
structure Branch where
  /-- The step's own decisions taken (names, options, values). -/
  taken : Array Taken
  res : Res
  /-- The state after it (for `.stop`, the state at the throw). -/
  succ : Nat
  deriving Inhabited

def Branch.eintr1 (b : Branch) : Bool :=
  b.taken.any fun t => t.name == "net.read.eintr" && t.value != 0

structure G where
  keys : Array PKey := #[]
  index : Std.HashMap PKey Nat := {}
  /-- Per state: each live thread with the branches of its step. -/
  edges : Array (Array (Nat × Array Branch)) := #[]
  /-- Per state with no live thread: the judge's verdict (`runTWith`'s body after `interleave`). -/
  final : Array (Option (Option (String × String))) := #[]
  /-- Blocked steps whose state changed (expected none: a blocked step is a no-op). -/
  blockedMoves : Nat := 0
  /-- Step runs. -/
  runs : Nat := 0
  /-- `check`: (state, thread) pairs and final states checked with the logs in the other order. -/
  checked : Nat := 0
  /-- … whose steps (results, decisions, canonical successors) or verdicts' presence differ. -/
  checkFails : Nat := 0
  /-- … final states whose first-reported violation differs (presence equal). -/
  checkFirstDiffers : Nat := 0
  deriving Inhabited

def G.intern (g : G) (k : PKey) : G × Nat × Bool :=
  match g.index.get? k with
  | some i => (g, i, false)
  | none =>
    let i := g.keys.size
    ({ g with keys := g.keys.push k, index := g.index.insert k i, edges := g.edges.push #[],
               final := g.final.push none }, i, true)

def procOf (k : PKey) (path : Array Nat) : Process TMem TTh :=
  { memory := k.mem, threads := k.threads, decisions := { source := Source.path path, limit := 100000 } }

def liveOf (k : PKey) : List Nat :=
  (List.range k.threads.size).filter fun i => (k.threads.getD i none).isSome

/-- Every value sequence of thread `t`'s step decisions, in `nextPath` order. -/
partial def branchesOf (k : PKey) (t : Nat) (locals : TTh) : Array (Array Taken × Res × PKey) := Id.run do
  let mut out := #[]
  let mut path : Array Nat := #[]
  for _ in [0:100000] do
    let (taken, res, q) := match (iterStep t locals).run (procOf k path) with
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

/-- Round 3's `tJudge` (Threads.lean) without its output property ("eval output reaches its
client"), for the scenarios run on jank's real, unlocked capture (`T3u`, `T9u`): there R125 (stdout
capture is process-wide) breaks the output property on most timelines and, as the first violation,
would hide any other. Everything else is `tJudge`'s, in its order. -/
def tJudgeNoOut (aside : Aside) (scripts : List (List TReq)) (m : TMem) : Option (String × String) := Id.run do
  if let some c := m.crashed then return some ("the process stays up", c)
  let specs := scripts.zipIdx.flatMap fun (sc, cid) => tSpecOf aside.variant cid sc
  for s in m.sent do
    let rs := tRepliesOf m s
    if let some sess := s.session then
      for r in rs do
        if strField r "session" != some sess then
          return some ("every reply carries the request's id and session", s!"{s.id}: {JVal.render r} lacks session {sess}")
    match rs.findIdx? tIsDone with
    | none => return some ("a request's replies end with done", s!"{s.id}: no done among {rs.length} replies")
    | some i => if i + 1 != rs.length then return some ("a request's replies end with done", s!"{s.id}: replies after done")
    match s.req with
    | .eval code _ =>
      match specs.lookup s.id with
      | some sp =>
        let q : SReq := .eval code (some "user")
        let ans : JankAns := { replies := rs, handlerError := none }
        let out := rs.flatMap fun r => match Jank.NreplServer.jget r (JVal.s "out") with | .str b => b | _ => []
        match judgeEval .loadString { aside with blankOut := true } q ans { sp with out } with
        | some (p, d) => return some (p, s!"{s.id}: {d}")
        | none => pure ()
      | none => pure ()
    | _ => pure ()
  return none

/-- The verdict `runTWith` gives a process with no live thread (`noOut`: R125's two properties,
output and fd 1, set aside). -/
def judgeEnd (s : TScenario) (m : TMem) (noOut : Bool := false) : Option (String × String) :=
  if noOut then tJudgeNoOut s.aside s.scripts m else
  match tJudge s.aside s.scripts m with
  | some v => some v
  | none =>
    match m.fd 1 with
    | some .terminal => none
    | d => some ("stdout is restored after every eval", s!"fd 1 is left on {reprStr d}")

/-! ## The per-client logs, canonically ordered

`TMem` keeps six process-wide logs in the order events happened across clients: `replies` (what the
clients decoded, pushed by `tClientRead`), `sent` (pushed by a client's `.send`), `evals` (pushed by a
connection's `.evalReplies`), `handlerErrors`, `connEnded` and `hung` (pushed by a connection). Every
reader takes one client's part of a log, in its order: `tClientStep .wait` and `tRepliesOf` filter
`replies` by cid and id; `tJudge` finds an eval by cid and id, a handler error by cid; `tStuck` and
`tConnStep` test membership by cid. Only `tJudge`'s loop over `sent` follows the cross-client order,
and only to pick which of several violations a timeline reports first; whether it has one does not
depend on it. So two states that differ only in how the clients' entries are interleaved in these
logs have the same futures and the same verdicts (up to that choice of first violation).

`canonMem` orders each log by client (stable: each client's entries keep their order). The graph built
with it (`build … canon := true`) merges such states. The argument above is from the code; `build`
also checks it at every state it reaches (`check := true`): each step is run from the state with its
logs ordered the other way (clients in decreasing order), and the result, canonically ordered, must be
the same, for every thread and every value of the step's decisions; and the judge must find a
violation in both orders or in neither. -/

/-- Client `c`'s part of a log (`c = n`: entries of any client numbered `n` or more). -/
def bucket {α : Type} (n : Nat) (key : α → Nat) (c : Nat) (x : α) : Bool :=
  if c == n then decide (key x ≥ n) else key x == c

def cidsOf (n : Nat) (desc : Bool) : List Nat :=
  if desc then (List.range (n + 1)).reverse else List.range (n + 1)

/-- A log ordered by client: each client's entries in their order, clients in increasing order
(`desc`: decreasing). -/
def byCid {α : Type} (n : Nat) (key : α → Nat) (desc : Bool) (xs : List α) : List α :=
  (cidsOf n desc).flatMap fun c => xs.filter (bucket n key c)

def orderMem (desc : Bool) (m : TMem) : TMem :=
  let n := m.nClients
  { m with
    replies := (byCid n (·.1) desc m.replies.toList).toArray
    sent := (byCid n (·.cid) desc m.sent.toList).toArray
    evals := (byCid n (·.cid) desc m.evals.toList).toArray
    handlerErrors := byCid n (·.1) desc m.handlerErrors
    connEnded := byCid n id desc m.connEnded
    hung := byCid n (·.1) desc m.hung }

def canonMem (m : TMem) : TMem := orderMem false m
def canonKey (k : PKey) : PKey := { k with mem := canonMem k.mem }
def altKey (k : PKey) : PKey := { k with mem := orderMem true k.mem }

/-- Builds the graph of every state reachable under any schedule (breadth first), up to `maxStates`
states or `deadlineMs`. Returns the graph and whether it is complete. -/
def build (s : TScenario) (maxStates : Nat) (deadlineMs : Nat := 0) (canon check : Bool := false)
    (noOut : Bool := false) : IO (G × Bool) := do
  let t0 ← IO.monoMsNow
  let p0 := tInitial s.cfg s.scripts
  let norm (k : PKey) : PKey := if canon then canonKey k else k
  let (g, _, _) := ({} : G).intern (norm (PKey.of p0))
  let mut g := g
  let mut i := 0
  while i < g.keys.size do
    if g.keys.size > maxStates then return (g, false)
    if deadlineMs > 0 && i % 256 == 0 && (← IO.monoMsNow) - t0 > deadlineMs then return (g, false)
    if i > 0 && i % 100000 == 0 then
      IO.println s!"    … {i} states expanded, {g.keys.size} found ({(← IO.monoMsNow) - t0} ms)"
      (← IO.getStdout).flush
    let k := g.keys[i]!
    let live := liveOf k
    if live.isEmpty then
      let v := judgeEnd s k.mem noOut
      g := { g with final := g.final.set! i (some v) }
      if check then
        let v' := judgeEnd s (altKey k).mem noOut
        g := { g with checked := g.checked + 1 }
        if v.isSome != v'.isSome then g := { g with checkFails := g.checkFails + 1 }
        else if (v.map (·.1)) != (v'.map (·.1)) then g := { g with checkFirstDiffers := g.checkFirstDiffers + 1 }
    else
      let mut es : Array (Nat × Array Branch) := #[]
      for t in live do
        let some locals := k.threads.getD t none | continue
        let mut bs : Array Branch := #[]
        let brs := branchesOf k t locals
        if check then
          let ka := altKey k
          let some la := ka.threads.getD t none | continue
          let brs' := branchesOf ka t la
          g := { g with checked := g.checked + 1 }
          let same := brs.size == brs'.size && (brs.zip brs').all fun ((ta, ra, qa), (tb, rb, qb)) =>
            ta.map (·.value) == tb.map (·.value) && ra.isSome == rb.isSome &&
            (match ra, rb with
              | .stop _, .stop _ => true
              | x, y => x == y) && canonKey qa == canonKey qb
          if !same then g := { g with checkFails := g.checkFails + 1 }
        for (taken, res, q) in brs do
          let (g', j, _) := g.intern (norm q)
          g := { g' with runs := g'.runs + 1 }
          if res == .blocked && j != i then g := { g with blockedMoves := g.blockedMoves + 1 }
          bs := bs.push { taken, res, succ := j }
        es := es.push (t, bs)
      g := { g with edges := g.edges.set! i es }
    i := i + 1
  return (g, true)

/-- Every state where a step draws `net.read.eintr` with EINTR off: do the branches that differ only
in that draw lead to the same state with the same result? (Round 5's nREPLA5-4, checked at every
reachable state.) Returns (draw sites, branch groups checked, groups that differ). -/
def eintrCheck (s : TScenario) (g : G) : Nat × Nat × Nat := Id.run do
  if s.cfg.eintr then return (0, 0, 0)
  let mut sites := 0
  let mut groups := 0
  let mut bad := 0
  for i in [0:g.keys.size] do
    for (_, bs) in g.edges.getD i #[] do
      if !(bs.any fun b => b.taken.any (·.name == "net.read.eintr")) then continue
      sites := sites + 1
      let norm (b : Branch) : List (String × Nat) :=
        b.taken.toList.filterMap fun t => if t.name == "net.read.eintr" then none else some (t.name, t.value)
      let keys := (bs.toList.map norm).eraseDups
      for key in keys do
        groups := groups + 1
        let grp := bs.toList.filter fun b => norm b == key
        match grp with
        | [] => pure ()
        | b :: rest =>
          if !(rest.all fun c => c.succ == b.succ && c.res == b.res) then bad := bad + 1
  return (sites, groups, bad)

/-! ## Counting preemption-bounded timelines -/

structure Sum where
  /-- Timelines. -/
  n : Nat := 0
  /-- Timelines whose `net.read.eintr` draws are all 0. -/
  n0 : Nat := 0
  /-- Per property: timelines whose first violation it is (all, eintr-0). -/
  viol : List (String × Nat × Nat) := []
  /-- One detail per property. -/
  ex : List (String × String) := []
  /-- Per final state (when kept): timelines ending there (all, eintr-0). -/
  finals : List (Nat × Nat × Nat) := []
  /-- The most loop iterations (step attempts) of a timeline from here. -/
  maxIt : Nat := 0
  /-- The most decisions of a timeline from here. -/
  maxDec : Nat := 0
  deriving Inhabited

def addAssoc3 (xs : List (α × Nat × Nat)) (k : α) (a b : Nat) [BEq α] : List (α × Nat × Nat) :=
  match xs.find? (·.1 == k) with
  | some _ => xs.map fun (k', x, y) => if k' == k then (k', x + a, y + b) else (k', x, y)
  | none => xs ++ [(k, a, b)]

/-- `acc` plus `c` (a child reached through `dec` more decisions, `keep0`: counted in n0). -/
def Sum.add (acc c : Sum) (keep0 : Bool) (dec : Nat) : Sum :=
  let k0 := if keep0 then 1 else 0
  { n := acc.n + c.n
    n0 := acc.n0 + c.n0 * k0
    viol := c.viol.foldl (fun xs (p, a, b) => addAssoc3 xs p a (b * k0)) acc.viol
    ex := c.ex.foldl (fun xs (p, d) => if (xs.lookup p).isSome then xs else xs ++ [(p, d)]) acc.ex
    finals := c.finals.foldl (fun xs (f, a, b) => addAssoc3 xs f a (b * k0)) acc.finals
    maxIt := max acc.maxIt (c.maxIt + 1)
    maxDec := max acc.maxDec (c.maxDec + dec) }

def leafSum (id : Nat) (v : Option (String × String)) (keepFinals : Bool) : Sum :=
  { n := 1, n0 := 1,
    viol := match v with | some (p, _) => [(p, 1, 1)] | none => []
    ex := match v with | some (p, d) => [(p, d)] | none => []
    finals := if keepFinals then [(id, 1, 1)] else [] }

abbrev SKey := Nat × Option Nat × List Nat × Nat × Option Nat

structure CState where
  memo : Std.HashMap SKey Sum := {}
  deriving Inhabited

def insertSorted (t : Nat) : List Nat → List Nat
  | [] => [t]
  | x :: xs => if t < x then t :: x :: xs else if t == x then x :: xs else x :: insertSorted t xs

/-- The timelines of `interleavePB` from state `i` with the scheduler's `cur`, `blocked` and budget
`left` (ThreadSearch.lean `interleavePB`). -/
partial def countFrom (s : TScenario) (g : G) (keepFinals : Bool) (i : Nat) (cur : Option Nat)
    (blocked : List Nat) (left : Nat) (cuts : Option Nat) : StateM CState Sum := do
  let key : SKey := (i, cur, blocked, left, cuts)
  if let some r := (← get).memo.get? key then return r
  let k := g.keys[i]!
  let live := liveOf k
  let r ← do
    if live.isEmpty then
      pure (leafSum i ((g.final.getD i none).getD none) keepFinals)
    else
      let ready := live.filter (!blocked.contains ·)
      if ready.isEmpty then
        let d := (tStuck (procOf k #[])).getD ""
        pure (leafSum i (some ("every request gets a done reply (no hang)", d)) keepFinals)
      else
        -- (thread, budget left after the choice, decisions the choice took)
        let choices : List (Nat × Nat × Nat) := match cur with
          | some c =>
            if ready.contains c then
              let others := ready.filter (· != c)
              if left > 0 && !others.isEmpty then
                (c, left, 1) :: others.map fun o => (o, left - 1, 1)
              else [(c, left, 0)]
            else [((ready.find? (· > c)).getD (ready.headD 0), left, 0)]
          | none => [(ready.headD 0, left, 0)]
        let es := g.edges[i]!
        let mut acc : Sum := {}
        for (t, left', d0) in choices do
          let bs := (es.find? (·.1 == t)).map (·.2) |>.getD #[]
          for b in bs do
            -- round 5's `cuts` walk: a timeline with more partial reads than `cuts` is not counted
            let partials := b.taken.foldl (fun n t => if t.name == "net.read.split" && t.value != 0 then n + 1 else n) 0
            let cuts' := cuts.map (· - partials)
            if let some c := cuts then
              if partials > c then continue
            let c ← match b.res with
              | .stop v => pure (leafSum b.succ v keepFinals)
              | .ran => countFrom s g keepFinals b.succ (some t) [] left' cuts'
              | .done => countFrom s g keepFinals b.succ (some t) [] left' cuts'
              | .blocked => countFrom s g keepFinals b.succ (some t) (insertSorted t blocked) left' cuts'
            acc := acc.add c (!b.eintr1) (d0 + b.taken.size)
        pure acc
  modify fun st => { st with memo := st.memo.insert key r }
  return r

/-- The timelines of `interleavePB` at ≤ `budget` preemptions from the initial state. -/
def count (s : TScenario) (g : G) (budget : Nat) (keepFinals : Bool) (cuts : Option Nat := none) : Sum × Nat :=
  let (r, st) := (countFrom s g keepFinals 0 none [] budget cuts).run {}
  (r, st.memo.size)

/-! ## Every schedule (no preemption bound) -/

structure Reach where
  states : Nat := 0
  finals : List Nat := []
  /-- Final states and their verdicts. -/
  finalViol : List (Nat × String × String) := []
  /-- Steps that threw a violation. -/
  stepViol : List (Nat × String × String) := []
  /-- States where every live thread's step only blocks (a deadlock under every scheduler). -/
  deadlocks : List Nat := []
  /-- A progress step (ran/done) that returns to its own state. -/
  selfLoops : Nat := 0
  /-- Longest chain of progress steps from the initial state (the graph is checked acyclic). -/
  longest : Nat := 0
  acyclic : Bool := true
  deriving Inhabited

/-- Longest progress path from each state, with a cycle check (iterative DFS, colors). -/
def longestPaths (g : G) : Array Nat × Bool := Id.run do
  let n := g.keys.size
  let mut color : Array UInt8 := Array.replicate n 0
  let mut len : Array Nat := Array.replicate n 0
  let mut acyclic := true
  let succs (i : Nat) : List Nat :=
    ((g.edges.getD i #[]).toList.flatMap fun (_, bs) => bs.toList.filterMap fun b =>
      match b.res with
      | .ran | .done => if b.succ != i then some b.succ else none
      | _ => none).eraseDups
  for root in [0:n] do
    if color[root]! != 0 then continue
    let mut stack : List (Nat × List Nat) := [(root, succs root)]
    color := color.set! root 1
    while !stack.isEmpty do
      match stack with
      | [] => break
      | (v, todo) :: rest =>
        match todo with
        | [] =>
          let l := (succs v).foldl (fun a w => max a (len[w]! + 1)) 0
          len := len.set! v l
          color := color.set! v 2
          stack := rest
        | w :: more =>
          stack := (v, more) :: rest
          if color[w]! == 1 then acyclic := false
          else if color[w]! == 0 then
            color := color.set! w 1
            stack := (w, succs w) :: stack
  return (len, acyclic)

def reach (g : G) : Reach := Id.run do
  let mut r : Reach := { states := g.keys.size }
  for i in [0:g.keys.size] do
    match g.final.getD i none with
    | some v =>
      r := { r with finals := r.finals ++ [i] }
      if let some (p, d) := v then r := { r with finalViol := r.finalViol ++ [(i, p, d)] }
    | none =>
      let es := g.edges.getD i #[]
      let mut allBlock := !es.isEmpty
      for (_, bs) in es do
        for b in bs do
          match b.res with
          | .stop (some (p, d)) => r := { r with stepViol := r.stepViol ++ [(i, p, d)] }
          | .blocked => pure ()
          | .ran | .done =>
            allBlock := false
            if b.succ == i then r := { r with selfLoops := r.selfLoops + 1 }
          | .stop none => allBlock := false
      if allBlock then r := { r with deadlocks := r.deadlocks ++ [i] }
  let (len, acyclic) := longestPaths g
  return { r with longest := len.getD 0 0, acyclic }

end Jank.R6.Nrepl
