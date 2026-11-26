import Replica.Tree

/-!
# A tree run: the queue, the judgments, the nodes, the timelines (main.zig:4006-4390)

A model system runs the timelines (`Sys`, see Tree.lean's header). Each timeline's run is what
the worker does (main.zig:3425-3750): its strategy may give it another seed at its `branch`
(3474-3486), its tape's header says the seed it ran with and `chain` = its plan's path
(3754-3780). A node is made for each return (6440-6531): a holder of a timeline of the
generation being judged (the timeline's own running state, `registry.take`), or a replay along
the parent's recorded path with the parent's planned seed (`Recorded.load(arena, tapes,
making.parent.index, making.parent.seed, ...)`, 6612 and 7489-7492: `assert(parent_recorded.seed
== parent.seed)`; node.zig:30-39, 83-104, 165-180).

Not exact: a judgment is made at once (the Zig starts queued filler while its nodes are made:
the returns' numbers are the same while the pipeline's filler is queued); the host's memory
(nodes skipped past half of it), the bandit, novelty steering, horizons, holders' spacing and
targeted runs are left out; `branch_seed` and the trace hash are a stand-in mix, not Wyhash.
-/

namespace Replica.Tree

open Determinismo

/-- The model system: `len` events at 10, 20, ... µs, each below `kinds`, drawn at its pull. -/
structure Sys where
  len : Nat := 6
  kinds : Nat := 3
  pulls : List Nat := [1, 2, 3, 4, 5]
  soughtValue : Nat := 0
  deriving Inhabited, Repr

def mix (a b : Nat) : Nat := ((a * 6364136223846793005 + b * 1442695040888963407 + 1013904223) % 18446744073709551616) / 536870912

/-- A timeline's seeds over time: the seed in effect at each moment. -/
abbrev Sched := Nat → Nat

def events (sys : Sys) (seedAt : Sched) : List Nat := Id.run do
  let mut out := []
  let mut prev := 0
  for k in [1:sys.len + 1] do
    let v := if sys.pulls.contains k then mix (seedAt (10 * k)) k % sys.kinds else (prev + 1) % sys.kinds
    out := out ++ [v]
    prev := v
  return out

/-- The schedule a recorded path replays (node.zig:165-180, explore --tape): each ancestor's
recorded seed up to its segment's moment, then the timeline's own. -/
def pathSched (path : List Segment) (own : Nat) : Sched := fun t =>
  match path.find? (fun s => t ≤ s.vtime) with
  | some s => s.seed
  | none => own

/-- The behaviors a timeline's events leave (events.zig behavior_note, scored_note), in the
order the table keeps them. -/
def behaviorsOf (sys : Sys) (evs : List Nat) : List Behavior := Id.run do
  let mut out : Array Behavior := #[]
  let mut k := 0
  for v in evs do
    k := k + 1
    let t := 10 * k
    -- Three events of the timeline at 10k, 10k + 2 and 10k + 4 µs: an output line, the
    -- assertion, the optimize call (one behavior an event, as behavior_note keeps them).
    if !(out.any (·.hash == 1 + v)) then
      out := out.push { hash := 1 + v, vtime := t, label := s!"line {v}" }
    if v == sys.soughtValue && !(out.any (·.hash == 1000)) then
      out := out.push { hash := 1000, vtime := t + 2, label := "sometimes \"zero\": true", sought := true }
    match out.findIdx? (·.hash == 2000) with
    | some i =>
      if (out[i]!.score.getD 0) < (Int.ofNat v) then out := out.set! i { out[i]! with score := some (Int.ofNat v), vtime := t + 4 }
    | none => out := out.push { hash := 2000, vtime := t + 4, label := "optimize \"top\"", score := some (Int.ofNat v) }
  return out.toList

def traceHash (evs : List Nat) : Nat := evs.foldl (fun h v => mix h (v + 1)) 17

def lastPullOf (sys : Sys) : Nat := 10 * ((sys.pulls.filter (· ≤ sys.len)).foldl max 0)

def endOf (sys : Sys) : Nat := 10 * sys.len + 5

/-- A strategy plugin: what it decides (PLUGINS.md's `branch` and `returns`). -/
structure Strat where
  /-- Gives timelines a seed at `branch`: always this one (plugins/python/same_seed.py), or
  drawn among none and it when `sometimes`. -/
  seed : Option Nat := none
  sometimes : Bool := false
  /-- Answers `returns` with moments of its own. -/
  returns : Bool := false
  /-- `"decides": true`: no holders (main.zig:4024-4028). -/
  decides : Bool := false
  deriving Inhabited, Repr

structure Config where
  label : String
  sys : Sys := {}
  size : Nat := 4
  children : Nat := 1
  pipeline : Nat := 1
  total : Nat := 8
  jobs : Nat := 1
  archive : Bool := true
  /-- `--return-offsets`, scaled: the default's 0, 0, 0, 1 s, 5 s, 30 s as 0, 0, 0, 7, 15, 33 µs
  (odd: two places, 2 µs apart or more and even, never meet by an offset). -/
  offsets : List Nat := [0, 0, 0, 7, 15, 33]
  strategy : Option Strat := none
  /-- The run's seed menu (the world decides among them). -/
  bases : List Nat := [7, 11, 23, 42]
  /-- The judgment's draws from the generation's seed (main.zig:6386: `generation_seed`), not the
  search's: two runs judging the same generation draw the same. -/
  seededJudgment : Bool := false
  /-- Round 6: main.zig as at a7fe05d (`plan_adopt_ran`, 6399-6410, 6490: a judged timeline's
  plan takes the seed it ran with) unless a theorem about 3939448 says so. -/
  ver : Ver := .va7fe05d
  deriving Inhabited

def branchSeed (base index : Nat) : Nat := mix (base * 1000003 + 77) (index + 1)

/-- A timeline as it ran. -/
structure Ran where
  planned : Planned
  /-- The seed it ran with (its strategy's at `branch`, else its plan's). -/
  seed : Nat
  /-- Where it started (0: the setup snapshot). -/
  start : Nat
  sched : Sched
  evs : List Nat
  summary : Summary
  /-- Its tape: the seed in its header, its chain (its plan's path). -/
  tapeSeed : Nat
  tapeChain : List Segment

instance : Inhabited Ran := ⟨{ planned := default, seed := 0, start := 0, sched := fun _ => 0, evs := [], summary := default, tapeSeed := 0, tapeChain := [] }⟩

/-- A node made for a return: how, and the state (schedule up to its moment). -/
structure Made where
  back : TreeReturn
  parent : Nat
  holder : Bool
  sched : Sched
  moment : Nat

/-- A judgment, for the properties. -/
structure Judged where
  generation : Nat
  members : List Nat
  candidates : List Candidate
  /-- The returns as the explorer made them (after returns_earlier). -/
  returns : List TreeReturn
  /-- Before returns_earlier moved them. -/
  returnsAt : List TreeReturn
  made : List Made
  fillFresh : Bool
  /-- Repeats among the members (their trace equal to an earlier one's). -/
  repeats : List Nat
  cellsAfter : Array Cell
  judgedSize : Nat
  planned : Nat
  fresh : Nat
  /-- Behaviors new this generation (`reached`'s keys) and the frontier's doom draw. -/
  reachedKeys : List Nat
  doomFrontier : Bool
  strategyAnswer : Option Answer

structure RS where
  decisions : Decisions := {}
  log : Array String := #[]
  cfg : Config := default
  base : Nat := 0
  size : Nat := 4
  st : TreeState := {}
  queue : Array Planned := #[]
  head : Nat := 0
  fillerStart : Nat := 0
  nextIndex : Nat := 0
  running : Array Planned := #[]
  batch : Array Ran := #[]
  ran : Array Ran := #[]
  /-- Each planned index's start: its node's schedule and moment. -/
  starts : List (Nat × (Sched × Nat)) := []
  judged : Array Judged := #[]
  deriving Inhabited

instance : Chaotic RS where
  decisions s := s.decisions
  setDecisions s d := { s with decisions := d }

abbrev RM := EStateM Stop RS

def say' (line : String) : RM Unit := modify fun s => { s with log := s.log.push line }

/-- main.zig:4463-4481: a planned timeline before the filler; filler at the end. -/
def queuePlan (p : Planned) : RM Unit := modify fun s =>
  let at_ := max s.fillerStart s.head
  { s with queue := s.queue.insertIdxIfInBounds at_ p, fillerStart := at_ + 1 }

def queueFill (p : Planned) : RM Unit := modify fun s => { s with queue := s.queue.push p }

/-- A JM computation (the judgment's draws) inside the run. -/
def liftJ {α : Type} (x : JM α) : RM α := do
  let s ← get
  match x.run { decisions := s.decisions } with
  | .ok a j => set { s with decisions := j.decisions, log := s.log ++ j.log }; pure a
  | .error e j => set { s with decisions := j.decisions, log := s.log ++ j.log }; throw e

/-- The worker: a timeline started from its plan (3425-3750). -/
def runTimeline (p : Planned) : RM Ran := do
  let s ← get
  let cfg := s.cfg
  let (node, start) := (lookup s.starts p.index).getD ((fun _ => p.seed), 0)
  -- Its strategy hears it start, and may give it another seed (3474-3486).
  let mut seed := p.seed
  if let some st := cfg.strategy then
    if let some fixed := st.seed then
      if st.sometimes then
        if (← below "strategy.branch_seed" 2) == 1 then seed := fixed
      else seed := fixed
  let sched : Sched := fun t => if t ≤ start then node t else seed
  let evs := events cfg.sys sched
  let summary : Summary := {
    index := p.index, startNs := start, endNs := endOf cfg.sys,
    behaviors := behaviorsOf cfg.sys evs, traceHash := traceHash evs, lastPull := lastPullOf cfg.sys }
  return { planned := p, seed, start, sched, evs, summary, tapeSeed := seed, tapeChain := p.path }

/-- A strategy's `returns` reply, drawn (PLUGINS.md's protocol): up to two moments, each of a
candidate (any moment of its span, past its last pull too) or of an offered archive cell, its
branches (the default, one, or the whole budget), and the fill. -/
def strategyAnswer (st : Strat) (chosen : List Candidate) (offers : List Offer) (children budget : Nat) : RM (Option Answer) := do
  if !st.returns then return none
  let count ← below "strategy.returns" 3
  let mut asked : List SReturn := []
  for _ in [0:count] do
    let fromArchive ← if offers.length > 0 then do pure ((← below "strategy.from_archive" 2) == 1) else pure false
    if fromArchive then
      let o := offers[(← below "strategy.offer" offers.length)]!
      asked := asked ++ [{ branch := o.branch, vtime := o.vtime }]
    else if chosen.length > 0 then
      let c := chosen[(← below "strategy.candidate" chosen.length)]!
      let s := c.summary
      let span := s.endNs - s.startNs
      let v := s.startNs + 1 + (← below "strategy.moment" (max 1 (span - 1)))
      asked := asked ++ [{ branch := s.index, vtime := v }]
    let b := [none, some 1, some budget][(← below "strategy.branches" 3)]!
    asked := match asked.reverse with
      | [] => []
      | r :: rs => ({ r with branches := b } :: rs).reverse
  let fresh := (← below "strategy.fill" 2) == 1
  let a := answerParse asked fresh children budget
  -- strategies.zig:286-288: the first plugin that names returns gives them (and its fill).
  return if a.returns.isEmpty then none else some a

/-- main.zig:6318-6681: a judgment of the batch's complete generations, its nodes made, its
branches and fresh timelines planned. -/
def judge : RM Unit := do
  let s ← get
  let cfg := s.cfg
  let judgedN := judgeCount s.batch.size s.size
  let judgedSize := max judgedN s.size
  let batchDone := s.batch.toList.take judgedN
  let done := sortBy (fun (a b : Ran) => a.planned.index < b.planned.index) batchDone
  let plan := done.map (·.planned)
  let summaries := done.map (·.summary)
  let generation := s.st.generation
  let draw {α : Type} (x : JM α) : RM α :=
    if cfg.seededJudgment then liftJ (unrecorded (mix s.base (generation + 1)) x) else liftJ x
  -- What each new behavior was reached by (6358-6364).
  let mut reached : List (Nat × Nat) := []
  for sm in summaries do
    for b in sm.behaviors do
      if s.st.seen.contains b.hash then continue
      reached := bump reached b.hash
  let mut st := s.st
  for sm in summaries do st := archiveAdd st plan sm
  let doomShift ← draw (below "doom.weight" 7)
  let doomFrontier ← draw (below "doom.frontier" 2)
  st := { st with doomWeight := 2 ^ doomShift, doomFrontier := doomFrontier == 1 }
  let mut candidates : List Candidate := []
  let mut repeats : List Nat := []
  for sm in summaries do
    if st.traces.contains sm.traceHash then
      repeats := repeats ++ [sm.index]
      continue
    st := { st with traces := st.traces ++ [sm.traceHash] }
    let c := frontierChoose st sm reached
    if c.novel > 0 then
      if let some planned := lookup st.planned sm.index then
        if let some h := planned.cell then
          if let some i := st.cells.findIdx? (·.hash == h) then
            st := { st with cells := st.cells.modify i fun cell => { cell with paid := cell.paid + 1 } }
    candidates := candidates ++ [c]
  st := { st with seen := st.seen ++ (reached.map (·.1)).filter (fun h => !st.seen.contains h) }
  let chosen := sortBy candidateBefore candidates
  st ← draw (memoryForget st)
  -- A plugin is offered the archive's best cells (6418-6420).
  let mut offers : List Offer := []
  let mut answer : Option Answer := none
  if let some strat := cfg.strategy then
    if strat.returns && st.archive && st.cells.size > 0 then
      let ranked ← draw (archiveRanked st)
      let count := min ranked.length (2 * nodes judgedSize cfg.children)
      let cells := st.cells
      offers := ranked.take count |>.filterMap fun h => (cells.find? (·.hash == h)).map fun c =>
        ({ hash := h, branch := c.place.branch, vtime := c.place.vtime } : Offer)
    answer ← strategyAnswer strat chosen offers cfg.children judgedSize
  let (st1, returns0, fillFresh) ← draw (treeReturns st answer chosen judgedSize cfg.children offers)
  st := st1
  let mut returns := returns0
  if st.archive && !fillFresh then
    let (st2, r) ← draw (archiveReturns st judgedSize cfg.children returns)
    st := st2
    returns := r
  let returnsAt := returns
  returns ← draw (returnsEarlier cfg.offsets returns)
  for sm in summaries do
    for b in sm.behaviors do st := { st with visits := bump st.visits b.hash }
  -- The nodes (6440-6531): the parent in this generation's plan, else an earlier one's.
  let mut made : List Made := []
  for back in returns do
    let inBatch := done.find? (·.planned.index == back.branch)
    let earlierPlan := lookup st.planned back.branch
    let parentRan? := inBatch <|> (s.ran.toList.find? (·.planned.index == back.branch))
    let some parentRan := parentRan? | continue
    let parent := match inBatch with | some r => r.planned | none => earlierPlan.getD parentRan.planned
    -- a7fe05d: the plan has the seed its timeline ran with (CE23's fix).
    let parent := if cfg.ver.sinceA7 then { parent with seed := parentRan.seed } else parent
    if inBatch.isNone && earlierPlan.isNone then continue
    let holding := match cfg.strategy with | some strat => !strat.decides | none => true
    let holder ← if holding && inBatch.isSome then do pure ((← below "node.holder" 2) == 0) else pure false
    let m := back.vtime
    let nodeSched : Sched :=
      if holder then parentRan.sched
      else
        -- A replay: from the parent's start node (this generation's) or along its recorded path
        -- from the setup (an earlier generation's), the parent's own part with its planned seed.
        let startPart : Sched := if inBatch.isSome && parent.path.length > 0 then parentRan.sched else pathSched parent.path parent.seed
        fun t => if t ≤ parentRan.start then startPart t else parent.seed
    made := made ++ [{ back, parent := back.branch, holder, sched := nodeSched, moment := m }]
  -- judge_plan_one (6263-6310) for each node in order, then the fresh fill (6643-6658).
  let mut planned := 0
  for mk in made do
    let parent := match done.find? (·.planned.index == mk.parent) with
      | some r => if cfg.ver.sinceA7 then { r.planned with seed := r.seed } else r.planned
      | none =>
        let p := (lookup st.planned mk.parent).getD default
        if cfg.ver.sinceA7 then
          match s.ran.toList.find? (fun (r : Ran) => r.planned.index == mk.parent) with
          | some r => { p with seed := r.seed }
          | none => p
        else p
    let path := parent.path ++ [{ branch := parent.index, seed := parent.seed, vtime := mk.moment }]
    for _ in [0:(mk.back.branches.getD cfg.children)] do
      let s ← get
      if s.nextIndex ≥ cfg.total then break
      let p : Planned := { index := s.nextIndex, seed := branchSeed s.base s.nextIndex, path, generation := generation + 1,
                           cell := mk.back.cell, why := mk.back.why }
      queuePlan p
      modify fun s => { s with nextIndex := s.nextIndex + 1, starts := s.starts ++ [(p.index, (mk.sched, mk.moment))] }
      planned := planned + 1
  let mut fresh := 0
  while planned < done.length do
    let s ← get
    if s.nextIndex ≥ cfg.total then break
    queuePlan { index := s.nextIndex, seed := branchSeed s.base s.nextIndex, generation := generation + 1, why := "From the setup snapshot" }
    modify fun s => { s with nextIndex := s.nextIndex + 1 }
    planned := planned + 1
    fresh := fresh + 1
  let j : Judged := { generation, members := done.map (·.planned.index), candidates := chosen, returns, returnsAt,
                      made, fillFresh, repeats, cellsAfter := st.cells, judgedSize, planned, fresh,
                      reachedKeys := reached.map (·.1), doomFrontier := st.doomFrontier, strategyAnswer := answer }
  modify fun s => { s with st := { st with generation := generation + 1 }, batch := s.batch.extract judgedN s.batch.size,
                           judged := s.judged.push j }

/-- main.zig:4006-4390: the run. -/
def run : RM Unit := do
  let cfg := (← get).cfg
  let base := cfg.bases[(← below "world.base" cfg.bases.length)]!
  let size := cfg.size
  modify fun s => { s with base, size, st := { archive := cfg.archive } }
  for planned in [0:cfg.pipeline * size] do
    let s ← get
    if s.nextIndex ≥ cfg.total then break
    let p : Planned := { index := s.nextIndex, seed := branchSeed base s.nextIndex }
    if planned < size then queuePlan p else queueFill p
    modify fun s => { s with nextIndex := s.nextIndex + 1 }
  let mut steps := 0
  while steps < 10000 do
    steps := steps + 1
    let s ← get
    if s.batch.size ≥ s.size then
      judge
      continue
    if s.running.size < cfg.jobs && s.head < s.queue.size then
      let p := s.queue[s.head]!
      set { s with head := s.head + 1, running := s.running.push p }
      continue
    if s.running.size > 0 then
      let i ← if s.running.size == 1 then pure 0 else below "world.finishes" s.running.size
      let p := s.running[i]!
      let r ← runTimeline p
      modify fun s => { s with running := s.running.eraseIdxIfInBounds i, batch := s.batch.push r, ran := s.ran.push r }
      continue
    if s.batch.size > 0 && s.nextIndex < cfg.total then
      judge
      if (← get).head < (← get).queue.size then continue
    break

def runOf (cfg : Config) (source : Source) : Except Stop RS × RS :=
  match run.run { decisions := { source }, cfg } with
  | .ok _ s => (.ok s, s)
  | .error e s => (.error e, s)

end Replica.Tree
