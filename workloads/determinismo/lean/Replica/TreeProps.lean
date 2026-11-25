import Replica.TreeRun

/-!
# The tree's properties, each from the documentation (or a code comment where the docs say
nothing), checked over whole runs of `TreeRun.run`.
-/

namespace Replica.Tree

open Determinismo

structure TProp where
  name : String
  source : String
  check : Config → RS → Option String

def ranOf (s : RS) (i : Nat) : Option Ran := s.ran.toList.find? (·.planned.index == i)

def showPath (p : List Segment) : String :=
  String.intercalate " → " (p.map fun g => s!"#{g.branch}(seed {g.seed % 10000}…) to {g.vtime} µs")

/-- The events up to (and at) moment `m`: event k is at 10k µs. -/
def upTo (evs : List Nat) (m : Nat) : List Nat := evs.take (m / 10)

/-- README_AI.md: "replay any timeline exactly", "every timeline replays bit-identically";
docs/ANTITHESIS.md (Branching from interesting states): "every timeline's path in its record and
tape (it replays alone)"; PLUGINS.md (`branch`): "to give the branch another seed (...: its tape's
header says it, so its replay needs no plugin)". -/
def replaysFromTape : TProp :=
  { name := "every timeline replays alone from its tape"
    source := "README_AI.md (\"every timeline replays bit-identically\"); docs/ANTITHESIS.md, Branching (\"every timeline's path in its record and tape (it replays alone)\"); docs/PLUGINS.md, branch (\"its tape's header says it, so its replay needs no plugin\")"
    check := fun cfg s => Id.run do
      for r in s.ran do
        let replayed := events cfg.sys (pathSched r.tapeChain r.tapeSeed)
        if replayed != r.evs then
          return some s!"timeline {r.planned.index} ran {r.evs} (seed {r.seed % 10000}…, from {r.start} µs); its tape (header seed {r.tapeSeed % 10000}…, chain {showPath r.tapeChain}) replays {replayed}"
      return none }

/-- PLUGINS.md (returns): "Nodes replay their parents with their tapes, so what the strategy
decided there stays"; ARCHITECTURE.md §8: a node is "a snapshot at a moment of an earlier
timeline"; docs/AGENTS.md: the tree "returned to just after it". -/
def nodeIsParentsState : TProp :=
  { name := "a node made by a replay is its parent's state at the moment"
    source := "docs/PLUGINS.md, returns (\"Nodes replay their parents with their tapes, so what the strategy decided there stays\"); ARCHITECTURE.md glossary (Tree node: \"A snapshot at a moment of an earlier timeline\")"
    check := fun cfg s => Id.run do
      for j in s.judged do
        for mk in j.made do
          if mk.holder then continue
          let some parent := ranOf s mk.parent | continue
          let node := upTo (events cfg.sys mk.sched) mk.moment
          let had := upTo parent.evs mk.moment
          if node != had then
            return some s!"generation {j.generation}: a return to #{mk.parent} at {mk.moment} µs replayed {node}; #{mk.parent} had {had} there (it ran with seed {parent.seed % 10000}…, its plan's {parent.planned.seed % 10000}…)"
      return none }

/-- ARCHITECTURE.md §9: "Repeats: a timeline whose whole trace equals an earlier one's is never
returned to". The explorer's own returns (a strategy's are its call). -/
def noRepeatReturned : TProp :=
  { name := "a timeline whose trace equals an earlier one's is never returned to"
    source := "ARCHITECTURE.md §9 (\"Repeats: a timeline whose whole trace equals an earlier one's is never returned to\")"
    check := fun _ s => Id.run do
      let mut repeats : List Nat := []
      for j in s.judged do
        repeats := repeats ++ j.repeats
        for r in j.returns do
          if r.strategy then continue
          if repeats.contains r.branch then
            let src := if r.cell.isSome then "the archive" else "the frontier"
            return some s!"generation {j.generation}: {src} returned to #{r.branch} at {r.vtime} µs, a repeat (its trace equals an earlier timeline's)"
      return none }

/-- docs/AGENTS.md: "A generation of 16 is 4 fresh starts and 3 moments with 4 branches each";
main.zig:7077-7080 (archive_returns): "half the generation's moments ... go to the archive's most
promising cells: rare ... and seldom returned to ...; each return counts". -/
def distinctMoments : TProp :=
  { name := "a generation's returns are distinct moments, each counted as a return to its cell"
    source := "docs/AGENTS.md (\"A generation of 16 is 4 fresh starts and 3 moments with 4 branches each\"); main.zig:7077-7080 archive_returns (\"seldom returned to ... each return counts\")"
    check := fun _ s => Id.run do
      for j in s.judged do
        let own := j.returns.filter (!·.strategy)
        for i in [0:own.length] do
          for k in [i+1:own.length] do
            let a := own[i]!
            let b := own[k]!
            if a.branch == b.branch && a.vtime == b.vtime then
              let kind (r : TreeReturn) := if r.cell.isSome then "the archive's" else "the frontier's"
              return some s!"generation {j.generation}: {kind a} and {kind b} returns both to #{a.branch} at {a.vtime} µs, two nodes and their branches at one moment: \"{a.why}\" and \"{b.why}\""
      return none }

/-- PLUGINS.md (returns): "Choose up to K moments ...; with fewer, the explorer fills the rest
with its own rule, the frontier then the archive (other timelines than those chosen)". -/
def fillOtherTimelines : TProp :=
  { name := "the explorer's fill returns to other timelines than those a strategy chose"
    source := "docs/PLUGINS.md, returns (\"with fewer, the explorer fills the rest with its own rule, the frontier then the archive (other timelines than those chosen)\")"
    check := fun _ s => Id.run do
      for j in s.judged do
        let chosen := (j.returns.filter (·.strategy)).map (·.branch)
        for r in j.returns do
          if !r.strategy && chosen.contains r.branch then
            return some s!"generation {j.generation}: the strategy chose #{r.branch}; the explorer's fill returned there too at {r.vtime} µs ({r.why})"
      return none }

/-- main.zig:7279-7287 and ARCHITECTURE.md §9: "branch points come before a timeline's last
randomness pull (past it, every child would be the same timeline)"; the explorer's returns lie
inside their timeline's span. -/
def explorerInsideSpan : TProp :=
  { name := "the explorer's returns lie inside their timeline, before its last randomness pull"
    source := "ARCHITECTURE.md §9 (\"branch points come before a timeline's last randomness pull (past it, every child would be the same timeline)\"); main.zig:7279-7287"
    check := fun _ s => Id.run do
      for j in s.judged do
        for r in j.returns do
          if r.strategy then continue
          let some t := ranOf s r.branch | continue
          let sm := t.summary
          if !(sm.startNs < r.vtime && r.vtime < sm.endNs && (sm.cut || r.vtime < sm.lastPull)) then
            return some s!"generation {j.generation}: a return to #{r.branch} at {r.vtime} µs; it ran {sm.startNs}..{sm.endNs} µs, its last pull at {sm.lastPull} µs"
      return none }

def strategyBeforeLastPull : TProp :=
  { name := "every branch point (a strategy's too) comes before its timeline's last randomness pull"
    source := "ARCHITECTURE.md §9 (\"branch points come before a timeline's last randomness pull (past it, every child would be the same timeline)\")"
    check := fun _ s => Id.run do
      for j in s.judged do
        for r in j.returns do
          if !r.strategy then continue
          let some t := ranOf s r.branch | continue
          if !(t.summary.cut || r.vtime < t.summary.lastPull) then
            return some s!"generation {j.generation}: the strategy's return to #{r.branch} at {r.vtime} µs, past its last pull at {t.summary.lastPull} µs: its {r.branches.getD 1} children are the same timeline"
      return none }

/-- docs/AGENTS.md (a generation's shape) and PLUGINS.md (returns: "each return may take
`branches` of them, as many as it likes up to the budget ... `fill` says what the timelines it
left are"): a judgment plans as many timelines as it judged (the run's total aside), its returns'
branches within the budget. -/
def generationShape : TProp :=
  { name := "a judgment plans as many timelines as it judged, its returns within the budget"
    source := "docs/AGENTS.md (\"A generation of 16 is 4 fresh starts and 3 moments with 4 branches each\"); docs/PLUGINS.md, returns (\"as many as it likes up to the budget\")"
    check := fun cfg s => Id.run do
      for j in s.judged do
        let branches := j.made.foldl (fun t m => t + m.back.branches.getD cfg.children) 0
        if branches > j.judgedSize then
          return some s!"generation {j.generation}: returns of {branches} timelines past the budget of {j.judgedSize}"
        let explorer := j.made.filter (!·.back.strategy)
        let eb := explorer.foldl (fun t m => t + m.back.branches.getD cfg.children) 0
        if j.strategyAnswer.isNone && eb > nodes j.judgedSize cfg.children * cfg.children then
          return some s!"generation {j.generation}: the explorer's returns take {eb} timelines, past {nodes j.judgedSize cfg.children} moments of {cfg.children}"
        if j.planned < j.members.length && s.nextIndex < cfg.total then
          return some s!"generation {j.generation}: {j.members.length} judged, {j.planned} planned"
      return none }

/-- Usage of --no-prefer-sometimes (main.zig:119-122): "returns go first to just after a
`sometimes` or `reachable` assertion made true"; docs/AGENTS.md: "A `sometimes` or `reachable`
made true comes first (the frontier's moment...)". The frontier's choice of moment. -/
def soughtMomentFirst : TProp :=
  { name := "a timeline's frontier is a sometimes made true when it has an open new one"
    source := "docs/AGENTS.md (\"A `sometimes` or `reachable` made true comes first (the frontier's moment, a heavier archive cell)\"); main.zig usage, --no-prefer-sometimes"
    check := fun _ s => Id.run do
      for j in s.judged do
        for c in j.candidates do
          let sm := c.summary
          let roomEnd := if sm.cut then sm.endNs - ms else sm.endNs
          let openSought := sm.behaviors.any fun b => b.sought && b.vtime > sm.startNs && j.reachedKeys.contains b.hash &&
            b.vtime ≤ roomEnd && (sm.cut || b.vtime + after < sm.lastPull) && !(j.doomFrontier && doomedAt sm b.vtime)
          if openSought && !c.sought then
            return some s!"generation {j.generation}: #{sm.index}'s frontier is {c.label}, not its new sometimes"
      return none }

/-- The same, for where the return lands: "returns go first to just after a `sometimes` ...
made true" (usage), "the tree returns there" (AGENTS.md: "put one on each rare state worth
building on ..., and the tree returns there"). -/
def soughtReturnAfter : TProp :=
  { name := "a return for a sometimes made true lands after it"
    source := "docs/AGENTS.md (\"put one on each rare state worth building on (a failover, a retry path, a recovery), and the tree returns there\"); main.zig usage (\"returns go first to just after a `sometimes` or `reachable` assertion made true\")"
    check := fun _ s => Id.run do
      for j in s.judged do
        for r in j.returns do
          if r.strategy || r.cell.isSome then continue
          let some c := j.candidates.find? (·.summary.index == r.branch) | continue
          if !c.sought then continue
          let some m := c.moment | continue
          if r.vtime ≤ m then
            return some s!"generation {j.generation}: #{r.branch}'s sometimes was made true at {m} µs; its return landed at {r.vtime} µs ({r.why})"
      return none }

/-- docs/AGENTS.md: "`sdk.optimize(message, bucket, value, .maximize)`: each bucket keeps its best
state so far". The cell's best is the best open score any judged timeline reached in it. -/
def objectiveKeepsBest : TProp :=
  { name := "an optimize bucket's cell keeps the best state reached so far"
    source := "docs/AGENTS.md (\"each bucket keeps its best state so far and the tree returns there, climbing\"); events.zig:291-294"
    check := fun _ s => Id.run do
      let mut best : Option Int := none
      for j in s.judged do
        for i in j.members do
          let some t := ranOf s i | continue
          let sm := t.summary
          for b in sm.behaviors do
            let some score := b.score | continue
            if b.vtime ≤ sm.startNs then continue
            let at_ := objectivePlace sm (b.vtime + after)
            if (sm.cut || at_ < sm.lastPull) && at_ < sm.endNs then
              best := some (match best with | some x => max x score | none => score)
        let cell := j.cellsAfter.find? (·.hash == 2000)
        match best, cell with
        | some b, some c => if c.best != some b then return some s!"generation {j.generation}: the bucket's best open score is {b}, its cell keeps {c.best}"
        | some b, none => return some s!"generation {j.generation}: the bucket reached {b}, no cell"
        | _, _ => pure ()
      return none }

def objectiveReturnsThere : TProp :=
  { name := "a return to an optimize bucket lands at its best state"
    source := "docs/AGENTS.md (\"each bucket keeps its best state so far and the tree returns there, climbing\")"
    check := fun _ s => Id.run do
      for j in s.judged do
        for (r, r0) in j.returns.zip j.returnsAt do
          if r.cell == some 2000 && r.vtime != r0.vtime then
            return some s!"generation {j.generation}: the bucket's best is #{r0.branch} at {r0.vtime} µs; the return landed at {r.vtime} µs"
      return none }

def allTProps : List TProp :=
  [replaysFromTape, nodeIsParentsState, noRepeatReturned, distinctMoments, fillOtherTimelines,
   explorerInsideSpan, strategyBeforeLastPull, generationShape, soughtMomentFirst, soughtReturnAfter,
   objectiveKeepsBest, objectiveReturnsThere]

def judgeT (p : TProp) (cfg : Config) (source : Source) : Ended :=
  let (r, s) := runOf cfg source
  match r with
  | .ok s => { taken := s.decisions.taken, violation := (p.check cfg s).map fun d => (p.name, d) }
  | .error _ => { taken := s.decisions.taken, violation := none }

def storyT (cfg : Config) (source : Source) : List String :=
  let (_, s) := runOf cfg source
  [s!"run seed {s.base}, generation size {s.size}, {cfg.children} from each moment, pipeline {cfg.pipeline}, {cfg.jobs} jobs"] ++
  (s.ran.toList.map fun r =>
    s!"#{r.planned.index} (gen {r.planned.generation}): plan seed {r.planned.seed % 10000}…, ran with {r.seed % 10000}…, from {r.start} µs, path [{showPath r.planned.path}], events {r.evs}") ++
  (s.judged.toList.map fun j =>
    s!"judgment {j.generation}: members {j.members}, repeats {j.repeats}; returns " ++
      String.intercalate "; " (j.returns.map fun r => s!"#{r.branch}@{r.vtime}{if r.strategy then " (strategy)" else if r.cell.isSome then s!" (archive cell {r.cell.getD 0})" else ""}") ++
      s!"; nodes " ++ String.intercalate ", " (j.made.map fun m => s!"#{m.parent}@{m.moment} {if m.holder then "holder" else "replay"}") ++
      s!"; {j.fresh} fresh")

/-! ## Same timelines whatever the workers (README_AI.md; ARCHITECTURE.md §9) -/

/-- Each planned index's start: its path and seed. -/
def placesOf (s : RS) : List (Nat × (List Segment × Nat)) :=
  s.ran.toList.map fun r => (r.planned.index, (r.planned.path, r.planned.seed))

/-- A run with `jobs` workers (finishing order drawn) against the same run with one worker
(finishing in order), the judgment's draws from the generation's seed in both (main.zig:6386).
`sizeOf` gives each its generation size: fixed (`--generation`), or `generation_for(jobs)`. -/
def sameTimelines (cfg : Config) (sizeOf : Nat → Nat) (source : Source) : Ended :=
  let many := { cfg with seededJudgment := true, size := sizeOf cfg.jobs }
  let (r, s) := runOf many source
  match r with
  | .error _ => { taken := s.decisions.taken, violation := none }
  | .ok s =>
    let baseIndex := (s.decisions.taken.find? (·.name == "world.base")).map (·.value) |>.getD 0
    let one := { cfg with seededJudgment := true, jobs := 1, size := sizeOf 1, bases := [s.base] }
    let (_, s1) := runOf one (Source.path #[baseIndex])
    let a := placesOf s
    let b := placesOf s1
    let diff := a.find? fun (i, pl) => match lookup b i with | some q => q != pl | none => false
    let name := "the same timelines as one worker (--jobs)"
    match diff with
    | some (i, (path, _)) =>
      let other := (lookup b i).map (·.1) |>.getD []
      { taken := s.decisions.taken,
        violation := some (name, s!"timeline {i}: with {cfg.jobs} workers (generation {sizeOf cfg.jobs}) it starts at [{showPath path}]; with one (generation {sizeOf 1}) at [{showPath other}]") }
    | none => { taken := s.decisions.taken, violation := none }

def sameStory (cfg : Config) (sizeOf : Nat → Nat) (source : Source) : List String :=
  let many := { cfg with seededJudgment := true, size := sizeOf cfg.jobs }
  let (_, s) := runOf many source
  let baseIndex := (s.decisions.taken.find? (·.name == "world.base")).map (·.value) |>.getD 0
  let one := { cfg with seededJudgment := true, jobs := 1, size := sizeOf 1, bases := [s.base] }
  [s!"with {cfg.jobs} workers:"] ++ storyT many source ++ [s!"with one worker:"] ++ storyT one (Source.path #[baseIndex])

/-! ## Worlds -/

def tworlds : List Config :=
  [ { label := "no strategy, a generation of 4 (1 fresh, 3 moments of 1), one worker, 12 timelines", total := 12 },
    { label := "no strategy, a generation of 4 (1 fresh, 1 moment of 3), one worker, 12 timelines", children := 3, total := 12 },
    { label := "no strategy, kinds 2, few pulls (repeats likely), 12 timelines", total := 12, sys := { kinds := 2, pulls := [2, 4] } },
    { label := "same_seed.py (every timeline one seed, decides false: holders), 12 timelines", total := 12,
      strategy := some { seed := some 66 } },
    { label := "a strategy giving some timelines a seed, deciding (no holders), 12 timelines", total := 12,
      strategy := some { seed := some 66, sometimes := true, decides := true } },
    { label := "a strategy answering returns (decides false), 12 timelines", total := 12,
      strategy := some { returns := true } },
    { label := "a strategy answering returns and giving some seeds, 12 timelines", total := 12,
      strategy := some { returns := true, seed := some 66, sometimes := true } } ]

def searchTree (exhaustRuns seeds : Nat) : IO Unit := do
  for p in allTProps do
    say s!"== tree property: {p.name}"
    say s!"   source: {p.source}"
    let mut exhausted := false
    let mut explored := false
    for cfg in tworlds do
      if !exhausted then
        if let some f ← exhaustSaid s!"{p.name} / {cfg.label}" (judgeT p cfg) exhaustRuns then
          printFound f (storyT cfg); exhausted := true
      if !explored then
        if let some f ← exploreSaid s!"{p.name} / {cfg.label}" (judgeT p cfg) seeds then
          printFound f (storyT cfg); explored := true

/-- The jobs worlds: timing alone (a fixed generation), and generation_for(jobs). -/
def searchJobs (exhaustRuns seeds : Nat) : IO Unit := do
  say "== tree property: the same timelines as one worker (--jobs)"
  say "   source: README_AI.md (\"Branches run on every CPU (`--jobs`, same timelines as one worker)\"); ARCHITECTURE.md §9 (\"The tree's generations are judged in order, each once complete (a seed gives the same tree)\")"
  let timing : Config := { label := "a fixed generation of 4, pipeline 2, 2 workers, 12 timelines", pipeline := 2, jobs := 2, total := 12 }
  let fixed : Nat → Nat := fun _ => 4
  if let some f ← exhaustSaid s!"same timelines / {timing.label} / --generation 4 given (timing alone)" (sameTimelines timing fixed) exhaustRuns then
    printFound f (sameStory timing fixed)
  if let some f ← exploreSaid s!"same timelines / {timing.label} / --generation 4 given (timing alone)" (sameTimelines timing fixed) seeds then
    printFound f (sameStory timing fixed)
  let zig : Config := { label := "the default generation (generation_for(jobs)), pipeline 3, 32 workers, 56 timelines",
                        pipeline := 3, jobs := 32, total := 56, children := 4 }
  if let some f ← exploreSaid s!"same timelines / {zig.label}" (sameTimelines zig generationFor) seeds then
    printFound f (sameStory zig generationFor)

end Replica.Tree

namespace Replica.Tree

open Determinismo

/-- Per world, over seeds `0 .. count - 1`: how many runs break each property (one run checked
against all of them), and how many judgments made a duplicate moment or returned to a repeat. -/
def treeCensus (count : Nat) : IO Unit := do
  for cfg in tworlds do
    let mut counts : Array Nat := (List.replicate allTProps.length 0).toArray
    let mut judgments := 0
    let mut dupJudgments := 0
    let mut repeatJudgments := 0
    for i in [0:count] do
      let (r, _) := runOf cfg (Source.seeded i)
      match r with
      | .error _ => pure ()
      | .ok s =>
        for (p, k) in allTProps.zipIdx do
          if (p.check cfg s).isSome then counts := counts.modify k (· + 1)
        let mut repeats : List Nat := []
        for j in s.judged do
          judgments := judgments + 1
          repeats := repeats ++ j.repeats
          let own := j.returns.filter (!·.strategy)
          let pairs := own.map fun r => (r.branch, r.vtime)
          if pairs.eraseDups.length < pairs.length then dupJudgments := dupJudgments + 1
          if own.any (fun r => repeats.contains r.branch) then repeatJudgments := repeatJudgments + 1
    say s!"census [{cfg.label}, seeds 0..{count - 1}]: {judgments} judgments, {dupJudgments} with two returns at one moment, {repeatJudgments} returning to a repeat"
    for (p, k) in allTProps.zipIdx do
      say s!"  {counts[k]!} of {count} runs break: {p.name}"

end Replica.Tree
