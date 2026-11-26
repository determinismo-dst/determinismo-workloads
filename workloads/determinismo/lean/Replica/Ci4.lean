import Replica.Ci

/-!
# determinismo-ci, continued: per-shard reports, the `{shard}` mode, and the coverage gate
(platform 3939448)

- `tests_judge` (src/products/ci.zig:440-485) over serve's properties: `reported` is the most
  timelines any test was hit in, over the whole run (all shards); `unreported` = `timelines` (one
  shard's) minus it; its comment (436-438): "\"error\" when a timeline stated no test (the run
  command died before its report)", and its line (477) "<k> timelines without their JUnit report".
- A shard's line (ci.zig:278-291): its test count is the list's positions modulo the shards
  (281-283), whatever the run command does: in the `{shard}` mode (230-233) the runner shards the
  suite itself.
- serve's coverage gate (src/serve.zig:690-752): a running run whose first 4 ended timelines
  carry no `coverage` event is stopped; the watcher (650-678) ingests what ended since its last
  look, then looks. determinismo-ci (ci.zig:254-270) posts its run with no `"coverage"` asked, and
  a shard with fewer than `timelines` timelines stating its property is "error" (285).
- What reports coverage in a CI job's run command (`det-nodes exec --coverage`,
  guest/runtime/nodes.zig:3744-3752): a JVM's agent on JAVA_TOOL_OPTIONS (instruments as classes
  load on a JVM of 24 or later; 17 to 23 only jars instrumented ahead of time:
  sdk/java/DeterminismoCoverage.java:9-12), Python's sitecustomize (3.12 or later:
  guest/runtime/python/sitecustomize.py:14-23), nothing for other runtimes (no NODE_OPTIONS):
  each process reports a line the first time it runs it (DeterminismoCoverage.java:126-131 with
  `queued` and `reported`; sdk/python/determinismo.py:648-656 `reported`).
-/

namespace Replica.Ci4

open Determinismo
open Replica.Ci

/-! ## Per-shard reports -/

/-- The timelines of the run (sessions aside) that stated no test (hung, or died before the
report). -/
def withoutReport (j : Job) (ver : Ver := .v3939448) : Nat :=
  (j.stated.filter fun s => !s.session && s.tests.isEmpty && (ver == .v3939448 || s.shardCondition.isSome)).length

def unreportedCounted : CProp :=
  { name := "tests_judge counts every timeline that stated no test (and calls the job error)"
    source := "ci.zig:436-438 (tests_judge: \"\\\"error\\\" when a timeline stated no test (the run command died before its report)\"); ci.zig:477 (\"<k> timelines without their JUnit report\")"
    check := fun cfg j =>
      if !cfg.junit then none else
      let v := verdictOf cfg j
      -- 62e06e3 (ci.zig:296-308): the timelines that stated their shard's property and no test,
      -- each; a hung one (no statement) is its shard's failure (shard_verdict).
      let none' := withoutReport j cfg.ver
      if v.unreported != none' then
        some s!"{describe j}: {none'} timelines stated no test; tests_judge says {v.unreported} timelines without their JUnit report (the job {v.job}, exit {v.exit})"
      else none }

/-- The same outcomes in a shard give the same exit whatever another shard did, when that one
passes everywhere (a shard's verdict is its timelines'). -/
def shardsIndependent : CProp :=
  { name := "a shard's failures give the job the same exit whatever a passing shard beside it reports"
    source := "docs/CI.md (\"Each timeline runs its shard's tests ... A shard failing in every timeline fails, in some is flaky\"; \"Exit status 0 when every shard passes, 1 when one fails, 2 when one is flaky\")"
    check := fun cfg j => Id.run do
      -- 3939448's count (round 4); 62e06e3 counts per timeline (unreportedCounted judges it).
      if cfg.ver.since62 then return none
      if !cfg.junit || j.shardCount < 2 then return none
      -- Shard 1 passing in every timeline: its tests reported everywhere. The job without it
      -- (its timelines' statements dropped): the other shards' verdicts alone.
      let shard1 := (j.outcomes.zipIdx.filter fun (_, t) => t % j.shardCount == 0).map (·.1)
      if !shard1.all (· == .passes) then return none
      let others := { j with stated := j.stated.filter (·.shard != 1) }
      let a := verdictOf cfg j
      -- The others' own count of timelines without a report, as tests_judge would make it.
      let props := testProperties others
      let reported := props.foldl (fun m (_, h, _) => max m h) 0
      let alone := if cfg.timelines > reported then "error" else a.job
      if alone == "error" && a.job != "error" then
        return some s!"{describe j}: with shard 1 passing beside it the job is {a.job} (exit {a.exit}); its other shards' timelines alone report {cfg.timelines - reported} timelines without their report: error (exit 1)"
      return none }

def worlds37 : List Cfg :=
  [ { label := "three tests, two shards of 2 timelines, junit", tests := ["t1", "t2", "t3"], shards := 2, timelines := 2 },
    { label := "two tests, two shards of 3 timelines, junit", tests := ["t1", "t2"], shards := 2, timelines := 3 },
    { label := "two tests, one shard of 3 timelines, junit", tests := ["t1", "t2"], shards := 1, timelines := 3 } ]

/-! ## The `{shard}` mode's line -/

/-- A runner that shards itself by contiguous blocks (pytest-split, a file-based split), against
the line's count by positions modulo the shards (ci.zig:281-283). -/
def lineCount (tests shards number : Nat) : Nat := Id.run do
  let mut count := 0
  let mut at_ := number - 1
  while at_ < tests do
    count := count + 1
    at_ := at_ + shards
  return count

def blockCount (tests shards number : Nat) : Nat :=
  let per := (tests + shards - 1) / shards
  let first := (number - 1) * per
  if first ≥ tests then 0 else min per (tests - first)

/-! ## The coverage gate on a CI job -/

inductive Runner where
  | python312
  | python311
  | jdk24
  | jdk21
  | jdk21Aot
  | jest
  | goPlain
  deriving BEq, Repr, Inhabited

def Runner.show : Runner → String
  | .python312 => "pytest on Python 3.12 (sitecustomize)"
  | .python311 => "pytest on Python 3.11"
  | .jdk24 => "JUnit on JDK 24 (the agent)"
  | .jdk21 => "JUnit on JDK 21, jars as built"
  | .jdk21Aot => "JUnit on JDK 21, jars instrumented ahead of time"
  | .jest => "Jest (docs/CI.md's own example config)"
  | .goPlain => "go test, built without determinismo-toolexec"

/-- Whether the runner's processes report `coverage` events in a timeline (a new process each:
its lines reported the first time it runs them). -/
def Runner.covered : Runner → Bool
  | .python312 | .jdk24 | .jdk21Aot => true
  | _ => false

structure GCfg where
  label : String
  shards : Nat := 2
  timelines : Nat := 3
  runners : List Runner := [.python312, .python311, .jdk24, .jdk21, .jdk21Aot, .jest, .goPlain]
  /-- Round 6: serve.zig as at a7fe05d (a CI job never stopped by the gate, 765-769) unless a
  theorem about 3939448 or 62e06e3 says so. -/
  ver : Ver := .vdf8f08b
  deriving Inhabited

structure Gate where
  runner : Runner
  /-- The ingests: how many timelines each brought (the timelines' ends between two looks). -/
  batches : List Nat
  stoppedAt : Option Nat
  /-- Per shard, the timelines that stated its property. -/
  stated : List Nat
  verdict : String
  exit : Nat
  deriving Repr, Inhabited

/-- serve.zig:703-752 `coverage_gate`, looked at after each ingest that brought timelines
(serve.zig:675-677), and ci.zig:277-301's shard verdicts. Every test passes. -/
def gateRun (cfg : GCfg) : CM Gate := do
  let runner := cfg.runners[(← below "world.runner" cfg.runners.length)]!
  let total := cfg.shards * cfg.timelines
  let mut ended := 0
  let mut batches := []
  let mut stoppedAt : Option Nat := none
  while ended < total do
    let left := total - ended
    let n := 1 + (← below "watcher.ingest" left)
    ended := ended + n
    batches := batches ++ [n]
    let going := ended < total
    if !runner.covered && going && ended ≥ 4 && !cfg.ver.sinceA7 then
      stoppedAt := some ended
      break
  -- The timelines that ended, in index order of their ends (all of them pass): shard t % S + 1.
  let stated := (List.range cfg.shards).map fun k =>
    ((List.range ended).filter fun t => t % cfg.shards == k).length
  let verdict := if stated.any (· < cfg.timelines) then "error" else "pass"
  return { runner, batches, stoppedAt, stated, verdict, exit := if verdict == "pass" then 0 else 1 }

def gateProperty : String := "a CI job whose tests all pass exits 0 (an uncovered runner runs uncovered and says so)"
def gateSource : String := "docs/CI.md (Coverage: \"An older Python or JVM runs uncovered and says so on standard error\"; Running it: \"Exit status 0 when every shard passes\"; the config example's `\"run\": \"cd /app && npx jest --ci --shard={shard}/{shards}\"`)"

def judgeG (cfg : GCfg) (source : Source) : Ended :=
  match (gateRun cfg).run { decisions := { source } } with
  | .ok g s => { taken := s.decisions.taken, violation :=
      if g.exit != 0 then some (gateProperty, s!"{g.runner.show}: every test passes; timelines ingested in batches {g.batches}; serve stopped the run after {g.stoppedAt.getD 0} ended timelines with no coverage; shards stated {g.stated} of {cfg.timelines} timelines: determinismo-ci says {g.verdict}, exit {g.exit}") else none }
  | .error _ s => { taken := s.decisions.taken, violation := none }

def storyG (cfg : GCfg) (source : Source) : List String :=
  match (gateRun cfg).run { decisions := { source } } with
  | .ok g _ =>
    [s!"{cfg.shards} shards of {cfg.timelines} timelines, {g.runner.show} (coverage events: {g.runner.covered})",
     s!"the watcher ingests the ended timelines in batches {g.batches}",
     match g.stoppedAt with
     | some n => s!"after {n} ended timelines with no coverage event (the run still going): serve stops the run (\"no coverage in its first {n} timelines\")"
     | none => "the run ends before the gate stops it (or it is covered)",
     s!"shards' timelines stating their property: {g.stated}; determinismo-ci: {g.verdict}, exit {g.exit}",
     "the same job with every timeline ended before the gate's first look: pass, exit 0 (an `uncovered` file only)"]
  | .error _ _ => []

/-! ## The JVM agent's and Python's per-process reports, and a process from the setup -/

/-- A process's report set (DeterminismoCoverage's `queued`/`reported`, Python's `reported`):
the lines it ran before, kept in its memory, so in the setup's snapshot when it started there. -/
def reportsOf (before : List Nat) (runs : List Nat) : List Nat := Id.run do
  let mut seen := before
  let mut out := []
  for l in runs do
    if !seen.contains l then
      seen := seen ++ [l]
      out := out ++ [l]
  return out

def searchAll (exhaustRuns seeds : Nat) : IO Unit := do
  for p in [unreportedCounted, shardsIndependent] do
    say s!"== ci property: {p.name}"
    say s!"   source: {p.source}"
    for cfg in worlds37 do
      if let some f ← exhaustSaid s!"{p.name} / {cfg.label}" (judgeC p cfg) exhaustRuns then
        printFound f (storyC cfg)
  say s!"== ci property: {gateProperty}"
  say s!"   source: {gateSource}"
  for cfg in [({ label := "two shards of 3 timelines, every runner" } : GCfg),
              { label := "docs/CI.md's example shape: 8 shards of 3 timelines, Jest", shards := 8, timelines := 3, runners := [.jest] },
              { label := "examples/ci-demo's shape: 3 shards of 12 timelines, Python 3.12", shards := 3, timelines := 12, runners := [.python312] },
              { label := "62e06e3: docs/CI.md's example shape: 8 shards of 3 timelines, Jest", shards := 8, timelines := 3, runners := [.jest], ver := .v62e06e3 }] do
    if let some f ← exhaustSaid s!"{gateProperty} / {cfg.label}" (judgeG cfg) exhaustRuns then
      printFound f (storyG cfg)
    if let some f ← exploreSaid s!"{gateProperty} / {cfg.label}" (judgeG cfg) seeds then
      printFound f (storyG cfg)
  say "== ci property: a shard's line counts the tests its runner ran (the {shard} mode)"
  say "   source: docs/CI.md (\"the job's log shows each shard's verdict\"); ci.zig:288-291 (\"shard k: <verdict> <n> tests\")"
  let mut differ := 0
  let mut first := ""
  for tests in [1:13] do
    for shards in [1:tests + 1] do
      for number in [1:shards + 1] do
        let line := lineCount tests shards number
        let ran := blockCount tests shards number
        if line != ran then
          differ := differ + 1
          if first == "" then first := s!"{tests} tests, {shards} shards, shard {number}: the line says {line} tests, a runner splitting in blocks ran {ran}"
  say s!"search exhaust [shard line counts / 1 to 12 tests, every shard count, a runner splitting in blocks]: {differ} shard lines differ; the first: {first}"
  say "== ci property: the coverage gate stops only runs without their language's instrumentation (the JVM agent and Python)"
  say "   source: docs/SDKS.md:101-105; serve.zig:731-733 (\"its system runs without its language's instrumentation\")"
  say s!"a JVM node started in the setup (agent on, JDK 24) ran lines {[1, 2, 3]} there; each timeline runs {[1, 2, 3]} again: reports {reportsOf [1, 2, 3] [1, 2, 3]} (none): stopped as uninstrumented after 4 timelines (CE30's case, the JVM's `queued` set in the setup's snapshot)"
  say s!"a Python node started in the setup (coverage_start): the same: reports {reportsOf [1, 2] [1, 2]}; a CI run command's new process reports {reportsOf [] [1, 2]}"

end Replica.Ci4
