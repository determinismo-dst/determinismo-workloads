import Replica.Prelude
import Replica.Searching

/-!
# determinismo-ci end to end, replicated (src/products/ci.zig, src/store.zig, platform 3939448)

A job is one run of `shards * timelines` timelines from the setup's checkpoint (ci.zig:200-270),
timeline t of shard `t % shards + 1` (explore's `{timeline%N+1}`). Each timeline runs its shard's
tests; its script (ci.zig:236-250) then, with `junit`, states each test case as
`always(passed) "test passes: <case>"` (`det-assert junit`, guest/runtime/junit.zig), and last
`det-assert always "the CI shard's tests pass" $s {"shard":k,"status":$s}`.

The verdict (ci.zig:277-301): `shard_sql` (273-275) over `timeline_events` counts per shard the
timelines that stated the shard property and those where it was false; a shard is "error" when
fewer than `timelines` stated it, else pass / fail (false in every one) / flaky. With `junit`,
`tests_judge` (440-485) over serve's properties (store.zig:1144-1257, `properties_sql`: a session's
timelines left out): each test failing in every timeline it was hit in is "fail", in some
"flaky"; `reported` is the most timelines any test was hit in, `unreported` = timelines - that,
and any unreported makes the job "error". The job is the worst; exit 0 pass, 2 flaky (0 with
`--flaky-passes`), 1 otherwise (299-301).

A timeline's run (the world's decisions): its tests pass, some fail, it hangs (cut at its
limit: nothing after the run command is stated), or the runner dies before its report (exit
status nonzero, no report). A session (docs/AGENTS.md, Sessions) may be opened on one of the
run's timelines before the job reads its verdict: a timeline of the run of its own (`extends`),
its events its parent's up to its moment (store.zig:663-675, `steps`), then its own.
-/

namespace Replica.Ci

open Determinismo

inductive Outcome where
  | passes
  /-- These of the shard's tests (by position) fail. -/
  | fails (which : List Nat)
  | hangs
  | dies
  deriving Repr, BEq, Inhabited

/-- A timeline's statements: its tests' (name, passed) and its shard property's condition. -/
structure Stated where
  timeline : Nat
  shard : Nat
  /-- A person's session (timelines.extends set). -/
  session : Bool := false
  tests : List (String × Bool) := []
  shardCondition : Option Bool := none
  deriving Repr, Inhabited

structure Cfg where
  label : String
  tests : List String := ["t1", "t2"]
  shards : Nat := 1
  timelines : Nat := 3
  junit : Bool := true
  flakyPasses : Bool := false
  sessions : Bool := false
  /-- Round 5: ci.zig as at 62e06e3 unless a theorem about 3939448 says so. -/
  ver : Ver := .v62e06e3
  deriving Inhabited

structure CS where
  decisions : Decisions := {}
  deriving Inhabited

instance : Chaotic CS where
  decisions s := s.decisions
  setDecisions _ d := { decisions := d }

abbrev CM := EStateM Stop CS

/-- The shard's tests: positions whose index modulo the shards is the shard's (ci.zig:226). -/
def shardTests (cfg : Cfg) (shardCount shard : Nat) : List String :=
  (cfg.tests.zipIdx.filter fun (_, i) => i % shardCount == shard - 1).map (·.1)

def statedOf (cfg : Cfg) (shardCount t : Nat) (o : Outcome) : Stated :=
  let shard := t % shardCount + 1
  let tests := shardTests cfg shardCount shard
  match o with
  | .passes => { timeline := t, shard, tests := if cfg.junit then tests.map (·, true) else [], shardCondition := some true }
  | .fails which =>
    { timeline := t, shard, shardCondition := some false,
      tests := if cfg.junit then tests.zipIdx.map fun (n, i) => (n, !which.contains i) else [] }
  | .hangs => { timeline := t, shard }
  | .dies => { timeline := t, shard, shardCondition := some false }

structure Job where
  shardCount : Nat
  outcomes : List Outcome
  stated : List Stated
  deriving Inhabited

def drawJob (cfg : Cfg) : CM Job := do
  let shardCount := min cfg.shards cfg.tests.length
  let mut outcomes := []
  let mut stated := []
  for t in [0:shardCount * cfg.timelines] do
    let shard := t % shardCount + 1
    let n := (shardTests cfg shardCount shard).length
    let o ← match (← below "world.outcome" 4) with
      | 0 => pure Outcome.passes
      | 1 => do
        let mut which := []
        for i in [0:n] do
          if (← below "world.test_fails" 2) == 1 then which := which ++ [i]
        pure (if which.isEmpty then Outcome.fails [0] else Outcome.fails which)
      | 2 => pure Outcome.hangs
      | _ => pure Outcome.dies
    outcomes := outcomes ++ [o]
    stated := stated ++ [statedOf cfg shardCount t o]
  -- A session on one of the run's timelines, its run going on (live): from before its shard
  -- assertion, its own end (passing: a fix at its REPL; or failing as its parent did); or from
  -- after it, its parent's statements its own (timeline_events' steps).
  let opened ← if cfg.sessions then do pure ((← below "world.session" 2) == 1) else pure false
  if opened then
    let parent := stated[(← below "world.session_parent" stated.length)]!
    let t := shardCount * cfg.timelines
    let own ← match (← below "world.session_end" 3) with
      | 0 => pure parent
      | 1 => pure (statedOf cfg shardCount parent.timeline .passes)
      | _ => pure (statedOf cfg shardCount parent.timeline (.fails [0]))
    stated := stated ++ [{ own with timeline := t, session := true }]
  return { shardCount, outcomes, stated }

/-- ci.zig:273-275 `shard_sql` over `timeline_events` (sessions' timelines included) at 3939448;
over `explored_timeline_events` (sessions left out) at 62e06e3 (ci.zig:340-342, CE28's fix). -/
def shardRow (j : Job) (shard : Nat) (ver : Ver := .v62e06e3) : Nat × Nat :=
  let rows := j.stated.filter fun s => s.shard == shard && s.shardCondition.isSome && (ver == .v3939448 || !s.session)
  ((rows.filter (·.shardCondition == some false)).length, rows.length)

/-- store.zig:1144-1190 `properties_sql` for the tests' properties: (message, hit, failing),
sessions left out (`per`). -/
def testProperties (j : Job) : List (String × Nat × Nat) := Id.run do
  let mut out : List (String × Nat × Nat) := []
  for s in j.stated do
    if s.session then continue
    for (name, passed) in s.tests do
      let message := s!"test passes: {name}"
      out := match out.findIdx? (·.1 == message) with
        | some i => out.set i (message, out[i]!.2.1 + 1, out[i]!.2.2 + (if passed then 0 else 1))
        | none => out ++ [(message, 1, if passed then 0 else 1)]
  return out

def rank : String → Nat
  | "error" => 3 | "fail" => 2 | "flaky" => 1 | _ => 0

def worse (a b : String) : String := if rank b > rank a then b else a

structure Verdict where
  job : String
  exit : Nat
  shards : List (Nat × String × Nat × Nat)
  tests : List (String × String)
  unreported : Nat
  deriving Repr, Inhabited

/-- ci.zig:277-301 and 440-485 (3939448); 62e06e3: ci.zig:262-296 with `shard_verdict` (326-330:
a timeline that never stated its shard's property failed it), `tests_judge` (483-513: no count of
reports) and `unreported_sql` (305-308: the run's timelines that stated their shard's property
and no test, each; "error" only for one whose shard passed). -/
def verdictOf (cfg : Cfg) (j : Job) : Verdict := Id.run do
  if cfg.ver == .v62e06e3 then
    let mut verdict := "pass"
    let mut shards := []
    for number in [1:j.shardCount + 1] do
      let (rowFailing, rowTimelines) := shardRow j number .v62e06e3
      let failing := rowFailing + (cfg.timelines - rowTimelines)
      let v := if failing == 0 then "pass" else if failing ≥ cfg.timelines then "fail" else "flaky"
      verdict := worse verdict v
      shards := shards ++ [(number, v, failing, cfg.timelines)]
    let mut tests := []
    let mut unreported := 0
    if cfg.junit then
      let mut failing := 0
      let mut flaky := 0
      for (message, hit, f) in testProperties j do
        if f == 0 then
          tests := tests ++ [(message, "pass")]
          continue
        if f ≥ hit then
          failing := failing + 1
          tests := tests ++ [(message, "fail")]
        else
          flaky := flaky + 1
          tests := tests ++ [(message, "flaky")]
      verdict := worse verdict (if failing > 0 then "fail" else if flaky > 0 then "flaky" else "pass")
      let silent := j.stated.filter fun s => !s.session && s.shardCondition.isSome && s.tests.isEmpty
      unreported := silent.length
      if silent.any (·.shardCondition == some true) then verdict := "error"
    let exit := if verdict == "pass" then 0 else if verdict == "flaky" then (if cfg.flakyPasses then 0 else 2) else 1
    return { job := verdict, exit, shards, tests, unreported }
  let mut verdict := "pass"
  let mut shards := []
  for number in [1:j.shardCount + 1] do
    let (failing, timelines) := shardRow j number .v3939448
    let v := if timelines < cfg.timelines then "error" else if failing == 0 then "pass"
      else if failing ≥ timelines then "fail" else "flaky"
    verdict := worse verdict v
    shards := shards ++ [(number, v, failing, timelines)]
  let mut tests := []
  let mut unreported := 0
  if cfg.junit then
    let props := testProperties j
    let mut reported := 0
    let mut failing := 0
    let mut flaky := 0
    for (message, hit, f) in props do
      reported := max reported hit
      if f == 0 then
        tests := tests ++ [(message, "pass")]
        continue
      if f ≥ hit then
        failing := failing + 1
        tests := tests ++ [(message, "fail")]
      else
        flaky := flaky + 1
        tests := tests ++ [(message, "flaky")]
    unreported := cfg.timelines - reported
    let tv := if unreported > 0 then "error" else if failing > 0 then "fail" else if flaky > 0 then "flaky" else "pass"
    verdict := worse verdict tv
  let exit := if verdict == "pass" then 0 else if verdict == "flaky" then (if cfg.flakyPasses then 0 else 2) else 1
  return { job := verdict, exit, shards, tests, unreported }

/-- docs/CI.md's model: a timeline passes when its run command exits 0 ("`run`: ... exit status
0 when they pass"); a hang never does. Per shard (and per test, with `junit`, over the timelines
that reported it): failing in every timeline, fail; in some, flaky; in none, pass. The job the
worst of them; exit 0, 1 or 2 (`--flaky-passes`: flaky as passing). -/
def documented (cfg : Cfg) (j : Job) : String := Id.run do
  let mut verdict := "pass"
  for number in [1:j.shardCount + 1] do
    let mine := (j.outcomes.zipIdx.filter fun (_, t) => t % j.shardCount + 1 == number).map (·.1)
    let notPassing := (mine.filter (· != .passes)).length
    let v := if notPassing == 0 then "pass" else if notPassing == mine.length then "fail" else "flaky"
    verdict := worse verdict v
  if cfg.junit then
    for name in cfg.tests do
      -- The timelines that ran it and reported: passing or failing there.
      let shard := (cfg.tests.idxOf name) % j.shardCount + 1
      let mine := (j.outcomes.zipIdx.filter fun (_, t) => t % j.shardCount + 1 == shard).map (·.1)
      let pos := (shardTests cfg j.shardCount shard).idxOf name
      let reports := mine.filterMap fun
        | .passes => some true
        | .fails which => some (!which.contains pos)
        | _ => none
      let f := (reports.filter (!·)).length
      let v := if f == 0 then "pass" else if f == reports.length then "fail" else "flaky"
      verdict := worse verdict v
  return verdict

def exitOf (cfg : Cfg) (v : String) : Nat :=
  if v == "pass" then 0 else if v == "flaky" then (if cfg.flakyPasses then 0 else 2) else 1

structure CProp where
  name : String
  source : String
  check : Cfg → Job → Option String

def describe (j : Job) : String :=
  String.intercalate ", " (j.outcomes.zipIdx.map fun (o, t) => s!"timeline {t} (shard {t % j.shardCount + 1}): {reprStr o}") ++
    (match j.stated.find? (·.session) with
     | some s => s!"; a session (timeline {s.timeline}) on shard {s.shard}: shard property {reprStr s.shardCondition}"
     | none => "")

def jobVerdict : CProp :=
  { name := "the job's verdict is the documented one (a timeline that never exits 0 is not passing)"
    source := "docs/CI.md (Verdicts per test: \"failing in every timeline, fail; in some, flaky, with how often; in none, pass\"; config `run`: \"exit status 0 when they pass\"; Running it: \"Exit status 0 when every shard passes, 1 when one fails, 2 when one is flaky\")"
    check := fun cfg j =>
      let v := verdictOf cfg j
      let d := documented cfg j
      if v.job != d then some s!"{describe j}: determinismo-ci says {v.job} (exit {v.exit}; shards {reprStr v.shards}), the docs {d} (exit {exitOf cfg d})" else none }

def failingCount : CProp :=
  { name := "a shard's line counts every timeline that did not pass"
    source := "docs/CI.md (\"the job's log shows each shard's verdict\"); ci.zig:288-291 (`shard k: <verdict> n tests, failing in f of T timelines`)"
    check := fun cfg j => Id.run do
      let v := verdictOf cfg j
      for (number, verdict, failing, _) in v.shards do
        let mine := (j.outcomes.zipIdx.filter fun (_, t) => t % j.shardCount + 1 == number).map (·.1)
        let notPassing := (mine.filter (· != .passes)).length
        if failing != notPassing then
          return some s!"{describe j}: shard {number}: \"{verdict}, failing in {failing} of {cfg.timelines} timelines\"; {notPassing} did not pass"
      return none }

def exitAsDocumented : CProp :=
  { name := "the exit status is the documented one"
    source := "docs/CI.md, Running it (\"Exit status 0 when every shard passes, 1 when one fails, 2 when one is flaky (`--flaky-passes` counts flaky as passing)\")"
    check := fun cfg j =>
      let v := verdictOf cfg j
      let d := exitOf cfg (documented cfg j)
      if v.exit != d then some s!"{describe j}: exit {v.exit} ({v.job}), the docs {d}" else none }

def runsTimelinesOnly : CProp :=
  { name := "a shard's verdict is its timelines' (a person's session is not the run's)"
    source := "docs/CI.md (\"A job is one run: shards times timelines ... failing in every timeline, fail; in some, flaky\"); store.zig:676-679 (\"What the run explored: its timelines but those that extend one (a person's sessions ...). What a run found is judged over these\")"
    check := fun cfg j =>
      let runOnly := { j with stated := j.stated.filter (!·.session) }
      let a := verdictOf cfg j
      let b := verdictOf cfg runOnly
      if a.job != b.job || a.exit != b.exit then
        some s!"{describe j}: with the session {a.job} (exit {a.exit}, shards {reprStr a.shards}); its timelines alone {b.job} (exit {b.exit})"
      else none }

def allCProps : List CProp := [jobVerdict, failingCount, exitAsDocumented, runsTimelinesOnly]

def judgeC (p : CProp) (cfg : Cfg) (source : Source) : Ended :=
  match (drawJob cfg).run { decisions := { source } } with
  | .ok j s => { taken := s.decisions.taken, violation := (p.check cfg j).map fun d => (p.name, d) }
  | .error _ s => { taken := s.decisions.taken, violation := none }

def storyC (cfg : Cfg) (source : Source) : List String :=
  match (drawJob cfg).run { decisions := { source } } with
  | .ok j _ =>
    let v := verdictOf cfg j
    [describe j] ++ (v.shards.map fun (n, verdict, f, _) => s!"  shard {n}: {verdict} failing in {f} of {cfg.timelines} timelines") ++
      (v.tests.map fun (m, t) => s!"  {t} {m}") ++ [s!"determinismo-ci: {v.job} (exit {v.exit}); the docs: {documented cfg j}"]
  | .error _ _ => []

def cworlds : List Cfg :=
  [ { label := "two tests, one shard of 3 timelines, junit", tests := ["t1", "t2"], timelines := 3 },
    { label := "two tests, one shard of 3 timelines, no junit", tests := ["t1", "t2"], timelines := 3, junit := false },
    { label := "two tests, one shard of 3 timelines, junit, --flaky-passes", tests := ["t1", "t2"], timelines := 3, flakyPasses := true },
    { label := "three tests, two shards of 2 timelines, junit", tests := ["t1", "t2", "t3"], shards := 2, timelines := 2 },
    { label := "one test, one shard of 3 timelines, no junit, a session opened", tests := ["t1"], timelines := 3, junit := false, sessions := true },
    { label := "two tests, one shard of 2 timelines, junit, --flaky-passes, a session opened", tests := ["t1", "t2"], timelines := 2, flakyPasses := true, sessions := true } ]

def searchAll (exhaustRuns : Nat) : IO Unit := do
  for p in allCProps do
    say s!"== ci property: {p.name}"
    say s!"   source: {p.source}"
    for cfg in cworlds do
      if let some f ← exhaustSaid s!"{p.name} / {cfg.label}" (judgeC p cfg) exhaustRuns then
        printFound f (storyC cfg)

end Replica.Ci
