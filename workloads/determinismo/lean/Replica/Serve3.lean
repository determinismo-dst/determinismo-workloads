import Replica.Prelude
import Replica.Searching

/-!
# Serve: a stopped run resumed, the coverage gate, the properties with sessions (platform 3939448)

## Resume (src/serve.zig:5630-5696 `run_resume`; src/main.zig:2103-2194 `resume_read`, 3460-3462,
1106-1170 `system_run`)

A stopped (or interrupted) run is continued by its explorer with `--resume`: the timelines its
record has are skipped (`exploration.done`, explore_branches 3460-3462: `continue`, nothing
absorbed), the rest run; when every index below `--branches` is recorded, `resume_read` says "the
run is complete" and exits 0 (2189-2192). The explorer's verdict is its multiverse's
(`command_explore` 1106-1113: `failing_violations`, `sometimes_unmet`, the catalog), its exit
status 3 or 0 (1166-1170, and serve's `state`: 0 "passed", 3 "failed", 6226-6235). Serve's
properties (store.zig `properties_sql`) are the database's: every timeline ingested, the recorded
ones too.

## The coverage gate (serve.zig:689-752 `coverage_gate`)

At each ingest of a running run: any `coverage` event in `events`, the gate is done; else once
`SELECT count(*) FROM timelines` (sessions included) reaches 4, the run is stopped "no coverage
in its first 4 timelines: its system runs without its language's instrumentation". A coverage
event is sent the first time a process of the timeline runs an edge no process of the timeline
ran before (sdk/zig/determinismo.zig:2084-2200: a bit per edge in /opt/determinismo/coverage,
"shared by every process of every node"; guest/runtime/init.zig:214-223: a tmpfs mounted at boot,
so in the setup's snapshot, and every timeline goes on from the bits its setup set).

## properties_sql with sessions (store.zig:1144-1257)

Each timeline's verdicts (`timeline_properties`), sessions' left out (`per`); a property failing
where a timeline failed it, unreached when no timeline hit it, a sometimes failing when none made
it true.
-/

namespace Replica.Serve3

open Determinismo

/-! ## Resume -/

/-- A timeline's verdicts: an always made false, a sometimes evaluated (made true or not). -/
structure TL where
  alwaysFalse : Bool := false
  sometimesHit : Bool := false
  sometimesTrue : Bool := false
  deriving Repr, BEq, Inhabited

/-- The explorer's verdict over the timelines it ran (report.zig `failing_violations`,
`sometimes_unmet`, main.zig:1106-1156): 3 when an always failed or a sometimes was reached and
never made true, else 0. -/
def explorerExit (ran : List TL) : Nat :=
  if ran.any (·.alwaysFalse) then 3
  else if ran.any (·.sometimesHit) && !ran.any (·.sometimesTrue) then 3
  else 0

/-- serve.zig:6226-6235 `state`. -/
def state (status : Nat) : String := if status == 0 then "passed" else if status == 3 then "failed" else "error"

/-- store.zig `properties_sql`'s statuses for the run's two properties, over every timeline. -/
def runFailing (all : List TL) : Bool :=
  all.any (·.alwaysFalse) || (all.any (·.sometimesHit) && !all.any (·.sometimesTrue))

structure RW where
  branches : Nat := 3
  deriving Inhabited

structure RSt where
  decisions : Decisions := {}
  deriving Inhabited

instance : Chaotic RSt where
  decisions s := s.decisions
  setDecisions _ d := { decisions := d }

structure Resumed where
  timelines : List TL
  recorded : Nat
  status : Nat
  deriving Inhabited

def drawResume (w : RW) : EStateM Stop RSt Resumed := do
  let mut tls := []
  for _ in [0:w.branches] do
    let a := (← below "world.always_false" 2) == 1
    let hit := (← below "world.sometimes_hit" 2) == 1
    let tr ← if hit then do pure ((← below "world.sometimes_true" 2) == 1) else pure false
    tls := tls ++ [{ alwaysFalse := a, sometimesHit := hit, sometimesTrue := tr }]
  -- Stopped after `recorded` timelines had their lines in the record (a flat run's order).
  let recorded ← below "world.recorded" (w.branches + 1)
  -- main.zig:2186-2192: all recorded, "the run is complete", exit 0; else the rest run and the
  -- explorer judges what it ran (3460-3462: the recorded skipped).
  let status := if recorded == w.branches then 0 else explorerExit (tls.drop recorded)
  return { timelines := tls, recorded, status }

def resumeVerdict : String × String :=
  ("a resumed run's state is its timelines' verdict",
   "serve.zig:5912 recorded_status (\"A failing property fails the run, as explore exits\"); serve.zig:5630-5633 run_resume (\"Continues a run that ended before its end ...: its explorer again\"); main.zig:242-244 usage (\"--resume ... continue that run, its recorded timelines skipped\")")

def judgeResume (w : RW) (source : Source) : Ended :=
  match (drawResume w).run { decisions := { source } } with
  | .ok r s =>
    let failing := runFailing r.timelines
    let says := state r.status
    let ok := (says == "failed") == failing
    { taken := s.decisions.taken,
      violation := if ok then none else some (resumeVerdict.1,
        s!"timelines {reprStr r.timelines}; {r.recorded} recorded before the stop; resumed, the explorer exits {r.status}: serve says {says}, its properties {if failing then "failing" else "passing"}") }
  | .error _ s => { taken := s.decisions.taken, violation := none }

/-! ## The coverage gate -/

structure GW where
  label : String
  edges : Nat := 3
  timelinesMax : Nat := 5
  sessions : Bool := false
  /-- The system's language instrumented (its coverage reported), or drawn. -/
  instrumented : Option Bool := none
  deriving Inhabited

structure Gate where
  /-- Each ended row of `timelines`, in order: a session or not, its coverage events. -/
  rows : List (Bool × Nat)
  stoppedAt : Option Nat
  instrumented : Bool
  setupEdges : List Nat
  edgesRun : List (List Nat)
  deriving Inhabited

/-- What a timeline reports: the edges it runs that no process of it ran before, its setup's
included (sdk/zig/determinismo.zig:2122-2177). -/
def reported (setupEdges run : List Nat) : Nat :=
  (run.eraseDups.filter (!setupEdges.contains ·)).length

def drawGate (w : GW) : EStateM Stop RSt Gate := do
  let instrumented ← match w.instrumented with
    | some b => pure b
    | none => do pure ((← below "world.instrumented" 2) == 1)
  -- The setup runs some of the system's code; each timeline runs some.
  let mut setupEdges := []
  for e in [0:w.edges] do
    if (← below "world.setup_edge" 2) == 1 then setupEdges := setupEdges ++ [e]
  let n := 1 + (← below "world.timelines" w.timelinesMax)
  let mut rows := []
  let mut edgesRun := []
  let mut stoppedAt := none
  for i in [0:n] do
    -- A session is opened at a moment of a timeline already there: never the first row.
    let session ← if w.sessions && i > 0 then do pure ((← below "world.session" 4) == 0) else pure false
    let mut run := []
    for e in [0:w.edges] do
      if (← below "world.edge" 2) == 1 then run := run ++ [e]
    -- A timeline runs some of the system's code.
    if run.isEmpty then run := [0]
    -- Uninstrumented code reports nothing at all.
    let events := if instrumented then reported setupEdges run else 0
    rows := rows ++ [(session, events)]
    edgesRun := edgesRun ++ [run]
    -- serve.zig:703-752 at this ingest: covered, done; else 4 rows of `timelines`: stopped.
    if rows.any (·.2 > 0) then break
    if rows.length ≥ 4 then
      stoppedAt := some i
      break
  return { rows, stoppedAt, instrumented, setupEdges, edgesRun }

def gateProp : String × String :=
  ("the coverage gate stops only runs without instrumentation",
   "docs/SDKS.md:101-105 (\"A run without coverage is explored blind, so serve does not let one go unnoticed\"); serve.zig:689-700 (\"A system without its language's instrumentation is explored blind\") and 731-733, the stop's reason: \"its system runs without its language's instrumentation (coverage always)\"; docs/CI.md (\"serve can tell a job that ran from one that did not\")")

def gateCounts : String × String :=
  ("the coverage gate judges the run's own first 4 timelines",
   "docs/SDKS.md:101-102 (\"a run whose first 4 ended timelines report none is stopped\"); store.zig:676-680 (sessions are not what the run explored)")

def judgeGate (which : Nat) (w : GW) (source : Source) : Ended :=
  match (drawGate w).run { decisions := { source } } with
  | .ok g s =>
    let v := if which == 0 then
        if g.stoppedAt.isSome && g.instrumented then
          some (gateProp.1, s!"an instrumented system: its setup ran edges {g.setupEdges}, its first timelines ran {g.edgesRun}, each reporting none (all its setup's): stopped, \"its system runs without its language's instrumentation\"")
        else none
      else
        let own := (g.rows.filter (!·.1)).length
        if g.stoppedAt.isSome && own < 4 then
          some (gateCounts.1, s!"stopped after {own} of the run's timelines and {g.rows.length - own} session(s): rows {reprStr g.rows}")
        else none
    { taken := s.decisions.taken, violation := v }
  | .error _ s => { taken := s.decisions.taken, violation := none }

/-! ## properties_sql with sessions -/

structure PRow where
  timeline : Nat
  session : Bool
  hits : Nat
  trues : Nat
  failed : Bool
  deriving Repr, Inhabited

/-- store.zig:1146-1190 for one property (type, message): its status. -/
def statusOf (kind : String) (rows : List PRow) : String :=
  let per := rows.filter (!·.session)
  let hit := (per.filter (·.hits > 0)).length
  let trues := (per.filter (·.trues > 0)).length
  let failing := (per.filter (·.failed)).length
  if failing > 0 then "failing"
  else if (kind == "always" || kind == "sometimes" || kind == "reachable") && hit == 0 then "unreached"
  else if kind == "sometimes" && trues == 0 then "failing"
  else "passing"

def drawRows (n : Nat) : EStateM Stop RSt (List PRow) := do
  let mut rows := []
  for t in [0:n] do
    let session := (← below "world.session" 2) == 1
    let hits ← below "world.hits" 2
    let mut trues := 0
    let mut failed := false
    if hits > 0 then
      trues ← below "world.trues" 2
      failed := (← below "world.failed" 2) == 1
    rows := rows ++ [{ timeline := t, session, hits, trues, failed }]
  return rows

def sessionsProp : String × String :=
  ("a session's evaluations never change a property's status",
   "store.zig:676-679 (\"What a run found is judged over these (its properties, findings, statistics, logged errors): a crash someone caused at a REPL is in its own timeline's events ..., never among the run's findings\"); docs/AGENTS.md, Sessions")

def judgeSessions (kind : String) (n : Nat) (source : Source) : Ended :=
  match (drawRows n).run { decisions := { source } } with
  | .ok rows s =>
    let a := statusOf kind rows
    let b := statusOf kind (rows.filter (!·.session))
    { taken := s.decisions.taken, violation := if a == b then none else some (sessionsProp.1, s!"{kind}: {a} with sessions, {b} without") }
  | .error _ s => { taken := s.decisions.taken, violation := none }

def searchAll (exhaustRuns : Nat) : IO Unit := do
  say s!"== serve property: {resumeVerdict.1}"
  say s!"   source: {resumeVerdict.2}"
  for n in [1, 2, 3] do
    let w : RW := { branches := n }
    if let some f ← exhaustSaid s!"{resumeVerdict.1} / {n} timelines" (judgeResume w) exhaustRuns then
      printFound f (fun src => match (drawResume w).run { decisions := { source := src } } with
        | .ok r _ => [s!"timelines {reprStr r.timelines}", s!"stopped with {r.recorded} recorded; resumed: exit {r.status} ({state r.status})", s!"properties: {if runFailing r.timelines then "failing" else "passing"}"]
        | .error _ _ => [])
  for (which, p) in [(0, gateProp), (1, gateCounts)] do
    say s!"== serve property: {p.1}"
    say s!"   source: {p.2}"
    for w in [({ label := "an instrumented system, 3 edges, up to 5 timelines", instrumented := some true } : GW),
              { label := "3 edges, up to 5 timelines" },
              { label := "3 edges, up to 5 timelines, sessions opened", sessions := true }] do
      if let some f ← exhaustSaid s!"{p.1} / {w.label}" (judgeGate which w) exhaustRuns then
        printFound f (fun src => match (drawGate w).run { decisions := { source := src } } with
          | .ok g _ => [s!"instrumented {g.instrumented}; setup edges {g.setupEdges}; timelines' edges {g.edgesRun}; rows (session, coverage events) {reprStr g.rows}; stopped at {reprStr g.stoppedAt}"]
          | .error _ _ => [])
  say s!"== serve property: {sessionsProp.1}"
  say s!"   source: {sessionsProp.2}"
  for kind in ["always", "sometimes", "reachable", "always_or_unreachable", "unreachable"] do
    for n in [1, 2, 3] do
      if let some f ← exhaustSaid s!"{sessionsProp.1} / {kind}, {n} timelines" (judgeSessions kind n) exhaustRuns then
        printFound f (fun _ => [])

end Replica.Serve3
