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
  /-- Round 6: serve.zig as at a7fe05d (`setup_covered`, `explored`) unless a theorem about
  3939448 says so. Round 8: c4f246e by default (CE56's fix, serve.zig:766-770). -/
  ver : Ver := .vc4f246e
  /-- Round 6: the run starts from a snapshot or checkpoint its setup ran in (another run's: a
  fast VM's explore-here, a checkpoint run, a moment's futures), or drawn. -/
  fromSnapshot : Option Bool := some false
  deriving Inhabited

structure Gate where
  /-- Each ended row of `timelines`, in order: a session or not, its coverage events. -/
  rows : List (Bool × Nat)
  stoppedAt : Option Nat
  instrumented : Bool
  setupEdges : List Nat
  edgesRun : List (List Nat)
  fromSnapshot : Bool := false
  /-- Round 7: the run ended unstopped with no coverage seen: the gate's end (serve.zig:762-772)
  writes its `uncovered` file, "no coverage in its N timelines: its system runs without its
  language's instrumentation". -/
  labeled : Bool := false
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
  let fromSnapshot ← match w.fromSnapshot with
    | some b => pure b
    | none => do pure ((← below "world.from_snapshot" 2) == 1)
  -- serve.zig:703-727 (a7fe05d) `setup_covered`: a coverage event in the run's own
  -- events/setup.jsonl. A run from a snapshot opens that file and writes nothing to it (main.zig:
  -- 2690-2703: its setup ran where the snapshot was made).
  let setupCovered := w.ver.sinceA7 && instrumented && !fromSnapshot && !setupEdges.isEmpty
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
    -- a7fe05d (750-755): or the setup covered; 4 rows of `explored` (sessions left out).
    if rows.any (·.2 > 0) || setupCovered then break
    let counted := if w.ver.sinceA7 then (rows.filter (!·.1)).length else rows.length
    -- df8f08b (serve.zig:779-783): a run from a machine's checkpoint or a fork's snapshot is
    -- never stopped (CE50's fix); it runs to its end.
    if counted ≥ 4 && !(w.ver.sinceDf && fromSnapshot) then
      stoppedAt := some i
      break
  -- c4f246e (serve.zig:766-770, CE56's fix): the end's label is not written for a run from a
  -- machine's checkpoint or a fork's snapshot either.
  let labeled := stoppedAt.isNone && !(rows.any (·.2 > 0) || setupCovered) && !(w.ver.sinceC4 && fromSnapshot)
  return { rows, stoppedAt, instrumented, setupEdges, edgesRun, fromSnapshot, labeled }

def gateProp : String × String :=
  ("the coverage gate stops only runs without instrumentation",
   "docs/SDKS.md:101-105 (\"A run without coverage is explored blind, so serve does not let one go unnoticed\"); serve.zig:689-700 (\"A system without its language's instrumentation is explored blind\") and 731-733, the stop's reason: \"its system runs without its language's instrumentation (coverage always)\"; docs/CI.md (\"serve can tell a job that ran from one that did not\")")

/-- Round 7: what the gate says of a run, stopped or ended. -/
def gateSays : String × String :=
  ("the coverage gate says a run's system runs without its language's instrumentation only when it does",
   "docs/SDKS.md:101-105; serve.zig:756-757 (df8f08b): the remedy \"its system runs without its language's instrumentation (coverage always); build its workload with it\", in the stop's reason and in the `uncovered` file of a run that ended (762-772); serve.zig:779-783 (df8f08b, CE50's fix): a run from a checkpoint or a fork's snapshot is \"judged at its end, never stopped as uninstrumented\"")

/-- Round 8: the other direction, as serve.zig's own comments say it: an uninstrumented run
that ended unstopped is said so at its end. -/
def gateSaysUninstrumented : String × String :=
  ("a run of an uninstrumented system that ends unstopped is said uncovered at its end",
   "serve.zig:686-690 (c4f246e: \"One that ended by itself before the gate looked keeps its verdict and gets an `uncovered` file saying the same\"), 783-787 (CE50's exemption: a run from a checkpoint or a fork's snapshot is \"Judged at its end, never stopped as uninstrumented\"); docs/SDKS.md:101-105 (\"A run without coverage is explored blind, so serve does not let one go unnoticed\")")

def gateCounts : String × String :=
  ("the coverage gate judges the run's own first 4 timelines",
   "docs/SDKS.md:101-102 (\"a run whose first 4 ended timelines report none is stopped\"); store.zig:676-680 (sessions are not what the run explored)")

def judgeGate (which : Nat) (w : GW) (source : Source) : Ended :=
  match (drawGate w).run { decisions := { source } } with
  | .ok g s =>
    let v := if which == 3 then
        if !g.instrumented && g.stoppedAt.isNone && !g.labeled && g.rows.length > 0 then
          some (gateSaysUninstrumented.1, s!"an uninstrumented system{if g.fromSnapshot then " run from a machine's checkpoint or a fork's snapshot" else ""}: its {g.rows.length} timelines reported no coverage; never stopped, and its end writes no `uncovered` file: nothing says it ran blind")
        else none
      else if which == 2 then
        if g.labeled && g.instrumented then
          some (gateSays.1, s!"an instrumented system: its setup ran edges {g.setupEdges}{if g.fromSnapshot then " in the snapshot the run starts from (a machine's checkpoint or a fork's: this run's events/setup.jsonl empty)" else ""}, its {g.rows.length} timelines ran {g.edgesRun}, each reporting none (all the setup's): never stopped, but its end writes `uncovered`: \"its system runs without its language's instrumentation ... build its workload with it\"")
        else none
      else if which == 0 then
        if g.stoppedAt.isSome && g.instrumented then
          some (gateProp.1, s!"an instrumented system: its setup ran edges {g.setupEdges}{if g.fromSnapshot then " in the snapshot the run starts from (another run's setup: this run's events/setup.jsonl empty)" else ""}, its first timelines ran {g.edgesRun}, each reporting none (all its setup's): stopped, \"its system runs without its language's instrumentation\"")
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
  for (which, p) in [(0, gateProp), (1, gateCounts), (2, gateSays), (3, gateSaysUninstrumented)] do
    say s!"== serve property: {p.1}"
    say s!"   source: {p.2}"
    for w in [({ label := "an instrumented system, 3 edges, up to 5 timelines", instrumented := some true } : GW),
              { label := "3 edges, up to 5 timelines" },
              { label := "3 edges, up to 5 timelines, sessions opened", sessions := true },
              -- Round 6: a run from a snapshot its setup ran in (another run's), or not.
              { label := "an instrumented system, 3 edges, up to 5 timelines, from a snapshot or not", instrumented := some true, fromSnapshot := none },
              -- Round 7: the same at a7fe05d (CE50 found again).
              { label := "a7fe05d: an instrumented system, 3 edges, up to 5 timelines, from a snapshot or not", instrumented := some true, fromSnapshot := none, ver := .va7fe05d },
              -- Round 8: df8f08b's (CE56 found again), and either system from a snapshot or not.
              { label := "df8f08b: an instrumented system, 3 edges, up to 5 timelines, from a snapshot or not", instrumented := some true, fromSnapshot := none, ver := .vdf8f08b },
              { label := "3 edges, up to 5 timelines, from a snapshot or not", fromSnapshot := none },
              { label := "3939448: an instrumented system, 3 edges, up to 5 timelines", instrumented := some true, ver := .v3939448 },
              { label := "3939448: 3 edges, up to 5 timelines, sessions opened", sessions := true, ver := .v3939448 }] do
      if let some f ← exhaustSaid s!"{p.1} / {w.label}" (judgeGate which w) exhaustRuns then
        printFound f (fun src => match (drawGate w).run { decisions := { source := src } } with
          | .ok g _ => [s!"instrumented {g.instrumented}; setup edges {g.setupEdges}{if g.fromSnapshot then " (in the snapshot the run starts from: its setup.jsonl empty)" else ""}; timelines' edges {g.edgesRun}; rows (session, coverage events) {reprStr g.rows}; stopped at {reprStr g.stoppedAt}"]
          | .error _ _ => [])
  say s!"== serve property: {sessionsProp.1}"
  say s!"   source: {sessionsProp.2}"
  for kind in ["always", "sometimes", "reachable", "always_or_unreachable", "unreachable"] do
    for n in [1, 2, 3] do
      if let some f ← exhaustSaid s!"{sessionsProp.1} / {kind}, {n} timelines" (judgeSessions kind n) exhaustRuns then
        printFound f (fun _ => [])

end Replica.Serve3
