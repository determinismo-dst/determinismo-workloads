import Replica.Verdicts

/-!
# A resumed run's verdict at 62e06e3, and serve's view of its end (round 5)

CE29's fix (src/main.zig, src/report.zig, 62e06e3):
- each timeline's record line keeps its properties (report.zig:28-45 `Recorded`, 513-531): those
  it evaluated (`hits > 0`), in its table's order, while their estimated size (`name.len + 128`
  bytes each) fits `recorded_bytes_max` (40 KiB); past it `properties_all` is false;
- `resume_read` (main.zig:2170-2176) collects them; `Resumed.merge_into` (2030-2036) merges the
  recorded timelines' into the resumed run's multiverse (report.zig:593-608 `recorded_merge`), so
  they count in its verdict as its own timelines' do (2828-2829);
- when every timeline is recorded, "the run is complete" (2212-2229): judged from the record alone
  by `failing_properties` (report.zig:458-464), its `exit` written, the process ended. Its comment:
  "A catalog's assertions no timeline reached are judged by the runs that ran timelines."
- otherwise the resumed run explores the rest and `system_run` judges as any run (main.zig:1104-1178:
  the scenario's failing violations, its unmet sometimes, the catalog across scenarios).

What a run's verdict is (the uninterrupted run's): `Verdicts.explorerExit` over all its timelines.

The model: one scenario's timelines (assertion lines: declarations and evaluations, as
Verdicts'), the stop after `recorded` of them had their record lines (a flat run's order), each
line's room in properties (the 40 KiB as a count of entries).

Serve (src/serve.zig, 62e06e3): `ended_status` (5903-5909) reads the explorer's `exit`, else the
record's last summary; discovery (5756) and an adopted run's reap (6017) use it. `runs_adopt`
(5803-5818), for a run resumed from a command line (the explorer's `runs.adopt_note`, main.zig:
1287-1294) whose explorer ended before serve's watcher looked, deletes `exit` with the run's
other end notes (5808-5811) and takes `recorded_status(record)` (5815).
-/

namespace Replica.Resume5

open Determinismo
open Replica.Verdicts

/-- report.zig:513-531: the properties a record line keeps, at most `room` of them, and whether
it kept them all (`properties_all`). -/
def recordedOf (props : Array Property) (room : Nat) : List Property × Bool := Id.run do
  let mut kept : List Property := []
  let mut all := true
  for p in props do
    if p.hits == 0 then continue
    if kept.length ≥ room then
      all := false
      continue
    kept := kept ++ [p]
  return (kept, all)

/-- The aggregates the resumed run starts with: each recorded timeline's kept properties
(main.zig:2030-2036 `merge_into`; report.zig:593-608). -/
def recordedAggs (ts : List Timeline) (room : Nat) : Except String (Array Aggregate) := do
  let mut aggs : Array Aggregate := #[]
  for t in ts do
    let props ← timelineProps t
    for p in (recordedOf props room).1 do aggs := merge aggs p
  return aggs

/-- One scenario's exit from its aggregates, as `system_run` judges (main.zig:1104-1178): a
scenario with failing violations fails; else its unmet sometimes against the catalog; then the
catalog (every scenario explored). -/
def exitOfAggs (aggs : Array Aggregate) : Nat := Id.run do
  let cat := catalogReached [] aggs
  if failingViolations aggs > 0 then return 3
  if (sometimesUnmet aggs).any (!catalogMadeTrue cat ·) then return 3
  if catalogJudge cat true > 0 then return 3
  return 0

/-- The resumed run's exit (62e06e3): complete, `failing_properties` over the record; else the
recorded merged first, the rest explored, judged as any run. 3939448's (round 3's CE29): complete,
0; else the rest alone. -/
def resumedExit (ver : Ver) (ts : List Timeline) (recorded room : Nat) (ended : Bool := true) : Except String Nat := do
  let rest := ts.drop recorded
  if ver == .v3939448 then
    if rest.isEmpty then return 0
    return ← explorerExit [rest] 1
  -- a7fe05d (report.zig:51-78, 551-588): a record line of any size written whole, every
  -- property it evaluated in it (CE46's fix): no room.
  let room := if ver.sinceA7 then 1000000 else room
  let mut aggs ← recordedAggs (ts.take recorded) room
  if rest.isEmpty then
    -- df8f08b (main.zig:1170-1175, 2297, 2147-2154; CE45's fix): a run that reached its end
    -- recorded its catalog's verdict (`{"catalog":{"failing":n}}`), and the complete resume
    -- judges it with the timelines' properties. A stop after the last timeline's line and
    -- before the end (`ended` false) left no such line.
    let catalogFailing ← if ver.sinceDf && ended then do
        let all ← multiverse ts
        pure (catalogJudge (catalogReached [] all) true)
      else pure 0
    return if aggs.any (·.failing) || catalogFailing > 0 then 3 else 0
  for t in rest do
    let props ← timelineProps t
    for p in props do aggs := merge aggs p
  return exitOfAggs aggs

structure S where
  decisions : Decisions := {}
  deriving Inhabited

instance : Chaotic S where
  decisions s := s.decisions
  setDecisions _ d := { decisions := d }

/-- Round 6: a run whose numbers a session's timeline took one of (tape.claim_next: a session on
a running run takes the next free number; the explorer passes it over, main.zig:3539-3542,
4658-4664). `resume_read` (main.zig:2196-2199) skips a line that extends a timeline, so that
number is never `done`, and the run is never "complete" (2241-2243): resumed, it goes the
explorer's way, passes the number over again, runs what is left of its own (possibly nothing),
and judges the catalog of the aggregates it has: the recorded ones (main.zig:2865) and the
timelines it ran. -/
def resumedExitWithSession (ver : Ver) (ts : List Timeline) (recorded room : Nat) (session : Bool) (ended : Bool := true) : Except String Nat := do
  if !session || ver == .v3939448 then return ← resumedExit ver ts recorded room ended
  let room := if ver.sinceA7 then 1000000 else room
  let mut aggs ← recordedAggs (ts.take recorded) room
  for t in ts.drop recorded do
    let props ← timelineProps t
    for p in props do aggs := merge aggs p
  return exitOfAggs aggs

structure World where
  label : String
  menu : List AEvent
  timelines : Nat := 2
  lines : Nat := 2
  rooms : List Nat := [1000]
  ver : Ver := .vdf8f08b
  /-- Round 6: a session's timeline may take one of the run's numbers. -/
  sessions : Bool := false
  /-- Round 7: whether a complete record's run reached its end before its stop, drawn (else it
  did: a complete run resumed again). -/
  endedDrawn : Bool := false

structure Drawn where
  ts : List Timeline
  recorded : Nat
  room : Nat
  session : Bool := false
  /-- Round 7: a complete record's run reached its end before the stop (its catalog line written). -/
  ended : Bool := true
  deriving Inhabited

def draw (w : World) : EStateM Stop S Drawn := do
  let mut ts := []
  for _ in [0:w.timelines] do
    let mut evs := []
    for _ in [0:w.lines] do evs := evs ++ [w.menu[(← below "world.assertion" w.menu.length)]!]
    ts := ts ++ [{ scenario := 0, events := evs : Timeline }]
  let recorded ← below "world.recorded" (w.timelines + 1)
  let room := w.rooms[(← below "world.room" w.rooms.length)]!
  let session ← if w.sessions then do pure ((← below "world.session_takes_a_number" 2) == 1) else pure false
  let ended ← if w.endedDrawn && recorded == w.timelines then do pure ((← below "world.run_reached_its_end" 2) == 1) else pure true
  return { ts, recorded, room, session, ended }

def property : String := "a resumed run's verdict is the run's: its timelines' and its catalog's, as it would have ended uninterrupted"
def source : String := "src/main.zig:2023-2025 (62e06e3, Resumed.recorded: \"counted in the resumed run's verdict as its own timelines' are\"), 2828 (\"A resumed run's recorded timelines count in its verdict as its own do (CE29)\"), 2213-2215 (\"Judged from its record, as the run that recorded it would have been\"); serve.zig:5630-5633 (run_resume: \"Continues a run that ended before its end\"); README_AI.md (a run's exit status)"

def judge (w : World) (src : Source) : Ended :=
  match (draw w).run { decisions := { source := src } } with
  | .ok d s =>
    let whole := explorerExit [d.ts] 1
    let resumed := resumedExitWithSession w.ver d.ts d.recorded d.room d.session d.ended
    let v := match whole, resumed with
      | .ok a, .ok b => if a == b then none else
          some (property, s!"timelines {reprStr (d.ts.map (·.events))}{if d.session then ", a session's timeline holding one of the run's numbers" else ""}; stopped after {d.recorded} record lines (a line's room: {d.room} properties); uninterrupted the run exits {a}, resumed {b}")
      | _, _ => none
    { taken := s.decisions.taken, violation := v }
  | .error _ s => { taken := s.decisions.taken, violation := none }

def story (w : World) (src : Source) : List String :=
  match (draw w).run { decisions := { source := src } } with
  | .ok d _ =>
    (d.ts.zipIdx.map fun (t, i) =>
      let kept := match timelineProps t with
        | .ok props => let (k, all) := recordedOf props d.room; s!"its record line keeps {k.map fun p => (p.kind.name, p.name, p.hits, p.trues)}{if all then "" else " (properties_all false)"}"
        | .error e => e
      s!"timeline {i}: {reprStr t.events}; {if i < d.recorded then kept else "not recorded: run again on resume"}") ++
    [s!"uninterrupted: exit {reprStr (explorerExit [d.ts] 1)}",
     s!"resumed ({if d.recorded == d.ts.length && !d.session then "complete: judged from the record alone" else if d.recorded == d.ts.length then "not complete (the session's number is no record line of the run's): explored, nothing left to run, the recorded aggregates judged" else "the rest explored"}): exit {reprStr (resumedExitWithSession w.ver d.ts d.recorded d.room d.session d.ended)}"]
  | .error _ _ => []

def worlds : List World :=
  [ { label := "two timelines, an always evaluated, a sometimes evaluated (true or not)",
      menu := [.eval .always "a" true, .eval .always "a" false, .eval .sometimes "s" true, .eval .sometimes "s" false] },
    { label := "two timelines, a reachable declared (the catalog) and reached or not, an always",
      menu := [.declare .reachable "r", .eval .reachable "r" true, .eval .always "a" true, .eval .always "a" false] },
    { label := "two timelines, two always each evaluated, a record line's room of 1 or 1,000 properties",
      menu := [.eval .always "a" true, .eval .always "b" true, .eval .always "b" false], rooms := [1, 1000] },
    { label := "3939448: two timelines, an always evaluated, a sometimes evaluated", ver := .v3939448,
      menu := [.eval .always "a" true, .eval .always "a" false, .eval .sometimes "s" true, .eval .sometimes "s" false] },
    { label := "62e06e3: two timelines, two always each evaluated, a record line's room of 1 or 1,000 properties", ver := .v62e06e3,
      menu := [.eval .always "a" true, .eval .always "b" true, .eval .always "b" false], rooms := [1, 1000] },
    -- Round 6: a session's timeline holding one of the run's numbers.
    { label := "two timelines, a reachable declared and reached or not, an always; a session may hold a number",
      menu := [.declare .reachable "r", .eval .reachable "r" true, .eval .always "a" true, .eval .always "a" false],
      sessions := true },
    -- Round 7: a7fe05d's catalog world (CE45 found again), and df8f08b's with the stop drawn
    -- before or after the run's end.
    { label := "a7fe05d: two timelines, a reachable declared (the catalog) and reached or not, an always", ver := .va7fe05d,
      menu := [.declare .reachable "r", .eval .reachable "r" true, .eval .always "a" true, .eval .always "a" false] },
    { label := "two timelines, a reachable declared and reached or not, an always; a complete record's run stopped before or after its end",
      menu := [.declare .reachable "r", .eval .reachable "r" true, .eval .always "a" true, .eval .always "a" false],
      endedDrawn := true } ]

/-- serve.zig:5803-5818 `runs_adopt` (62e06e3) for a command-line resume whose explorer ended
before serve's watcher looked: its `exit` deleted, the record's summary read. The record's
summaries: the interrupted run's (when it wrote one before its stop) and the resumed explorer's
(written when it explored the rest: report.zig `record_summary`, its multiverse's `failing`
flags, no catalog); a complete resume writes none. -/
def adoptedStatus (ts : List Timeline) (recorded : Nat) (summaryBeforeStop : Bool) (ver : Ver := .vdf8f08b) : Except String Nat := do
  -- a7fe05d (serve.zig:5836-5851; main.zig:1293-1297): the resumed explorer removed its last
  -- end's `exit` as it began, runs_adopt keeps the one it wrote: ended_status reads it (CE47's fix).
  if ver.sinceA7 then return ← resumedExit ver ts recorded 1000000
  let rest := ts.drop recorded
  if rest.isEmpty then
    -- The record's last summary: the interrupted run's, if any (serve.zig:5939-5951; 255 none).
    if summaryBeforeStop then return ← recordedStatus ts
    return 255
  recordedStatus ts

def searchAll (exhaustRuns : Nat) : IO Unit := do
  say s!"== resume property: {property}"
  say s!"   source: {source}"
  for w in worlds do
    if let some f ← exhaustSaid s!"{property} / {w.label}" (judge w) exhaustRuns then
      printFound f (story w)

end Replica.Resume5
