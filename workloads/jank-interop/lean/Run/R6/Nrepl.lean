import Jank.R6.Nrepl.Sim
import Jank.R6.Nrepl.Lazy
import Jank.R6.Nrepl.Theorems
import Jank.R6.Nrepl.StateHash

/-!
# Round 6 driver: the nREPL (`jank6-nrepl <part> ...`)

- `graph NAME MAXSTATES [canon] [check]`: World T scenario NAME's state graph under every schedule,
  and what it decides (final states and their verdicts, step violations, deadlocks, cycles, the
  longest run). `canon`: logs ordered by client (Graph.lean); `check`: the order check.
- `count NAME B1,B2,... MAXSTATES [finals] [canon] [check]`: the graph, what it decides, then the exact
  number of `interleavePB` timelines at each budget, with violations by property.
- `lazy NAME B1,B2,... MAXSTATES SECONDS [canon] [check]`: the same counts with steps run on demand
  (Lazy.lean), for worlds whose whole graph is too large.
- `dfs NAME MAXSTATES SECONDS [canon] [check] [desc]`: every schedule, depth first, states kept as hash
  pairs (StateHash.lean); `desc`: the logs' normal form with clients in decreasing order.
- `cuts NAME B CUTS MAXSTATES`: timelines with at most CUTS partial reads (round 5's `cuts` walk).
- `eintr NAME MAXSTATES`: is `net.read.eintr` unused at every reachable state?
- `reduce MAXSTATES`: T7 against T7w: final states, and the stuttering simulation under α (Sim.lean).
NAME: T1 … T10 (round 3's `tScenarios`); T7w (T7 with whole-message reads: round 5's reduced world);
T3u, T9u (on jank's unlocked capture, R125's two properties set aside); T3f, T9f (unlocked, round 3's
full judge).
-/

open Determinismo Jank.R3.Nrepl Jank.R5.Nrepl Jank.R6.Nrepl Jank.NreplServer

def flushOut : IO Unit := do (← IO.getStdout).flush

/-- `T3u`, `T9u`: T3 and T9 on jank's real capture (no lock), judged without R125's two
properties (Graph.lean `tJudgeNoOut`). -/
def unlocked (name : String) : Bool := name == "T3u" || name == "T9u"

def scenarioOf (name : String) : Option TScenario :=
  if name == "T7w" then some t7Whole
  else if name == "T3f" || name == "T9f" then
    let base := tScenarios.getD (if name == "T3f" then 2 else 8) default
    some { base with name := base.name ++ " — on jank's capture (no lock), round 3's full judge",
                     cfg := { base.cfg with fixCapture := false } }
  else if unlocked name then
    let base := tScenarios.getD (if name == "T3u" then 2 else 8) default
    some { base with name := base.name ++ " — UNLOCKED (jank's capture), R125's properties set aside",
                     cfg := { base.cfg with fixCapture := false } }
  else if name.startsWith "T" then
    match (name.drop 1).toNat? with
    | some k => if 1 ≤ k ∧ k ≤ tScenarios.length then some (tScenarios.getD (k - 1) default) else none
    | none => none
  else none

def fmtNat (n : Nat) : String :=
  let s := (toString n).toList
  let len := s.length
  String.ofList (s.zipIdx.foldr (fun (c, i) acc =>
    if i > 0 && (len - i) % 3 == 0 then ',' :: c :: acc else c :: acc) [])

def buildIO (s : TScenario) (maxStates : Nat) (deadlineS : Nat := 1500) (canon check : Bool := false) : IO (G × Bool) := do
  let t0 ← IO.monoMsNow
  if canon then IO.println s!"  logs ordered by client (canonMem){if check then ", checked against the other order at every state" else ""}"
  let (g, complete) ← build s maxStates (deadlineS * 1000) canon check ((s.name.splitOn "UNLOCKED").length > 1)
  IO.println s!"  graph: {fmtNat g.keys.size} states, {fmtNat g.runs} step runs, {if complete then "complete (every reachable state)" else s!"STOPPED at {fmtNat g.keys.size} states (bound {fmtNat maxStates} or {deadlineS} s)"}; blocked steps that moved: {g.blockedMoves} ({(← IO.monoMsNow) - t0} ms)"
  if check then IO.println s!"  order check: {fmtNat g.checked} (state, thread) steps and final states run with the logs in the other order; {g.checkFails} differ; {g.checkFirstDiffers} final states report another first violation"
  flushOut
  pure (g, complete)

def printReach (g : G) : IO Unit := do
  let t0 ← IO.monoMsNow
  let r := reach g
  IO.println s!"  every schedule: {fmtNat r.states} states; {r.finals.length} final states; acyclic {r.acyclic}; progress self-loops {r.selfLoops}; longest run {r.longest} progress steps"
  IO.println s!"  final states with a violation: {r.finalViol.length}"
  for (i, p, d) in r.finalViol.take 5 do IO.println s!"    state {i}: {p}: {d.take 400}"
  IO.println s!"  step violations: {r.stepViol.length}"
  for (i, p, d) in r.stepViol.take 5 do IO.println s!"    state {i}: {p}: {d.take 400}"
  IO.println s!"  deadlocked states (every live thread blocks): {r.deadlocks.length}"
  for i in r.deadlocks.take 3 do
    IO.println s!"    state {i}: {((tStuck (procOf g.keys[i]! #[])).getD "").take 400}"
  let fps := (r.finals.map fun i => fpMem g.keys[i]!.mem).eraseDups
  IO.println s!"  distinct final fingerprints (round 5's fpMem): {fps.length}"
  IO.println s!"  ({(← IO.monoMsNow) - t0} ms)"
  flushOut

def graphCmd (name : String) (maxStates : Nat) (canon check : Bool := false) : IO Unit := do
  let some s := scenarioOf name | IO.println s!"unknown scenario {name}"
  IO.println s!"== {name}: {s.name}"
  IO.println s!"  cfg: partialReads {s.cfg.partialReads}, eintr {s.cfg.eintr}, fixCapture {s.cfg.fixCapture}, maxSteps {s.cfg.maxSteps}"
  let (g, complete) ← buildIO s maxStates 1500 canon check
  if !complete then return
  printReach g

def printSum (b : Nat) (r : Sum) (memo : Nat) (ms : Nat) (maxSteps : Nat) : IO Unit := do
  IO.println s!"  ≤{b}: {fmtNat r.n} timelines (complete); with every net.read.eintr draw 0: {fmtNat r.n0}; longest: {r.maxIt} iterations (bound {maxSteps}: {if r.maxIt ≤ maxSteps then "never reached" else "REACHED"}), {r.maxDec} decisions; {fmtNat memo} scheduler states ({ms} ms)"
  if r.viol.isEmpty then IO.println "      violations: nothing"
  for (p, a, a0) in r.viol do
    IO.println s!"      {p}: {fmtNat a} (eintr 0: {fmtNat a0})"
    if let some d := r.ex.lookup p then IO.println s!"        e.g. {d.take 400}"
  if !r.finals.isEmpty then
    IO.println s!"      final states reached: {r.finals.length}"
  flushOut

def countCmd (name : String) (budgets : List Nat) (maxStates : Nat) (keepFinals : Bool) (canon check : Bool := false) : IO Unit := do
  let some s := scenarioOf name | IO.println s!"unknown scenario {name}"
  IO.println s!"== {name}: {s.name}: interleavePB timelines counted on the state graph"
  let (g, complete) ← buildIO s maxStates 1500 canon check
  if !complete then return
  printReach g
  for b in budgets do
    let t0 ← IO.monoMsNow
    let (r, memo) := count s g b keepFinals
    printSum b r memo ((← IO.monoMsNow) - t0) s.cfg.maxSteps

def eintrCmd (name : String) (maxStates : Nat) : IO Unit := do
  let some s := scenarioOf name | IO.println s!"unknown scenario {name}"
  IO.println s!"== {name}: is `net.read.eintr` unused with EINTR off? (every reachable state)"
  let (g, complete) ← buildIO s maxStates
  if !complete then return
  let (sites, groups, bad) := eintrCheck s g
  IO.println s!"  {fmtNat sites} (state, thread) steps draw it; {fmtNat groups} groups of branches equal but for its value; {bad} lead to different states or results"
  flushOut

/-- Round 5's reduction, checked by its conclusion: T7 (partial reads) and T7 with whole-message
reads reach the same final states (memory and threads, the config's `partialReads` aside) under
every schedule. -/
def reduceCmd (maxStates : Nat) : IO Unit := do
  let some sc := scenarioOf "T7" | return
  let some sw := scenarioOf "T7w" | return
  IO.println "== T7 against T7 with whole-message reads: final states under every schedule"
  let (gc, cc) ← buildIO sc maxStates
  let (gw, cw) ← buildIO sw maxStates
  if !(cc && cw) then return
  let norm (k : PKey) : PKey := { k with mem := { k.mem with cfg := { k.mem.cfg with partialReads := false } } }
  let fc := (List.range gc.keys.size).filter fun i => (gc.final.getD i none).isSome
  let fw := (List.range gw.keys.size).filter fun i => (gw.final.getD i none).isSome
  IO.println s!"  T7: {fc.length} final states; T7w: {fw.length} final states"
  let missing := fc.filter fun i => !(fw.any fun j => norm gc.keys[i]! == gw.keys[j]!)
  let extra := fw.filter fun j => !(fc.any fun i => norm gc.keys[i]! == gw.keys[j]!)
  IO.println s!"  T7 final states not among T7w's: {missing.length}; T7w's not among T7's: {extra.length}"
  for i in fc do IO.println s!"  T7 final {i} verdict: {(gc.final.getD i none).getD none}"
  let t0 ← IO.monoMsNow
  let o := simCheck gc gw
  IO.println s!"  stuttering simulation under α, every reachable T7 state and step: {fmtNat o.states} states, {fmtNat o.edges} steps: {fmtNat o.stutters} stutter steps, {fmtNat o.matched} matched by a whole-read step, {o.unmatched} unmatched; α of a state outside the whole-read world: {o.unreached}; final states: {o.finalsOk} with the same verdict, {o.finalsBad} not ({(← IO.monoMsNow) - t0} ms)"
  if let some b := o.firstBad then
    IO.println s!"  FIRST FAILURE: {b}"
    for l in simDebug gc gw do IO.println s!"    {l.take 1500}"
  flushOut

/-- Counts at each budget with the steps run on demand (Lazy.lean), each budget its own walk. -/
def lazyCmd (name : String) (budgets : List Nat) (maxStates secs : Nat) (canon check : Bool) : IO Unit := do
  let some s := scenarioOf name | IO.println s!"unknown scenario {name}"
  IO.println s!"== {name}: {s.name}: interleavePB timelines counted with steps run on demand"
  if canon then IO.println s!"  logs ordered by client (canonMem){if check then ", checked against the other order at every step taken" else ""}"
  let t00 ← IO.monoMsNow
  for b in budgets do
    let t0 ← IO.monoMsNow
    let left := secs * 1000 - min (secs * 1000) (t0 - t00)
    let c : LCfg := { s, canon, check, noOut := (s.name.splitOn "UNLOCKED").length > 1, maxStates, deadline := t0 + left }
    let (r, st) ← countLazy c b
    if st.stopped then
      IO.println s!"  ≤{b}: STOPPED (bound {fmtNat maxStates} states or the time left, {left / 1000} s): {fmtNat st.keys.size} states, {fmtNat st.memo.size} scheduler states ({(← IO.monoMsNow) - t0} ms)"
      flushOut
      return
    IO.println s!"  ≤{b}: {fmtNat st.keys.size} states reached, {fmtNat st.runs} step runs"
    if check then IO.println s!"      order check: {fmtNat st.checked} steps and final states run with the logs in the other order; {st.checkFails} differ; {st.checkFirstDiffers} final states report another first violation"
    printSum b r st.memo.size ((← IO.monoMsNow) - t0) s.cfg.maxSteps

def dfsCmd (name : String) (maxStates secs : Nat) (canon check : Bool) (desc : Bool := false) : IO Unit := do
  let some s := scenarioOf name | IO.println s!"unknown scenario {name}"
  IO.println s!"== {name}: {s.name}: every schedule, depth first, states kept as 64+64-bit hash pairs (StateHash.lean)"
  if canon then IO.println s!"  logs ordered by client ({if desc then "clients in decreasing order" else "canonMem"}){if check then ", checked against the other order at every state expanded" else ""}"
  let t0 ← IO.monoMsNow
  let o ← dfsReach s canon check ((s.name.splitOn "UNLOCKED").length > 1) maxStates (secs * 1000) desc
  IO.println s!"  {if o.stopped then "STOPPED (state or time bound)" else "complete"}: {fmtNat o.states} states seen, {fmtNat o.expanded} expanded, {fmtNat o.runs} step runs, deepest stack {o.maxStack} ({(← IO.monoMsNow) - t0} ms)"
  if check then IO.println s!"  order check: {fmtNat o.checked} (state, thread) steps run with the logs in the other order; {o.checkFails} differ"
  IO.println s!"  final states: {fmtNat o.finals} reached ({o.finalKeys.size} distinct hash pairs); with a violation: {o.finalViol}; step violations: {o.stepViol}; deadlocked states: {o.deadlocks}; blocked steps that moved: {o.blockedMoves}"
  IO.println s!"  collision bound: a uniform 64-bit hash over {fmtNat o.states} states collides with probability below {(o.states * o.states * 1000000000000) / 36893488147419103232}·10⁻¹² (n²/2⁶⁵)"
  for e in o.examples.take 5 do IO.println s!"    {e}"
  flushOut

def main (args : List String) : IO Unit := do
  match args with
  | "graph" :: n :: m :: flags => graphCmd n m.toNat! (flags.contains "canon") (flags.contains "check")
  | "count" :: n :: bs :: m :: flags =>
    countCmd n ((bs.splitOn ",").map String.toNat!) m.toNat! (flags.contains "finals") (flags.contains "canon") (flags.contains "check")
  | "lazy" :: n :: bs :: m :: secs :: flags =>
    lazyCmd n ((bs.splitOn ",").map String.toNat!) m.toNat! secs.toNat! (flags.contains "canon") (flags.contains "check")
  | "dfs" :: n :: m :: secs :: flags => dfsCmd n m.toNat! secs.toNat! (flags.contains "canon") (flags.contains "check") (flags.contains "desc")
  | ["cuts", n, b, c, m] =>
    let some s := scenarioOf n | IO.println s!"unknown scenario {n}"
    IO.println s!"== {n}: timelines with at most {c} partial reads (round 5's `cuts` walk), counted on the state graph"
    let (g, complete) ← buildIO s m.toNat!
    if complete then
      let t0 ← IO.monoMsNow
      let (r, memo) := count s g b.toNat! true (some c.toNat!)
      printSum b.toNat! r memo ((← IO.monoMsNow) - t0) s.cfg.maxSteps
  | ["eintr", n, m] => eintrCmd n m.toNat!
  | ["reduce", m] => reduceCmd m.toNat!
  | _ => IO.println "usage: jank6-nrepl graph NAME MAXSTATES [canon] [check] | count NAME B1,B2,.. MAXSTATES [finals] [canon] [check] | lazy NAME B1,.. MAXSTATES SECONDS [canon] [check] | dfs NAME MAXSTATES SECONDS [canon] [check] [desc] | cuts NAME B CUTS MAXSTATES | eintr NAME MAXSTATES | reduce MAXSTATES"
