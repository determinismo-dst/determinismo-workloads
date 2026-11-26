import Jank.R8.Nrepl.Diverge
import Jank.R8.Nrepl.Walk

/-!
# Round 8 driver: the nREPL (`jank8-nrepl <part> ...`)

- `exact NAME B MAXSTATES SECONDS [slow] [raw]`: World T scenario NAME's every-schedule graph with the
  compact codec (Exact.lean), what it decides (final states and verdicts, step violations, deadlocks,
  acyclic, the longest progress path), then the combo graph and the exact `interleavePB` counts at
  ≤0 … ≤B. `slow`: no pointer fast path (every component hashed and compared); `raw`: logs not
  ordered by client.
NAME: T1 … T10 (round 3's `tScenarios`), T7w, T3u, T9u (unlocked, R125's two properties set aside),
T3f, T9f (unlocked, round 3's full judge).
-/

open Determinismo Jank.R3.Nrepl Jank.R5.Nrepl Jank.R6.Nrepl Jank.R8.Nrepl Jank.NreplServer

def flushOut : IO Unit := do (← IO.getStdout).flush

/-- Round 6's driver's scenario names (Run/R6/Nrepl.lean `scenarioOf`). -/
def unlocked (name : String) : Bool := name == "T3u" || name == "T9u"

/-- Small worlds for comparing the counter with the sdk's own walk (`walk`): W1 one client cloning,
W2 one client cloning and describing, W3 two clients cloning (whole reads, EINTR off). -/
def smallWorlds : List (String × List (List TReq)) :=
  [("W1", [[.clone]]), ("W2", [[.clone, .describe]]), ("W3", [[.clone], [.clone]])]

def scenarioOf (name : String) : Option TScenario :=
  if let some sc := smallWorlds.lookup name then
    some { name := s!"{name}: small world for the walk check", cfg := { partialReads := false }, aside := allAside, scripts := sc }
  else if name == "T7w" then some t7Whole
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

def exactCmd (name : String) (B maxStates secs : Nat) (fast canon : Bool) (check : Bool := false) : IO Unit := do
  let some s := scenarioOf name | IO.println s!"unknown scenario {name}"
  let noOut := unlocked name
  IO.println s!"== {name}: {s.name}"
  IO.println s!"  every schedule, exact (compact codec), logs {if canon then "ordered by client (canonMem)" else "as they are"}, fast path {if fast then "on (pointer identity)" else "off (every component hashed and compared)"}"
  flushOut
  let t0 ← IO.monoMsNow
  let (g, T, complete) ← exactGraph s canon noOut fast maxStates (secs * 1000) (fun i n => do
    IO.println s!"    … {fmtNat i} expanded, {fmtNat n} found ({(← IO.monoMsNow) - t0} ms)"
    flushOut) tStep check
  if check then
    IO.println s!"  order check (round 6's): {fmtNat g.checked} (state, thread) steps and final states also run with the logs in the other order; {g.checkFails} differ; {g.checkFirstDiffers} final states report another first violation"
  let t1 ← IO.monoMsNow
  IO.println s!"  graph: {fmtNat g.size} states, {fmtNat g.runs} step runs, {fmtNat g.edges.size} edges, {if complete then "COMPLETE (every reachable state)" else s!"STOPPED at {fmtNat g.eoff.size} expanded (bound {fmtNat maxStates} states or {secs} s)"} ({t1 - t0} ms)"
  IO.println s!"  tables: jw {T.jw.vals.size}, fds {T.fds.vals.size}, temps {T.temps.vals.size}, socks {T.socks.vals.size}, misc {T.misc.vals.size}, replies {T.replies.vals.size}, logs {T.logs.vals.size}, threads {T.th.vals.size}; fast-path components {fmtNat g.fastHits}; most threads {g.maxThreads}"
  IO.println s!"  final states: {g.finals.size}; with a violation: {g.finalViol.size}; step violations: {g.stepViol.size}; deadlocked states: {g.deadlocks.size}; blocked steps that moved: {g.blockedMoves}; progress self-loops: {g.progressSelf}"
  for (i, p, d) in g.finalViol.toList.take 5 do IO.println s!"    final {i}: {p}: {d.take 300}"
  for (i, p, d) in g.stepViol.toList.take 5 do IO.println s!"    step at {i}: {p}: {d.take 300}"
  flushOut
  if !complete then return
  let (longest, acyclic) := g.longest
  IO.println s!"  acyclic (progress steps): {acyclic}; longest progress path: {longest} steps ({(← IO.monoMsNow) - t1} ms)"
  flushOut
  let t2 ← IO.monoMsNow
  if B == 0 then
    let t4 ← IO.monoMsNow
    let (n, memo) := interCount g
    IO.println s!"  the sdk's interleave (thread.next at every step, no preemption bound): {fmtNat n} timelines, {fmtNat memo} (state, blocked) pairs ({(← IO.monoMsNow) - t4} ms)"
    flushOut
    return
  let (cg, cdone) ← comboGraph g 60000000 (t0 + secs * 1000)
  IO.println s!"  scheduler states (state, cur, blocked) any budget reaches: {fmtNat cg.keys.size}, {fmtNat cg.ce.size} entries, {if cdone then "complete" else "STOPPED"} ({(← IO.monoMsNow) - t2} ms)"
  flushOut
  if !cdone then return
  let t3 ← IO.monoMsNow
  let (_, longestIt) ← countLayers { cg with index := {}, keys := #[] } B fun L o => do
    IO.println s!"  ≤{L}: {fmtNat o.n} timelines (complete); eintr draws all 0: {fmtNat o.n0}; with a violation: {fmtNat o.v} ({(← IO.monoMsNow) - t3} ms)"
    flushOut
  IO.println s!"  longest timeline under any budget: {longestIt} step attempts (round 3's bound: {s.cfg.maxSteps}: {if longestIt ≤ s.cfg.maxSteps then "never reached" else "REACHED"})"
  flushOut

/-- World T8 (Diverge.lean): the graph under every schedule, and each quiescent or final state's
replies, by request id. -/
def divCmd (k maxStates secs : Nat) (canon : Bool) : IO Unit := do
  let some s := dScenarios[k]? | IO.println s!"no scenario D{k + 1}"
  IO.println s!"== {s.name}"
  IO.println s!"  cfg: fixCapture {s.cfg.fixCapture}; every schedule, exact (compact codec), World T8's step (t8Step)"
  flushOut
  let t0 ← IO.monoMsNow
  let (g, T, complete) ← exactGraph s canon false true maxStates (secs * 1000) (fun i n => do
    IO.println s!"    … {fmtNat i} expanded, {fmtNat n} found ({(← IO.monoMsNow) - t0} ms)"; flushOut) t8Step
  IO.println s!"  graph: {fmtNat g.size} states, {fmtNat g.runs} step runs, {if complete then "COMPLETE" else "STOPPED"} ({(← IO.monoMsNow) - t0} ms)"
  IO.println s!"  final states: {g.finals.size} ({g.finalViol.size} with a violation of round 3's judge); step violations: {g.stepViol.size}; states where every thread only blocks: {g.deadlocks.size}; progress self-loops (a spinning eval): {g.progressSelf}; blocked steps that moved: {g.blockedMoves}"
  for (i, p, d) in g.finalViol.toList.take 3 do IO.println s!"    final {i}: {p}: {d.take 300}"
  for (i, p, d) in g.stepViol.toList.take 3 do IO.println s!"    step at {i}: {p}: {d.take 300}"
  if !complete then return
  let mut seen : Std.HashMap String Nat := {}
  let mut quiet := 0
  for i in [0:g.size] do
    if g.quiet i then
      quiet := quiet + 1
      if let some k := g.decode T i then
        let line := (if (g.eoff.getD i 0) == (g.eoff.getD (i + 1) g.edges.size) then "FINAL " else if g.deadlocks.contains i then "STUCK " else "QUIESCENT ") ++ census k.mem
        seen := seen.insert line (seen.getD line 0 + 1)
  IO.println s!"  quiescent or final states: {quiet}; distinct outcomes: {seen.size}"
  for (l, n) in seen.toList do IO.println s!"    {n} × {l}"
  flushOut

/-- The exact count at each budget, with states expanded on demand (Exact.lean `countBounded`). -/
def boundedCmd (name : String) (budgets : List Nat) (maxStates maxCombos secs : Nat) : IO Unit := do
  let some s := scenarioOf name | IO.println s!"unknown scenario {name}"
  let noOut := unlocked name
  IO.println s!"== {name}: {s.name}"
  IO.println s!"  interleavePB timelines at each budget, states expanded on demand (compact codec), logs ordered by client"
  flushOut
  let t00 ← IO.monoMsNow
  for b in budgets do
    let t0 ← IO.monoMsNow
    let (o, lb, ncombos, complete) ← countBounded s b true noOut true maxStates maxCombos (t00 + secs * 1000)
    if !complete then
      IO.println s!"  ≤{b}: STOPPED (bound {fmtNat maxStates} states, {fmtNat maxCombos} scheduler states or the time): {fmtNat lb.g.size} states, {fmtNat ncombos} scheduler states ({(← IO.monoMsNow) - t0} ms)"
      flushOut
      return
    IO.println s!"  ≤{b}: {fmtNat o.n} timelines (complete); eintr draws all 0: {fmtNat o.n0}; with a violation: {fmtNat o.v}; {fmtNat lb.g.size} states reached, {fmtNat lb.g.runs} step runs, {fmtNat ncombos} scheduler states; final states {lb.g.finals.size} ({lb.g.finalViol.size} with a violation), step violations {lb.g.stepViol.size} ({(← IO.monoMsNow) - t0} ms)"
    for (i, p, d) in lb.g.finalViol.toList.take 3 do IO.println s!"    final {i}: {p}: {d.take 300}"
    for (i, p, d) in lb.g.stepViol.toList.take 3 do IO.println s!"    step at {i}: {p}: {d.take 300}"
    flushOut

/-- World T8 at one budget, states expanded on demand, the spinning step reported as blocked
(`t8StepB`): every quiescent state the schedules with at most B preemptions reach, with its replies. -/
def divbCmd (k b maxStates maxCombos secs : Nat) : IO Unit := do
  let some s := dScenarios[k]? | IO.println s!"no scenario D{k + 1}"
  IO.println s!"== {s.name}"
  IO.println s!"  cfg: fixCapture {s.cfg.fixCapture}; ≤{b} preemptions, states expanded on demand, the spinning eval's step reported as blocked (t8StepB)"
  flushOut
  let t0 ← IO.monoMsNow
  let (o, lb, nc, complete) ← countBounded s b true false true maxStates maxCombos (t0 + secs * 1000) t8StepB
  IO.println s!"  {if complete then "COMPLETE" else "STOPPED"}: {fmtNat lb.g.size} states, {fmtNat lb.g.runs} step runs, {fmtNat nc} scheduler states; timelines {fmtNat o.n}, ending where nothing but the spinning eval can move: {fmtNat o.v}; final states {lb.g.finals.size} ({lb.g.finalViol.size} with a violation of round 3's judge); step violations {lb.g.stepViol.size} ({(← IO.monoMsNow) - t0} ms)"
  for (i, p, d) in lb.g.finalViol.toList.take 3 do IO.println s!"    final {i}: {p}: {d.take 300}"
  for (i, p, d) in lb.g.stepViol.toList.take 3 do IO.println s!"    step at {i}: {p}: {d.take 300}"
  let mut seen : Std.HashMap String Nat := {}
  for i in lb.g.deadlocks.toList ++ lb.g.finals.toList do
    if let some k := lb.g.decode lb.T i then
      let line := (if lb.g.finals.contains i then "FINAL " else "QUIESCENT ") ++ census k.mem
      seen := seen.insert line (seen.getD line 0 + 1)
  IO.println s!"  quiescent or final states: {lb.g.deadlocks.size + lb.g.finals.size}; distinct outcomes: {seen.size}"
  for (l, n) in seen.toList do IO.println s!"    {n} × {l}"
  flushOut

/-- The sdk's own exhaustive walk (Search.lean `exhaust`) over round 3's `runT` (the sdk's `interleave`),
to compare with `exact NAME 0` (the same count on the state graph). -/
def walkCmd (name : String) (maxRuns : Nat) : IO Unit := do
  let some s := scenarioOf name | IO.println s!"unknown scenario {name}"
  IO.println s!"== {name}: {s.name}: the sdk's exhaust over runT (interleave), every timeline, up to {fmtNat maxRuns}"
  flushOut
  let t0 ← IO.monoMsNow
  let run : Source → Ended := fun src => (runT s.cfg s.aside s.scripts src).1
  match exhaust run maxRuns with
  | .complete n => IO.println s!"  complete: {fmtNat n} timelines, no violation ({(← IO.monoMsNow) - t0} ms)"
  | .stopped n => IO.println s!"  STOPPED at {fmtNat n} timelines ({(← IO.monoMsNow) - t0} ms)"
  | .found c => IO.println s!"  violation after {fmtNat c.runs} timelines: {c.property}: {c.detail.take 300}"
  flushOut

/-- The sdk's exhaust over round 3's `runTWith (some b)` (interleavePB at ≤ b), to compare with the
layered counter (`exact NAME B`). -/
def walkPBCmd (name : String) (b maxRuns : Nat) : IO Unit := do
  let some s := scenarioOf name | IO.println s!"unknown scenario {name}"
  IO.println s!"== {name}: {s.name}: the sdk's exhaust over runTWith ≤{b} (interleavePB), up to {fmtNat maxRuns}"
  flushOut
  let t0 ← IO.monoMsNow
  let run : Source → Ended := fun src => (runTWith (some b) s.cfg s.aside s.scripts src).1
  match exhaust run maxRuns with
  | .complete n => IO.println s!"  ≤{b}: complete: {fmtNat n} timelines, no violation ({(← IO.monoMsNow) - t0} ms)"
  | .stopped n => IO.println s!"  ≤{b}: STOPPED at {fmtNat n} timelines ({(← IO.monoMsNow) - t0} ms)"
  | .found c => IO.println s!"  ≤{b}: violation after {fmtNat c.runs} timelines: {c.property}: {c.detail.take 300}"
  flushOut

def main (args : List String) : IO Unit := do
  match args with
  | "exact" :: n :: b :: m :: secs :: flags =>
    exactCmd n b.toNat! m.toNat! secs.toNat! (!flags.contains "slow") (!flags.contains "raw") (flags.contains "check")
  | ["bounded", n, bs, m, mc, secs] =>
    boundedCmd n ((bs.splitOn ",").map String.toNat!) m.toNat! mc.toNat! secs.toNat!
  | ["divb", k, b, m, mc, secs] => divbCmd (k.toNat! - 1) b.toNat! m.toNat! mc.toNat! secs.toNat!
  | ["walk", n, m] => walkCmd n m.toNat!
  | ["walkpb", n, b, m] => walkPBCmd n b.toNat! m.toNat!
  | "div" :: k :: m :: secs :: flags => divCmd (k.toNat! - 1) m.toNat! secs.toNat! (!flags.contains "raw")
  | _ => IO.println "usage: jank8-nrepl exact NAME B MAXSTATES SECONDS [slow] [raw] | div K MAXSTATES SECONDS [raw]"
