import Jank.R9.Nrepl.Runs
import Jank.R9.Nrepl.Store
import Jank.R9.Nrepl.TreeCheck

/-!
# Round 9 driver: the nREPL (`jank9-nrepl <part> ...`)

- `fix NAME MAXSTATES SECONDS [stock] [noq1] [noq2] [nov37i]`: World TQ (the fixes Q1, Q2, V37i in
  World T, Jank/R9/Nrepl/Fix.lean) under every schedule for scenario NAME (T9, T3, D3q, D3b, D3c,
  D3d, I1, D1q), with round 3's judge, the protocol for every request, and the replies holding only
  an id and a session at every final and quiescent state. `stock`: round 3's step instead.
-/

open Determinismo Jank.R3.Nrepl Jank.R6.Nrepl Jank.R8.Nrepl Jank.R9.Nrepl Jank.NreplServer

/-- T9, T3 (round 3's, capture locked) and T9u, T3u (jank's capture, R125's properties set aside). -/
def flatScenario (name : String) : Option (TScenario × Bool) :=
  let base (k : Nat) := tScenarios.getD k default
  match name with
  | "T9" => some (base 8, false)
  | "T3" => some (base 2, false)
  | "T9u" => some ({ base 8 with cfg := { (base 8).cfg with fixCapture := false } }, true)
  | "T3u" => some ({ base 2 with cfg := { (base 2).cfg with fixCapture := false } }, true)
  | _ => none

def flatCmd (name : String) (logCap maxStates secs : Nat) : IO Unit := do
  let some (s, noOut) := flatScenario name | IO.println s!"unknown scenario {name}"
  let w := 7 + 1 + 2 * s.scripts.length
  IO.println s!"== {name}: {s.name}{if noOut then " — UNLOCKED (jank's capture), R125's properties set aside" else ""}"
  IO.println s!"  every schedule, exact, flat store ({w} UInt32 per state, table 2^{logCap} slots), logs ordered by client, no edges kept"
  flushOut
  let t0 ← IO.monoMsNow
  let o ← flatSearch s noOut w logCap maxStates (secs * 1000) tStep (fun i n => do
    IO.println s!"    … {fmtN i} expanded, {fmtN n} found ({(← IO.monoMsNow) - t0} ms)"; flushOut)
  IO.println s!"  {if o.complete then "COMPLETE" else "STOPPED"}: {fmtN o.states} states found, {fmtN o.expanded} expanded, {fmtN o.runs} step runs ({(← IO.monoMsNow) - t0} ms)"
  IO.println s!"  final states: {o.finals} ({o.finalViol} with a violation); step violations: {o.stepViol}; deadlocked states: {o.deadlocks}; blocked steps that moved: {o.blockedMoves}; progress self-loops: {o.progressSelf}; most threads: {o.maxThreads}; codes wider than the store: {o.overWidth}"
  for e in o.examples do IO.println s!"    {e}"
  flushOut

/-- Round 8's small worlds (Run/R8/Nrepl.lean `smallWorlds`) and round 3's T9, T9u, T3. -/
def treeWorld (name : String) : Option TScenario :=
  match name with
  | "W1" => some { name := "W1 one client cloning", cfg := { partialReads := false }, aside := allAside, scripts := [[.clone]] }
  | "W2" => some { name := "W2 one client cloning and describing", cfg := { partialReads := false }, aside := allAside, scripts := [[.clone, .describe]] }
  | "W3" => some { name := "W3 two clients cloning", cfg := { partialReads := false }, aside := allAside, scripts := [[.clone], [.clone]] }
  | n => (flatScenario n).map (·.1)

/-- `Tree.checkTreelike` over round 3's `runTWith` (budget b, or the sdk's `interleave` when b is "all"). -/
def treeCmd (name : String) (b : Option Nat) (maxRuns : Nat) : IO Unit := do
  let some s := treeWorld name | IO.println s!"unknown world {name}"
  let t0 ← IO.monoMsNow
  let o := Tree.checkTreelike (fun src => (runTWith b s.cfg s.aside s.scripts src).1) 100000 maxRuns
  IO.println s!"{name} {match b with | some k => s!"interleavePB ≤{k}" | none => "interleave (no bound)"}: {if o.complete then "COMPLETE" else "STOPPED"} after {fmtN o.runs} timelines; values not the path's modulo options: {o.valueBad}; decisions with < 2 options: {o.optBad}; at the decision limit: {o.limitHit}; causality broken between consecutive timelines: {o.causalBad}; with a violation: {o.violations}; most decisions in a timeline: {o.maxDepth}{match o.example? with | some e => s!" (e.g. {e})" | none => ""} ({(← IO.monoMsNow) - t0} ms)"
  flushOut

def main (args : List String) : IO Unit := do
  match args with
  | "fix" :: n :: m :: secs :: flags =>
    let fx : QFix := { q1 := !flags.contains "noq1", q2 := !flags.contains "noq2", v37i := !flags.contains "nov37i" }
    fixRun n fx (flags.contains "stock") m.toNat! secs.toNat!
  | ["flat", n, logCap, m, secs] => flatCmd n logCap.toNat! m.toNat! secs.toNat!
  | "divq" :: b :: m :: mc :: secs :: flags => divqRun {} (flags.contains "stock") b.toNat! m.toNat! mc.toNat! secs.toNat!
  | ["tree", n, b, m] => treeCmd n (if b == "all" then none else some b.toNat!) m.toNat!
  | _ => IO.println "usage: jank9-nrepl fix NAME MAXSTATES SECONDS [stock] [noq1] [noq2] [nov37i]"
