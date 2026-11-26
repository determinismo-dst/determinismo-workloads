import Replica.ComposerProps
import Replica.Searching

/-!
# The composer's searches: small worlds exhausted, drawn scenarios explored
-/

namespace Replica.Composer

open Determinismo

structure World where
  label : String
  scenario : Scenario
  cmdline : Cmdline := {}
  consts : Consts := Consts.tiny

def cmd (name : String) (kind : Kind) (runs : List Nat := []) (exits : List Exit := [])
    (workload : Bool := false) : Command :=
  { name, kind, runs, exits, workload }

/-- Small worlds: each a scenario of the kinds a property is about. Without the swarm they are
exhausted to the end; with it (its draws are 7 and 8 options each, the Zig's), explored. -/
def worlds : List World :=
  [ { label := "first + parallel + serial + eventually + finally, no swarm"
      scenario := { commands := [cmd "first" .first [1], cmd "drive" .parallel_driver [1, 7],
                                 cmd "serial" .serial_driver [2], cmd "check" .eventually [1],
                                 cmd "final" .finally [1]] }
      cmdline := { swarmOff := true } },
    { label := "setup + first + parallel + anytime + finally, parallel_max 2, no swarm"
      scenario := { commands := [cmd "setup" .setup [1], cmd "first" .first [2], cmd "drive" .parallel_driver [1, 9],
                                 cmd "probe" .anytime [3], cmd "final" .finally [1]],
                    parallelMax := some 2 }
      cmdline := { swarmOff := true } },
    { label := "parallel (exits 0 or 1) + eventually, min_drive 0, no swarm"
      scenario := { commands := [cmd "drive" .parallel_driver [1, 3] [.code 0, .code 1], cmd "check" .eventually [1]],
                    minDriveMs := some 0 }
      cmdline := { swarmOff := true } },
    { label := "parallel (exits 0 or 1) + eventually, min_drive default, no swarm"
      scenario := { commands := [cmd "drive" .parallel_driver [1, 3] [.code 0, .code 1], cmd "check" .eventually [1]] }
      cmdline := { swarmOff := true } },
    { label := "parallel (ends by itself or by a signal) + finally, a 60 ms length, no swarm"
      scenario := { commands := [cmd "drive" .parallel_driver [20, 100] [.code 0, .signal 9],
                                 cmd "check" .finally [1]] }
      cmdline := { swarmOff := true, timelineMs := some 60 } },
    { label := "serial (1 or 200 ms) + parallel, a 60 ms length, no swarm"
      scenario := { commands := [cmd "serial" .serial_driver [1, 200], cmd "drive" .parallel_driver [20]] }
      cmdline := { swarmOff := true, timelineMs := some 60 } },
    { label := "singleton (1 or 200 ms) + parallel, a 60 ms length, no swarm"
      scenario := { commands := [cmd "alone" .singleton_driver [1, 200], cmd "drive" .parallel_driver [20]] }
      cmdline := { swarmOff := true, timelineMs := some 60 } },
    { label := "singleton + parallel + anytime, no swarm"
      scenario := { commands := [cmd "alone" .singleton_driver [5], cmd "drive" .parallel_driver [1],
                                 cmd "probe" .anytime [1]] }
      cmdline := { swarmOff := true } },
    { label := "singleton (marked workload) + two parallel nemeses, swarm"
      scenario := { commands := [cmd "workload" .singleton_driver [1] [] true,
                                 cmd "nemesis1" .parallel_driver [1], cmd "nemesis2" .parallel_driver [1]] } },
    { label := "first (marked workload) + two parallel nemeses, swarm"
      scenario := { commands := [cmd "load" .first [1] [] true,
                                 cmd "nemesis1" .parallel_driver [1], cmd "nemesis2" .parallel_driver [1]] } },
    { label := "five anytime commands, none marked, swarm"
      scenario := { commands := [cmd "a1" .anytime [1], cmd "a2" .anytime [1], cmd "a3" .anytime [1],
                                 cmd "a4" .anytime [1], cmd "a5" .anytime [1]] } },
    { label := "parallel (marked) + parallel nemesis + finally, swarm"
      scenario := { commands := [cmd "workload" .parallel_driver [1] [] true,
                                 cmd "nemesis" .parallel_driver [1], cmd "check" .finally [1]] } },
    { label := "parallel, a 30 ms timeline limit (no length), swarm"
      scenario := { commands := [cmd "drive" .parallel_driver [1]] }
      cmdline := { timelineLimitMs := some 30 } },
    { label := "parallel (exits 0 or 1) + eventually, min_drive 0, pauses of 0 to 2 ms, no swarm"
      scenario := { commands := [cmd "drive" .parallel_driver [1, 3] [.code 0, .code 1], cmd "check" .eventually [1]],
                    minDriveMs := some 0 }
      cmdline := { swarmOff := true }
      consts := { Consts.tiny with pauseMax := 3 } },
    -- Round 2's worlds.
    { label := "a parallel driver of 400 ms holding the only slot, another of 1 ms, a 600 ms limit, no swarm"
      scenario := { commands := [cmd "holding" .parallel_driver [400], cmd "next" .parallel_driver [1]],
                    parallelMax := some 1 }
      cmdline := { swarmOff := true, timelineLimitMs := some 600 } },
    { label := "singleton (1 or 200 ms) + parallel, drive_ms_max 60 ms, no swarm"
      scenario := { commands := [cmd "alone" .singleton_driver [1, 200], cmd "drive" .parallel_driver [20]],
                    driveMsMax := some 60 }
      cmdline := { swarmOff := true } },
    { label := "parallel (exits 0, or its own SIGKILL) + eventually, min_drive 0, pauses of 0 to 2 ms, no swarm"
      scenario := { commands := [cmd "drive" .parallel_driver [1, 3] [.code 0, .signal 9], cmd "check" .eventually [1]],
                    minDriveMs := some 0 }
      cmdline := { swarmOff := true }
      consts := { Consts.tiny with pauseMax := 3 } },
    -- Round 5 (world 17): a second driver phase (composer.again, which the explorer answers
    -- for a return to an objective's best) under a timeline limit and no length.
    { label := "a parallel driver of 10 or 270 ms, one at a time, a 600 ms limit, a second phase asked (composer.again: yes once), no swarm"
      scenario := { commands := [cmd "drive" .parallel_driver [10, 270]], parallelMax := some 1 }
      cmdline := { swarmOff := true, timelineLimitMs := some 600, againAsked := true } } ]

/-- The story of a world's timeline. -/
def worldStory (wd : World) (source : Source) : List String :=
  story wd.scenario wd.cmdline wd.consts source

/-- The story of a drawn scenario's timeline. -/
def drawnStory (consts : Consts) (source : Source) : List String :=
  let w0 : W := { decisions := { source }, consts }
  match genScenario.run w0 with
  | .error _ _ => ["(no scenario)"]
  | .ok (scenario, cmdline) w =>
    let header := s!"scenario: {reprStr (scenario.commands.map fun c => (c.name, c.kind.name, c.workload, c.runs, reprStr c.exits))} minDrive={scenario.minDriveMs} driveMsMax={scenario.driveMsMax} parallelMax={scenario.parallelMax} cmdline: swarmOff={cmdline.swarmOff} timelineMs={cmdline.timelineMs} limitMs={cmdline.timelineLimitMs}"
    let w1 : W := { w with scenario, cmdline }
    let (w2, stop) := match main.run w1 with
      | .ok _ w => (w, none)
      | .error e w => (w, some e)
    let lines := w2.log.toList.filterMap fun
      | .start pid ci mode t => some s!"{t} ms: start {nameOf w2 ci}#{pid} {mode}"
      | .exit pid ci status killed t =>
        some (s!"{t} ms: reaped {nameOf w2 ci}#{pid}: " ++ (if killed then "reported killed" else s!"status {status.getD 0}"))
      | .assertion k m c t => some s!"{t} ms: assert {k.name} \"{m}\" {c}"
      | .declare _ _ => none
      | .faults on t => some s!"{t} ms: faults {if on then "start" else "stop"}"
      | .note text t => some s!"{t} ms: {text}"
    header :: lines ++ (w2.insts.toList.map fun i => s!"truth: {describeInst w2 i}") ++ [s!"end: {reprStr stop}"]

/-- Every property: each small world exhausted (up to `exhaustRuns` timelines) and explored
(`worldRuns` seeds), then drawn scenarios explored with the Zig's constants (`drawnRuns` seeds).
The first counterexample of each kind of search is kept. -/
def searchAll (exhaustRuns worldRuns drawnRuns : Nat) (only : Option Nat := none) : IO (List Found) := do
  let mut found : List Found := []
  for (p, index) in allProps.zipIdx do
    if let some i := only then
      if i != index then continue
    say s!"== composer property: {p.name}"
    say s!"   source: {p.source}"
    let mut exhausted := false
    let mut explored := false
    for wd in worlds do
      let run := judge p wd.scenario wd.cmdline wd.consts
      -- With the swarm on, the composer's load may draw quiet stretch after quiet stretch
      -- (composer.zig:760): the tree of decisions has no end, and depth first goes down it at a
      -- cost that grows with the depth. Those worlds get a smaller budget, and their seeds.
      let budget := if wd.cmdline.swarmOff then exhaustRuns else min exhaustRuns 5000
      if !exhausted then
        if let some f ← exhaustSaid s!"{p.name} / {wd.label}" run budget then
          printFound f (worldStory wd)
          found := found ++ [f]
          exhausted := true
      if !explored && worldRuns > 0 then
        if let some f ← exploreSaid s!"{p.name} / {wd.label}" run worldRuns then
          printFound f (worldStory wd)
          found := found ++ [f]
          explored := true
    if drawnRuns > 0 then
      let consts : Consts := {}
      if let some f ← exploreSaid s!"{p.name} / drawn scenarios, the Zig's constants" (judgeDrawn p consts) drawnRuns then
        printFound f (drawnStory consts)
        found := found ++ [f]
  return found

end Replica.Composer

namespace Replica.Composer

instance : Inhabited Prop' := ⟨oneEnding⟩
instance : Inhabited World := ⟨{ label := "", scenario := { commands := [] } }⟩

/-- One property on one small world: exhausted, then explored from `first`. -/
def searchWorld (p : Nat) (w : Nat) (exhaustRuns seeds first : Nat) : IO Unit := do
  let prop := allProps[p]!
  let wd := worlds[w]!
  say s!"== composer property: {prop.name}"
  let run := judge prop wd.scenario wd.cmdline wd.consts
  if exhaustRuns > 0 then
    if let some f ← exhaustSaid s!"{prop.name} / {wd.label}" run exhaustRuns then printFound f (worldStory wd)
  if seeds > 0 then
    if let some f ← exploreSaid s!"{prop.name} / {wd.label}" run seeds first then printFound f (worldStory wd)

/-- Drawn scenarios with the Zig's constants, seeds `first` on. -/
def searchDrawn (p : Nat) (seeds first : Nat) : IO Unit := do
  let prop := allProps[p]!
  let consts : Consts := {}
  if let some f ← exploreSaid s!"{prop.name} / drawn scenarios, the Zig's constants" (judgeDrawn prop consts) seeds first then
    printFound f (drawnStory consts)

end Replica.Composer
