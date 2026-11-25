import Replica.ComposerSearch

/-!
# CE2's remainder in drawn worlds made for it

Round 2 found CE2's remainder in one small world (16): with `--min-drive 0`, `min_drive` returns
at once (guest/runtime/composer.zig:853-856), the drivers are not reaped before the ending's
`kill_all` (401-407), and a driver that died of its own SIGKILL (the OOM killer, a kill from
outside the composer) is reaped there as killed by the composer: never judged.

Here scenarios are drawn around it, with the Zig's constants: one to three parallel or serial
drivers (some marked workloads), each ending by itself (exit 0 or 1) or by its own SIGKILL at a
drawn time, an eventually or a finally ending (or both), `min_drive` 0 or small, the swarm on or
off, a length or none, `parallel_max` drawn. The property is round 1's 13th ("a command that
ended on its own is judged by its exit"), unchanged.

`ce2Census` counts, over seeds, how many drawn timelines break it, and how many have the shape
it needs (a driver's own SIGKILL before an ending): how likely CE2 is where it can happen.
-/

namespace Replica.Composer

open Determinismo

def genCe2 : EStateM Stop W (Scenario × Cmdline) := do
  let n := 1 + (← below "gen.drivers" 3)
  let mut commands : List Command := []
  for i in [0:n] do
    let k := [Kind.parallel_driver, .parallel_driver, .serial_driver][(← below "gen.kind" 3)]!
    let workload := (← below "gen.workload" 2) == 0
    let runs := [[5, 50], [200, 2000], [10, 1000, 60000], [3000]][(← below "gen.runs" 4)]!
    let exits := [[Exit.code 0, .signal 9], [.signal 9], [.code 1, .signal 9], [.code 0, .code 137, .signal 9]][(← below "gen.exits" 4)]!
    commands := commands ++ [{ name := s!"d{i}", kind := k, workload, runs, exits }]
  let endings := [[Kind.eventually], [.finally], [.eventually, .finally]][(← below "gen.endings" 3)]!
  for k in endings do
    commands := commands ++ [{ name := s!"{k.name}", kind := k, runs := [1, 100] }]
  let minDriveMs := [some 0, some 0, some 20, none][(← below "gen.min_drive" 4)]!
  let parallelMax := [none, some 1, some 2][(← below "gen.parallel_max" 3)]!
  let timelineMs := [none, some 500, some 5000][(← below "gen.timeline" 3)]!
  let swarmOff := (← below "gen.no_swarm" 2) == 0
  pure ({ commands, minDriveMs, parallelMax, endingMsMax := some 60000 }, { swarmOff, timelineMs })

def judgeCe2 (consts : Consts) (source : Source) : Ended :=
  let w0 : W := { decisions := { source }, consts }
  match genCe2.run w0 with
  | .error _ w => { taken := w.decisions.taken, violation := none }
  | .ok (scenario, cmdline) w =>
    let w1 : W := { w with scenario, cmdline }
    let (w2, stop) := match main.run w1 with
      | .ok _ w => (w, none)
      | .error e w => (w, some e)
    match stop with
    | some (.violation "composer errs" _) => { taken := w2.decisions.taken, violation := none }
    | _ => { taken := w2.decisions.taken, violation := (exitsJudged.check w2 stop).map fun d => (exitsJudged.name, d) }

def ce2Story (consts : Consts) (source : Source) : List String :=
  let w0 : W := { decisions := { source }, consts }
  match genCe2.run w0 with
  | .error _ _ => ["(no scenario)"]
  | .ok (scenario, cmdline) w =>
    let header := s!"scenario: {reprStr (scenario.commands.map fun c => (c.name, c.kind.name, c.workload, c.runs, reprStr c.exits))} minDrive={scenario.minDriveMs} parallelMax={scenario.parallelMax} swarmOff={cmdline.swarmOff} timelineMs={cmdline.timelineMs}"
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

/-- Counts over seeds `first` .. `first + count - 1`: timelines that finished, those with a
driver's own SIGKILL, and those breaking the property. -/
def ce2Census (count first : Nat) : IO Unit := do
  let consts : Consts := {}
  let mut finishedN := 0
  let mut ownKill := 0
  let mut broken := 0
  let mut minDrive0 := 0
  let mut broken0 := 0
  for i in [first:first + count] do
    let w0 : W := { decisions := { source := Source.seeded i }, consts }
    match genCe2.run w0 with
    | .error _ _ => pure ()
    | .ok (scenario, cmdline) w =>
      let w1 : W := { w with scenario, cmdline }
      let (w2, stop) := match main.run w1 with
        | .ok _ w => (w, none)
        | .error e w => (w, some e)
      if !finished stop then continue
      finishedN := finishedN + 1
      let zero := scenario.minDriveMs == some 0
      if zero then minDrive0 := minDrive0 + 1
      if w2.insts.any (fun i => !i.killedByComposer && i.ownExit == some (.signal 9) && i.endedAt.isSome) then ownKill := ownKill + 1
      if (exitsJudged.check w2 stop).isSome then
        broken := broken + 1
        if zero then broken0 := broken0 + 1
  say s!"census [CE2 drawn, seeds {first}..{first + count - 1}]: {finishedN} finished timelines, {ownKill} with a driver's own SIGKILL, {broken} broke \"{exitsJudged.name}\"; with min_drive 0: {minDrive0} timelines, {broken0} broke it"

def searchCe2 (seeds : Nat) : IO Unit := do
  say s!"== composer property: {exitsJudged.name} (CE2's remainder, drawn worlds made for it)"
  say s!"   source: {exitsJudged.source}"
  let consts : Consts := {}
  if let some f ← exploreSaid s!"{exitsJudged.name} / CE2's drawn worlds, the Zig's constants" (judgeCe2 consts) seeds then
    printFound f (ce2Story consts)
  ce2Census seeds 0

end Replica.Composer
