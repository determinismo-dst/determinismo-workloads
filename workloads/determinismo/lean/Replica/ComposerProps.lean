import Replica.Composer

/-!
# What the documentation promises of the composer

Each property reads one timeline of the replica (`Composer.runTimeline`): what truly happened
to every command start (`Inst`: when it began, when and how it ended) beside what the composer
said. The sources are in `docs`, one per property.
-/

namespace Replica.Composer

open Determinismo

def kindOf (w : W) (ci : Nat) : Kind := (cmdOf w ci).kind
def nameOf (w : W) (ci : Nat) : String := (cmdOf w ci).name

/-- Alive at `t`: begun, not ended (an end at `t` is over at `t`). -/
def Inst.aliveAt (i : Inst) (t : Nat) : Bool :=
  i.start ≤ t && (match i.endedAt with | some e => e > t | none => true)

/-- Two starts ran at the same time (open intervals overlap). -/
def Inst.overlaps (a b : Inst) : Bool :=
  let aEnd := a.endedAt.getD (a.start + 1000000000)
  let bEnd := b.endedAt.getD (b.start + 1000000000)
  a.start < bEnd && b.start < aEnd && a.start != aEnd && b.start != bEnd

def isEnding (k : Kind) : Bool := k == .eventually || k == .finally
def isDriving (k : Kind) : Bool :=
  k == .parallel_driver || k == .serial_driver || k == .anytime || k == .singleton_driver

/-- Ran to completion, as the composer counts it (composer.zig:172, 324): ended on its own,
not by a signal, its code under 128. -/
def Inst.completed (i : Inst) : Bool :=
  !i.killedByComposer && match i.ownExit with
    | some (.code n) => n % 256 < 128
    | _ => false

def describeInst (w : W) (i : Inst) : String :=
  let how := if i.killedByComposer then "killed by the composer"
    else match i.ownExit with
      | some (.code n) => s!"exited {n}" | some (.signal s) => s!"ended by signal {s}" | none => "running"
  s!"{nameOf w i.cmd}#{i.pid} [{i.start},{i.endedAt.getD 0}] {how}"

structure Prop' where
  name : String
  /-- Where the documentation says it. -/
  source : String
  check : W → Option Stop → Option String

/-- The timeline ended as a composer's does (composer_done), not by a panic or an error. -/
def finished (stop : Option Stop) : Bool := stop.isNone

def oneEnding : Prop' :=
  { name := "a timeline runs one ending command"
    source := ".claude/skills/determinismo-workload/SKILL.md: \"A timeline runs one ending command: one `eventually` or one `finally` among the scenario's (Antithesis's rule)\""
    check := fun w _ =>
      let n := (w.insts.filter fun i => isEnding (kindOf w i.cmd)).size
      if n ≤ 1 then none else some s!"{n} ending commands ran" }

def eventuallyAlone : Prop' :=
  { name := "an eventually command runs with every other command ended"
    source := "docs/ANTITHESIS.md (Test templates): \"an eventually command kills every command still running (and faults stop)\""
    check := fun w stop => Id.run do
      if !finished stop then return none
      for e in w.insts do
        if kindOf w e.cmd != .eventually then continue
        for o in w.insts do
          if o.pid == e.pid then continue
          if o.aliveAt e.start || o.start > e.start then
            return some s!"{describeInst w o} alive as {nameOf w e.cmd} starts at {e.start}"
      return none }

/-- The rule as the Zig's comment reads it (composer.zig:517): commands the timeline's length
killed are forgiven; any other command that did not run to completion keeps the finally out. -/
def finallyAfterCompletion : Prop' :=
  { name := "a finally command runs only when every command ran to completion (the length's kills aside)"
    source := "docs/ANTITHESIS.md (Test templates): \"a finally command waits for them and runs only when every command ran to completion\"; composer.zig:517: drivers ended by the length are by design"
    check := fun w stop => Id.run do
      if !finished stop then return none
      for f in w.insts do
        if kindOf w f.cmd != .finally then continue
        for o in w.insts do
          if o.pid == f.pid then continue
          if o.aliveAt f.start then
            return some s!"{describeInst w o} alive as {nameOf w f.cmd} starts"
          let lengthKill := o.killedByComposer && (match w.lengthEnd with
            | some e => o.endedAt == some (e + w.consts.graceMs) | none => false)
          if !o.completed && !lengthKill then
            return some s!"{describeInst w o} did not run to completion, and {nameOf w f.cmd} ran at {f.start}"
      return none }

/-- The rule as the documentation states it, without the code comment's exception. -/
def finallyAfterCompletionStrict : Prop' :=
  { name := "a finally command runs only when every command ran to completion"
    source := "docs/ANTITHESIS.md (Test templates)"
    check := fun w stop => Id.run do
      if !finished stop then return none
      for f in w.insts do
        if kindOf w f.cmd != .finally then continue
        for o in w.insts do
          if o.pid == f.pid then continue
          if !o.completed then
            return some s!"{describeInst w o} did not run to completion, and {nameOf w f.cmd} ran at {f.start}"
      return none }

def singletonAlone : Prop' :=
  { name := "a timeline that runs a singleton driver runs no parallel or serial driver"
    source := ".claude/skills/determinismo-workload/SKILL.md: \"A `singleton_driver` runs alone: a timeline that draws it runs no other driver (Antithesis's rule)\""
    check := fun w _ => Id.run do
      let singles := w.insts.filter fun i => kindOf w i.cmd == .singleton_driver
      if singles.isEmpty then return none
      for o in w.insts do
        let k := kindOf w o.cmd
        if k == .parallel_driver || k == .serial_driver then
          return some s!"{describeInst w o} in a timeline with {describeInst w singles[0]!}"
        if k == .singleton_driver && o.pid != singles[0]!.pid then
          return some s!"two singleton starts"
      return none }

/-- The same, an anytime command counted as a driver (the swarm's comment, composer.zig:214,
calls anytime commands drivers). -/
def singletonAloneStrict : Prop' :=
  { name := "a singleton driver runs with no other driving command (anytime counted)"
    source := "SKILL.md as above, with composer.zig:214's \"each parallel, serial and anytime driver\""
    check := fun w _ => Id.run do
      for s in w.insts do
        if kindOf w s.cmd != .singleton_driver then continue
        for o in w.insts do
          if o.pid != s.pid && isDriving (kindOf w o.cmd) && o.overlaps s then
            return some s!"{describeInst w o} beside {describeInst w s}"
      return none }

def serialAlone : Prop' :=
  { name := "a serial driver runs with no other driver"
    source := "docs/ANTITHESIS.md (Test templates: serial drivers, Antithesis's reference: one at a time, never beside another driver)"
    check := fun w _ => Id.run do
      for s in w.insts do
        if kindOf w s.cmd != .serial_driver then continue
        for o in w.insts do
          if o.pid != s.pid && isDriving (kindOf w o.cmd) && o.overlaps s then
            return some s!"{describeInst w o} beside {describeInst w s}"
      return none }

def parallelismBound : Prop' :=
  { name := "drivers running at once never exceed parallel_max (32 unless set)"
    source := "sdk/zig/schema.zig Scenario.parallel_max: \"The most drivers running at once\""
    check := fun w _ => Id.run do
      let cap := match w.scenario.parallelMax with
        | some most => min (2 ^ w.consts.parallelismLog2Max) (max most 1)
        | none => 2 ^ w.consts.parallelismLog2Max
      for s in w.insts do
        let n := (w.insts.filter fun o => isDriving (kindOf w o.cmd) && o.aliveAt s.start).size
        if n > cap then return some s!"{n} drivers running at {s.start}, cap {cap}"
      return none }

def faultsWindow : Prop' :=
  { name := "faults run in the driver phase only: after the first command, stopped before the ending"
    source := "docs/ANTITHESIS.md (Pausing faults): \"faults only in the driver phase\"; composer.zig:336"
    check := fun w stop => Id.run do
      let some fs := w.faultsStarted | return none
      for i in w.insts do
        let k := kindOf w i.cmd
        if (k == .first || k == .setup) && (i.endedAt.getD (fs + 1)) > fs then
          return some s!"{describeInst w i} still running as faults start at {fs}"
        if isEnding k then
          match w.faultsStopped with
          | some fe => if i.start < fe then return some s!"{describeInst w i} starts before faults stop at {fe}"
          | none => if finished stop then return some s!"{describeInst w i} runs and faults never stopped"
      return none }

def workloadKept : Prop' :=
  { name := "the swarm keeps one marked driver at least (one driver, when none is marked), and the composer goes on"
    source := ".claude/skills/determinismo-workload/SKILL.md: \"the composer's swarm then leaves any driver out of some timelines ... and keeps one marked driver at least\"; sdk/zig/schema.zig Command.workload"
    check := fun w stop => Id.run do
      if let some (.violation "composer panics" msg) := stop then
        return some s!"the composer panics: {msg}"
      if !w.swarmed then return none
      let marked := w.commands.any (·.workload)
      let ok := if marked then w.commands.any fun c => c.workload && c.kept && swarmable c.kind
        else w.commands.any fun c => c.kept && swarmable c.kind
      if ok then none else some (if marked then "no marked driver kept" else "no driver kept") }

def noPanic : Prop' :=
  { name := "the composer never panics on a valid scenario"
    source := "composer.zig's asserts (ReleaseSafe): a panic ends the timeline without its driver phase's verdicts"
    check := fun _ stop => match stop with
      | some (.violation "composer panics" msg) => some msg
      | _ => none }

/-- With a length (explore's --timeline, or a drawn drive_ms_max), the drivers still running at
its end get a grace, then are killed. -/
def lengthBound : Prop' :=
  { name := "with a timeline length, no driver runs past the length's end and its grace"
    source := "sdk/zig/schema.zig Scenario.drive_ms_max: \"drivers started until it passed: a timeline's length no longer follows how slow its commands are\"; composer.zig:504-513: \"the commands still running get a grace, then are killed\""
    check := fun w stop => Id.run do
      if !finished stop then return none
      let some ds := w.driveStart | return none
      let endT ← match w.lengthEnd, w.cmdline.timelineMs with
        | some e, _ => pure e
        | none, some l => pure (ds + l)
        | none, none => return none
      for i in w.insts do
        if !isDriving (kindOf w i.cmd) || i.start > endT then continue
        if (i.endedAt.getD (endT + w.consts.graceMs + 1)) > endT + w.consts.graceMs then
          return some s!"{describeInst w i} runs past the length's end {endT} and its grace {w.consts.graceMs}"
      return none }

/-- Every start that ended on its own is judged as its own: its failing exit fails "test
commands exit successfully", its success reaches "test command completed". Only the composer's
own kills are no exits. -/
def exitsJudged : Prop' :=
  { name := "a command that ended on its own is judged by its exit (only the composer's kills are not)"
    source := "docs/ANTITHESIS.md (Default: commands finish with zero exit code; Test templates: \"killed commands are no failing exits\")"
    check := fun w stop => Id.run do
      if !finished stop then return none
      for i in w.insts do
        if i.killedByComposer then continue
        if i.reportedKilled == some true then
          return some s!"{describeInst w i} reported as killed: its exit never judged"
      return none }

def noStartPastHalfLimit : Prop' :=
  { name := "no driver starts past half the timeline's limit"
    source := "composer.zig:730: \"No driver starts past half the timeline's limit\" (a code comment)"
    check := fun w _ => Id.run do
      let some limit := w.cmdline.timelineLimitMs | return none
      if w.lengthEnd.isSome || w.cmdline.timelineMs.isSome then return none
      let some ds := w.driveStart | return none
      for i in w.insts do
        let k := kindOf w i.cmd
        if (k == .parallel_driver || k == .serial_driver || k == .anytime) && i.start > ds + limit / 2 then
          return some s!"{describeInst w i} starts past {ds + limit / 2}"
      return none }

def allProps : List Prop' :=
  [oneEnding, eventuallyAlone, finallyAfterCompletion, finallyAfterCompletionStrict, singletonAlone,
   singletonAloneStrict, serialAlone, parallelismBound, faultsWindow, workloadKept, noPanic,
   lengthBound, exitsJudged, noStartPastHalfLimit]

/-- One timeline judged by one property. -/
def judge (p : Prop') (scenario : Scenario) (cmdline : Cmdline) (consts : Consts) (source : Source) :
    Ended :=
  let (w, stop) := runTimeline scenario cmdline consts source
  let violation := (p.check w stop).map fun d => (p.name, d)
  { taken := w.decisions.taken, violation }

/-- A timeline's story: what the composer did, line by line. -/
def story (scenario : Scenario) (cmdline : Cmdline) (consts : Consts) (source : Source) : List String :=
  let (w, stop) := runTimeline scenario cmdline consts source
  let lines := w.log.toList.map fun
    | .start pid ci mode t => s!"{t} ms: start {nameOf w ci}#{pid} {mode}"
    | .exit pid ci status killed t =>
      s!"{t} ms: reaped {nameOf w ci}#{pid}: " ++ (if killed then "reported killed" else s!"status {status.getD 0}")
    | .assertion k m c t => s!"{t} ms: assert {k.name} \"{m}\" {c}"
    | .declare k m => s!"declare {k.name} \"{m}\""
    | .faults on t => s!"{t} ms: faults {if on then "start" else "stop"}"
    | .note text t => s!"{t} ms: {text}"
  let truth := w.insts.toList.map fun i => s!"truth: {describeInst w i}"
  lines.filter (fun l => !l.startsWith "declare") ++ truth ++ [s!"end: {reprStr stop}"]

/-- A scenario drawn by decisions (`gen.*`), then its timeline: explore's world. -/
def genScenario : EStateM Stop W (Scenario × Cmdline) := do
  let n := 1 + (← below "gen.commands" 5)
  let kinds := #[Kind.first, .parallel_driver, .serial_driver, .singleton_driver, .anytime,
                 .eventually, .finally, .parallel_driver, .parallel_driver]
  let mut commands : List Command := []
  for i in [0:n] do
    let k := kinds[(← below "gen.kind" kinds.size)]!
    let workload := (← below "gen.workload" 4) == 0
    let runs := [[10, 1000, 60000], [50, 500], [100000, 400000], [200, 2000]][(← below "gen.runs" 4)]!
    let exits := [[Exit.code 0], [.code 0, .code 1], [.code 0, .signal 9], [.code 0, .code 137]][(← below "gen.exits" 4)]!
    commands := commands ++ [{ name := s!"c{i}", kind := k, workload, runs, exits }]
  let withSetup := (← below "gen.setup" 4) == 0
  if withSetup then commands := { name := "setup", kind := .setup, runs := [100] } :: commands
  let minDriveMs := [none, some 0, some 2000][(← below "gen.min_drive" 3)]!
  let driveMsMax := [none, some 30000, some 120000][(← below "gen.drive_max" 3)]!
  let parallelMax := [none, some 1, some 4][(← below "gen.parallel_max" 3)]!
  let timelineMs := [none, some 30000, some 100000][(← below "gen.timeline" 3)]!
  let timelineLimitMs := [none, some 600000, some 3600000][(← below "gen.limit" 3)]!
  let swarmOff := (← below "gen.no_swarm" 4) == 0
  pure ({ commands, minDriveMs, driveMsMax, parallelMax, endingMsMax := some 60000 },
        { swarmOff, timelineMs, timelineLimitMs })

/-- Explore's world: the scenario drawn, then one of its timelines, judged by `p`. -/
def judgeDrawn (p : Prop') (consts : Consts) (source : Source) : Ended :=
  let w0 : W := { decisions := { source }, consts }
  match genScenario.run w0 with
  | .error _ w => { taken := w.decisions.taken, violation := none }
  | .ok (scenario, cmdline) w =>
    let w1 : W := { w with scenario, cmdline }
    let (w2, stop) := match main.run w1 with
      | .ok _ w => (w, none)
      | .error e w => (w, some e)
    -- An invalid scenario (no driver at all, two setups) is refused by validate: not judged.
    match stop with
    | some (.violation "composer errs" _) => { taken := w2.decisions.taken, violation := none }
    | _ => { taken := w2.decisions.taken, violation := (p.check w2 stop).map fun d => (p.name, d) }

/-- The drawn scenario of a source, for a counterexample's story. -/
def drawnOf (consts : Consts) (source : Source) : Option (Scenario × Cmdline × Decisions) :=
  let w0 : W := { decisions := { source }, consts }
  match genScenario.run w0 with
  | .ok (s, c) w => some (s, c, w.decisions)
  | .error _ _ => none

end Replica.Composer
