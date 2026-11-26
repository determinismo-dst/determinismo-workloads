import Replica.Prelude

/-!
# det-composer, replicated (guest/runtime/composer.zig, platform 3939448)

Round 2: the Zig's line numbers below are 3939448's where a function changed (swarm_commands
221-283, reap 315-345, run_alone_until 413-419, main 434-552, rescue_counts 686-692,
run_singleton 715-737, run_drivers 750-811, clock_start_draw 905-927); the others' kept
round 1's numbers, their code unchanged but shifted by the additions above them.

One timeline of a scenario, function by function, with the Zig's line numbers. Every decision
keeps the Zig's name (`composer.swarm <name>`, `composer.load`, ...); the SDK's unnamed draws
(`sdk.random_below`, `sdk.random_choice`) are named `random_below` here.

What the replica does not run: processes. A command start is a decision of the world
(`world.run_ms <name>`: how long it runs, from the command's menu; `world.exit <name>`: how it
ends), the same for every start of that command. Time is in milliseconds (the Zig's are
nanoseconds; `pause` draws whole milliseconds), and every constant is a field of `Consts`: the
Zig's values by default, smaller ones in small worlds (`Consts.small`), the code around them
unchanged.

`wait4(-1)` returns the child that exited with the lowest pid first (Linux scans its children
in fork order); the fault injector, also a child, never exits on its own here (its 10,000
injections are not modeled), so `reap` never meets it.
-/

namespace Replica.Composer

open Determinismo

/-- schema.zig's `Kind`. -/
inductive Kind where
  | setup | first | parallel_driver | serial_driver | singleton_driver | anytime | eventually | finally
  deriving BEq, Repr, Inhabited, DecidableEq

def Kind.name : Kind → String
  | .setup => "setup" | .first => "first" | .parallel_driver => "parallel_driver"
  | .serial_driver => "serial_driver" | .singleton_driver => "singleton_driver"
  | .anytime => "anytime" | .eventually => "eventually" | .finally => "finally"

/-- How a command start ends on its own: an exit code, or a signal. -/
inductive Exit where
  | code (n : Nat)
  | signal (s : Nat)
  deriving BEq, Repr, Inhabited

/-- The wait status bits Linux gives the composer (composer.zig:323). -/
def Exit.bits : Exit → Nat
  | .code n => (n % 256) * 256
  | .signal s => s % 128

/-- composer.zig:121 `Command`, with the world's menus for its starts. -/
structure Command where
  name : String
  kind : Kind
  workload : Bool := false
  kept : Bool := true
  weight : Nat := 1
  /-- How long a start runs (ms), the world's options; empty: `Consts.runMenu`. -/
  runs : List Nat := []
  /-- How a start ends, the world's options; empty: `Consts.exitMenu`. -/
  exits : List Exit := []
  deriving Repr, Inhabited

/-- schema.zig's `Scenario` (the fields the composer reads). -/
structure Scenario where
  commands : List Command
  faults : Bool := true
  minDriveMs : Option Nat := none
  driveMsMax : Option Nat := none
  endingMsMax : Option Nat := none
  parallelMax : Option Nat := none
  /-- `Scenario.node` set and no `program` (Antithesis test templates): a template without
  drivers is the system driving itself. -/
  templates : Bool := false
  deriving Repr, Inhabited

/-- The kernel command line's words the composer reads (explore's options). -/
structure Cmdline where
  /-- det.swarm=0 (--no-swarm). -/
  swarmOff : Bool := false
  /-- det.keep= (--keep). -/
  keep : List String := []
  /-- det.timeline_ms= (--timeline). -/
  timelineMs : Option Nat := none
  /-- det.timeline_limit_ms= (--timeline-limit). -/
  timelineLimitMs : Option Nat := none
  /-- det.min_drive_ms= (--min-drive). -/
  minDriveMs : Option Nat := none
  /-- det.drive_ms_max= (--drive-max). -/
  driveMsMax : Option Nat := none
  /-- det.drivers_cpu_weight=. -/
  driversCpuWeight : Option Nat := none
  /-- The explorer answers `composer.again` (advisor.zig:78): only for a return to an
  objective's best. Off: no second phase (the timeline's own draw says yes once in 2^62). -/
  againAsked : Bool := false
  /-- det.clock_start_max_ms= (--clock-start-max; none: the composer's hour). -/
  clockStartMaxMs : Option Nat := none
  deriving Repr, Inhabited

/-- The composer's constants (ms). Defaults are the Zig's. -/
structure Consts where
  /-- pause_ns_max (20 ms): `pause` draws below it. -/
  pauseMax : Nat := 20
  /-- min_drive_poll_ns (50 ms). -/
  pollMs : Nat := 50
  /-- length_grace_ns (30 s). -/
  graceMs : Nat := 30000
  /-- min_drive_ms_default (10 s). -/
  minDriveDefault : Nat := 10000
  /-- ending_ms_max_default (20 min). -/
  endingDefault : Nat := 1200000
  /-- starts_max (64). -/
  startsMax : Nat := 64
  /-- `composer.starts_log2`'s range (5: 2 to 63 starts). -/
  startsLog2 : Nat := 5
  /-- parallelism_log2_max (5: up to 32). -/
  parallelismLog2Max : Nat := 5
  /-- running_max (32). -/
  runningMax : Nat := 32
  /-- A quiet stretch: 1 s + `composer.quiet_ms` below 14,001. -/
  quietBase : Nat := 1000
  quietRange : Nat := 14001
  /-- A steady or spike stretch: 10 s + `composer.load_ms` below 110,001. -/
  loadBase : Nat := 10000
  loadRange : Nat := 110001
  /-- The world's options for a start's run time and its end, unless a command has its own. -/
  runMenu : List Nat := [10, 1000, 60000]
  exitMenu : List Exit := [.code 0, .code 1]
  /-- Draws that change nothing the properties see (composer.drivers_cpu): made when true. -/
  irrelevantDraws : Bool := true
  /-- Loop steps before a timeline is cut (an end, not a failure). -/
  fuel : Nat := 200000
  /-- Round 5: the platform's code modeled, 62e06e3 unless a theorem about 3939448 says so. -/
  ver : Ver := .va7fe05d
  deriving Repr, Inhabited

/-- Tiny worlds: one start's run and end fixed unless a command says, four starts without the
swarm, no pause draw. -/
def Consts.tiny : Consts :=
  { pauseMax := 1, pollMs := 5, graceMs := 30, minDriveDefault := 20, endingDefault := 100,
    startsMax := 5, startsLog2 := 1, parallelismLog2Max := 1, runningMax := 4,
    quietBase := 10, quietRange := 1, loadBase := 20, loadRange := 1,
    runMenu := [1], exitMenu := [.code 0], irrelevantDraws := false, fuel := 20000 }

/-- Small worlds: few options per decision, every structure of the Zig kept. -/
def Consts.small : Consts :=
  { pauseMax := 2, pollMs := 5, graceMs := 30, minDriveDefault := 20, endingDefault := 100,
    startsMax := 6, startsLog2 := 1, parallelismLog2Max := 1, runningMax := 4,
    quietBase := 10, quietRange := 2, loadBase := 20, loadRange := 2,
    runMenu := [1, 50], exitMenu := [.code 0, .code 1], irrelevantDraws := false, fuel := 20000 }

/-- composer.zig:929-932 `clock_start_bands`: doublings from a second, the last ending at
`max_ms`; none under a second. -/
def clockStartBands (maxMs : Nat) : Nat :=
  if maxMs < 1000 then 0 else Nat.log2 (maxMs / 1000) + 1

/-- composer.zig:934-937 `clock_start_band`. -/
def clockStartBand (maxMs band : Nat) : Nat × Nat :=
  let low := 1000 * 2 ^ band
  (low, min maxMs (2 * low - 1))

/-- The property kinds (events.zig:19). -/
inductive AKind where
  | always | always_or_unreachable | sometimes | reachable | unreachable
  deriving BEq, Repr, Inhabited, DecidableEq

def AKind.name : AKind → String
  | .always => "always" | .always_or_unreachable => "always_or_unreachable" | .sometimes => "sometimes"
  | .reachable => "reachable" | .unreachable => "unreachable"

/-- What a timeline's composer said, with the moment. -/
inductive Ev where
  /-- A start of command `cmd` (its pid), how it was announced. -/
  | start (pid cmd : Nat) (mode : String) (t : Nat)
  /-- composer.zig:1199 `report_exit`: the status it reported, or killed. -/
  | exit (pid cmd : Nat) (status : Option Nat) (killed : Bool) (t : Nat)
  | assertion (kind : AKind) (message : String) (cond : Bool) (t : Nat)
  | declare (kind : AKind) (message : String)
  /-- The fault injector runs (on) or stops (off). -/
  | faults (on : Bool) (t : Nat)
  | note (text : String) (t : Nat)
  deriving Repr, Inhabited

/-- A running child (composer.zig:134 `Running`), with what the world decided for it. -/
structure Proc where
  pid : Nat
  cmd : Nat
  /-- When it ends: on its own, or when the composer killed it. -/
  stop : Nat
  exit : Exit
  /-- Killed by the composer while it still ran (kill_all). -/
  killed : Bool := false
  deriving Repr, Inhabited

/-- What truly happened to a start (the world's view, beside what the composer reported). -/
structure Inst where
  pid : Nat
  cmd : Nat
  start : Nat
  /-- When it ended, and how: on its own (its exit), or killed by the composer. -/
  endedAt : Option Nat := none
  ownExit : Option Exit := none
  killedByComposer : Bool := false
  /-- What reap reported: killed (true) or its status (false). -/
  reportedKilled : Option Bool := none
  deriving Repr, Inhabited

inductive Ending where
  | eventually | finally | none
  deriving BEq, Repr, Inhabited

structure W where
  decisions : Decisions := {}
  consts : Consts := {}
  cmdline : Cmdline := {}
  scenario : Scenario := { commands := [] }
  now : Nat := 0
  /-- The scenario's commands but its setup (composer.zig:419-436); the setup is index
  `commands.size`. -/
  commands : Array Command := #[]
  setup : Option Command := none
  running : Array Proc := #[]
  nextPid : Nat := 1
  interrupted : Nat := 0
  startedCount : Nat := 0
  startedSaid : List Nat := []
  completedSaid : List Nat := []
  exitSuccessSaid : Bool := false
  faultsOn : Bool := false
  faultsStarted : Option Nat := none
  faultsStopped : Option Nat := none
  driveStart : Option Nat := none
  lengthEnd : Option Nat := none
  singletonTimeline : Bool := false
  swarmed : Bool := false
  log : Array Ev := #[]
  insts : Array Inst := #[]
  steps : Nat := 0
  /-- Round 5: the explorer's yes to `composer.again` given (advisor.zig:79-83: `again_left`
  1, then no). -/
  againTaken : Nat := 0
  deriving Inhabited

instance : Chaotic W where
  decisions w := w.decisions
  setDecisions w d := { w with decisions := d }

abbrev M := EStateM Stop W

/-- A composer `assert` that fails: ReleaseSafe panics there (the timeline loses its composer). -/
def panic {α : Type} (msg : String) : M α := throw (.violation "composer panics" msg)

def check (ok : Bool) (msg : String) : M Unit := unless ok do panic msg

def tick : M Unit := do
  modify fun w => { w with steps := w.steps + 1 }
  if (← get).steps > (← get).consts.fuel then throw .limit

def emit (e : Ev) : M Unit := modify fun w => { w with log := w.log.push e }
def nowM : M Nat := do pure (← get).now
def note (text : String) : M Unit := do emit (.note text (← nowM))
def sleepUntil (t : Nat) : M Unit := modify fun w => { w with now := max w.now t }
def assertComputed (kind : AKind) (cond : Bool) (message : String) : M Unit := do
  emit (.assertion kind message cond (← nowM))

def cmdOf (w : W) (i : Nat) : Command :=
  if i < w.commands.size then w.commands[i]! else w.setup.getD default

def setCommand (i : Nat) (c : Command) : M Unit :=
  modify fun w => { w with commands := w.commands.set! i c }

/-- composer.zig:177 `kind_count`: the kept commands of `kind`. -/
def kindCount (w : W) (kind : Kind) : Nat :=
  w.commands.foldl (fun n c => if c.kind == kind && c.kept then n + 1 else n) 0

/-- composer.zig:188 `pick`. -/
def pick (kind : Kind) : M Nat := do
  let w ← get
  let count := kindCount w kind
  check (count > 0) "pick: no kept command of its kind (composer.zig:190)"
  let listed := (List.range w.commands.size).filter fun i =>
    w.commands[i]!.kind == kind && w.commands[i]!.kept
  let total := listed.foldl (fun t i => t + w.commands[i]!.weight) 0
  if total == listed.length then
    let v ← below "composer.command" listed.length
    return listed[v]!
  let mut draw ← below "composer.command_weighted" total
  for i in listed do
    let weight := w.commands[i]!.weight
    if draw < weight then return i
    draw := draw - weight
  panic "unreachable (composer.zig:211)"

def isDriver (k : Kind) : Bool := k == .parallel_driver || k == .serial_driver
def swarmable (k : Kind) : Bool := isDriver k || k == .anytime

/-- composer.zig:686-692 `rescue_counts` (3939448): the marked workload's among the swarm's
commands when one is marked, else the drivers, else (none) the anytime commands. -/
def rescueCounts (kind : Kind) (workload workloadMarked : Bool) (drivers : Nat) : Bool :=
  if !isDriver kind && kind != .anytime then false
  else if workloadMarked then workload
  else if drivers > 0 then isDriver kind else kind == .anytime

/-- composer.zig:221 `swarm_commands`. -/
def swarmCommands : M Unit := do
  let w ← get
  if w.cmdline.swarmOff then return
  modify fun w => { w with swarmed := true }
  -- composer.zig:226-235 (3939448): marked among the swarm's commands only, drivers counted.
  let workloadMarked := w.commands.any fun c => swarmable c.kind && c.workload
  let nSwarmable := w.commands.foldl (fun n c => if swarmable c.kind then n + 1 else n) 0
  let drivers := w.commands.foldl (fun n c => if isDriver c.kind then n + 1 else n) 0
  if !workloadMarked && nSwarmable ≤ 4 then
    for i in [0:w.commands.size] do
      let c := (← get).commands[i]!
      if !swarmable c.kind then continue
      let v ← below s!"composer.weight {c.name}" 7
      setCommand i { c with weight := 2 ^ v }
      note s!"command_weight {c.name} {2 ^ v}"
    return
  let eighths := 1 + (← below "composer.swarm_p" 7)
  let mut needed := 0
  let mut neededKept := 0
  for i in [0:w.commands.size] do
    let c := (← get).commands[i]!
    let driver := isDriver c.kind
    if !driver && c.kind != .anytime then continue
    let v ← below s!"composer.swarm {c.name}" 8
    let kept := v < eighths || w.cmdline.keep.contains c.name
    setCommand i { c with kept }
    let counts := rescueCounts c.kind c.workload workloadMarked drivers
    if counts then needed := needed + 1
    if counts && kept then neededKept := neededKept + 1
  if needed > 0 && neededKept == 0 then
    let mut pickIndex ← below "composer.swarm_one" needed
    for i in [0:w.commands.size] do
      let c := (← get).commands[i]!
      let counts := rescueCounts c.kind c.workload workloadMarked drivers
      if !counts then continue
      if pickIndex == 0 then setCommand i { c with kept := true }
      pickIndex := pickIndex - 1 -- `-|=`: saturating
  for c in (← get).commands do
    if !c.kept then note s!"command_left_out {c.name} kept_eighths={eighths}"

/-- composer.zig:276 `start`: the world decides how this start runs. -/
def start (ci : Nat) : M Unit := do
  let w ← get
  check (w.running.size < w.consts.runningMax) "running_max (composer.zig:277)"
  let c := cmdOf w ci
  unless w.startedSaid.contains ci do
    modify fun w => { w with startedSaid := ci :: w.startedSaid }
    assertComputed .reachable true s!"test command started: {c.name}"
  let runs := if c.runs.isEmpty then w.consts.runMenu else c.runs
  let exits := if c.exits.isEmpty then w.consts.exitMenu else c.exits
  let r ← below s!"world.run_ms {c.name}" runs.length
  let e ← below s!"world.exit {c.name}" exits.length
  let w ← get
  let pid := w.nextPid
  let p : Proc := { pid, cmd := ci, stop := w.now + runs[r]!, exit := exits[e]! }
  emit (.start pid ci "" w.now)
  set { w with running := w.running.push p, nextPid := pid + 1, startedCount := w.startedCount + 1,
               insts := w.insts.push { pid, cmd := ci, start := w.now } }

/-- composer.zig:587 `announce`. -/
def announce (ci : Nat) (mode : String) : M Unit := do
  let w ← get
  note s!"command_start {(cmdOf w ci).name} {mode}"

/-- composer.zig:1199 `report_exit`. -/
def reportExit (p : Proc) (killed : Bool) : M Unit := do
  let w ← get
  let name := (cmdOf w p.cmd).name
  if killed then
    emit (.exit p.pid p.cmd none true w.now)
    return
  let bits := p.exit.bits
  let exited := bits % 128 == 0
  if exited && !w.completedSaid.contains p.cmd then
    modify fun w => { w with completedSaid := p.cmd :: w.completedSaid }
    assertComputed .reachable true s!"test command completed: {name}"
  let code := if exited then (bits / 256) % 256 else 128 + bits % 128
  emit (.exit p.pid p.cmd (some code) false (← nowM))
  let w ← get
  if code != 0 || !w.exitSuccessSaid then
    modify fun w => { w with exitSuccessSaid := w.exitSuccessSaid || code == 0 }
    assertComputed .always (code == 0) "test commands exit successfully"

/-- composer.zig:309 `reap`: one exited child reported, waited for when `hang`. -/
def reap (killed hang : Bool) : M Bool := do
  let w ← get
  check (w.running.size > 0) "reap with nothing running (composer.zig:310)"
  let exited := (List.range w.running.size).filter fun i => w.running[i]!.stop ≤ w.now
  if exited.isEmpty then
    if !hang then return false
    let next := w.running.foldl (fun m p => min m p.stop) w.running[0]!.stop
    sleepUntil next
  let w ← get
  let exited := (List.range w.running.size).filter fun i => w.running[i]!.stop ≤ w.now
  let idx := exited.foldl (fun best i => if w.running[i]!.pid < w.running[best]!.pid then i else best)
    exited.head!
  let p := w.running[idx]!
  let bits := p.exit.bits
  let signaled := bits % 128 != 0 || (bits / 256) % 256 ≥ 128
  -- composer.zig:335-340 (3939448): killed by the composer only when SIGKILL ended it.
  let byKill := killed && bits % 128 == 9
  if signaled || byKill then modify fun w => { w with interrupted := w.interrupted + 1 }
  reportExit p byKill
  modify fun w =>
    let insts := w.insts.map fun inst =>
      if inst.pid == p.pid then
        { inst with endedAt := some p.stop, ownExit := if p.killed then none else some p.exit,
                    killedByComposer := p.killed, reportedKilled := some byKill }
      else inst
    { w with running := swapRemove w.running idx, insts }
  return true

/-- composer.zig:375 `wait_below` (`deadline` none: maxInt, waited for as they end). -/
def waitBelow (count : Nat) (deadline : Option Nat) : M Unit := do
  for _ in [0:(← get).consts.fuel] do
    tick
    if (← get).running.size < count then return
    match deadline with
    | none =>
      let r ← reap false true
      check r "wait_below (composer.zig:378)"
    | some dl =>
      if ← reap false false then continue
      let now ← nowM
      if now ≥ dl then return
      -- The Zig sleeps to min(deadline, now + poll) and reaps again; nothing changes until a
      -- child exits, so the replica goes at once to the first poll at or past the earliest exit
      -- (or to the deadline): the same polls' outcome, without the empty ones.
      let w ← get
      let poll := max 1 w.consts.pollMs
      let minStop := w.running.foldl (fun m p => min m p.stop) w.running[0]!.stop
      let k := max 1 ((minStop - now + poll - 1) / poll)
      sleepUntil (min dl (now + k * poll))
  throw .limit

/-- composer.zig:363 `wait_all` (wait_one until none runs). -/
def waitAll : M Unit := waitBelow 1 none

/-- composer.zig:369 `wait_until`. -/
def waitUntil (deadline : Nat) : M Unit := waitBelow 1 (some deadline)

/-- composer.zig:390 `kill_all`: every running command killed (its group), then reaped as killed.
A child that had exited already (a zombie) keeps its exit; at 3939448 it is reaped as killed all
the same. At 62e06e3 (composer.zig:401-412) what ended on its own is reaped first, judged by its
own status (`while (running_count > 0 and reap(false, false)) {}`), then the rest killed. -/
def killAll : M Unit := do
  if (← get).consts.ver.since62 then
    for _ in [0:(← get).consts.fuel] do
      tick
      if (← get).running.size == 0 then break
      if !(← reap false false) then break
  modify fun w => { w with running := w.running.map fun p =>
    if p.stop > w.now then { p with stop := w.now, exit := .signal 9, killed := true } else p }
  for _ in [0:(← get).consts.fuel] do
    tick
    if (← get).running.size == 0 then return
    let r ← reap true true
    check r "kill_all (composer.zig:395)"
  throw .limit

/-- composer.zig:398 `run_to_completion`. -/
def runToCompletion (ci : Nat) : M Unit := do
  check ((← get).running.size == 0) "run_to_completion with commands running (composer.zig:399)"
  announce ci "complete"
  start ci
  waitAll

/-- composer.zig:413-419 `run_alone_until` (3939448): alone until it ends or `deadline` (a
length's end; none: run_to_completion). -/
def runAloneUntil (ci : Nat) (deadline : Option Nat) : M Unit := do
  match deadline with
  | none => runToCompletion ci
  | some dl =>
    check ((← get).running.size == 0) "run_alone_until with commands running (composer.zig:415)"
    announce ci "complete"
    start ci
    waitUntil dl

/-- composer.zig:338 `faults_start`. -/
def faultsStart : M Unit := do
  let w ← get
  if w.faultsOn then panic "faults_start twice (composer.zig:339)"
  if !w.scenario.faults then return
  modify fun w => { w with faultsOn := true, faultsStarted := some w.now }
  emit (.faults true w.now)
  assertComputed .reachable true "the fault injector started"

/-- composer.zig:353 `faults_stop`. -/
def faultsStop : M Unit := do
  let w ← get
  if !w.faultsOn then return
  modify fun w => { w with faultsOn := false, faultsStopped := some w.now }
  emit (.faults false w.now)

/-- composer.zig:1220 `pause`. -/
def pause (ms : Nat) : M Unit := modify fun w => { w with now := w.now + ms }

/-- composer.zig:659 `singleton_drawn`. -/
def singletonDrawn : M Bool := do
  if (← get).cmdline.swarmOff then return (← below "random_below" 2) == 0
  let eighths := 1 + (← below "composer.singleton_eighths" 7)
  return (← below "composer.singleton" 8) < eighths

/-- composer.zig:715-737 `run_singleton` (3939448): its end when --timeline gave a length (a
drawn length does not bound it, by design). -/
def runSingleton : M (Option Nat) := do
  check (kindCount (← get) .singleton_driver > 0) "run_singleton (composer.zig:666)"
  if kindCount (← get) .anytime > 0 then
    if (← below "random_below" 2) == 0 then
      let a ← pick .anytime
      announce a "start"
      start a
  let d ← pick .singleton_driver
  announce d "start"
  start d
  if let some length := (← get).cmdline.timelineMs then
    let endT := (← nowM) + length
    waitUntil endT
    return some endT
  waitAll
  return none

/-- composer.zig:693 `starts_draw`. -/
def startsDraw : M Nat := do
  let w ← get
  if w.cmdline.swarmOff then return 4 + (← below "random_below" (w.consts.startsMax - 4))
  let low := 2 <<< (← below "composer.starts_log2" w.consts.startsLog2)
  return low + (← below "composer.starts" low)

/-- composer.zig:837 `drive_drawn_ns`. -/
def driveDrawn (driveMsMax : Option Nat) : M (Option Nat) := do
  match driveMsMax with
  | none => return none
  | some maxMs =>
    let top := max 1 (maxMs >>> (← below "composer.drive_ms" 7))
    let ms := top / 2 + (← below "random_below" (top - top / 2 + 1))
    note s!"drive_drawn {ms} {maxMs}"
    return some ms

/-- composer.zig:752 `Load`. -/
structure Load where
  parallelism : Nat
  log2Max : Nat
  /-- none: maxInt (--no-swarm). -/
  untilT : Option Nat
  quiet : Bool := false

/-- composer.zig:760 `Load.next`. -/
def loadNext (load : Load) (endT : Option Nat) : M (Bool × Load) := do
  let now ← nowM
  let c := (← get).consts
  let mut load := load
  if load.untilT.isSome && now ≥ load.untilT.get! then
    let shape ← below "composer.load" 3
    let stretch ← if shape == 1 then pure (c.quietBase + (← below "composer.quiet_ms" c.quietRange))
      else pure (c.loadBase + (← below "composer.load_ms" c.loadRange))
    let parallelism ← match shape with
      | 0 => pure (2 ^ (← below "composer.parallelism_log2" (load.log2Max + 1)))
      | 1 => pure 1
      | _ => pure (2 ^ load.log2Max)
    load := { load with untilT := some (now + stretch), quiet := shape == 1, parallelism }
    note s!"composer_load {shape} {parallelism} {stretch}"
  if !load.quiet then return (true, load)
  let untilT := load.untilT.getD now
  sleepUntil (match endT with | some e => min untilT e | none => untilT)
  return (false, load)

/-- composer.zig:814 `driver_start_by` (3939448); 62e06e3's (883-898) takes the slot's deadline
(`start_by_ns`) and a serial driver's bound (`run_until_ns`) apart: `runUntil` defaults to the
slot's deadline, as 3939448's one deadline did. -/
def driverStartBy (kinds : List Kind) (parallelism : Nat) (deadline : Option Nat)
    (runUntil : Option Nat := deadline) : M Unit := do
  let kind := kinds[(← below "random_below" kinds.length)]!
  match kind with
  | .serial_driver =>
    waitBelow 1 deadline
    if (← get).running.size > 0 then return
    runAloneUntil (← pick .serial_driver) runUntil
  | .parallel_driver | .anytime =>
    waitBelow parallelism deadline
    if (← get).running.size ≥ parallelism then return
    let c ← pick kind
    announce c "start"
    start c
  | _ => panic "unreachable (composer.zig:829)"
  pause (← below "random_below" (← get).consts.pauseMax)

/-- composer.zig:700 `run_drivers`: when the timeline's length ends, if it has one. a7fe05d
(composer.zig:767, 801-804) takes the drivers' start: every phase's stop is half the limit since
the drivers began; 62e06e3 drew it from the phase's own start (CE42). -/
def runDrivers (driveStart : Nat) (driveMsMax : Option Nat) (parallelMax : Option Nat) : M (Option Nat) := do
  let w ← get
  let timelineMs ← match w.cmdline.timelineMs with
    | some l => pure (some l)
    | none => driveDrawn driveMsMax
  let starts ← if timelineMs.isNone then startsDraw else pure 0
  let log2Max := match parallelMax with
    | some most => min w.consts.parallelismLog2Max (Nat.log2 (max most 1))
    | none => w.consts.parallelismLog2Max
  let parallelism := 2 ^ (← below "composer.parallelism_log2" (log2Max + 1))
  let now0 ← nowM
  let mut load : Load := { parallelism, log2Max,
                           untilT := if w.cmdline.swarmOff then none else some now0 }
  check (starts ≤ w.consts.startsMax) "starts_max (composer.zig:709)"
  let w ← get
  let kinds := [Kind.parallel_driver, .serial_driver, .anytime].filter (kindCount w · > 0)
  check (kinds.length > 0) "run_drivers: no driver kind kept (composer.zig:718: assert(kinds.len > 0))"
  match timelineMs with
  | some length =>
    let endT := (← nowM) + length
    for _ in [0:w.consts.fuel] do
      tick
      if (← nowM) ≥ endT then return some endT
      let (ok, l) ← loadNext load (some endT)
      load := l
      if !ok then continue
      driverStartBy kinds load.parallelism (some endT)
    throw .limit
  | none =>
    let stop := w.cmdline.timelineLimitMs.map fun limit =>
      if w.consts.ver.sinceA7 then driveStart + limit / 2 else w.now + limit / 2
    for started in [0:starts] do
      -- composer.zig:795-803 (3939448): the stop checked after a quiet stretch too.
      for _ in [0:w.consts.fuel] do
        tick
        let (ok, l) ← loadNext load stop
        load := l
        if ok then break
        if let some s := stop then
          if (← nowM) ≥ s then break
      if let some s := stop then
        if (← nowM) ≥ s then
          note s!"drivers_stopped {started} {starts}"
          break
      -- composer.zig:809-813 (62e06e3): the slot waited for until the stop at most; a serial
      -- driver started runs to its end (no length bounds it here). 3939448: no deadline.
      if w.consts.ver.since62 then driverStartBy kinds load.parallelism stop (runUntil := none)
      else driverStartBy kinds load.parallelism none
    return none

/-- composer.zig:792 `min_drive`. -/
def minDrive (driveStart : Nat) (scenarioMs : Option Nat) : M Unit := do
  let w ← get
  if w.running.size == 0 then return
  let maxMs := match w.cmdline.minDriveMs with
    | some ms => ms
    | none => scenarioMs.getD w.consts.minDriveDefault
  if maxMs == 0 then return
  let floor := maxMs / 10
  let drawn := floor + (← below "composer.min_drive_ms" (maxMs - floor + 1))
  let running := w.running.size
  waitUntil (driveStart + drawn)
  note s!"min_drive drawn={drawn} running={running} ended={running - (← get).running.size}"

/-- composer.zig:878 `drive_again`. -/
def driveAgain (driveStart : Nat) : M Bool := do
  let w ← get
  if let some limit := w.cmdline.timelineLimitMs then
    if w.now - driveStart ≥ limit / 4 then return false
  if !w.cmdline.againAsked then return false
  -- advisor.zig:79-83: yes `again_left` (1) times, then no.
  if w.againTaken ≥ 1 then return false
  let yes := (← below "composer.again" 2) == 1
  if yes then modify fun w => { w with againTaken := w.againTaken + 1 }
  return yes

/-- composer.zig:931 `ending_pick`. -/
def endingPick : M Ending := do
  let w ← get
  let ev := kindCount w .eventually > 0
  let fin := kindCount w .finally > 0
  -- Zig's `and`/`or` short-circuit: the coin is drawn only when the scenario has both.
  if ev then
    if !fin then return .eventually
    if (← below "random_below" 2) == 0 then return .eventually
  return if fin then .finally else .none

def endingWindowProperty := "an ending command finishes within its window"

/-- composer.zig:955 `run_ending_command`. -/
def runEndingCommand (ci : Nat) (windowMs : Nat) : M Unit := do
  check ((← get).running.size == 0) "run_ending_command (composer.zig:956)"
  announce ci "complete"
  start ci
  waitUntil ((← nowM) + windowMs)
  let finished := (← get).running.size == 0
  assertComputed .always finished endingWindowProperty
  if !finished then killAll

/-- composer.zig:938 `run_ending`. -/
def runEnding (ending : Ending) (windowMs : Nat) : M Unit := do
  check ((← get).running.size == 0) "run_ending (composer.zig:939)"
  match ending with
  | .eventually => runEndingCommand (← pick .eventually) windowMs
  | .finally =>
    if (← get).interrupted == 0 then runEndingCommand (← pick .finally) windowMs
    else note s!"finally_skipped interrupted={(← get).interrupted}"
  | .none => pure ()

/-- composer.zig:1174 `commands_declare`. -/
def commandsDeclare : M Unit := do
  let w ← get
  if w.scenario.faults then emit (.declare .reachable "the fault injector started")
  for c in w.commands do
    emit (.declare .reachable s!"test command started: {c.name}")
    emit (.declare .reachable s!"test command completed: {c.name}")

/-- composer.zig:406 `main`, from the scenario's commands on (no script, no dev mode). -/
def main : M Unit := do
  let w ← get
  let sc := w.scenario
  let mut setup : Option Command := none
  let mut commands : Array Command := #[]
  for c in sc.commands do
    if c.kind == .setup then
      if setup.isSome then panic "SeveralSetupCommands (composer.zig:424)"
      setup := some c
      continue
    commands := commands.push c
  modify fun w => { w with commands, setup }
  if setup.isSome then runToCompletion commands.size
  -- sdk.setup_complete: the snapshot every timeline starts from.
  note "setup_complete"
  commandsDeclare
  let w ← get
  let drivers := kindCount w .parallel_driver + kindCount w .serial_driver
  let singletons := kindCount w .singleton_driver
  let selfDriven := drivers + singletons + kindCount w .anytime == 0
  if selfDriven && !sc.templates then throw (.violation "composer errs" "NoDriverCommands (composer.zig:463)")
  -- composer.zig:905-927 `clock_start_draw`: the wall clock's start, a band by name then a plain
  -- draw in it. Changes no command's timing (the monotonic clock stays). 3939448 drew it after
  -- the composer_start event, an hour's cap by default; 62e06e3 (491-496, 913-914) before it, 30
  -- minutes by default.
  if w.consts.ver == .v3939448 then note "composer_start"
  if w.consts.irrelevantDraws then
    let maxMs := w.cmdline.clockStartMaxMs.getD (if w.consts.ver == .v3939448 then 3600000 else 1800000)
    let bands := clockStartBands maxMs
    if bands > 0 then
      let band ← below "composer.clock_start" bands
      let (low, high) := clockStartBand maxMs band
      let ms := low + (← below "random_below" (high - low + 1))
      note s!"clock_start {ms} {maxMs}"
  if w.consts.ver.since62 then note "composer_start"
  if w.consts.irrelevantDraws && w.cmdline.driversCpuWeight.isNone && !w.cmdline.swarmOff then
    let _ ← below "composer.drivers_cpu" 3
  if kindCount (← get) .first > 0 then runToCompletion (← pick .first)
  let singletonTimeline ← if singletons > 0 then
      (if drivers == 0 then pure true else singletonDrawn)
    else pure false
  modify fun w => { w with singletonTimeline }
  -- swarm_seed_write (composer.zig:978): "swarm.seed", 2^64 options, only seeds sdk.swarm_choice
  -- in the commands: not modeled.
  if !singletonTimeline && !selfDriven then swarmCommands
  note "faults_phase start"
  faultsStart
  let driveStart ← nowM
  modify fun w => { w with driveStart := some driveStart }
  let mut lengthEnd : Option Nat := none
  let driveMax := sc.driveMsMax <|> w.cmdline.driveMsMax
  if selfDriven then
    let length ← match w.cmdline.timelineMs with
      | some l => pure l
      | none => match ← driveDrawn driveMax with
        | some l => pure l
        | none => match w.cmdline.timelineLimitMs with
          | some limit => pure (limit / 2)
          | none => throw (.violation "composer errs" "NoDriverCommands (composer.zig:485)")
    note s!"self_driven {length}"
    sleepUntil (driveStart + length)
  else if singletonTimeline then
    lengthEnd ← runSingleton
  else
    lengthEnd ← runDrivers driveStart driveMax sc.parallelMax
    for _ in [0:4] do
      if !(← driveAgain driveStart) then break
      lengthEnd ← runDrivers driveStart driveMax sc.parallelMax
  modify fun w => { w with lengthEnd }
  let ending ← endingPick
  if ending == .eventually then
    minDrive driveStart sc.minDriveMs
    killAll
  else if let some endT := lengthEnd then
    waitUntil (endT + (← get).consts.graceMs)
    if (← get).running.size > 0 then
      note s!"length_reached running={(← get).running.size}"
      -- composer.zig:534-539 (3939448): only the length's own kills forgiven.
      let interrupted := (← get).interrupted
      killAll
      modify fun w => { w with interrupted }
  else waitAll
  faultsStop
  note "faults_phase stop"
  runEnding ending (sc.endingMsMax.getD (← get).consts.endingDefault)
  note s!"composer_done {(← get).startedCount}"

/-- One timeline: the composer's final state, and how it ended (`none`: composer_done). -/
def runTimeline (scenario : Scenario) (cmdline : Cmdline) (consts : Consts) (source : Source) :
    W × Option Stop :=
  let w0 : W := { decisions := { source }, consts, cmdline, scenario }
  match main.run w0 with
  | .ok _ w => (w, none)
  | .error e w => (w, some e)

end Replica.Composer
