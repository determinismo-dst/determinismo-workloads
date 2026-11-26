import Replica.Prelude
import Replica.Searching

/-!
# A run's recorded request against the machine its analyses boot (round 6)

a7fe05d's own fix: a run started from a command line records `--clock-start-max` in its request
(main.zig:1400-1406, `run_request_write`), so serve's analyses of it boot its guest's command line
(the test "a run's request keeps what its guest's command line needs: the wall clock's start",
main.zig:1354-1369). What an analysis boots (serve.zig: `replay_argv` 2865-2880 and the
analyses at 2201, 4173, 4350, 4699, 4849): the run's explorer, `run_machine` (its machine.json,
6639-6645), `system_arguments` (its request.json, 5565-5600).

The machine's inputs (main.zig:8676-8705 `inputs_hash`): the kernel, the initramfs (the system
`prepare` builds, injectors included: main.zig:1680-1695), the guest's command line
(`cmdline_build`, 1835-1908: `det.timeline_limit_ms=` always, an hour by default; `det.swarm=0`;
`det.clock_start_max_ms=`; `det.drive_ms_max=` ...), the timers' slack and landing, the epoch
when not the default. A tape whose header's inputs differ is refused (2615-2621,
TapeInputsDiffer).

What a command-line run records (main.zig:1374-1487): request.json (`serve.RunRequest`: no
`timeline_limit`, `swarm` left at its default, no `injectors`) and machine.json (kernel, initrd,
cmdline as given, cache, memory, branch event, the clock's jitter, cpuid, guest CPU, disks: no
`--epoch`, `--timer-slack-us`, `--timer-landing-permille`). A run serve starts records the
request it was posted (with `timeline_limit`, `swarm`, `injectors`) and serve's own machine
options as its machine.json: its analyses boot what it booted.

The property (a7fe05d's test and comment, 1402-1405: "In the guest's command line too: left out,
serve's analyses of a run started with --clock-start-max 0 booted another guest line, and its
tapes were refused"; the request's own comments: "In the guest's command line: replays need
it"): an analysis of a run boots the inputs the run's tapes were recorded with.
-/

namespace Replica.Request6

open Determinismo

/-- What explore was given (the parts that reach the machine's inputs). -/
structure Asked where
  timelineLimitMs : Nat := 3600000
  swarm : Bool := true
  clockStartMaxMs : Option Nat := none
  driveMaxMs : Option Nat := none
  epoch : Option Nat := none
  timerSlackUs : Nat := 1000
  timerLandingPermille : Nat := 0
  injectors : List String := []
  deriving Repr, BEq, Inhabited

/-- The machine's inputs (inputs_hash's parts): the command line's words, the timers, the epoch,
the initramfs's injectors. -/
def inputs (a : Asked) : List String :=
  [s!"det.timeline_limit_ms={a.timelineLimitMs}"] ++
  (if a.swarm then [] else ["det.swarm=0"]) ++
  (match a.clockStartMaxMs with | some ms => [s!"det.clock_start_max_ms={ms}"] | none => []) ++
  (match a.driveMaxMs with | some ms => [s!"det.drive_ms_max={ms}"] | none => []) ++
  [s!"timer_slack_ns={a.timerSlackUs * 1000}"] ++
  (if a.timerLandingPermille == 0 then [] else [s!"timer_delay_permille={a.timerLandingPermille}"]) ++
  (match a.epoch with | some e => [s!"epoch_seconds={e}"] | none => []) ++
  a.injectors.map (s!"initramfs injector {·}")

/-- What an analysis boots of a command-line run: its request (as `run_request_write` at `ver`
wrote it) through `system_arguments`, its machine.json through `run_machine`. df8f08b
(main.zig:1441-1453, 1519-1522; CE51's fix): `timeline_limit` as given, `swarm`, `injectors` (kept
by content) in the request, which system_arguments gives again (serve.zig:5595-5602); `--epoch`,
`--timer-slack-us`, `--timer-landing-permille` in machine.json when not the default: every input. -/
def analysisOfCommandLine (ver : Ver) (a : Asked) : Asked :=
  -- Round 7: the injectors in the request are the kept copies (runs.zig:217-219,
  -- `<hash>-<basename>`), which the run never booted: the system disk takes each by its
  -- basename (prepare.zig:195-199, 1464-1471), so the analysis's is another disk.
  if ver.sinceDf then { a with injectors := a.injectors.map ("0123456789abcdef-" ++ ·) } else
  { timelineLimitMs := 3600000          -- no `timeline_limit` in the request: the default hour
    swarm := true                        -- `swarm` written at its default
    clockStartMaxMs := if ver.sinceA7 then a.clockStartMaxMs else none   -- a7fe05d's fix
    driveMaxMs := a.driveMaxMs           -- `drive_max`, recorded since before
    epoch := none                        -- not in machine.json
    timerSlackUs := 1000
    timerLandingPermille := 0
    injectors := [] }                    -- no `injectors` in the request

/-- What an analysis boots of a run serve started: the posted request and serve's machine. -/
def analysisOfServeRun (a : Asked) : Asked := a

def menu : List (String × (Asked → Asked)) :=
  [ ("--timeline-limit 30s", fun a => { a with timelineLimitMs := 30000 }),
    ("--no-swarm", fun a => { a with swarm := false }),
    ("--clock-start-max 0", fun a => { a with clockStartMaxMs := some 0 }),
    ("--drive-max 5m", fun a => { a with driveMaxMs := some 300000 }),
    ("--epoch 2030-01-01", fun a => { a with epoch := some 1893456000 }),
    ("--timer-slack-us 50", fun a => { a with timerSlackUs := 50 }),
    ("--timer-landing-permille 500", fun a => { a with timerLandingPermille := 500 }),
    ("--injector ./chaos", fun a => { a with injectors := ["./chaos"] }) ]

structure S where
  decisions : Decisions := {}
  deriving Inhabited

instance : Chaotic S where
  decisions s := s.decisions
  setDecisions _ d := { decisions := d }

structure World where
  label : String
  /-- Who started the run: a command line (explore with a run directory) or serve. -/
  commandLine : Bool := true
  /-- The commit whose explorer wrote the request (a run recorded before a7fe05d), and serve's. -/
  recordedBy : Ver := .vdf8f08b
  deriving Inhabited

def draw : EStateM Stop S (List String × Asked) := do
  let mut given := []
  let mut a : Asked := {}
  for (flag, f) in menu do
    if (← below s!"world.flag {flag}" 2) == 1 then
      given := given ++ [flag]
      a := f a
  return (given, a)

def property : String := "an analysis of a run (causality, explain, a session, a replay) boots the inputs its tapes were recorded with"
def source : String := "src/main.zig:1400-1406 (a7fe05d: \"In the guest's command line too: left out, serve's analyses of a run started with --clock-start-max 0 booted another guest line, and its tapes were refused (TapeInputsDiffer ...)\"), 1354-1369 (its test: \"a run's request keeps what its guest's command line needs\"), 1395-1414 (\"In the guest's command line: replays need it\"); serve.zig:5583-5590 (\"Part of the inputs (the guest's command line): replays need it too\"; \"given to the run alone, every replay and session of a swarm-less run was refused (TapeInputsDiffer ...)\")"

def judge (w : World) (src : Source) : Ended :=
  match draw.run { decisions := { source := src } } with
  | .ok (given, a) s =>
    let booted := if w.commandLine then analysisOfCommandLine w.recordedBy a else analysisOfServeRun a
    let ran := inputs a
    let replayed := inputs booted
    { taken := s.decisions.taken,
      violation := if ran == replayed then none else
        some (property, s!"a {if w.commandLine then "command-line" else "serve"} run{if w.recordedBy != .vdf8f08b then s!" recorded by {reprStr w.recordedBy}" else ""} given {given}: its tapes' inputs {ran}; its analyses boot {replayed}: TapeInputsDiffer, every tape refused") }
  | .error _ s => { taken := s.decisions.taken, violation := none }

def worlds : List World :=
  [ { label := "a run started from a command line (df8f08b)" },
    { label := "a run serve started (df8f08b)", commandLine := false },
    { label := "a command-line run recorded by 62e06e3's explorer, analyzed by df8f08b's serve", recordedBy := .v62e06e3 },
    -- Round 7: a7fe05d's command-line runs (CE51 found again), and such a run recorded before
    -- df8f08b, analyzed by df8f08b's serve (its request has none of the new fields).
    { label := "a command-line run recorded by a7fe05d's explorer, analyzed by df8f08b's serve", recordedBy := .va7fe05d } ]

def searchAll (exhaustRuns : Nat) : IO Unit := do
  say s!"== request property: {property}"
  say s!"   source: {source}"
  for w in worlds do
    if let some f ← exhaustSaid s!"{property} / {w.label}" (judge w) exhaustRuns then
      printFound f (fun _ => [])
  -- Each flag alone, a command-line run.
  for (flag, f) in menu do
    let a := f {}
    say s!"a command-line run given only {flag}: its analyses boot its inputs: {inputs a == inputs (analysisOfCommandLine .vdf8f08b a)} (df8f08b), {inputs a == inputs (analysisOfCommandLine .va7fe05d a)} (a7fe05d), {inputs a == inputs (analysisOfCommandLine .v62e06e3 a)} (62e06e3)"

end Replica.Request6
