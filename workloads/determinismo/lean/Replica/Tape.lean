import Replica.Prelude
import Replica.Searching

/-!
# Tapes and replay, replicated (platform 3939448)

Round 2: a fork's index and serve's status pull say their `decision` event whether answered or
replayed (vm.zig:3691-3694, 3805-3806); `check` stops a replay past the next checkpoint's count
(tape.zig:223-233); `checkpoint_keep` thins again until a slot frees (tape.zig:593-608); and the
tables a replay loads its tape into are modeled with their sizes: `override_count_max` (65,536,
tape.zig:8, `override_parse` 554-556) and `reason_count_max` (1,024, tape.zig:117, 565-567), a
fuller tape refused (`TapeTooLong`).

A timeline's inputs recorded and replayed (src/core/tape.zig, src/core/vm.zig, src/core/decisions.zig):

- the default answer to a pull is a function of (seed, pull index) (decisions.zig:15 `random`);
- a strategy (the explorer's advisor, src/advisor.zig) may override a pull: the override is
  written to the tape with its reason (vm.zig:3813-3829), a `decision` event in the timeline
  when the advice is a decision with a reason;
- the platform's own answers (vm.zig:3645-3803): a fast VM's fact (`det.explore_here`), a
  fork's index (`det.fork_index`), the outside's answers (`det.egress_status`,
  `det.ingress_status`) and serve's (`det.serve_status`): each on the tape, each taken from it
  by a replay, each with its own rule for the `decision` event;
- checkpoints (vm.zig:3384 `checkpoint`): after a guest's event whose count is a multiple of
  `checkpoint_interval` (64), `{events, branches, events_hash}` written to the tape being
  recorded, or compared with the tape being replayed (tape.zig:219 `Overrides.check`: compared
  only when the counts are equal; a mismatch ends the replay, `ReplayDiverged`); a tape's
  checkpoints thinned past `checkpoint_count_max` (tape.zig:585 `checkpoint_keep`);
- a replay from inside a segment (a holder's snapshot, tape.zig:232 `seek_inside`): overrides
  of earlier pulls passed, checkpoints unchecked;
- the VM's own events, which call no checkpoint: `decision` events (vm.zig:3845) and the
  kernel's console lines (vm.zig:2665 `console_line`).

The guest is a program of steps drawn by the world: its events carry the values its pulls got,
so a replay that answers otherwise emits other events. A replay may be perturbed (the world's
`world.perturb`: a kernel line more, a guest event's content changed), as a nondeterminism
would; the documentation says such a replay stops where it diverges.

Constants: the checkpoint interval and the checkpoint table's size are parameters (64 and
16,384 in the Zig).
-/

namespace Replica.Tape

open Determinismo

/-- The pull labels whose answers vm.zig's `decide_random` treats apart. -/
inductive Label where
  | plain | exploreHere | forkIndex | egressStatus | ingressStatus | serveStatus | driveMs
  deriving BEq, Repr, Inhabited, DecidableEq

def Label.name : Label → String
  | .plain => "plain" | .exploreHere => "det.explore_here" | .forkIndex => "det.fork_index"
  | .egressStatus => "det.egress_status" | .ingressStatus => "det.ingress_status"
  | .serveStatus => "det.serve_status" | .driveMs => "composer.drive_ms"

/-- tape.zig:103 `Kind`, told by the override's reason. -/
inductive OKind where
  | decision | egress | ingress | serve
  deriving BEq, Repr, Inhabited, DecidableEq

def egressReason := "an egress answer to the guest (sdk.egress)"
def ingressReason := "an ingress answer to the guest (sdk.ingress)"
def serveReason := "serve's reply to the guest (sdk.serve)"
def forkReason := "a fork's index: 0 where it was asked, k in its future k"
def exploreHereReason := "explore_here"
def driveReason := "the driver phase's length from the run's novelty curve"

/-- tape.zig:108 `kind_of`. -/
def kindOf (reason : String) : OKind :=
  if reason == ingressReason then .ingress
  else if reason == egressReason then .egress
  else if reason == serveReason then .serve
  else .decision

/-- A tape line: an override (pull, value, reason), or a checkpoint; at 62e06e3 also the
recorder's `tape_full` marker (tape.zig:406-414). -/
inductive Line where
  | override (pull : Nat) (value : Nat) (reason : String)
  | checkpoint (events : Nat) (hash : UInt64)
  | full (pull : Nat)
  deriving BEq, Repr, Inhabited

structure Entry where
  pull : Nat
  value : Nat
  kind : OKind
  deriving Repr, Inhabited

/-- tape.zig:129 `Overrides`. -/
structure Overrides where
  entries : Array Entry := #[]
  cursor : Nat := 0
  reasons : Array (Nat × String) := #[]
  reasonCursor : Nat := 0
  checkpoints : Array (Nat × UInt64) := #[]
  checkpointCursor : Nat := 0
  checkpointEvery : Nat := 1
  /-- 62e06e3 (tape.zig:139-141): where its recorder stopped taping. -/
  fullAt : Option Nat := none
  deriving Repr, Inhabited

structure Consts where
  /-- checkpoint_interval (64). -/
  interval : Nat := 4
  /-- checkpoint_count_max (16,384). -/
  checkpointMax : Nat := 3
  /-- override_count_max (65,536): the overrides a replay holds. -/
  overrideMax : Nat := 1000000
  /-- reason_count_max (1,024): the decisions' reasons a replay holds. -/
  reasonMax : Nat := 1000000
  /-- Round 5: tape.zig and vm.zig as at 62e06e3 unless a theorem about 3939448 says so. At
  62e06e3 `overrideMax` (override_count_max, 1,048,576) bounds the recorder too. -/
  ver : Ver := .vdf8f08b
  deriving Repr, Inhabited

/-- tape.zig:603 `checkpoint_kept`. -/
def kept (interval events every : Nat) : Bool := (events / interval) % every == 0

/-- tape.zig:585 `checkpoint_keep`, its `assert(checkpoint_count < checkpoint_count_max)`
(tape.zig:598) an error: ReleaseSafe panics there. -/
def checkpointKeep (c : Consts) (o : Overrides) (cp : Nat × UInt64) : Except String Overrides := do
  if !kept c.interval cp.1 o.checkpointEvery then return o
  let mut o := o
  -- tape.zig:595-606 (3939448): thinned again until a doubling frees a slot.
  for _ in [0:32] do
    if o.checkpoints.size != c.checkpointMax then break
    let every := o.checkpointEvery * 2
    o := { o with checkpointEvery := every,
                  checkpoints := o.checkpoints.filter fun e => kept c.interval e.1 every }
    if !kept c.interval cp.1 o.checkpointEvery then return o
  if o.checkpoints.size ≥ c.checkpointMax then
    throw s!"panic: assert(checkpoint_count < checkpoint_count_max) (tape.zig:598), the checkpoints kept {o.checkpoints.toList.map (·.1)} and {cp.1}"
  return { o with checkpoints := o.checkpoints.push cp }

/-- tape.zig:514 `parse` (and `override_parse`, 548; `checkpoint_parse`, 573). -/
def parse (c : Consts) (lines : List Line) : Except String Overrides := do
  let mut o : Overrides := {}
  -- tape.zig:592-593 (62e06e3): the table sized from the tape's own count of overrides, at most
  -- override_count_max (`reserve`, 180-187).
  if c.ver.since62 then
    let count := (lines.filter fun | .override .. => true | _ => false).length
    if count > c.overrideMax then throw "TapeTooLong (override_count_max)"
  -- tape.zig:605 (a7fe05d): the reason table sized from the tape's own count of lines with a
  -- reason (`,"reason":"`), as the overrides' (CE48's fix); before, reason_count_max.
  let reasonTable := if c.ver.sinceA7 then
      (lines.filter fun | .override _ _ r => !r.isEmpty | _ => false).length
    else c.reasonMax
  for l in lines do
    match l with
    | .checkpoint e h => o ← checkpointKeep c o (e, h)
    | .full pull => o := { o with fullAt := some pull }
    | .override pull value reason =>
      -- tape.zig:554-556 and 565-567: the tables' sizes.
      if o.entries.size == c.overrideMax then throw "TapeTooLong (override_count_max)"
      let kind := kindOf reason
      o := { o with entries := o.entries.push { pull, value, kind } }
      if !reason.isEmpty && kind == .decision then
        if o.reasons.size == reasonTable then throw "TapeTooLong (reason_count_max)"
        o := { o with reasons := o.reasons.push (pull, reason) }
  return o

/-- tape.zig:159 `kind_at`. -/
def Overrides.kindAt (o : Overrides) (pull : Nat) : Option OKind :=
  if o.cursor == o.entries.size then none
  else if o.entries[o.cursor]!.pull == pull then some o.entries[o.cursor]!.kind else none

/-- tape.zig:295-297 (62e06e3) `passed`: the tape's next override is for an earlier pull. -/
def Overrides.passed (o : Overrides) (pull : Nat) : Bool :=
  o.cursor < o.entries.size && o.entries[o.cursor]!.pull < pull

/-- tape.zig:301-305 (62e06e3) `past_full`. -/
def Overrides.pastFull (o : Overrides) (pull : Nat) : Bool :=
  match o.fullAt with
  | some at_ => pull ≥ at_
  | none => false

/-- tape.zig:245 `apply` (62e06e3: 308, TapeFull past the marker). -/
def Overrides.apply (o : Overrides) (pull : Nat) : Except String (Option Nat × Overrides) :=
  if o.pastFull pull then .error "TapeFull"
  else if o.cursor == o.entries.size then .ok (none, o)
  else
    let e := o.entries[o.cursor]!
    if e.pull < pull then .error "TapeOutOfOrder"
    else if e.pull > pull then .ok (none, o)
    else .ok (some e.value, { o with cursor := o.cursor + 1 })

/-- tape.zig:208 `reason`. -/
def Overrides.reason (o : Overrides) (pull : Nat) : Option String × Overrides := Id.run do
  let mut o := o
  while o.reasonCursor < o.reasons.size do
    let (p, r) := o.reasons[o.reasonCursor]!
    if p > pull then return (none, o)
    o := { o with reasonCursor := o.reasonCursor + 1 }
    if p == pull then return (some r, o)
  return (none, o)

/-- tape.zig:219 `check`. -/
def Overrides.check (o : Overrides) (events : Nat) (hash : UInt64) : Except String Overrides :=
  if o.checkpointCursor == o.checkpoints.size then .ok o
  else
    let (e, h) := o.checkpoints[o.checkpointCursor]!
    -- tape.zig:226-233 (3939448): below the next count nothing to compare; at or past it,
    -- compared (past it: diverged).
    if events < e then .ok o
    else if e != events || h != hash then .error s!"ReplayDiverged at event {events}"
    else .ok { o with checkpointCursor := o.checkpointCursor + 1 }

/-- tape.zig:232 `seek_inside`. -/
def Overrides.seekInside (o : Overrides) (pull : Nat) : Overrides := Id.run do
  let mut o := o
  while o.cursor < o.entries.size && o.entries[o.cursor]!.pull < pull do o := { o with cursor := o.cursor + 1 }
  while o.reasonCursor < o.reasons.size && o.reasons[o.reasonCursor]!.1 < pull do
    o := { o with reasonCursor := o.reasonCursor + 1 }
  return { o with checkpointCursor := o.checkpoints.size }

/-- A guest step. -/
inductive Step where
  /-- An event of the guest's (through the doorbell: a checkpoint may follow). -/
  | event
  /-- A kernel console line (an event of the VM's: no checkpoint follows). -/
  | console
  /-- A pull of this label. -/
  | pull (label : Label)
  deriving BEq, Repr, Inhabited

/-- An event: who made it, and what it says (its hash's input). -/
structure Ev where
  text : String
  deriving BEq, Repr, Inhabited

/-- The machine (vm.zig's fields this replicates). -/
structure VM where
  seed : Nat
  pulls : Nat := 0
  events : Array Ev := #[]
  hash : UInt64 := 7
  /-- Recording: the tape written. -/
  tape : Array Line := #[]
  recording : Bool := true
  /-- Replaying: the tape's overrides. -/
  overrides : Option Overrides := none
  values : Array Nat := #[]
  /-- The advisor's answers while recording: (pull index → value, reason, decision). -/
  advice : List (Nat × Nat × String × Bool) := []
  /-- A fork's index (vm.fork_index), 0 unless the machine is a future of a fork. -/
  forkIndex : Nat := 0
  /-- What the outside answers now (egress, ingress, serve), when asked live. -/
  outside : Nat := 1
  error : Option String := none
  /-- Where the replay reported it parted (its event count). -/
  diverged : Option Nat := none
  /-- 62e06e3 (vm.zig:345-347): overrides taped so far, and whether the tape filled. -/
  tapeWritten : Nat := 0
  tapeFull : Bool := false
  /-- The caps and the version (the world's `Consts`). -/
  consts : Consts := {}
  deriving Inhabited

def mix (h : UInt64) (s : String) : UInt64 :=
  s.foldl (fun h c => (h ^^^ c.toNat.toUInt64) * 1099511628211) (h * 31 + 17)

/-- events.zig `emit`: counted and hashed. -/
def emit (vm : VM) (text : String) : VM :=
  { vm with events := vm.events.push { text }, hash := mix vm.hash text }

/-- vm.zig:3384 `checkpoint`, after a guest's event. -/
def checkpoint (c : Consts) (vm : VM) : VM :=
  let count := vm.events.size
  if count % c.interval != 0 then vm
  else
    let vm := if vm.recording then { vm with tape := vm.tape.push (.checkpoint count vm.hash) } else vm
    match vm.overrides with
    | none => vm
    | some o => match o.check count vm.hash with
      | .ok o => { vm with overrides := some o }
      | .error e => { vm with error := some e, diverged := some count }

/-- decisions.zig:15: the default answer, a function of (seed, pull index). -/
def defaultValue (seed pull : Nat) : Nat := (seed * 7 + pull * 3 + 1) % 4

def decisionEvent (vm : VM) (pull : Nat) (reason : String) : VM :=
  emit vm s!"decision pull={pull} reason={reason}"

/-- tape.write_override (3939448); vm.zig:3684-3699 (62e06e3) `tape_override`: override_count_max
at most, then the `tape_full` marker (once, with its event) and nothing more. -/
def writeOverride (vm : VM) (pull value : Nat) (reason : String) : VM :=
  if !vm.recording then vm
  else if vm.consts.ver == .v3939448 then { vm with tape := vm.tape.push (.override pull value reason) }
  else if vm.tapeWritten ≥ vm.consts.overrideMax then
    if vm.tapeFull then vm
    else emit { vm with tapeFull := true, tape := vm.tape.push (.full pull) } s!"tape_full pull={pull} overrides={vm.tapeWritten}"
  else { vm with tape := vm.tape.push (.override pull value reason), tapeWritten := vm.tapeWritten + 1 }

/-- vm.zig:3627 `override_apply` (no extending tape here). -/
def overrideApply (vm : VM) (pull : Nat) : Except String (Option Nat × VM) := do
  match vm.overrides with
  | none => return (none, vm)
  | some o =>
    let (v, o) ← o.apply pull
    return (v, { vm with overrides := some o })

/-- vm.zig:3645 `decide_random`, for one pull of `label`: the value the guest gets. -/
def decideRandom (vm : VM) (label : Label) : Except String (Nat × VM) := do
  let pull := vm.pulls
  -- vm.zig:3708-3709 (62e06e3): past where the tape's recorder stopped, nothing answers.
  if let some o := vm.overrides then
    if o.pastFull pull then throw "TapeFull"
  let mut vm := { vm with pulls := pull + 1 }
  let mut value := defaultValue vm.seed pull
  match label with
  | .exploreHere =>
    -- vm.zig:3660: from the tape when replaying, a fact otherwise; written and said either way.
    let (taped, vm1) ← overrideApply vm pull
    vm := vm1
    value := taped.getD 1
    vm := writeOverride vm pull value exploreHereReason
    vm := decisionEvent vm pull exploreHereReason
    return (value, vm)
  | .forkIndex =>
    -- vm.zig:3680: from the tape only when its override there is a fork's; said only when not.
    let mut taped := none
    if let some o := vm.overrides then
      let (r, o) := o.reason pull
      vm := { vm with overrides := some o }
      if r == some forkReason then
        let (t, vm1) ← overrideApply vm pull
        taped := t
        vm := vm1
    match taped with
    | some v => value := v
    | none =>
      value := vm.forkIndex
      vm := writeOverride vm pull value forkReason
    -- vm.zig:3691-3694 (3939448): said whether answered or replayed.
    vm := decisionEvent vm pull forkReason
    return (value, vm)
  | .egressStatus | .ingressStatus | .serveStatus =>
    let (kind, reason) := match label with
      | .egressStatus => (OKind.egress, egressReason)
      | .ingressStatus => (OKind.ingress, ingressReason)
      | _ => (OKind.serve, serveReason)
    let mut taped := none
    if let some o := vm.overrides then
      if o.kindAt pull == some kind then
        let (t, vm1) ← overrideApply vm pull
        taped := t
        vm := vm1
      else if label == .ingressStatus && vm.consts.ver.since62 then
        -- vm.zig:3806-3815 (62e06e3): an idle poll's nothing is never taped, so a replay answers
        -- a status pull its tape lacks with it, unless the tape's next answer is for an earlier
        -- pull (it passed it: diverged).
        if o.passed pull then throw "TapeOutOfOrder"
        taped := some 1
    match taped with
    | some v => value := v
    | none =>
      value := vm.outside
      -- vm.zig:3837 (62e06e3): an idle poll's nothing (1 here) is not taped.
      if !(label == .ingressStatus && vm.consts.ver.since62 && value == 1) then
        vm := writeOverride vm pull value reason
    match label with
    | .egressStatus => vm := decisionEvent vm pull reason -- vm.zig:3730: answered or replayed
    | .ingressStatus => if value != 1 then vm := decisionEvent vm pull reason -- 3765: when something came
    | _ => vm := decisionEvent vm pull reason -- 3805-3806 (3939448): answered or replayed
    return (value, vm)
  | .plain | .driveMs =>
    match vm.overrides with
    | some o =>
      -- vm.zig:3805: a replay never consults the explorer.
      let (t, vm1) ← overrideApply vm pull
      vm := vm1
      if let some v := t then
        value := v
        let (r, o) := vm.overrides.get!.reason pull
        vm := { vm with overrides := some o }
        if let some reason := r then vm := decisionEvent vm pull reason
      let _ := o
      return (value, vm)
    | none =>
      -- vm.zig:3813: the advisor's answer, taped; said when a decision with a reason.
      if let some (_, v, reason, decision) := vm.advice.find? (·.1 == pull) then
        value := v
        vm := writeOverride vm pull value reason
        if decision && !reason.isEmpty then vm := decisionEvent vm pull reason
      else if label == .driveMs then
        -- vm.zig:3832: the explorer's own answer to the driver phase's length.
        value := 2
        vm := writeOverride vm pull value driveReason
        vm := decisionEvent vm pull driveReason
      return (value, vm)

/-- A perturbation of the replay's guest: a kernel line more before step `at`, or that step's
event saying something else. -/
inductive Perturb where
  | none
  | consoleBefore (step : Nat)
  | eventChanged (step : Nat)
  deriving BEq, Repr, Inhabited

/-- The guest runs its steps; its events carry its pulls' values so far. -/
def runGuest (c : Consts) (steps : List Step) (vm : VM) (perturb : Perturb) : VM := Id.run do
  let mut vm := vm
  let mut i := 0
  for s in steps do
    if vm.error.isSome then break
    if perturb == .consoleBefore i then vm := emit vm "kernel: an extra line"
    match s with
    | .event =>
      let changed := perturb == .eventChanged i
      vm := emit vm s!"guest {i} saw {vm.values.toList}{if changed then " (changed)" else ""}"
      vm := checkpoint c vm
    | .console => vm := emit vm s!"kernel {i}"
    | .pull l =>
      match decideRandom vm l with
      | .ok (v, vm1) => vm := { vm1 with values := vm1.values.push v }
      | .error e => vm := { vm with error := some e, diverged := some vm.events.size }
    i := i + 1
  return vm

structure TS where
  decisions : Decisions := {}
  deriving Inhabited

instance : Chaotic TS where
  decisions s := s.decisions
  setDecisions _ d := { decisions := d }

structure TWorld where
  label : String
  steps : Nat := 6
  labels : List Label := [.plain]
  consoles : Bool := false
  perturbs : Bool := false
  consts : Consts := {}

/-- A world: the guest's steps, the advisor's answers, the replay's perturbation. -/
structure Drawn where
  steps : List Step
  advice : List (Nat × Nat × String × Bool)
  forkIndex : Nat
  outsideRecord : Nat
  outsideReplay : Nat
  perturb : Perturb
  deriving Inhabited

def drawT (wd : TWorld) : EStateM Stop TS Drawn := do
  let kinds : List Step := [.event] ++ (if wd.consoles then [.console] else []) ++ wd.labels.map .pull
  let mut steps := []
  for _ in [0:wd.steps] do steps := steps ++ [kinds[(← below "world.step" kinds.length)]!]
  let npulls := (steps.filter fun | .pull _ => true | _ => false).length
  let mut advice := []
  for p in [0:npulls] do
    let a ← below "strategy.answer" 3
    if a == 1 then advice := advice ++ [(p, 3, "", true)]
    if a == 2 then advice := advice ++ [(p, 0, "the strategy's reason", true)]
  let forkIndex ← below "world.fork_index" 2
  let outsideRecord ← below "world.outside" 2
  let perturb ← if wd.perturbs then do
      let k ← below "world.perturb" 3
      let pos ← below "world.perturb_at" wd.steps
      pure (match k with | 1 => Perturb.consoleBefore pos | 2 => .eventChanged pos | _ => .none)
    else pure .none
  -- The outside answers a replay as it likes: it is never asked (the tape answers).
  return { steps, advice, forkIndex, outsideRecord, outsideReplay := 1 - outsideRecord, perturb }

/-- Record, then replay from the tape. -/
def recordReplay (wd : TWorld) (d : Drawn) (seed : Nat := 5) : VM × VM :=
  let rec0 : VM := { seed, recording := true, advice := d.advice, forkIndex := d.forkIndex, outside := d.outsideRecord, consts := wd.consts }
  let recorded := runGuest wd.consts d.steps rec0 .none
  match parse wd.consts recorded.tape.toList with
  | .error e => (recorded, { seed, recording := false, error := some e })
  | .ok o =>
    let rep0 : VM := { seed, recording := false, overrides := some o, forkIndex := 0, outside := d.outsideReplay, consts := wd.consts }
    let replayed := runGuest wd.consts d.steps rep0 d.perturb
    (recorded, replayed)

structure TProp where
  name : String
  source : String
  check : TWorld → Drawn → VM → VM → Option String

def firstDifference (a b : Array Ev) : Option Nat := Id.run do
  for i in [0:max a.size b.size] do
    if a[i]? != b[i]? then return some (i + 1)
  return none

def replaysExactly : TProp :=
  { name := "a timeline replayed from its tape has its recorded history"
    source := "README_AI.md: \"every timeline replays bit-identically\"; ARCHITECTURE.md M3: \"Record → replay matches all checkpoints\"; vm.zig:3730 (egress): \"a replay's history is the run's\""
    check := fun _ d rec rep =>
      if d.perturb != .none then none
      -- 62e06e3: a full tape stops its replay by design (replaysToItsFull judges it).
      else if rec.tape.any (fun | .full _ => true | _ => false) then none
      else if let some e := rep.error then some s!"the replay stopped: {e} (recorded {rec.events.size} events)"
      else if let some i := firstDifference rec.events rep.events then
        some s!"histories part at event {i}: recorded {(rec.events[i-1]?.map (·.text)).getD "-"}, replayed {(rep.events[i-1]?.map (·.text)).getD "-"}"
      else none }

def pullsRepeat : TProp :=
  { name := "on replay the n-th pull gets the n-th answer"
    source := "ARCHITECTURE.md §7: \"On replay the n-th pull gets the n-th answer\"; \"Replay reads the tape and never asks the decider again\""
    check := fun _ d rec rep =>
      if d.perturb != .none || rep.error.isSome then none
      else if rec.values != rep.values then some s!"recorded values {rec.values.toList}, replayed {rep.values.toList}" else none }

def stopsWhereItDiverges : TProp :=
  { name := "a replay that parts from its tape stops at its next checkpoint"
    source := "README_AI.md: \"tapes with checkpoints (a replay stops where it diverges)\"; ARCHITECTURE.md §7: \"Checkpoints ... for divergence detection\""
    check := fun wd _ rec rep => Id.run do
      let some i := firstDifference rec.events rep.events | return none
      -- The tape's checkpoints a replay keeps (thinned past the table's size), at or past the
      -- first difference.
      let cps := match parse wd.consts rec.tape.toList with
        | .ok o => (o.checkpoints.map fun (cp : Nat × UInt64) => cp.1).toList
        | .error _ => []
      let some next := cps.find? (· ≥ i) | return none
      -- The replay's history went that far (or further).
      if rep.events.size < next then return none
      match rep.diverged with
      | some stopped =>
        if stopped ≤ next + wd.consts.interval then return none
        return some s!"parted at event {i}, stopped only at {stopped} (checkpoint {next})"
      | none => return some s!"histories part at event {i}; the tape's checkpoint at {next} passed, the replay ran to its end ({rep.events.size} events) unstopped" }

/-- Round 5 (62e06e3): a full tape's replay has the recorded history up to its recorder's stop,
and stops there (TapeFull); any other tape replays whole. -/
def replaysToItsFull : TProp :=
  { name := "a replay has its recorded history to where its recorder stopped taping (tape_full), and stops there"
    source := "vm.zig:3684-3687 (62e06e3): \"there the tape says it is full (a replay stops at that pull, TapeFull) ... instead of a tape no replay can read\"; tape.zig:139-141, 403-414; README_AI.md: \"every timeline replays bit-identically\""
    check := fun _ d rec rep =>
      if d.perturb != .none then none
      else
        let full := rec.tape.toList.findSome? fun | .full p => some p | _ => none
        match full with
        | none =>
          if let some e := rep.error then some s!"the replay stopped: {e} (recorded {rec.events.size} events, no tape_full)"
          else if let some i := firstDifference rec.events rep.events then
            some s!"histories part at event {i}: recorded {(rec.events[i-1]?.map (·.text)).getD "-"}, replayed {(rep.events[i-1]?.map (·.text)).getD "-"}"
          else none
        | some p =>
          if rep.error != some "TapeFull" then some s!"the tape is full at pull {p}; the replay ended with {rep.error}"
          -- The refused pull is not counted (decide_random throws before taking it).
          else if rep.pulls != p then some s!"the tape is full at pull {p}; the replay stopped at pull {rep.pulls}"
          else if (rep.events.toList.zip rec.events.toList).any (fun (a, b) => a != b) || rep.events.size > rec.events.size then
            some s!"the replay's history is not the recording's up to the stop"
          else none }

def allTProps : List TProp := [replaysExactly, pullsRepeat, stopsWhereItDiverges, replaysToItsFull]

def judgeT (p : TProp) (wd : TWorld) (source : Source) : Ended :=
  match (drawT wd).run { decisions := { source } } with
  | .ok d s =>
    let (rec, rep) := recordReplay wd d
    { taken := s.decisions.taken, violation := (p.check wd d rec rep).map fun x => (p.name, x) }
  | .error _ s => { taken := s.decisions.taken, violation := none }

def tstory (wd : TWorld) (source : Source) : List String :=
  match (drawT wd).run { decisions := { source } } with
  | .ok d _ =>
    let (rec, rep) := recordReplay wd d
    [s!"guest steps: {reprStr d.steps}", s!"advice: {d.advice}", s!"replay perturbed: {reprStr d.perturb}",
     s!"tape: {reprStr rec.tape.toList}"] ++
    (rec.events.toList.zipIdx.map fun (e, i) => s!"recorded {i + 1}: {e.text}") ++
    (rep.events.toList.zipIdx.map fun (e, i) => s!"replayed {i + 1}: {e.text}") ++
    [s!"replay: error={rep.error} diverged={rep.diverged}"]
  | .error _ _ => []

def tworlds : List TWorld :=
  [ { label := "plain pulls with strategy answers", steps := 7, labels := [.plain] },
    { label := "plain and drive pulls, explore_here", steps := 7, labels := [.plain, .driveMs, .exploreHere] },
    { label := "egress and ingress answers", steps := 7, labels := [.egressStatus, .ingressStatus] },
    { label := "serve's replies", steps := 7, labels := [.serveStatus] },
    { label := "a fork's index", steps := 7, labels := [.forkIndex] },
    { label := "replays perturbed by a kernel line or a changed event", steps := 9, labels := [.plain],
      consoles := true, perturbs := true },
    { label := "guest events and kernel lines, a table of two checkpoints every two events", steps := 12,
      labels := [], consoles := true, consts := { interval := 2, checkpointMax := 2 } },
    -- Round 2: the replay's tables at a small size (65,536 overrides and 1,024 reasons in the Zig).
    { label := "ingress polls (each answer on the tape), a table of 4 overrides", steps := 7,
      labels := [.ingressStatus], consts := { overrideMax := 4 } },
    { label := "plain pulls with strategy answers, a table of 2 reasons", steps := 7,
      labels := [.plain], consts := { reasonMax := 2 } },
    -- Round 5 (62e06e3): the recorder's cap and its marker, idle polls untaped.
    { label := "ingress polls and plain pulls with strategy answers, a cap of 2 overrides", steps := 8,
      labels := [.ingressStatus, .plain], consts := { overrideMax := 2 } },
    { label := "egress, ingress and serve answers, a fork's index, a cap of 3 overrides", steps := 8,
      labels := [.egressStatus, .ingressStatus, .serveStatus, .forkIndex], consts := { overrideMax := 3 } } ]

def searchAll (exhaustRuns : Nat) : IO (List Found) := do
  let mut found := []
  for p in allTProps do
    say s!"== tape property: {p.name}"
    say s!"   source: {p.source}"
    for wd in tworlds do
      if let some f ← exhaustSaid s!"{p.name} / {wd.label}" (judgeT p wd) exhaustRuns then
        printFound f (tstory wd)
        found := found ++ [f]
  return found

end Replica.Tape
