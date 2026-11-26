import Replica.Prelude
import Replica.Searching

/-!
# corrupt_reads's reads named by the block layer's tracepoint (62e06e3, round 5)

CE31's fix (guest/runtime/nodes.zig, 62e06e3):
- `disk_fail` (2007-2062): for corrupt_reads, `disk_reads_trace_start` (2173-2229) before the
  table fails reads: a tracefs instance `det-reads-<mapper>` with `block_bio_queue` filtered to
  the node's device-mapper device, its `trace_pipe` opened, then a detached reader process (its
  pid in `<node>/disk-reads-tracer`) that turns each read bio line into a `disk_corrupt_read` event
  (`disk_reads_read`, 2231-2266: node, file, sectors, the device's byte `sector * 512 +
  corrupt_byte - 1`), at most 4,096 a fault;
- `disk_heal` (2400-2421): the baseline table loaded and swapped in (`mapper_table`, a
  device-mapper suspend that waits for in-flight I/O), then `disk_reads_trace_stop` (2308-2324):
  the reader's pid read, SIGKILL sent, the event disabled, the instance removed (`rmdir`).

What it promises:
- schema.zig:520-524: "Every read it corrupts is an event (`disk_corrupt_read`: node, file,
  sectors, byte), so a durability judge excludes those pages, or flags a loss inside one: a loss
  outside every such read is the system's (CE31)";
- nodes.zig:1983-1986: "Every read it corrupts is named ... so a durability judge excludes those
  pages, or flags a loss inside one, without guessing";
- nodes.zig:2052-2055: "Its reads named from before the table fails them (a read just before is
  named too: never one missed)", and 2415: "After the table heals: a read just before it is named
  too".

What Linux does (kernel/trace/trace.c; Documentation/trace/ftrace.rst): a read of `trace_pipe`
consumes what it returns; a tracepoint's line waits in the instance's ring buffer until a reader
takes it (the reader woken by an irq_work, then scheduled as any task); `kill(2)` returns before
its target has exited and closed its files; removing an instance whose `trace_pipe` is open
fails with EBUSY (`__remove_instance`: `tr->trace_ref`), its buffer kept with what was in it; a
later reader of the same instance reads that first.

The model: one node, its corrupt_reads faults one after another (each a byte of its own), reads
queued while one lasts (each corrupted, each a line in the instance's buffer), the reader taking
what is buffered when it runs (a decision: the scheduler's), the heal (kill, then rmdir that
fails while the killed reader still holds the pipe: a decision), and a later fault's reader.
-/

namespace Replica.Disk5

open Determinismo

/-- A read bio's line in the instance: the read's number, and the fault whose table corrupted it. -/
structure Line where
  read : Nat
  fault : Nat
  deriving Repr, BEq, Inhabited

/-- A `disk_corrupt_read` event: the read it names, under the fault whose reader named it. -/
structure Named where
  read : Nat
  fault : Nat
  deriving Repr, BEq, Inhabited

structure S where
  decisions : Decisions := {}
  /-- Round 6: nodes.zig as at a7fe05d (the drain) unless a theorem about 62e06e3 says so. -/
  ver : Ver := .vdf8f08b
  /-- Round 6: whether pidfd_open may fail in the heal (a decision), the drain's fallback. -/
  pidfdMayFail : Bool := false
  /-- Faults whose tracer said it failed (`disk_reads_trace_failed`: "drain", "rmdir"). -/
  said : List (Nat × String) := []
  /-- A reader left running past its heal (no pidfd: never waited for nor killed): its fault. -/
  stray : Option Nat := none
  /-- The heal's end marker in the instance, not yet read (the stray's way out). -/
  markerPending : Bool := false
  /-- The fault under way (its number), if any. -/
  active : Option Nat := none
  faults : Nat := 0
  /-- The instance exists, and its unread lines. -/
  instance_ : Bool := false
  buffer : List Line := []
  /-- The reader running: the fault it was started for. -/
  reader : Option Nat := none
  reads : Nat := 0
  corrupted : List Line := []
  named : List Named := []
  log : Array String := #[]
  /-- Round 7: the reader may die while its fault lasts (the OOM killer: a step of its own). -/
  readerMayDie : Bool := false
  /-- Round 7: the fault whose reader died before its heal. -/
  deadReader : Option Nat := none
  /-- Round 7: faults whose heal SIGKILLed another process (the dead reader's pid reused). -/
  strangersKilled : List Nat := []
  deriving Inhabited

instance : Chaotic S where
  decisions s := s.decisions
  setDecisions s d := { s with decisions := d }

abbrev DM := EStateM Stop S

def note (line : String) : DM Unit := modify fun s => { s with log := s.log.push line }

/-- disk_fail with corrupt_reads (nodes.zig:2052-2060): the instance made (or there already), its
pipe opened, the reader started, then the table. -/
def fail : DM Unit := do
  if (← get).active.isSome then return
  -- a7fe05d (nodes.zig:2199-2205): an instance left behind (its removal failed) is cleared.
  if (← get).ver.sinceA7 && (← get).instance_ then
    note s!"corrupt_reads #{(← get).faults} begins: the instance is there (mkdir EEXIST): its trace cleared ({(← get).buffer.length} lines{if (← get).markerPending then ", the end marker among them" else ""})"
    modify fun s => { s with buffer := [], markerPending := false }
  modify fun s => { s with active := some s.faults, faults := s.faults + 1, instance_ := true, reader := some s.faults }
  note s!"corrupt_reads #{(← get).faults - 1} begins: the reader starts on the instance ({(← get).buffer.length} lines already in it)"

/-- A read of an uncached page while the fault lasts: corrupted by dm-flakey, its bio's line in
the instance's buffer (block_bio_queue). -/
def read : DM Unit := do
  let s ← get
  let some f := s.active | return
  let l : Line := { read := s.reads, fault := f }
  modify fun s => { s with reads := s.reads + 1, corrupted := s.corrupted ++ [l], buffer := s.buffer ++ [l] }
  note s!"read {l.read} during fault #{f}: corrupted, its line buffered"

/-- The reader scheduled: it takes every buffered line and names each (disk_reads_read). -/
def readerRuns : DM Unit := do
  let s ← get
  -- A stray reader (round 6: its heal never waited for it) shares the pipe: whichever the
  -- scheduler runs takes what is buffered.
  let f ← match s.reader, s.stray with
    | some r, some t => do pure (if (← below "world.which_reader" 2) == 0 then r else t)
    | some r, none => pure r
    | none, some t => pure t
    | none, none => return
  if s.stray == some f && s.markerPending then
    -- It reaches the heal's end marker: names what is before it and exits.
    modify fun s => { s with named := s.named ++ s.buffer.map fun l => { read := l.read, fault := f },
                             buffer := [], stray := none, markerPending := false }
    note s!"the stray reader of fault #{f} runs: names {s.buffer.map (·.read)}, reaches the end marker and exits"
    return
  if s.buffer.isEmpty then return
  modify fun s => { s with named := s.named ++ s.buffer.map fun l => { read := l.read, fault := f }, buffer := [] }
  note s!"the reader of fault #{f} runs: names {s.buffer.map (·.read)}"

/-- disk_heal (nodes.zig:2412-2415): the table back, the reader killed, the instance removed
unless the killed reader still holds its pipe (a decision: has it exited yet?). -/
def heal62 : DM Unit := do
  let s ← get
  let some f := s.active | return
  let exited := (← below "world.reader_exited_before_rmdir" 2) == 1
  modify fun s => { s with active := none, reader := none }
  if exited then
    modify fun s => { s with instance_ := false, buffer := [] }
    note s!"fault #{f} heals: its reader killed; the instance removed, {s.buffer.length} unread lines gone with it"
  else
    note s!"fault #{f} heals: its reader killed; rmdir refused (its pipe still open: EBUSY): the instance stays with {s.buffer.length} unread lines"

/-- disk_heal at a7fe05d (nodes.zig:2450-2461, 2329-2364): the table back; then
`disk_reads_trace_stop`: the event disabled (no read traced from here), the end marker written
after the buffered lines, the reader waited for 2 s (its pidfd): it names every line before the
marker and exits, unless it is not scheduled within them (a decision); then killed ("drain"
said), its unread lines lost, waited for 2 s more; `tracing_on` 0; the instance removed, refused
while a killed reader still holds the pipe ("rmdir" said). With `pidfdMayFail`, pidfd_open may
fail: no wait and no kill, rmdir at once (refused: the reader holds the pipe), the reader left
running on the instance. -/
def healA7 : DM Unit := do
  let s ← get
  let some f := s.active | return
  modify fun s => { s with active := none }
  let watched ← if s.pidfdMayFail then do pure ((← below "world.pidfd_open_fails" 2) == 0) else pure true
  if !watched then
    modify fun s => { s with reader := none, stray := some f, markerPending := true, said := s.said ++ [(f, "rmdir")] }
    note s!"fault #{f} heals: the marker written; pidfd_open failed: no wait, no kill; rmdir refused (the reader holds its pipe): the instance stays, its reader running with {s.buffer.length} lines unread"
    return
  let drained := (← below "world.reader_runs_within_2s" 2) == 1
  if drained then
    modify fun s => { s with named := s.named ++ s.buffer.map fun l => { read := l.read, fault := f },
                             buffer := [], reader := none, instance_ := false }
    note s!"fault #{f} heals: the marker written; its reader names {s.buffer.map (·.read)} up to it and exits; the instance removed"
  else
    let exited := (← below "world.killed_reader_exited_within_2s" 2) == 1
    modify fun s => { s with reader := none, said := s.said ++ [(f, "drain")] ++ (if exited then [] else [(f, "rmdir")]) }
    if exited then
      modify fun s => { s with instance_ := false, buffer := [] }
      note s!"fault #{f} heals: its reader not scheduled within 2 s: killed (\"drain\" said), {s.buffer.length} lines never named; the instance removed"
    else
      note s!"fault #{f} heals: its reader not scheduled within 2 s: killed (\"drain\" said) and not exited 2 s later: rmdir refused (\"rmdir\" said), the instance stays with {s.buffer.length} lines"

/-- Round 7: the reader dies while its fault lasts (the OOM killer; nothing else kills it: it
runs in det-faults' process group, which faults_stop signals by pid alone). What it had not read
stays in the instance. -/
def readerDies : DM Unit := do
  let s ← get
  let some f := s.active | return
  if s.reader != some f then return
  modify fun s => { s with reader := none, deadReader := some f }
  note s!"the reader of fault #{f} dies (the OOM killer): {s.buffer.length} lines unread, none read from here"

/-- Round 7: disk_reads_trace_stop (nodes.zig:2384-2420, a7fe05d and df8f08b) when the reader
died during the fault. `pidfd_open(pid)` fails with ESRCH (no "drain": `watched` false, no wait,
no kill), or its pid was reused (a decision) and opens that process: not exited within 2 s,
"drain" said, SIGKILLed. Either way the dead reader holds no pipe: rmdir succeeds, the unread lines
gone with the instance. -/
def healDeadReader (f : Nat) : DM Unit := do
  let s ← get
  modify fun s => { s with active := none, deadReader := none }
  let reused := (← below "world.reader_pid_reused" 2) == 1
  if reused then
    modify fun s => { s with said := s.said ++ [(f, "drain")], strangersKilled := s.strangersKilled ++ [f],
                             instance_ := false, buffer := [] }
    note s!"fault #{f} heals: the marker written; the dead reader's pid is another process's now: pidfd_open opens it, it does not exit within 2 s: \"drain\" said, SIGKILL sent to it; the instance removed, {s.buffer.length} lines never named"
  else
    modify fun s => { s with instance_ := false, buffer := [] }
    note s!"fault #{f} heals: the marker written; pidfd_open fails (ESRCH: the reader is gone): no wait, no kill, nothing said; rmdir succeeds, {s.buffer.length} lines never named"

def heal : DM Unit := do
  let s ← get
  if let some f := s.active then
    if s.ver.sinceA7 && s.deadReader == some f then return ← healDeadReader f
  if (← get).ver.sinceA7 then healA7 else heal62

def timeline (steps : Nat) : DM Unit := do
  for _ in [0:steps] do
    match (← below "step" (if (← get).readerMayDie then 5 else 4)) with
    | 0 => fail
    | 1 => read
    | 2 => readerRuns
    | 3 => heal
    | _ => readerDies

def everyReadNamed : String := "every read a corrupt_reads fault corrupts is named in that fault (disk_corrupt_read), one just before the heal too"
def everyReadNamedSource : String := "sdk/zig/schema.zig:520-524 (62e06e3): \"Every read it corrupts is an event (`disk_corrupt_read` ...): a loss outside every such read is the system's\"; nodes.zig:1983-1986; nodes.zig:2052-2055 (\"a read just before is named too: never one missed\"); 2415 (\"After the table heals: a read just before it is named too\")"

def namedRight : String := "a disk_corrupt_read names a read under the fault that corrupted it (its byte that fault's)"

/-- Round 6: every corrupted read named in its own fault, or that fault said its tracer failed
(`disk_reads_trace_failed`, as a judge would read it: those reads unnamed). -/
def everyReadNamedOrSaid : String := "every read a corrupt_reads fault corrupts is named in that fault, or the fault says its tracer failed (disk_reads_trace_failed)"

/-- Round 7: the heal stops its own reader and nothing else (nodes.zig:2390-2391: "The tracer
stopped (its pid read and killed, its instance removed)"). -/
def killsOnlyItsReader : String := "a corrupt_reads heal kills its own reader and no other process"

def judgeWith (prop : String) (steps : Nat) (src : Source) (ver : Ver := .vdf8f08b) (pidfdMayFail : Bool := false) (readerMayDie : Bool := false) : Ended :=
  match (timeline steps).run { decisions := { source := src }, ver, pidfdMayFail, readerMayDie } with
  | .ok _ s =>
    let v := if prop == killsOnlyItsReader then
        match s.strangersKilled.head? with
        | some f => some s!"fault #{f}'s heal SIGKILLed the process that took its dead reader's pid"
        | none => none
      else if prop == everyReadNamed || prop == everyReadNamedOrSaid then
        -- Judged once the faults ended (the last one healed): each corrupted read named in its own fault.
        if s.active.isSome then none
        else match s.corrupted.find? fun l => !s.named.contains { read := l.read, fault := l.fault } &&
                (prop == everyReadNamed || !s.said.any (·.1 == l.fault)) with
          | some l => some s!"read {l.read}, corrupted by fault #{l.fault}, is never named in it{if s.named.any (·.read == l.read) then s!" (named later, under fault #{(s.named.find? (·.read == l.read)).get!.fault})" else ""}{if s.said.any (·.1 == l.fault) then s!" (the fault said {(s.said.filter (·.1 == l.fault)).map (·.2)})" else ""}"
          | none => none
      else match s.named.find? fun n => !s.corrupted.contains { read := n.read, fault := n.fault } with
        | some n => some s!"read {n.read} named under fault #{n.fault}, which did not corrupt it (its byte is another fault's)"
        | none => none
    { taken := s.decisions.taken, violation := v.map (prop, ·) }
  | .error _ s => { taken := s.decisions.taken, violation := none }

def storyD (steps : Nat) (src : Source) (ver : Ver := .vdf8f08b) (pidfdMayFail : Bool := false) (readerMayDie : Bool := false) : List String :=
  match (timeline steps).run { decisions := { source := src }, ver, pidfdMayFail, readerMayDie } with
  | .ok _ s => s.log.toList ++ [s!"named: {reprStr s.named}"]
  | .error _ s => s.log.toList

def searchAll (exhaustRuns seeds : Nat) : IO Unit := do
  for (prop, src) in [(everyReadNamed, everyReadNamedSource),
                      (everyReadNamedOrSaid, everyReadNamedSource ++ "; nodes.zig:2340-2356 (a7fe05d: the drain, \"disk_reads_trace_failed\" when it is cut)"),
                      (namedRight, "nodes.zig:2262-2280 (a7fe05d: the event's byte, `sector * 512 + corrupt_byte - 1`, the fault's own corrupt_byte); 2199-2205 (an instance left behind cleared)")] do
    say s!"== disk property: {prop}"
    say s!"   source: {src}"
    for (ver, pidfd, label) in [(Ver.va7fe05d, false, "a7fe05d"), (Ver.va7fe05d, true, "a7fe05d, pidfd_open may fail"), (Ver.v62e06e3, false, "62e06e3")] do
      for steps in [4, 6, 8] do
        if let some f ← exhaustSaid s!"{prop} / {label} / {steps} steps" (judgeWith prop steps · ver pidfd) exhaustRuns then
          printFound f (storyD steps · ver pidfd)
        if let some f ← exploreSaid s!"{prop} / {label} / {steps} steps" (judgeWith prop steps · ver pidfd) seeds then
          printFound f (storyD steps · ver pidfd)

end Replica.Disk5
