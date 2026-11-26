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
  let some f := s.reader | return
  if s.buffer.isEmpty then return
  modify fun s => { s with named := s.named ++ s.buffer.map fun l => { read := l.read, fault := f }, buffer := [] }
  note s!"the reader of fault #{f} runs: names {s.buffer.map (·.read)}"

/-- disk_heal (nodes.zig:2412-2415): the table back, the reader killed, the instance removed
unless the killed reader still holds its pipe (a decision: has it exited yet?). -/
def heal : DM Unit := do
  let s ← get
  let some f := s.active | return
  let exited := (← below "world.reader_exited_before_rmdir" 2) == 1
  modify fun s => { s with active := none, reader := none }
  if exited then
    modify fun s => { s with instance_ := false, buffer := [] }
    note s!"fault #{f} heals: its reader killed; the instance removed, {s.buffer.length} unread lines gone with it"
  else
    note s!"fault #{f} heals: its reader killed; rmdir refused (its pipe still open: EBUSY): the instance stays with {s.buffer.length} unread lines"

def timeline (steps : Nat) : DM Unit := do
  for _ in [0:steps] do
    match (← below "step" 4) with
    | 0 => fail
    | 1 => read
    | 2 => readerRuns
    | _ => heal

def everyReadNamed : String := "every read a corrupt_reads fault corrupts is named in that fault (disk_corrupt_read), one just before the heal too"
def everyReadNamedSource : String := "sdk/zig/schema.zig:520-524 (62e06e3): \"Every read it corrupts is an event (`disk_corrupt_read` ...): a loss outside every such read is the system's\"; nodes.zig:1983-1986; nodes.zig:2052-2055 (\"a read just before is named too: never one missed\"); 2415 (\"After the table heals: a read just before it is named too\")"

def namedRight : String := "a disk_corrupt_read names a read under the fault that corrupted it (its byte that fault's)"

def judgeWith (prop : String) (steps : Nat) (src : Source) : Ended :=
  match (timeline steps).run { decisions := { source := src } } with
  | .ok _ s =>
    let v := if prop == everyReadNamed then
        -- Judged once the faults ended (the last one healed): each corrupted read named in its own fault.
        if s.active.isSome then none
        else match s.corrupted.find? fun l => !s.named.contains { read := l.read, fault := l.fault } with
          | some l => some s!"read {l.read}, corrupted by fault #{l.fault}, is never named in it{if s.named.any (·.read == l.read) then s!" (named later, under fault #{(s.named.find? (·.read == l.read)).get!.fault})" else ""}"
          | none => none
      else match s.named.find? fun n => !s.corrupted.contains { read := n.read, fault := n.fault } with
        | some n => some s!"read {n.read} named under fault #{n.fault}, which did not corrupt it (its byte is another fault's)"
        | none => none
    { taken := s.decisions.taken, violation := v.map (prop, ·) }
  | .error _ s => { taken := s.decisions.taken, violation := none }

def storyD (steps : Nat) (src : Source) : List String :=
  match (timeline steps).run { decisions := { source := src } } with
  | .ok _ s => s.log.toList ++ [s!"named: {reprStr s.named}"]
  | .error _ s => s.log.toList

def searchAll (exhaustRuns seeds : Nat) : IO Unit := do
  for (prop, src) in [(everyReadNamed, everyReadNamedSource), (namedRight, "nodes.zig:2244-2252 (62e06e3: the event's byte, `sector * 512 + corrupt_byte - 1`, the fault's own corrupt_byte)")] do
    say s!"== disk property: {prop}"
    say s!"   source: {src}"
    for steps in [4, 6, 8] do
      if let some f ← exhaustSaid s!"{prop} / {steps} steps" (judgeWith prop steps) exhaustRuns then
        printFound f (storyD steps)
      if let some f ← exploreSaid s!"{prop} / {steps} steps" (judgeWith prop steps) seeds then
        printFound f (storyD steps)

end Replica.Disk5
