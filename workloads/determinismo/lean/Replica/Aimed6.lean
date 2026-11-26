import Replica.Prelude
import Replica.Searching

/-!
# corrupt_reads aimed at a file: the byte each read names (round 6)

guest/runtime/nodes.zig (a7fe05d):
- `file_extents` (2375-2410): the aimed file's extents at the fault's start (FIEMAP; delalloc ones,
  with no place on disk yet, left out), adjacent ones in the map's (logical) order joined, sorted;
- `aimed_record` (2415-2434): the table, a segment a line: the failing target (dm-flakey with
  `corrupt_bio_byte <n> r <value> 0`, 2030-2034) over each extent, `linear` over the rest;
- `disk_reads_read` (2250-2288): each read bio queued on the device (block_bio_queue: its first
  sector and its count) that overlaps an aimed extent is a `disk_corrupt_read` with `.byte = sector
  * 512 + corrupt_byte - 1` (2278: "The device's byte the fault changed").

What the kernel does (drivers/md/dm.c, dm-flakey.c): a bio that spans segments is split at
their boundaries, one clone a target (`max_io_len_target_boundary`); dm-flakey changes byte
`corrupt_bio_byte` of each read clone it completes (`corrupt_bio_data` in `flakey_end_io`), the
clone's own start counted from. So a read over a linear part then an aimed extent has the
extent's first sector's byte changed, not the read's; one over two aimed extents with a gap has
two bytes changed. ext4 places a block written into a hole next to its logical neighbour
(`ext4_ext_find_goal`: the left extent's block plus the distance, or before the extent the hole
precedes), so a file written out of order (a database's preallocated, sparse file) gets the hole's
block between or beside its extents, and a read (readahead) over the run makes one bio.

The promise: schema.zig (a7fe05d) `corrupt_reads`: "Every read it corrupts is named
(`disk_corrupt_read`: node, file, sectors, the byte ...), so a durability judge excludes those
pages, or flags a loss inside one, without guessing"; nodes.zig:2278: "The device's byte the
fault changed".

The model: a file of logical blocks, each on a physical block or a hole; the aimed extents at the
fault's start; holes filled during the fault at ext4's goal when free; a read bio over a run of
the file's logically and physically consecutive blocks; dm's split; the bytes changed and the
byte named (blocks for sectors, `corrupt_byte` 1).
-/

namespace Replica.Aimed6

open Determinismo

/-- file_extents: runs of logically consecutive, physically adjacent blocks, sorted by start. -/
def extentsOf (phys : List (Option Nat)) : List (Nat × Nat) := Id.run do
  let mut out : Array (Nat × Nat) := #[]
  for p in phys do
    match p with
    | none => pure ()
    | some b =>
      if out.size > 0 && out.back!.1 + out.back!.2 == b then
        out := out.modify (out.size - 1) fun (s, c) => (s, c + 1)
      else out := out.push (b, 1)
  return (out.toList.mergeSort fun a b => a.1 ≤ b.1)

/-- dm's split of a bio [start, start + count) by the aimed segments: each flakey clone's start. -/
def changed (aimed : List (Nat × Nat)) (start count : Nat) : List Nat :=
  aimed.filterMap fun (s, c) =>
    if start < s + c && s < start + count then some (max start s) else none

/-- disk_reads_read: named when it overlaps an aimed extent, its byte the bio's first sector's. -/
def named (aimed : List (Nat × Nat)) (start count : Nat) : Option Nat :=
  if aimed.any fun (s, c) => start < s + c && s < start + count then some start else none

/-- ext4_ext_find_goal for a hole at logical `i`: the left neighbour's block plus one, else the
right neighbour's minus one. -/
def goal (phys : List (Option Nat)) (i : Nat) : Option Nat :=
  match (if i > 0 then phys[i - 1]? else none) with
  | some (some b) => some (b + 1)
  | _ => match phys[i + 1]? with
    | some (some b) => if b > 0 then some (b - 1) else none
    | _ => none

structure S where
  decisions : Decisions := {}
  deriving Inhabited

instance : Chaotic S where
  decisions s := s.decisions
  setDecisions _ d := { decisions := d }

structure W where
  label : String
  blocks : Nat := 3
  device : Nat := 6
  deriving Inhabited

structure Drawn where
  before : List (Option Nat)
  after : List (Option Nat)
  aimed : List (Nat × Nat)
  bio : Option (Nat × Nat)
  deriving Repr, Inhabited

def draw (w : W) : EStateM Stop S Drawn := do
  -- The file at the fault's start: each block on a free physical block, or a hole.
  let mut before : List (Option Nat) := []
  for _ in [0:w.blocks] do
    if (← below "file.block_written" 2) == 1 then
      let used := before.filterMap id
      let free := (List.range w.device).filter (!used.contains ·)
      if free.isEmpty then before := before ++ [none]
      else before := before ++ [some free[(← below "file.block_at" free.length)]!]
    else before := before ++ [none]
  let aimed := extentsOf before
  -- While the fault lasts: holes written (each a decision), at ext4's goal when it is free.
  let mut after := before
  for i in [0:w.blocks] do
    if after[i]! == none then
      if (← below "system.writes_the_hole" 2) == 1 then
        if let some g := goal after i then
          if g < w.device && !(after.filterMap id).contains g then after := after.set i (some g)
  -- A read of a run of the file's blocks, logically and physically consecutive (one bio).
  let first ← below "read.first_block" w.blocks
  let count := 1 + (← below "read.blocks" (w.blocks - first))
  let run := (after.drop first).take count
  let bio := match run.head? with
    | some (some b) =>
      if run.zipIdx.all (fun (p, k) => p == some (b + k)) then some (b, count) else none
    | _ => none
  return { before, after, aimed, bio }

def property : String := "a disk_corrupt_read names the byte its read had changed, and every read's changed byte is named"
def source : String := "sdk/zig/schema.zig (a7fe05d) corrupt_reads: \"Every read it corrupts is named (`disk_corrupt_read`: node, file, sectors, the byte ...), so a durability judge excludes those pages, or flags a loss inside one, without guessing\"; guest/runtime/nodes.zig:2278 (\".byte = read.sector * 512 + corrupt_byte - 1, // The device's byte the fault changed.\")"

def judge (w : W) (src : Source) : Ended :=
  match (draw w).run { decisions := { source := src } } with
  | .ok d s =>
    let v := match d.bio with
      | none => none
      | some (start, count) =>
        let ch := changed d.aimed start count
        let nm := named d.aimed start count
        let ok := match nm with
          | none => ch.isEmpty
          | some b => ch == [b]
        if ok then none else
          some (property, s!"the file's blocks {reprStr d.before} at the fault's start (aimed extents {d.aimed}), {reprStr d.after} once a hole was written; a read of blocks {start}..{start + count - 1}: dm splits it, the bytes changed at the starts of blocks {ch}; the event names the byte at block {reprStr nm}")
    { taken := s.decisions.taken, violation := v }
  | .error _ s => { taken := s.decisions.taken, violation := none }

def worlds : List W :=
  [ { label := "a file of 3 blocks on a device of 6" },
    { label := "a file of 4 blocks on a device of 8", blocks := 4, device := 8 } ]

/-- Per world, over seeds: the reads drawn (a bio), those named wrongly or with a byte unnamed. -/
def census (w : W) (count : Nat) : IO Unit := do
  let mut reads := 0
  let mut wrong := 0
  let mut aimedReads := 0
  for i in [0:count] do
    match (draw w).run { decisions := { source := Source.seeded i } } with
    | .ok d _ =>
      if let some (start, n) := d.bio then
        reads := reads + 1
        if !(changed d.aimed start n).isEmpty then aimedReads := aimedReads + 1
        if (judge w (Source.seeded i)).violation.isSome then wrong := wrong + 1
    | .error _ _ => pure ()
  say s!"census [{w.label}]: {count} timelines, {reads} reads of the file, {aimedReads} through an aimed extent, {wrong} named with the wrong byte or a byte unnamed"

def searchAll (exhaustRuns seeds : Nat) : IO Unit := do
  say s!"== disk property: {property}"
  say s!"   source: {source}"
  for w in worlds do
    if let some f ← exhaustSaid s!"{property} / {w.label}" (judge w) exhaustRuns then
      printFound f (fun _ => [])
    census w seeds

end Replica.Aimed6
