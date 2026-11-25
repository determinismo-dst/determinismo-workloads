import Replica.Prelude
import Replica.Searching

/-!
# Disk faults against the documented fault model (platform 3939448)

Replicated from the Zig: the failure drawn for a node's `disk` fault (guest/runtime/faults.zig:
916-922: every failure, or `disk_failures_kept` 954-964 when the node's `disk_lost_writes` is
off), the device-mapper table each failure swaps in (guest/runtime/nodes.zig:1956-1990
`disk_fail`: dm-flakey `error_writes`, `drop_writes`, `corrupt_bio_byte <n> r <value>`, all I/O
down; dm-delay), the heal (2179-2198 `disk_heal`: the table back; a node still running on a
writable layer goes on as it is, one that exited or went read-only is killed and its layer
unmounted, mounted afresh at its start), a crash (a power loss: what reached the device stays,
nodes.zig:1920-1923), and the drawn flusher of `writeback_s` (2811-2858 `writeback_loop`).

What the guest kernel does beneath them is modeled as Linux's page cache does it (an assumption,
said in REPORT-3.md): a buffered read fills the page through the device's table and keeps it
(clean); a write to part of a page not in the cache reads the page first (read-modify-write,
`block_write_begin`/`ext4_block_write_begin`), then dirties it; a sync writes dirty pages through
the table; a failed writeback leaves the page clean with the error noted; an unmount or a crash
drops the cache; a clean page can be evicted at any time (memory pressure).

A page is `bytes` bytes; the file is `pages` pages; values below 4.
-/

namespace Replica.Disk

open Determinismo

inductive Failure where
  | errors | writeErrors | lostWrites | corruptReads | slow
  deriving Repr, BEq, Inhabited, DecidableEq

def Failure.name : Failure → String
  | .errors => "errors" | .writeErrors => "write_errors" | .lostWrites => "lost_writes"
  | .corruptReads => "corrupt_reads" | .slow => "slow"

def allFailures : List Failure := [.errors, .writeErrors, .lostWrites, .corruptReads, .slow]

/-- faults.zig:954-964 `disk_failures_kept`: every failure but lost_writes. -/
def keptFailures : List Failure := allFailures.filter (· != .lostWrites)

structure Page where
  data : List Nat
  dirty : Bool
  deriving Repr, BEq, Inhabited

structure DS where
  decisions : Decisions := {}
  device : Array (List Nat) := #[]
  cache : Array (Option Page) := #[]
  /-- The table now: none healthy. corrupt_reads's byte (from 1) and value. -/
  table : Option Failure := none
  corruptByte : Nat := 1
  corruptValue : Nat := 0
  /-- What the system wrote, per page: the last value at each byte (its own view). -/
  written : Array (List Nat) := #[]
  /-- Synced: what an fsync returned 0 for. -/
  synced : Array (List Nat) := #[]
  /-- Every (byte, value) the system ever wrote to each page, its file's own first. -/
  ever : Array (List (Nat × Nat)) := #[]
  failure : Option Failure := none
  running : Bool := true
  log : Array String := #[]
  /-- What the system read after the heal, and what was stored then. -/
  readsAfterHeal : Array (Nat × List Nat × List Nat) := #[]
  healed : Bool := false
  deriving Inhabited

instance : Chaotic DS where
  decisions s := s.decisions
  setDecisions s d := { s with decisions := d }

abbrev DM := EStateM Stop DS

def say' (line : String) : DM Unit := modify fun s => { s with log := s.log.push line }

/-- A read of page `p` through the table (a bio of the page): corrupt_bio_byte changes its
`corruptByte`-th byte (nodes.zig:1979-1983, dm-flakey's corrupt_bio_byte with direction r). -/
def deviceRead (p : Nat) : DM (Option (List Nat)) := do
  let s ← get
  match s.table with
  | some .errors => return none
  | some .corruptReads =>
    let d := s.device[p]!
    return some (d.set (s.corruptByte - 1) s.corruptValue)
  | _ => return some s.device[p]!

/-- A writeback of page `p` through the table: true when acknowledged. -/
def deviceWrite (p : Nat) (data : List Nat) : DM Bool := do
  let s ← get
  match s.table with
  | some .errors | some .writeErrors => return false
  | some .lostWrites => return true -- drop_writes: acknowledged, never stored.
  | _ => set { s with device := s.device.set! p data }; return true

/-- A buffered read: the cache, else the device (the page kept clean). -/
def read (p : Nat) : DM (Option (List Nat)) := do
  let s ← get
  if let some pg := s.cache[p]! then return some pg.data
  match ← deviceRead p with
  | none => return none
  | some d =>
    modify fun s => { s with cache := s.cache.set! p (some { data := d, dirty := false }) }
    return some d

/-- A buffered write of `value` at byte `b` of page `p`: read-modify-write when not cached. -/
def write (p b value : Nat) : DM Bool := do
  match ← read p with
  | none => say' s!"write page {p} byte {b}: EIO (its read failed)"; return false
  | some d =>
    modify fun s => { s with cache := s.cache.set! p (some { data := d.set b value, dirty := true }),
                             written := s.written.set! p (s.written[p]!.set b value),
                             ever := s.ever.set! p (s.ever[p]! ++ [(b, value)]) }
    return true

/-- fsync: every dirty page written back; 0 when all were acknowledged. A failed one is left
clean (its error reported once). -/
def fsync : DM Bool := do
  let s ← get
  let mut ok := true
  for p in [0:s.cache.size] do
    let some pg := (← get).cache[p]! | continue
    if !pg.dirty then continue
    let acked ← deviceWrite p pg.data
    if !acked then ok := false
    modify fun s => { s with cache := s.cache.set! p (some { pg with dirty := false }) }
  if ok then modify fun s => { s with synced := s.written }
  return ok

/-- An unmount, a crash or eviction: the cache's clean pages gone (a crash: the dirty ones too). -/
def dropCache (dirtyToo : Bool) : DM Unit := modify fun s =>
  { s with cache := s.cache.map fun pg => match pg with
    | some p => if p.dirty && !dirtyToo then some p else none
    | none => none }

structure DW where
  label : String
  pages : Nat := 2
  bytes : Nat := 3
  /-- The node's `disk_lost_writes` (schema.zig:515-520). -/
  lostWrites : Bool := false
  steps : Nat := 5
  /-- The failure, when the world fixes it (else drawn as faults.zig:916-922 draws it). -/
  failure : Option Failure := none
  deriving Inhabited

/-- The world: a file of `pages` pages on the node's disk, synced, cold in the cache; a disk
fault of a drawn failure for a few steps, the system reading, writing and syncing; the heal
(the node running, or exited); then the system reads again after the heal. -/
def scenario (w : DW) : DM Unit := do
  let initial := (List.range w.pages).map fun p => (List.range w.bytes).map fun b => (p + b) % 4
  modify fun s => { s with device := initial.toArray, cache := (List.replicate w.pages none).toArray,
                           written := initial.toArray, synced := initial.toArray,
                           ever := (initial.map fun d => d.zipIdx.map fun (v, b) => (b, v)).toArray }
  let failures := if w.lostWrites then allFailures else keptFailures
  let failure ← match w.failure with
    | some f => pure f
    | none => do pure failures[(← below "fault.disk.failure" failures.length)]!
  let corruptByte := 1 + (← below "fault.disk.corrupt_byte" w.bytes)
  let corruptValue := ← below "fault.disk.corrupt_value" 4
  modify fun s => { s with table := some failure, corruptByte, corruptValue, failure := some failure }
  say' s!"disk fault: {failure.name}{if failure == .corruptReads then s!" (byte {corruptByte} reads {corruptValue})" else ""}"
  for _ in [0:w.steps] do
    match ← below "world.step" 5 with
    | 0 => pure ()
    | 1 =>
      let p ← below "world.page" w.pages
      let r ← read p
      say' s!"read page {p}: {reprStr r}"
    | 2 =>
      let p ← below "world.page" w.pages
      let b ← below "world.byte" w.bytes
      let v ← below "world.value" 4
      let ok ← write p b v
      say' s!"write page {p} byte {b} = {v}: {if ok then "ok" else "EIO"}"
    | 3 =>
      let ok ← fsync
      say' s!"fsync: {if ok then "0" else "EIO"}"
    | _ =>
      dropCache false
      say' "memory pressure: clean pages evicted"
  -- The heal (nodes.zig:2179-2198): the table back; an exited node's layer unmounted.
  let exited := (← below "world.exited_at_heal" 2) == 1
  modify fun s => { s with table := none, healed := true }
  if exited then
    _ ← fsync -- The unmount writes back what is dirty, through the healthy table.
    dropCache true
    say' "heal: the node had exited: killed, its layer unmounted, mounted afresh at its start"
  else say' "heal: the node runs on"
  -- After the heal: the system syncs and reads its pages again, and later a power loss may come.
  _ ← fsync
  for p in [0:w.pages] do
    let r ← read p
    modify fun s => { s with readsAfterHeal := s.readsAfterHeal.push (p, r.getD [], s.device[p]!) }
  if (← below "world.crash_after" 2) == 1 then
    dropCache true
    say' "a power loss after the heal"

structure DProp where
  name : String
  source : String
  /-- Which worlds it speaks of. -/
  check : DW → DS → Option String

/-- schema.zig:515-519: with `disk_lost_writes` off, "Its other failures leave what is stored
intact, so durability stays judgeable under them"; nodes.zig:1937 (corrupt_reads): "what is
stored is intact". Every byte stored is one the system wrote (or the file's own). -/
def storedIntact : DProp :=
  { name := "with disk_lost_writes off, a disk fault never stores a byte the system did not write"
    source := "sdk/zig/schema.zig:515-519 (disk_lost_writes: \"Its other failures leave what is stored intact, so durability stays judgeable under them\"); guest/runtime/nodes.zig:1936-1937 (corrupt_reads: \"Reads return one byte of each request changed (bit rot); what is stored is intact\")"
    check := fun w s => Id.run do
      if w.lostWrites then return none
      for p in [0:w.pages] do
        let stored := s.device[p]!
        for (v, b) in stored.zipIdx do
          if !(s.ever[p]!.contains (b, v)) then
            return some s!"page {p} stores {stored}: byte {b} = {v}, a value the system never wrote there (it wrote {s.ever[p]!.filter (·.1 == b) |>.map (·.2)})"
      return none }

/-- docs/ANTITHESIS.md (Disk I/O faults): the disk fails "for a while"; nodes.zig:1936-1937. After
the heal a read returns what is stored. -/
def readsAfterHealStored : DProp :=
  { name := "after a disk fault heals, reads return what is stored"
    source := "docs/ANTITHESIS.md, Disk I/O faults (\"`disk`: the node's disk through device-mapper, its table swapped for a while\"); sdk/zig/schema.zig:506 (\"Make its disk fail for a while\"); nodes.zig:1936-1937"
    check := fun _ s => Id.run do
      for (p, got, stored) in s.readsAfterHeal do
        -- A read the cache answers with what the system wrote is the page cache's; one that
        -- is neither that nor what is stored carries the fault past its end.
        if got != stored && got != s.written[p]! then
          return some s!"after the heal page {p} reads {got}: the disk stores {stored}, the system wrote {s.written[p]!}"
      return none }

/-- nodes.zig:1931-1933 (lost_writes): "Writes are acknowledged and never stored ...: a crash
after loses them although they were synced"; docs/ANTITHESIS.md: "writes acknowledged and never
stored (gone at the next crash, synced or not)". Until a crash, the system reads what it wrote. -/
def lostOnlyAtCrash : DProp :=
  { name := "lost writes are gone at the next crash, not before"
    source := "docs/ANTITHESIS.md, Disk I/O faults (\"writes acknowledged and never stored (gone at the next crash, synced or not)\"); nodes.zig:1931-1933"
    check := fun _ s => Id.run do
      if s.failure != some .lostWrites then return none
      for (p, got, _) in s.readsAfterHeal do
        let wrote := s.written[p]!
        if got != wrote then
          return some s!"no crash yet: page {p} reads {got}, the system wrote {wrote} (and synced it)"
      return none }

def allDProps : List DProp := [storedIntact, readsAfterHealStored, lostOnlyAtCrash]

def judgeD (p : DProp) (w : DW) (source : Source) : Ended :=
  match (scenario w).run { decisions := { source } } with
  | .ok _ s => { taken := s.decisions.taken, violation := (p.check w s).map fun d => (p.name, d) }
  | .error _ s => { taken := s.decisions.taken, violation := none }

def storyD (w : DW) (source : Source) : List String :=
  match (scenario w).run { decisions := { source } } with
  | .ok _ s => s.log.toList ++ [s!"stored: {s.device.toList}; the system wrote: {s.written.toList}"]
  | .error _ _ => []

/-! ## writeback_s (nodes.zig:2811-2858) -/

/-- `writeback_loop` for one node over `seconds` virtual seconds after the timelines part: its
flusher drawn at the part (`writeback.on`), synced at each window's end when on, switched one
window in four (`writeback.switch`). Returns, for a power loss at the end, the oldest unsynced
write's age (seconds), with a write every second. -/
structure WS where
  decisions : Decisions := {}
  deriving Inhabited

instance : Chaotic WS where
  decisions s := s.decisions
  setDecisions _ d := { decisions := d }

def writebackLoss (window seconds : Nat) : EStateM Stop WS (Nat × List String) := do
  let mut on := (← below "writeback.on" 2) == 0
  let mut last := 0
  let mut lastFlush := 0
  let mut log := [s!"flusher {if on then "on" else "off"} at the part"]
  for now in [1:seconds + 1] do
    if now - last < window then continue
    last := now
    if on then
      lastFlush := now
      log := log ++ [s!"{now} s: synced"]
    if (← below "writeback.switch" 4) == 0 then
      on := !on
      log := log ++ [s!"{now} s: flusher {if on then "on" else "off"}"]
  -- A write every second: at a power loss at `seconds`, every write after the last flush is lost.
  return (seconds - lastFlush, log)

def writebackProp : String × String :=
  ("with writeback_s, a crash loses only the last window's unsynced writes",
   "docs/ANTITHESIS.md, Disk faults (\"a node's `writeback_s`, its disk synced that often as a host's flusher would, so a crash loses only the last window's unsynced writes\")")

def judgeWriteback (window seconds : Nat) (source : Source) : Ended :=
  match (writebackLoss window seconds).run { decisions := { source } } with
  | .ok (age, _) s =>
    { taken := s.decisions.taken,
      violation := if age > window then some (writebackProp.1, s!"a power loss at {seconds} s loses {age} s of writes, a window of {window} s") else none }
  | .error _ s => { taken := s.decisions.taken, violation := none }

def dworlds : List DW :=
  [ { label := "disk_lost_writes off: corrupt_reads, 1 page of 2 bytes, 4 steps", pages := 1, bytes := 2, steps := 4, failure := some .corruptReads },
    { label := "disk_lost_writes off: write_errors, 1 page of 2 bytes, 4 steps", pages := 1, bytes := 2, steps := 4, failure := some .writeErrors },
    { label := "disk_lost_writes off: errors, 1 page of 2 bytes, 4 steps", pages := 1, bytes := 2, steps := 4, failure := some .errors },
    { label := "disk_lost_writes on: lost_writes, 1 page of 2 bytes, 4 steps", pages := 1, bytes := 2, steps := 4, lostWrites := true, failure := some .lostWrites },
    { label := "disk_lost_writes off (its failures drawn), 2 pages of 3 bytes, 5 steps" },
    { label := "disk_lost_writes on (its failures drawn), 2 pages of 3 bytes, 5 steps", lostWrites := true } ]

def searchAll (exhaustRuns : Nat) : IO Unit := do
  for p in allDProps do
    say s!"== disk property: {p.name}"
    say s!"   source: {p.source}"
    for w in dworlds do
      if let some f ← exhaustSaid s!"{p.name} / {w.label}" (judgeD p w) exhaustRuns then
        printFound f (storyD w)
      if w.failure.isNone then
        if let some f ← exploreSaid s!"{p.name} / {w.label}" (judgeD p w) (exhaustRuns / 10) then
          printFound f (storyD w)
  say s!"== disk property: {writebackProp.1}"
  say s!"   source: {writebackProp.2}"
  for (window, seconds) in [(5, 30), (30, 120)] do
    if let some f ← exhaustSaid s!"{writebackProp.1} / a window of {window} s, a loss at {seconds} s" (judgeWriteback window seconds) exhaustRuns then
      printFound f (fun src => match (writebackLoss window seconds).run { decisions := { source := src } } with
        | .ok (_, log) _ => log
        | .error _ _ => [])

end Replica.Disk
