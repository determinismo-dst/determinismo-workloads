import Replica.Prelude
import Replica.Searching

/-!
# Durability points and disk failures, replicated (platform 3939448)

## Durability points (guest/runtime/faults.zig, guest/module/det_guest.c)

- `layer_of` (faults.zig:1580-1585): `sync_stall` is a condition, `durable_crash` a process fault;
  `node_admits` (1632-1641): a node takes one fault a layer, and one in the other layer while
  busy only as the regime's overlap draws (`fault.overlap`, 0 to 8 eighths: 1141-1212);
- `durable_arm` (3224-3258): both arm the guest module for the node's cgroup, `.stall` for a
  sync_stall, `.crash_before`/`.crash_after` for a durable_crash (`durable_active` set);
  `durable_disarm` (3260-3272) arms it with `one_in` 0; their ends (2244-2262): a sync_stall's
  disarms, a durable_crash's clears `durable_active` and disarms;
- the module's arm ioctl (det_guest.c:461-497): one arm per cgroup, "Replaced (or disarmed)" by
  each arm; `det_durability` (404-439): a sync of an armed node is a decision (`det_pull`) on its
  mode's side of the sync, a stall or a park for a crash.

## Disk failures over Linux's page cache (guest/runtime/nodes.zig)

A node's file of `pages` pages, each stored on its disk and maybe cached (its data, dirty or
clean). The disk's table (nodes.zig:1956-2023 `disk_fail`): healthy, `write_errors` (dm-flakey
`error_writes`), `lost_writes` (`drop_writes`). Linux's behavior, as documented:

- a buffered write dirties the cached page (a partial write of an uncached page reads it first);
- writeback of a dirty page (the flusher, or the node's fsync) stores it; under `error_writes` it
  fails with EIO, and the page is left clean with the new data in the cache, the error recorded in
  the file's `errseq_t` (Documentation/filesystems/vfs.rst, "Handling errors during writeback":
  "the page is ... marked clean"; lib/errseq.c);
- `fsync` returns EIO once to each open file description whose sample predates an error it has
  not reported to that description (`file_check_and_advance_wb_err`); a description opened after
  an error nobody saw yet sees it too (`errseq_sample`, since Linux 4.16);
- under `drop_writes` writeback "succeeds" and nothing is stored (dm-flakey's documentation:
  "drop_writes: All write I/O is silently ignored");
- a clean page may be evicted under memory pressure, read back from the disk at the next read;
- a crash (or an unmount) drops the cache (nodes.zig:745-750 `crash`; 2179-2198 `disk_heal`
  unmounts a node that exited or whose filesystem went read-only).
-/

namespace Replica.Durable

open Determinismo

/-! ## Durability points -/

inductive Mode where
  | stall
  | crashBefore
  | crashAfter
  deriving BEq, Repr, Inhabited

def Mode.show : Mode → String
  | .stall => "stall"
  | .crashBefore => "crash_before"
  | .crashAfter => "crash_after"

inductive Kind where
  | syncStall
  | durableCrash
  deriving BEq, Repr, Inhabited

def Kind.show : Kind → String
  | .syncStall => "sync_stall"
  | .durableCrash => "durable_crash"

/-- A fault on the node: its kind, its arm's mode, and whether it is under way. -/
structure Fault where
  kind : Kind
  mode : Mode
  deriving BEq, Repr, Inhabited

structure DS where
  decisions : Decisions := {}
  /-- The module's arm for the node's cgroup (det_armed: one a cgroup, 3939448). -/
  armed : Option Mode := none
  /-- 62e06e3 (det_guest.c:249, 287-307, 490-494): two arms a cgroup, a stall's and a crash's,
  each replaced or disarmed by its own kind alone. -/
  armedStall : Option Mode := none
  armedCrash : Option Mode := none
  ver : Ver := .vdf8f08b
  /-- nodes_faulted's two layers: the process layer's and the condition layer's. -/
  process : Option Fault := none
  condition : Option Fault := none
  log : Array String := #[]
  violation : Option String := none
  deriving Inhabited

instance : Chaotic DS where
  decisions s := s.decisions
  setDecisions s d := { s with decisions := d }

abbrev DM := EStateM Stop DS

def note (line : String) : DM Unit := modify fun s => { s with log := s.log.push line }

/-- det_guest.c:461-497: an arm replaces the cgroup's, a disarm (one_in 0) clears it (3939448).
62e06e3: the arm of the fault's kind alone (`kind`: the sync_stall's or the durable_crash's;
faults.zig:2245-2250 and 3264 disarm by kind). -/
def moduleArm (m : Option Mode) (kind : Kind := .syncStall) : DM Unit := modify fun s =>
  if s.ver == .v3939448 then { s with armed := m }
  else if kind == .syncStall then { s with armedStall := m } else { s with armedCrash := m }

/-- faults.zig:1632-1641 `node_admits`: its layer free, and the other free or the overlap drawn
(`fault.overlap` below the regime's eighths: one value of 8 here, so both ways are searched). -/
def admits (layerFree otherFree : Bool) (overlapEighths : Nat) : DM Bool := do
  if !layerFree then return false
  if otherFree then return true
  return (← below "fault.overlap" 8) < overlapEighths

/-- A fault begins (faults.zig:2185-2215 node_start, 3224-3258 durable_arm). -/
def begin (k : Kind) (overlapEighths : Nat) : DM Unit := do
  let s ← get
  let mine := if k == .syncStall then s.condition else s.process
  let other := if k == .syncStall then s.process else s.condition
  if !(← admits mine.isNone other.isNone overlapEighths) then
    note s!"{k.show} turned away (its layer busy, or no overlap drawn)"
    return
  let mode ← if k == .syncStall then pure Mode.stall
    else do pure (if (← below "fault.durable_after" 2) == 1 then Mode.crashAfter else Mode.crashBefore)
  let f : Fault := { kind := k, mode }
  if k == .syncStall then modify fun s => { s with condition := some f }
  else modify fun s => { s with process := some f }
  moduleArm (some mode) k
  note s!"{k.show} begins: the module armed {mode.show}"

/-- A fault ends (faults.zig:2244-2262): both disarm the node's cgroup. -/
def finish (k : Kind) : DM Unit := do
  let s ← get
  let active := if k == .syncStall then s.condition else s.process
  if active.isNone then return
  if k == .syncStall then modify fun s => { s with condition := none }
  else modify fun s => { s with process := none }
  moduleArm none k
  note s!"{k.show} ends: the module disarmed"

/-- A sync of the node (det_guest.c:404-439): a decision on the armed mode's side. The
properties: while a sync_stall lasts each sync is a stall decision; while a durable_crash lasts,
a crash decision (ARCHITECTURE.md:360-368; docs/ANTITHESIS.md:57; faults.zig:53-60). -/
def sync (at_ : Nat) : DM Unit := do
  let s ← get
  -- 62e06e3 (det_guest.c:419-447): the crash arm decides on its side, then (before the sync,
  -- not crashed) the stall arm: one pull each.
  let decided : List Mode := if s.ver == .v3939448 then s.armed.toList
    else s.armedCrash.toList ++ s.armedStall.toList
  let what := if decided.isEmpty then "no decision (nothing armed)"
    else String.intercalate " and " (decided.map fun m => s!"a {m.show} decision")
  note s!"t={at_}: the node syncs: {what}"
  if s.violation.isSome then return
  for f in [s.condition, s.process].filterMap id do
    if !decided.contains f.mode then
      modify fun s => { s with violation := some s!"t={at_}: a {f.kind.show} fault is under way ({f.mode.show}), and the node's sync is {what}" }
      return

/-- A timeline: `steps` moments, at each a fault begins or ends, or the node syncs. -/
def timeline (steps overlapEighths : Nat) (ver : Ver := .vdf8f08b) : DM Unit := do
  modify fun s => { s with ver }
  for t in [0:steps] do
    match (← below "step" 5) with
    | 0 => begin .syncStall overlapEighths
    | 1 => begin .durableCrash overlapEighths
    | 2 => finish .syncStall
    | 3 => finish .durableCrash
    | _ => sync t

def durableProperty : String := "while a sync_stall or durable_crash lasts, each of the node's syncs is that fault's decision"
def durableSource : String := "ARCHITECTURE.md:360-368 (\"While a `sync_stall` or `durable_crash` fault lasts, each of its syncs is a decision (one randomness pull), and one in a few is picked\"); docs/ANTITHESIS.md:57 (Durability points); faults.zig:53-60 (\"while the fault lasts, the guest module makes each of the node's fsyncs and sync writes a decision\")"

def judgeD (steps overlapEighths : Nat) (source : Source) (ver : Ver := .vdf8f08b) : Ended :=
  match (timeline steps overlapEighths ver).run { decisions := { source } } with
  | .ok _ s => { taken := s.decisions.taken, violation := s.violation.map fun d => (durableProperty, d) }
  | .error _ s => { taken := s.decisions.taken, violation := none }

def storyD (steps overlapEighths : Nat) (source : Source) (ver : Ver := .vdf8f08b) : List String :=
  match (timeline steps overlapEighths ver).run { decisions := { source } } with
  | .ok _ s => s.log.toList
  | .error _ s => s.log.toList

/-! ## Disk failures and Linux's page cache -/

inductive Table where
  | healthy
  | writeErrors
  | lostWrites
  deriving BEq, Repr, Inhabited

structure Page where
  stored : Nat
  /-- In the cache: its data, and whether it is dirty. -/
  cached : Option (Nat × Bool) := none
  deriving Repr, Inhabited, BEq

/-- A file description of the node's: the errseq it last saw. -/
structure Fd where
  cursor : Nat
  deriving Repr, Inhabited, BEq

structure KS where
  decisions : Decisions := {}
  pages : Array Page
  table : Table := .healthy
  /-- The file's errseq_t: errors recorded so far, and whether the last was seen. -/
  errors : Nat := 0
  seen : Bool := true
  fds : Array Fd := #[{ cursor := 0 }]
  /-- What the node wrote last to each page, the fsync that returned 0 after it with no error
  reported to the node since (synced), and whether an error was reported to it since its write. -/
  wrote : Array (Option Nat)
  synced : Array Bool
  errorSince : Array Bool
  /-- Whether the node holds that its write is durable: a sync returned 0 after it. -/
  log : Array String := #[]
  violation : Option (String × String) := none
  crashes : Nat := 0
  deriving Inhabited

instance : Chaotic KS where
  decisions s := s.decisions
  setDecisions s d := { s with decisions := d }

abbrev KM := EStateM Stop KS

def kn (line : String) : KM Unit := modify fun s => { s with log := s.log.push line }

def broke (p d : String) : KM Unit := modify fun s => if s.violation.isNone then { s with violation := some (p, d) } else s

/-- What a read of page `i` returns: the cached data, else the stored (cached clean). -/
def readPage (i : Nat) : KM Nat := do
  let s ← get
  let p := s.pages[i]!
  match p.cached with
  | some (d, _) => return d
  | none =>
    set { s with pages := s.pages.set! i { p with cached := some (p.stored, false) } }
    return p.stored

/-- Writeback of page `i` (the flusher's or an fsync's): stored, failed or dropped. -/
def writeback (i : Nat) : KM Bool := do
  let s ← get
  let p := s.pages[i]!
  match p.cached with
  | some (d, true) =>
    match s.table with
    | .healthy => set { s with pages := s.pages.set! i { stored := d, cached := some (d, false) } }; return true
    | .lostWrites => set { s with pages := s.pages.set! i { p with cached := some (d, false) } }; return true
    | .writeErrors =>
      -- The page left clean with its data, the error in the file's errseq (a new one unseen).
      set { s with pages := s.pages.set! i { p with cached := some (d, false) },
                   errors := s.errors + 1, seen := false }
      return false
  | _ => return true

/-- fsync on description `f`: the dirty pages written back, then the errseq checked and advanced
(file_check_and_advance_wb_err): EIO when an error came since its cursor. -/
def fsync (f : Nat) : KM Bool := do
  for i in [0:(← get).pages.size] do let _ ← writeback i
  let s ← get
  let fd := s.fds[f]!
  if fd.cursor < s.errors then
    set { s with fds := s.fds.set! f { cursor := s.errors }, seen := true }
    return false
  return true

/-- A description opened now (errseq_sample): an error nobody saw is still to report to it. -/
def openFd : KM Unit := modify fun s =>
  let cursor := if s.seen || s.errors == 0 then s.errors else s.errors - 1
  { s with fds := s.fds.push { cursor } }

/-- The node's view: a write of value `v` to page `i`, buffered. -/
def nodeWrite (i v : Nat) : KM Unit := do
  let _ ← readPage i -- A partial write of an uncached page reads it first.
  modify fun s => { s with pages := s.pages.modify i fun p => { p with cached := some (v, true) },
                           wrote := s.wrote.set! i (some v), synced := s.synced.set! i false,
                           errorSince := s.errorSince.set! i false }

/-- The node's fsync on its description `f`: 0 makes every page it wrote synced, EIO marks an
error reported since each write. -/
def nodeFsync (f : Nat) : KM Unit := do
  let ok ← fsync f
  modify fun s => { s with
    synced := (s.synced.zip s.wrote).map fun (y, w) => if ok then (w.isSome || y) else y,
    errorSince := s.errorSince.map fun e => e || !ok }
  kn s!"the node's fsync on description {f}: {if ok then "0" else "EIO"}"

/-- A crash: the cache gone (nodes.zig:745-750); a heal of a node that exited unmounts it too. -/
def dropCache : KM Unit := modify fun s => { s with pages := s.pages.map fun p => { p with cached := none }, fds := #[{ cursor := s.errors }], seen := true }

structure KCfg where
  label : String
  pages : Nat := 1
  steps : Nat := 7
  /-- The failure the disk fault draws. -/
  failures : List Table := [.writeErrors]
  evictions : Bool := true
  deriving Inhabited

/-- Property: with `disk_lost_writes` off, a write the node synced, with no error reported to it
since, survives (schema.zig:515-519: "Its other failures leave what is stored intact, so
durability stays judgeable under them"). -/
def judgeable : String := "with disk_lost_writes off, a write whose fsync returned 0 (no error reported since) is stored"
def judgeableSource : String := "sdk/zig/schema.zig:515-519 (\"Its other failures leave what is stored intact, so durability stays judgeable under them\"); Linux: fsync(2) and Documentation/filesystems/vfs.rst (a writeback error is reported by the next fsync of each open description)"

/-- Property: lost writes are gone at the next crash: until then a read returns them. -/
def lostUntilCrash : String := "lost writes are gone at the next crash: until then, a read returns the node's last write"
def lostUntilCrashSource : String := "docs/ANTITHESIS.md:56 (\"writes acknowledged and never stored (gone at the next crash, synced or not)\"); nodes.zig:1932-1934 (lost_writes: \"a crash after loses them although they were synced\")"

def checkJudgeable : KM Unit := do
  let s ← get
  for i in [0:s.pages.size] do
    if let some w := s.wrote[i]! then
      if s.synced[i]! && !s.errorSince[i]! && s.pages[i]!.stored != w then
        broke judgeable s!"page {i}: the node wrote {w} and its fsync returned 0 (no error since); the disk stores {s.pages[i]!.stored}"

def disk (cfg : KCfg) : KM Unit := do
  for t in [0:cfg.steps] do
    let s ← get
    let options := if cfg.evictions then 9 else 8
    match (← below "disk.step" options) with
    | 0 => do
      let i ← below "disk.page" s.pages.size
      let v := 1 + t
      nodeWrite i v
      kn s!"t={t}: the node writes {v} to page {i}"
    | 1 => do
      let f ← below "disk.fd" s.fds.size
      kn s!"t={t}:"
      nodeFsync f
    | 2 => do
      for i in [0:s.pages.size] do let _ ← writeback i
      kn s!"t={t}: the flusher writes the dirty pages back"
    | 3 => do
      if s.table == .healthy then
        let failure := cfg.failures[(← below "fault.disk.failure" cfg.failures.length)]!
        modify fun s => { s with table := failure }
        kn s!"t={t}: the disk fails: {reprStr failure}"
    | 4 => do
      if s.table != .healthy then
        modify fun s => { s with table := .healthy }
        kn s!"t={t}: the disk heals (the node runs on, its layer writable: nothing else, nodes.zig:2192)"
    | 5 => do
      openFd
      kn s!"t={t}: the node opens the file again (description {s.fds.size})"
    | 6 => do
      -- A read of each page the node wrote, against what it wrote, while no crash came since.
      for i in [0:s.pages.size] do
        let v ← readPage i
        if let some w := (← get).wrote[i]! then
          if v != w then
            broke lostUntilCrash s!"t={t}: page {i}: the node wrote {w} ({if (← get).synced[i]! then "synced" else "not synced"}), no crash since; its read returns {v}"
      kn s!"t={t}: the node reads its pages"
    | 7 => do
      dropCache
      modify fun s => { s with crashes := s.crashes + 1, wrote := s.wrote.map fun _ => none }
      kn s!"t={t}: a crash (power loss): the cache gone; the node starts again"
    | _ => do
      -- Memory pressure: a clean page evicted.
      let i ← below "disk.evict" s.pages.size
      match s.pages[i]!.cached with
      | some (_, false) =>
        modify fun s => { s with pages := s.pages.modify i fun p => { p with cached := none } }
        kn s!"t={t}: memory pressure evicts page {i} (clean)"
      | _ => pure ()
    checkJudgeable

def judgeK (prop : String) (cfg : KCfg) (source : Source) : Ended :=
  let init : KS := { decisions := { source }, pages := Array.replicate cfg.pages { stored := 0 },
                     wrote := Array.replicate cfg.pages none, synced := Array.replicate cfg.pages false,
                     errorSince := Array.replicate cfg.pages false }
  match (disk cfg).run init with
  | .ok _ s => { taken := s.decisions.taken, violation := s.violation.filter (·.1 == prop) }
  | .error _ s => { taken := s.decisions.taken, violation := none }

def storyK (cfg : KCfg) (source : Source) : List String :=
  let init : KS := { decisions := { source }, pages := Array.replicate cfg.pages { stored := 0 },
                     wrote := Array.replicate cfg.pages none, synced := Array.replicate cfg.pages false,
                     errorSince := Array.replicate cfg.pages false }
  match (disk cfg).run init with
  | .ok _ s => s.log.toList
  | .error _ s => s.log.toList

def kworlds : List (String × KCfg) :=
  [ (judgeable, { label := "write_errors, one page, 7 steps", failures := [.writeErrors] }),
    (judgeable, { label := "write_errors, two pages, 7 steps, no eviction", pages := 2, failures := [.writeErrors], evictions := false }),
    (lostUntilCrash, { label := "lost_writes, one page, 6 steps, no eviction", steps := 6, failures := [.lostWrites], evictions := false }),
    (lostUntilCrash, { label := "lost_writes, one page, 6 steps", steps := 6, failures := [.lostWrites] }) ]

/-- How often: timelines of `steps` steps, the regime's overlap drawn 0 to 8 eighths (as
`fault.overlap_eighths` is), the steps drawn. -/
def durableCensus (steps count : Nat) : IO Unit := do
  let mut broken := 0
  let mut overlapped := 0
  for i in [0:count] do
    let src := Source.seeded i
    let eighths := (Determinismo.mixSeed (i + 77)) % 9
    match (timeline steps eighths).run { decisions := { source := src } } with
    | .ok _ s =>
      if s.violation.isSome then broken := broken + 1
      if s.log.any (fun l => l.startsWith "durable_crash begins") && s.log.any (fun l => l.startsWith "sync_stall begins") then overlapped := overlapped + 1
    | .error _ _ => pure ()
  say s!"census [{steps} steps, overlap eighths drawn 0..8, seeds 0..{count - 1}]: {broken} timelines with a sync not its fault's decision; {overlapped} had both kinds begin"

def searchAll (exhaustRuns seeds : Nat) : IO Unit := do
  durableCensus 8 seeds
  say s!"== durability property: {durableProperty}"
  say s!"   source: {durableSource}"
  for (steps, eighths) in [(4, 0), (5, 8), (6, 4)] do
    let label := s!"{steps} steps, overlap {eighths} eighths"
    if let some f ← exhaustSaid s!"{durableProperty} / {label}" (judgeD steps eighths) exhaustRuns then
      printFound f (storyD steps eighths)
    if let some f ← exploreSaid s!"{durableProperty} / {label}" (judgeD steps eighths) seeds then
      printFound f (storyD steps eighths)
  for (prop, cfg) in kworlds do
    say s!"== disk property: {prop}"
    say s!"   source: {if prop == judgeable then judgeableSource else lostUntilCrashSource}"
    if let some f ← exhaustSaid s!"{prop} / {cfg.label}" (judgeK prop cfg) exhaustRuns then
      printFound f (storyK cfg)
    if let some f ← exploreSaid s!"{prop} / {cfg.label}" (judgeK prop cfg) seeds then
      printFound f (storyK cfg)

end Replica.Durable
