import Replica.Prelude
import Replica.Searching

/-!
# Partial persistence at a power loss, replicated (guest/runtime/nodes.zig:753-955, platform 3939448)

At a drawn power loss of a node, half the time (`fault.partial`, faults.zig:801-805) part of what
it had not synced reaches its disk first, as a host's flusher may have written it back:
`partial_writeback` (875-881) walks the node's layer, and of a file in three (`partial_walk`,
883-913) `partial_file` (916-955) writes back:

- `chosen = 1 + below(min(pages, 16))` draws of a page in the file; one over blocks already
  allocated (an overwrite in place) is written back alone, one of new data skipped (941);
- its new data (FIEMAP's delayed-allocation and unwritten extents, `unallocated_of` 841-873:
  adjacent extents joined into one range): `left = 1 + below(total)` pages from the start of a
  drawn range (`range = below(ranges)`), on through the next ranges, wrapping (943-953);
- then, with `commit`, the journal committed (their allocation durable), else only pages over
  allocated blocks survive.

The draws come from a generator seeded by the platform's decision (`fault.partial`, then a
64-bit seed): named here `partial.*` for the search, not decisions of the platform.

The documentation (docs/ANTITHESIS.md, Partial persistence at a power loss): "its new data
(delayed or unwritten extents, FIEMAP) as an ascending run from the start of one of its new
ranges, as the flusher writes it (no hole before a kept page of a fresh file)"; nodes.zig:761-765:
"never a page before an earlier one of a fresh file, which leaves the earlier a hole (zeros)
under the committed size, what a real power loss hardly does".

A file here is its pages in order: a hole (never written), new data (written, not allocated yet),
or a page over an allocated block (clean, or dirtied again). A fresh file has no allocated page.
-/

namespace Replica.Persist

open Determinismo

inductive Page where
  | hole | new | allocClean | allocDirty
  deriving BEq, Repr, Inhabited, DecidableEq

def Page.name : Page → String
  | .hole => "hole" | .new => "new" | .allocClean => "allocated" | .allocDirty => "allocated, dirty"

/-- nodes.zig:841-873 `unallocated_of`: the new pages' ranges (first, count), in file order,
adjacent ones joined. -/
def unallocated (file : List Page) : List (Nat × Nat) := Id.run do
  let mut out : Array (Nat × Nat) := #[]
  for i in [0:file.length] do
    if file[i]! != .new then continue
    if out.size > 0 && out.back!.1 + out.back!.2 == i then
      out := out.set! (out.size - 1) (out.back!.1, out.back!.2 + 1)
    else out := out.push (i, 1)
  return out.toList

def contains (ranges : List (Nat × Nat)) (page : Nat) : Bool :=
  ranges.any fun (f, c) => f ≤ page && page < f + c

structure PS where
  decisions : Decisions := {}
  deriving Inhabited

instance : Chaotic PS where
  decisions s := s.decisions
  setDecisions _ d := { decisions := d }

/-- nodes.zig:916-955 `partial_file`: the pages written back, in the order written. -/
def partialFile (file : List Page) : EStateM Stop PS (List Nat) := do
  let pages := file.length
  if pages == 0 then return []
  let ranges := unallocated file
  let mut written : List Nat := []
  let chosen := 1 + (← below "partial.chosen" (min pages 16))
  for _ in [0:chosen] do
    let page ← below "partial.page" pages
    if contains ranges page then continue
    -- A hole's or a clean page's sync_file_range writes nothing (counted all the same, 942).
    if file[page]! == .allocDirty then written := written ++ [page]
  let total := ranges.foldl (fun t (_, c) => t + c) 0
  if total > 0 then
    let mut left := 1 + (← below "partial.left" total)
    let mut range ← below "partial.range" ranges.length
    for _ in [0:ranges.length + 1] do
      if left == 0 then break
      let (first, count) := ranges[range]!
      let run := min left count
      written := written ++ (List.range run).map (first + ·)
      left := left - run
      range := (range + 1) % ranges.length
  return written

/-- What a page holds after the power loss: its data kept, or lost (a new page reads zeros, an
overwrite its old content). With `commit` (the journal committed after), new pages written back
survive; without, only pages over allocated blocks. -/
def kept (file : List Page) (written : List Nat) (commit : Bool) (i : Nat) : Bool :=
  match file[i]! with
  | .new => commit && written.contains i
  | .allocDirty => written.contains i
  | _ => true

structure PWorld where
  label : String
  pagesMax : Nat := 5
  menu : List Page := [.hole, .new]

structure Drawn where
  file : List Page
  commit : Bool
  written : List Nat
  deriving Inhabited

def draw (wd : PWorld) : EStateM Stop PS Drawn := do
  let n := 1 + (← below "world.pages" wd.pagesMax)
  let mut file := []
  for _ in [0:n] do file := file ++ [wd.menu[(← below "world.page" wd.menu.length)]!]
  let commit := (← below "fault.partial_commit" 2) == 0
  let written ← partialFile file
  return { file, commit, written }

def fresh (file : List Page) : Bool := !file.any fun p => p == .allocClean || p == .allocDirty

structure PProp where
  name : String
  source : String
  check : Drawn → Option String

/-- No new page of a fresh file lost before one kept (in file order). -/
def noHoleBeforeKept : PProp :=
  { name := "no hole before a kept page of a fresh file"
    source := "docs/ANTITHESIS.md (Partial persistence at a power loss): \"its new data ... as an ascending run from the start of one of its new ranges, as the flusher writes it (no hole before a kept page of a fresh file)\"; nodes.zig:761-765"
    check := fun d => Id.run do
      if !fresh d.file then return none
      let newPages := (List.range d.file.length).filter fun i => d.file[i]! == .new
      for j in newPages do
        if !kept d.file d.written d.commit j then continue
        if let some i := newPages.find? fun i => i < j && !kept d.file d.written d.commit i then
          return some s!"page {j} kept, page {i} (written before it in the file, new data) lost: zeros under the committed size"
      return none }

/-- The new data written back is one ascending run. -/
def ascendingRun : PProp :=
  { name := "a file's new data is written back as an ascending run"
    source := "docs/ANTITHESIS.md (Partial persistence at a power loss): \"its new data ... as an ascending run from the start of one of its new ranges\""
    check := fun d => Id.run do
      let ranges := unallocated d.file
      let newWritten := d.written.filter (contains ranges ·)
      for k in [1:newWritten.length] do
        if newWritten[k]! < newWritten[k - 1]! then
          return some s!"new pages written back in the order {newWritten}"
      return none }

def allPProps : List PProp := [noHoleBeforeKept, ascendingRun]

def judgeP (p : PProp) (wd : PWorld) (source : Source) : Ended :=
  match (draw wd).run { decisions := { source } } with
  | .ok d s => { taken := s.decisions.taken, violation := (p.check d).map fun x => (p.name, x) }
  | .error _ s => { taken := s.decisions.taken, violation := none }

def pstory (wd : PWorld) (source : Source) : List String :=
  match (draw wd).run { decisions := { source } } with
  | .ok d _ =>
    [s!"the file's pages: {d.file.map Page.name}", s!"its new data's ranges (first, count): {unallocated d.file}",
     s!"written back, in order: {d.written}", s!"journal committed after: {d.commit}",
     s!"after the power loss: {(List.range d.file.length).map fun i => (i, if kept d.file d.written d.commit i then "kept" else "lost")}"]
  | .error _ _ => []

def pworlds : List PWorld :=
  [ { label := "fresh files of 1 to 5 pages, each new data or a hole" },
    { label := "files of 1 to 4 pages, any page", pagesMax := 4, menu := [.hole, .new, .allocClean, .allocDirty] } ]

def searchAll (exhaustRuns : Nat) : IO (List Found) := do
  let mut found := []
  for p in allPProps do
    say s!"== persistence property: {p.name}"
    say s!"   source: {p.source}"
    for wd in pworlds do
      if let some f ← exhaustSaid s!"{p.name} / {wd.label}" (judgeP p wd) exhaustRuns then
        printFound f (pstory wd)
        found := found ++ [f]
  return found

end Replica.Persist
