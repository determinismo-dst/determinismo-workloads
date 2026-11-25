import Replica.Prelude
import Replica.Searching
import Replica.Tree

/-!
# A resumed tree, replicated (src/main.zig, platform 3939448)

`--resume` continues a stopped run from its record (main.zig:242-244: "continue that run, its
recorded timelines skipped; ... a tree without a strategy, from its timelines' summaries"). A
tree is continued by judging its recorded generations again, so that "the queue is then the
interrupted run's" (`tree_rejudge`, 4643-4661) and "every index keeps its timeline"
(`queue_take`, 4552-4561).

Replicated, function by function:

- the interrupted run's judgment of a generation as the run's loop makes it: `tree_judge_begin`
  starts a node making per return, in the returns' order (6439-6560); the loop polls them
  (`tree_judge_poll`, 6219-6233), and each poll plans the made ones not planned yet in the
  makings' order (`judge_plan_ready`, 6254-6261; `judge_plan_one`, 6263-6310: `children`
  timelines each, numbered from `next_index`); between polls a worker that frees up takes the
  queue's next timeline, or with none queued while a judgment runs a fresh filler from the setup
  snapshot at the next index, recorded as `{"fresh":{generation,index}}` (`queue_take`,
  4562-4574); once every node is made, `tree_judge_end` fills the generation with fresh
  timelines (6647-6658);
- the record a stop leaves: a line per timeline that finished (its path's last place), the
  fillers' `fresh` lines, the generation's members;
- `resume_read` (2103-2194): each recorded timeline counted under the key (generation, its
  path's last branch, its moment), with its smallest index (`children`, `first_child`,
  2152-2163);
- `rejudge_load` (4677-4724): the recorded fillers of the generation queued first, each at the
  next index or the resume `.cut` (4694-4698); the last recorded generation `.last`, left to the
  run's loop (4720-4723);
- `recorded_returns` (6820-6841): the record's returns of the generation, one per key, in the
  order of their first child; `tree_judge_begin` takes them for a generation judged again
  (6427-6431); a return whose key has `children` recorded timelines makes no node: `ready`, its
  snapshot the setup's ("its timelines are planned from the setup snapshot, never started",
  6455-6466);
- after a `.cut`, the loop takes the recorded members from the queue (their summaries, 4303-4310)
  and judges the generation again, recording (4281-4285); its returns are then the judgment's own,
  which are the interrupted run's (the same members and state: the judgment is deterministic).

What is not modeled: the judgment itself (the returns are the world's: their order is the
makings' order), holders (a resumed run has none), memory caps, sessions. One generation (its
`size` members all recorded) is judged before the stop; the stop comes before the next one is
judged (fewer than `size` of the later timelines recorded).
-/

namespace Replica.Resume4

open Determinismo

/-- A return: the timeline returned to and the moment (µs). -/
structure Ret where
  branch : Nat
  vtime : Nat
  deriving BEq, Repr, Inhabited, DecidableEq

def Ret.show (r : Ret) : String := s!"#{r.branch} at {r.vtime} µs"

/-- A timeline's plan, as its record line says it: from the setup snapshot (a filler or the
fill), or a child of a return (its path's last place). -/
inductive Plan where
  | fresh
  | child (r : Ret)
  deriving BEq, Repr, Inhabited

def Plan.show : Plan → String
  | .fresh => "fresh from the setup snapshot"
  | .child r => s!"a child of the return to {r.show}"

structure Cfg where
  label : String
  size : Nat := 5
  children : Nat := 2
  /-- The judgment's returns, in the makings' order. -/
  rets : List Ret
  /-- How many times a worker may free up during a judgment (bounds the space). -/
  frees : Nat := 0
  /-- Every return has a timeline in the record (the stop came later). -/
  everyReturnRecorded : Bool := false
  /-- The resumed host's timing drawn; false: it makes its nodes in the makings' order, no
  worker frees up meanwhile (the same order the interrupted run had when it made them so). -/
  resumedTiming : Bool := true
  deriving Inhabited

structure RS where
  decisions : Decisions := {}
  deriving Inhabited

instance : Chaotic RS where
  decisions s := s.decisions
  setDecisions _ d := { decisions := d }

abbrev RM := EStateM Stop RS

/-- The plans a judgment made, the queue, the fillers' `fresh` lines. -/
structure Planning where
  next : Nat
  plans : List (Nat × Plan) := []
  queue : List Nat := []
  freshLines : List Nat := []
  /-- Indices planned from a `ready` making: their snapshot is the setup's (6463). -/
  fromReady : List Nat := []
  /-- The order the makings were planned in (for the story). -/
  order : List Nat := []
  deriving Inhabited

def planOf (p : Planning) (i : Nat) : Option Plan := (p.plans.find? (·.1 == i)).map (·.2)

/-- main.zig:6254-6261 `judge_plan_ready` with 6263-6310 `judge_plan_one`: each ready making not
planned yet, in the makings' order, its `children` timelines at the next indices, queued
(`queue_push` before the filler, 4476-4482). -/
def planReady (cfg : Cfg) (rets : List Ret) (ready : Array Bool) (readyAtStart : List Bool)
    (planned : Array Bool) (p : Planning) : Array Bool × Planning := Id.run do
  let mut planned := planned
  let mut p := p
  for k in [0:rets.length] do
    if !ready[k]! || planned[k]! then continue
    planned := planned.set! k true
    p := { p with order := p.order ++ [k] }
    for _ in [0:cfg.children] do
      p := { p with plans := p.plans ++ [(p.next, .child rets[k]!)], queue := p.queue ++ [p.next],
                    fromReady := if readyAtStart[k]! then p.fromReady ++ [p.next] else p.fromReady,
                    next := p.next + 1 }
  return (planned, p)

/-- The run's loop while a judgment's nodes are made (main.zig:4258-4262 the poll, 4303-4339 a
timeline started as a worker frees up): the makings not ready yet become ready in a drawn order
(the host's timing), a worker frees up between polls (at most `frees` times): the queue's next
timeline, or a fresh filler at the next index, recorded (`queue_take`); every poll plans the ready
ones (`judge_plan_ready`); the first poll comes before any worker frees up (4258, after 4283's
`continue`). Then `tree_judge_end`'s fill (6647-6658): the generation's `size` less the branches
planned, fresh. -/
def judging (name : String) (cfg : Cfg) (rets : List Ret) (readyAtStart : List Bool) (p : Planning)
    (drawn : Bool := true) : RM Planning := do
  let k := rets.length
  let mut ready := readyAtStart.toArray
  let mut planned := Array.replicate k false
  let mut p := p
  let mut frees := if drawn then cfg.frees else 0
  (planned, p) := planReady cfg rets ready readyAtStart planned p
  let mut guard := 0
  while ready.any (!·) && guard < 64 do
    guard := guard + 1
    let pending := (List.range k).filter (fun j => !ready[j]!)
    let options := pending.length + (if frees > 0 then 1 else 0)
    let d ← if drawn then below s!"{name}.step" options else pure 0
    if d < pending.length then
      ready := ready.set! pending[d]! true
    else
      frees := frees - 1
      match p.queue with
      | _ :: rest => p := { p with queue := rest }
      | [] => p := { p with plans := p.plans ++ [(p.next, .fresh)], freshLines := p.freshLines ++ [p.next], next := p.next + 1 }
    (planned, p) := planReady cfg rets ready readyAtStart planned p
  let branches := k * cfg.children
  for _ in [branches:cfg.size] do
    p := { p with plans := p.plans ++ [(p.next, .fresh)], next := p.next + 1 }
  return p

/-- main.zig:2152-2163: the recorded timelines counted under (generation, branch, moment), and
each key's smallest index. -/
def childrenOf (recorded : List (Nat × Plan)) (r : Ret) : Nat :=
  (recorded.filter fun (_, pl) => pl == .child r).length

/-- main.zig:6820-6841 `recorded_returns`: one return per key, in the order of their first child;
none when the record has no child. -/
def recordedReturns (recorded : List (Nat × Plan)) : Option (List Ret) := Id.run do
  let mut found : List (Ret × Nat) := []
  for (i, pl) in recorded do
    match pl with
    | .child r =>
      match found.findIdx? (·.1 == r) with
      | some k => if i < found[k]!.2 then found := found.set k (r, i)
      | none => found := found ++ [(r, i)]
    | .fresh => pure ()
  if found.isEmpty then return none
  let sorted := found.foldl (fun acc x => Replica.Tree.insertStable (fun a b => a.2 < b.2) x acc) []
  return some (sorted.map (·.1))

/-- One run: the interrupted run's judgment, its stop, the resume's. -/
structure Run where
  original : Planning
  recorded : List (Nat × Plan)
  cut : Bool
  resumedRets : List Ret
  readyR : List Bool
  resumed : Planning
  deriving Inhabited

def runOf (cfg : Cfg) : RM Run := do
  -- The interrupted run: generation 0 (indices 0 to size - 1) judged, its returns' nodes made.
  let original ← judging "original" cfg cfg.rets (cfg.rets.map fun _ => false) { next := cfg.size }
  -- The stop: the timelines that finished by then are recorded (fewer than a generation, so the
  -- next one was not judged).
  let mut recorded : List (Nat × Plan) := []
  for (i, pl) in original.plans do
    if recorded.length + 1 ≥ cfg.size then break
    if (← below "stop.recorded" 2) == 1 then recorded := recorded ++ [(i, pl)]
  -- resume_read; rejudge_load's fillers first (4694-4698).
  let mut p : Planning := { next := cfg.size }
  let mut cut := false
  for f in original.freshLines do
    if f != p.next then
      cut := true
      break
    p := { p with plans := p.plans ++ [(p.next, .fresh)], queue := p.queue ++ [p.next], next := p.next + 1 }
  let resumedRets := if cut then cfg.rets else (recordedReturns recorded).getD cfg.rets
  let readyR : List Bool := resumedRets.map fun r => decide (childrenOf recorded r ≥ cfg.children)
  let resumed ← judging "resumed" cfg resumedRets readyR p cfg.resumedTiming
  return { original, recorded, cut, resumedRets, readyR, resumed }

def isRecorded (r : Run) (i : Nat) : Bool := r.recorded.any (·.1 == i)

structure RProp where
  name : String
  source : String
  check : Cfg → Run → Option String

def showPlans (p : Planning) : String :=
  String.intercalate "; " (p.plans.map fun (i, pl) => s!"{i}: {pl.show}")

/-- Whether the run is one the world asks for (every return in the record, when asked). -/
def admitted (cfg : Cfg) (r : Run) : Bool :=
  !cfg.everyReturnRecorded || cfg.rets.all (fun ret => r.recorded.any (·.2 == .child ret))

def keepsRecorded : RProp :=
  { name := "every recorded timeline keeps its plan in the resumed tree"
    source := "main.zig:242-244 (--resume: \"continue that run, its recorded timelines skipped\"); main.zig:4643-4645 (tree_rejudge: \"the queue is then the interrupted run's\"); main.zig:4552-4561 (queue_take: \"so that every index keeps its timeline\"); main.zig:4136-4139 (\"a resumed run judges the same generations again\")"
    check := fun cfg r => Id.run do
      if !admitted cfg r then return none
      for (i, pl) in r.recorded do
        match planOf r.resumed i with
        | some pl' => if pl' != pl then
            return some s!"timeline {i} ran as {pl.show} (its record line); the resumed tree plans it as {pl'.show}, and judges its summary so"
        | none => return some s!"timeline {i} ran as {pl.show}; the resumed tree never plans it"
      return none }

def startsWhereItsPathSays : RProp :=
  { name := "every timeline the resumed tree runs starts where its path says (it replays from its tape)"
    source := "README_AI.md (\"every timeline replays bit-identically\"); docs/ANTITHESIS.md, Branching (\"every timeline's path in its record and tape (it replays alone)\"); main.zig:6458-6460 (a ready return's timelines are \"planned from the setup snapshot, never started\")"
    check := fun cfg r => Id.run do
      if !admitted cfg r then return none
      for i in r.resumed.fromReady do
        if isRecorded r i then continue
        let pl := (planOf r.resumed i).getD .fresh
        return some s!"timeline {i} is not recorded and runs: planned as {pl.show} from a ready return, it starts at the setup snapshot while its path (its tape's chain) says it begins inside #{match pl with | .child x => x.branch | .fresh => 0}"
      return none }

def keepsPlanned : RProp :=
  { name := "every timeline the interrupted run planned keeps its plan (every index keeps its timeline)"
    source := "main.zig:4552-4561 (queue_take: \"a resumed run takes it again at the same place (tree_rejudge), before that generation's plan, so that every index keeps its timeline\"); main.zig:4643-4645 (\"the queue is then the interrupted run's\")"
    check := fun cfg r => Id.run do
      if !admitted cfg r then return none
      for (i, pl) in r.original.plans do
        if isRecorded r i then continue
        match planOf r.resumed i with
        | some pl' => if pl' != pl then
            return some s!"timeline {i} (not recorded) was planned as {pl.show}; the resumed tree runs it as {pl'.show}"
        | none => return some s!"timeline {i} (not recorded) was planned as {pl.show}; the resumed tree never plans it"
      return none }

def neverCut : RProp :=
  { name := "a resume judges again every generation its record has whole, made with this plan"
    source := "main.zig:4643-4646 (tree_rejudge: \"A resumed run's recorded generations judged again, in their order ... the queue is then the interrupted run's. A generation whose summaries the interruption cut ends it\"); main.zig:4665-4669 (Rejudged.cut: \"Not the plan its record was made with, or cut by the interruption\"); main.zig:4692 (\"The fresh timelines taken while it was judged, before its plan as they were\")"
    check := fun _ r =>
      if r.cut then
        some s!"generation 0's record is whole and this plan's, its fillers taken at {r.original.freshLines} between its returns' timelines ({showPlans r.original}): rejudge_load cuts it, and the loop judges it again with the resumed host's timing: {showPlans r.resumed}"
      else none }

def allRProps : List RProp := [keepsRecorded, startsWhereItsPathSays, keepsPlanned, neverCut]

def judgeR (p : RProp) (cfg : Cfg) (source : Source) : Ended :=
  match (runOf cfg).run { decisions := { source } } with
  | .ok r s => { taken := s.decisions.taken, violation := (p.check cfg r).map fun d => (p.name, d) }
  | .error _ s => { taken := s.decisions.taken, violation := none }

def storyR (cfg : Cfg) (source : Source) : List String :=
  match (runOf cfg).run { decisions := { source } } with
  | .ok r _ =>
    [ s!"generation 0: timelines 0 to {cfg.size - 1}; returns, in the makings' order: {String.intercalate ", " (cfg.rets.map Ret.show)} ({cfg.children} branches each)",
      s!"the interrupted run planned (nodes made in the order {r.original.order}): {showPlans r.original}",
      s!"its fillers' fresh lines: {r.original.freshLines}",
      s!"recorded before the stop: {String.intercalate "; " (r.recorded.map fun (i, pl) => s!"{i} ({pl.show})")}",
      if r.cut then "resume: rejudge_load's fillers do not come first: .cut (the loop judges generation 0 again, recording)"
      else s!"resume: recorded_returns gives {String.intercalate ", " (r.resumedRets.map Ret.show)}; ready (no node, the setup's snapshot): {r.readyR}",
      s!"the resumed tree plans (planned in the order {r.resumed.order}): {showPlans r.resumed}" ]
  | .error _ _ => []

/-- Returns at distinct moments: A, B and C. -/
def retA : Ret := { branch := 0, vtime := 10 }
def retB : Ret := { branch := 1, vtime := 20 }
def retC : Ret := { branch := 2, vtime := 30 }

def rworlds : List Cfg :=
  [ { label := "size 4, 1 branch a return, 3 returns, no filler", size := 4, children := 1, rets := [retA, retB, retC] },
    { label := "size 5, 2 branches a return, 2 returns, no filler, every return recorded", size := 5, children := 2, rets := [retA, retB], everyReturnRecorded := true },
    { label := "size 5, 2 branches a return, 2 returns, every return recorded, nodes made again in the makings' order", size := 5, children := 2, rets := [retA, retB], everyReturnRecorded := true, resumedTiming := false },
    { label := "size 5, 2 branches a return, 2 returns, up to 3 fillers", size := 5, children := 2, rets := [retA, retB], frees := 3 },
    { label := "size 5, 2 branches a return, 2 returns, up to 3 fillers, every return recorded", size := 5, children := 2, rets := [retA, retB], frees := 3, everyReturnRecorded := true },
    { label := "size 4, 1 branch a return, two returns to one moment (CE26), every return recorded", size := 4, children := 1, rets := [retA, retA, retC], everyReturnRecorded := true },
    { label := "the default shape: size 16, 4 branches a return, 3 returns, up to 6 fillers", size := 16, children := 4, rets := [retA, retB, retC], frees := 6 } ]

def searchAll (exhaustRuns seeds : Nat) : IO Unit := do
  for p in allRProps do
    say s!"== resume property: {p.name}"
    say s!"   source: {p.source}"
    for cfg in rworlds do
      if let some f ← exhaustSaid s!"{p.name} / {cfg.label}" (judgeR p cfg) exhaustRuns then
        printFound f (storyR cfg)
      if let some f ← exploreSaid s!"{p.name} / {cfg.label}" (judgeR p cfg) seeds then
        printFound f (storyR cfg)

/-- How often: every world explored over `count` seeds, each property counted. -/
def census (count : Nat) : IO Unit := do
  for cfg in rworlds do
    let mut counts := Array.replicate allRProps.length 0
    let mut admittedRuns := 0
    let mut cuts := 0
    for i in [0:count] do
      match (runOf cfg).run { decisions := { source := Source.seeded i } } with
      | .ok r _ =>
        if !admitted cfg r then continue
        admittedRuns := admittedRuns + 1
        if r.cut then cuts := cuts + 1
        for (p, k) in allRProps.zipIdx do
          if (p.check cfg r).isSome then counts := counts.modify k (· + 1)
      | .error _ _ => pure ()
    say s!"census [{cfg.label}, seeds 0..{count - 1}]: {admittedRuns} resumed runs, {cuts} cut"
    for (p, k) in allRProps.zipIdx do
      say s!"  {counts[k]!} of {admittedRuns} break: {p.name}"

end Replica.Resume4
