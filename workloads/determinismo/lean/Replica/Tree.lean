import Replica.Prelude
import Replica.Searching

/-!
# The explorer's tree, replicated (src/main.zig, platform 3939448)

A tree run (`--branching tree`, the default) plans its timelines in generations
(`tree`, main.zig:3961-4004): the first `pipeline` generations from the setup snapshot, then after
each generation is judged (`tree_judge_begin` 6318-6585, `tree_judge_end` 6589-6681) its returns:
moments of judged timelines a node (a snapshot) is made at, and `children` new timelines from
each (`judge_plan_one` 6263-6310), the rest of the generation fresh from the setup again.

Replicated function by function, each with its lines:

- `tree.generation_for`, `roots`, `nodes`, `fits` (3961-4004), `judge_count` (4614-4620);
- `frontier_choose` (6696-6758) and `candidate_before` (7366-7371);
- `tree_returns` (7204-7341), the strategy's `returns` parsed by `answer_parse`
  (src/strategy.zig:702-745) and chosen by `Strategies.returns` (src/strategies.zig:274-290);
- `archive_add` (6989-7040), `objective_place` (7047-7052), `memory_forget` (7062-7075),
  `archive_returns` (7081-7123), `archive_ranked` (7134-7165), `archive_offered` (7167-7190),
  `Cell.place` (5807-5830);
- `returns_earlier` (6893-6918), `returns_branches` (6973-6977), `branch_start_ns` (6882-6886);
- the judgment's order of work (6318-6585), the parents found for returns (6443-6449), the node
  made by a holder of this generation's timeline or by a replay along the parent's recorded path
  (6466-6531, src/core/node.zig:16-40 and 165-180), `judge_plan_one`'s path and children
  (6263-6310), `tree_judge_end`'s fresh fill (6643-6658);
- the worker's start of a timeline: its strategy's `branch` reply giving it another seed
  (3474-3486) and its tape's header (`branch_announce`, 3754-3780: the seed it ran with, and
  `chain` = its plan's path);
- the queue (4463-4600): planned timelines before the filler, timelines taken in order as
  workers free up, a generation the next `size` timelines to finish.

The system the timelines run is a model (`Sys`): `len` events, one every 10 µs of virtual time,
each a value below `kinds`, drawn from the seed in effect at the event's pull (`pulls`), else the
previous value plus one. A timeline runs a schedule of seeds: each ancestor's from its start to
the moment the next one branched from it, then its own. Its behaviors are what events.zig keeps
(behavior_note 728-771, scored_note 701-722): an output line per value, a `sometimes` made true
(sought) the first time the value is `soughtValue`, and an `sdk.optimize` bucket whose score is
the highest value so far (its moment the first time it reached it).

Times are in µs: `return_after_ns` (6686) is 1, a millisecond 1000.

What the Zig draws from its generation's PRNG (`generation_seed`, 6386-6391: the doom draws,
`memory_forget`, `archive_ranked`'s exponential keys, `returns_earlier`'s offsets, a random
moment) are named decisions here, so a search walks them: every order `archive_ranked` can give has
a positive probability in the Zig (its keys are scores times unbounded exponential draws), and
explore draws them with weights 1/score as Efraimidis and Spirakis's sampling does.
-/

namespace Replica.Tree

open Determinismo

/-- main.zig:6686 `return_after_ns`: a return lands this long after its behavior (1 µs). -/
def after : Nat := 1
def ms : Nat := 1000

/-! ## The tree's shape (main.zig:3961-4004, 4614-4620) -/

def generationBase : Nat := 16
def generationMax : Nat := 256
def childrenDefault : Nat := 4

/-- main.zig:3973-3975 `generation_for(workers)`: the most multiples of 16 that run at once,
clamped to 16..256. `--generation` unless given is this of the run's jobs (main.zig:8883). -/
def generationFor (workers : Nat) : Nat :=
  max generationBase (min generationMax (workers / generationBase * generationBase))

def roots (size : Nat) : Nat := size / 4
def nodes (size branches : Nat) : Nat := (size - roots size) / branches
def fits (size branches : Nat) : Bool := branches > 0 && (size - roots size) % branches == 0

/-- main.zig:4614-4620 `judge_count`. -/
def judgeCount (complete size : Nat) : Nat :=
  if complete < size then complete else size * (complete / size)

/-! ## What a timeline leaves for its judgment -/

structure Behavior where
  hash : Nat
  vtime : Nat
  label : String
  sought : Bool := false
  severe : Bool := false
  /-- An optimization's bucket: its best score in the timeline (events.zig:291-294). -/
  score : Option Int := none
  deriving Repr, Inhabited, BEq

/-- tape.Segment: an ancestor, the seed recorded for it, and the moment the next branched. -/
structure Segment where
  branch : Nat
  seed : Nat
  vtime : Nat
  deriving Repr, Inhabited, BEq, DecidableEq

/-- main.zig:3810-3833 `Planned`. -/
structure Planned where
  index : Nat
  seed : Nat
  path : List Segment := []
  generation : Nat := 0
  why : String := ""
  cell : Option Nat := none
  deriving Repr, Inhabited, BEq

/-- main.zig:3835-3886 `Summary`, the fields the judgment reads. -/
structure Summary where
  index : Nat
  startNs : Nat
  endNs : Nat
  behaviors : List Behavior
  traceHash : Nat
  lastPull : Nat
  cut : Bool := false
  failing : Nat := 0
  doomedNs : Option Nat := none
  againNs : Option Nat := none
  deriving Repr, Inhabited

/-- main.zig:6802-6818 `Candidate`. -/
structure Candidate where
  summary : Summary
  novel : Nat
  score : Float
  moment : Option Nat
  label : String
  sought : Bool
  deriving Inhabited

/-- main.zig:6861-6880 `TreeReturn`. -/
structure TreeReturn where
  branch : Nat
  vtime : Nat
  why : String
  cell : Option Nat := none
  strategy : Bool := false
  branches : Option Nat := none
  earliest : Option Nat := none
  /-- "A random moment of ..." (archive_returns reads the why's start, 7095). -/
  randomMoment : Bool := false
  deriving Repr, Inhabited, BEq

structure Place where
  branch : Nat
  vtime : Nat
  doomed : Bool := false
  deriving Repr, Inhabited, BEq

/-- main.zig:5807-5830 `Cell`. -/
structure Cell where
  hash : Nat
  places : Array Place
  label : String
  visits : Nat := 0
  paid : Nat := 0
  sought : Bool := false
  severe : Bool := false
  best : Option Int := none
  deriving Repr, Inhabited

/-- `Cell.place` (5826-5829): its places in turn. -/
def Cell.place (c : Cell) : Place := c.places[c.visits % c.places.size]!

def cellPlacesMax : Nat := 4
def paidScale : Nat := 16
def soughtWeight : Nat := 4

/-- The tree's state (TreeState, 5611-5741), the parts the judgment reads and writes. -/
structure TreeState where
  /-- Behaviors the tree knows (`seen`). -/
  seen : List Nat := []
  /-- Timelines that reached each behavior (`visits`). -/
  visits : List (Nat × Nat) := []
  cells : Array Cell := #[]
  /-- Every judged timeline's plan (`planned`). -/
  planned : List (Nat × Planned) := []
  traces : List Nat := []
  archive : Bool := true
  preferSometimes : Bool := true
  preferSevere : Bool := true
  doomWeight : Nat := 1
  doomFrontier : Bool := false
  generation : Nat := 0
  deriving Inhabited

def lookup {α : Type} (xs : List (Nat × α)) (k : Nat) : Option α := (xs.find? (·.1 == k)).map (·.2)

def bump (xs : List (Nat × Nat)) (k : Nat) : List (Nat × Nat) :=
  if xs.any (·.1 == k) then xs.map fun (a, b) => if a == k then (a, b + 1) else (a, b) else xs ++ [(k, 1)]

/-! ## The judgment's pieces -/

/-- main.zig:6981-6984 `doomed_at`. -/
def doomedAt (s : Summary) (v : Nat) : Bool := match s.doomedNs with | some d => v ≥ d | none => false

/-- `TreeState.preferred` (main.zig:5727-5732), the history left out. -/
def preferred (st : TreeState) (b : Behavior) : Bool :=
  (st.preferSometimes && b.sought) || (st.preferSevere && b.severe)

/-- main.zig:6696-6758 `frontier_choose` (no targeted run: `--changed` is not modeled). -/
def frontierChoose (st : TreeState) (s : Summary) (reached : List (Nat × Nat)) : Candidate := Id.run do
  let mut novel := 0
  let mut moment : Option Nat := none
  let mut label := ""
  let mut score : Float := 0
  let mut momentReached := 1000000000
  let mut momentSought := false
  let roomEnd := if s.cut then s.endNs - ms else s.endNs
  for b in s.behaviors do
    if b.vtime ≤ s.startNs then continue
    let some timelines := lookup reached b.hash | continue
    novel := novel + 1
    let sought := preferred st b
    let weight : Float := if sought then soughtWeight.toFloat else 1
    score := score + weight / timelines.toFloat
    let opened := (s.cut || b.vtime + after < s.lastPull) && !(st.doomFrontier && doomedAt s b.vtime)
    let better := if sought != momentSought then sought else timelines ≤ momentReached
    if b.vtime ≤ roomEnd && opened && better then
      moment := some b.vtime
      momentReached := timelines
      momentSought := sought
      label := b.label
  return { summary := s, novel, score, moment, label, sought := momentSought }

/-- main.zig:7366-7371 `candidate_before` (no changed code): the most novel first, then by index. -/
def candidateBefore (a b : Candidate) : Bool :=
  if a.score != b.score then a.score > b.score else a.summary.index < b.summary.index

/-- Insertion: `x` before the first element it is before, after its equals (stable). -/
def insertStable {α : Type} (lt : α → α → Bool) (x : α) : List α → List α
  | [] => [x]
  | y :: ys => if lt x y then x :: y :: ys else y :: insertStable lt x ys

/-- `std.sort.insertion`: stable. -/
def sortBy {α : Type} (lt : α → α → Bool) (xs : List α) : List α :=
  xs.foldl (fun acc x => insertStable lt x acc) []

/-- main.zig:6973-6977 `returns_branches`. -/
def returnsBranches (rs : List TreeReturn) (children : Nat) : Nat :=
  rs.foldl (fun t r => t + r.branches.getD children) 0

/-- main.zig:7047-7052 `objective_place`. -/
def objectivePlace (s : Summary) (at_ : Nat) : Nat :=
  match s.againNs with
  | none => at_
  | some asked =>
    let before := asked - after
    if at_ ≤ before || before ≤ s.startNs + after then at_ else before

/-- main.zig:6989-7040 `archive_add`: the timeline's plan into `planned`, and with the archive
its behaviors past its start into cells. -/
def archiveAdd (st : TreeState) (plan : List Planned) (s : Summary) : TreeState := Id.run do
  let some planned := plan.find? (·.index == s.index) | return st
  let mut st := { st with planned := (st.planned.filter (·.1 != s.index)) ++ [(s.index, planned)] }
  if !st.archive then return st
  for b in s.behaviors do
    if b.vtime ≤ s.startNs then continue
    let reachedAt := b.vtime + after
    let at_ := if b.score.isSome then objectivePlace s reachedAt else reachedAt
    let opened := s.cut || at_ < s.lastPull
    if !opened || at_ ≥ s.endNs then continue
    let place : Place := { branch := s.index, vtime := at_, doomed := doomedAt s b.vtime }
    match st.cells.findIdx? (·.hash == b.hash) with
    | some i =>
      let cell := st.cells[i]!
      match b.score with
      | some score =>
        if let some best := cell.best then
          if score ≤ best then continue
        st := { st with cells := st.cells.set! i { cell with places := #[place], best := some score, visits := 0, paid := cell.paid + 1 } }
      | none =>
        if cell.places.size == cellPlacesMax then continue
        if cell.places.any (·.branch == s.index) then continue
        st := { st with cells := st.cells.set! i { cell with places := cell.places.push place } }
    | none =>
      st := { st with cells := st.cells.push { hash := b.hash, places := #[place], label := b.label,
                                               sought := b.sought, severe := b.severe, best := b.score } }
  return st

structure JS where
  decisions : Decisions := {}
  log : Array String := #[]
  deriving Inhabited

instance : Chaotic JS where
  decisions s := s.decisions
  setDecisions s d := { s with decisions := d }

abbrev JM := EStateM Stop JS

def note (line : String) : JM Unit := modify fun s => { s with log := s.log.push line }

/-- main.zig:7062-7075 `memory_forget`: k eighths kept, k drawn 0..8 (the bandit's draw too). -/
def memoryForget (st : TreeState) : JM TreeState := do
  let keep ← below "forget.archive" 9
  let _bandit ← below "forget.bandit" 9
  if keep < 8 then
    return { st with
      visits := st.visits.map fun (h, c) => (h, max 1 (c * keep / 8)),
      cells := st.cells.map fun c => { c with visits := c.visits * keep / 8, paid := c.paid * keep / 8 } }
  return st

/-- main.zig:7134-7165 `archive_ranked`: the cells' scores, and an order drawn among them
(weighted sampling without replacement, 1/score). -/
def cellScore (st : TreeState) (c : Cell) : Nat :=
  let timelines := (lookup st.visits c.hash).getD 0
  let pref := (st.preferSometimes && c.sought) || (st.preferSevere && c.severe)
  let prefers := st.preferSometimes || st.preferSevere
  let weight := if prefers && !pref then soughtWeight else 1
  let rarity := if c.best.isSome then 1 + c.visits else (1 + timelines) * (1 + c.visits) * weight
  let doom := if c.place.doomed then st.doomWeight else 1
  rarity * doom * paidScale / (1 + c.paid)

def archiveRanked (st : TreeState) : JM (List Nat) := do
  let mut left := st.cells.toList.map fun c => (c.hash, max 1 (cellScore st c))
  let mut order := []
  while left.length > 0 do
    let weights := left.map fun (_, s) => max 1 (1000000 / s)
    let i ← decideWeighted "archive.rank" weights
    order := order ++ [left[i]!.1]
    left := left.eraseIdx i
  return order

/-- main.zig:7081-7123 `archive_returns`. -/
def archiveReturns (st : TreeState) (size children : Nat) (returns : List TreeReturn) :
    JM (TreeState × List TreeReturn) := do
  let n := nodes size children
  let taken := (returns.takeWhile (·.strategy)).length
  let frontier := returns.drop taken
  let slots := (n * children - returnsBranches (returns.take taken) children) / children
  let novel := frontier.length > 0 && !(frontier[0]!.randomMoment)
  let keep := if novel then min frontier.length ((slots + 1) / 2) else 0
  let mut list := returns.take taken ++ frontier.take keep
  if st.cells.size == 0 then return (st, list)
  let ranked ← archiveRanked st
  let mut st := st
  for hash in ranked do
    if list.length ≥ taken + slots then break
    if (returns.take taken).any (·.cell == some hash) then continue
    let some i := st.cells.findIdx? (·.hash == hash) | continue
    let cell := st.cells[i]!
    let place := cell.place
    st := { st with cells := st.cells.set! i { cell with visits := cell.visits + 1 } }
    let start := match lookup st.planned place.branch with
      | some p => (p.path.getLast?.map (·.vtime)).getD 0
      | none => 0
    list := list ++ [{ branch := place.branch, vtime := place.vtime, cell := some hash, earliest := some (start + after),
                       why := s!"Go-Explore's archive: back to just after {cell.label}, as #{place.branch} reached it" }]
  return (st, list)

/-- A strategy's answer to `returns` (strategy.zig:664-669). -/
structure SReturn where
  branch : Nat
  vtime : Nat
  branches : Option Nat := none
  deriving Repr, Inhabited, BEq

structure Answer where
  returns : List SReturn := []
  fresh : Bool := false
  deriving Repr, Inhabited

/-- strategy.zig:702-745 `answer_parse`: at most `budget` timelines' worth of branches, the last
return getting what is left. -/
def answerParse (asked : List SReturn) (fresh : Bool) (branches budget : Nat) : Answer := Id.run do
  let mut taken := 0
  let mut out := []
  for r in asked do
    if taken ≥ budget then break
    let own := min (r.branches.getD branches) (budget - taken)
    taken := taken + own
    out := out ++ [{ r with branches := if r.branches.isSome || own != branches then some own else none }]
  return { returns := out, fresh }

/-- An archive cell offered to a plugin (main.zig:7167-7190): its place. -/
structure Offer where
  hash : Nat
  branch : Nat
  vtime : Nat
  deriving Repr, Inhabited

/-- main.zig:7204-7341 `tree_returns`. -/
def treeReturns (st : TreeState) (answer : Option Answer) (chosen : List Candidate) (size children : Nat)
    (offers : List Offer) : JM (TreeState × List TreeReturn × Bool) := do
  let n := nodes size children
  let mut list : List TreeReturn := []
  let mut fillFresh := false
  let mut st := st
  if let some a := answer then
    fillFresh := a.fresh
    for back in a.returns do
      match chosen.find? (·.summary.index == back.branch) with
      | some c =>
        if back.vtime ≤ c.summary.startNs || back.vtime ≥ c.summary.endNs then continue
      | none =>
        if (lookup st.planned back.branch).isNone then continue
      let cellHash := (offers.find? fun o => o.branch == back.branch && o.vtime == back.vtime).map (·.hash)
      if let some h := cellHash then
        if let some i := st.cells.findIdx? (·.hash == h) then
          st := { st with cells := st.cells.modify i fun c => { c with visits := c.visits + 1 } }
      list := list ++ [{ branch := back.branch, vtime := back.vtime, cell := cellHash, strategy := true,
                         branches := back.branches, why := s!"The strategy returned to #{back.branch} here" }]
  let strategyCount := list.length
  let fillNodes := if fillFresh then 0 else (n * children - returnsBranches list children) / children
  for c in chosen do
    if list.length ≥ strategyCount + fillNodes then break
    let s := c.summary
    if list.any (·.branch == s.index) then continue
    let endNs := min s.endNs s.lastPull
    let span := endNs - s.startNs
    if span < 2 * after then continue
    let extend := s.cut && c.novel > 0
    let afterAt ← if extend then pure (s.endNs - ms)
      else match c.moment with
        | some m => pure (m + after)
        | none => do pure (s.startNs + (← below "return.random_moment" span))
    let at_ := max (s.startNs + after) (min afterAt (endNs - after))
    list := list ++ [{ branch := s.index, vtime := at_,
                       randomMoment := !extend && c.moment.isNone,
                       why := if extend then s!"Extended #{s.index}" else match c.moment with
                         | some _ => s!"Returned to #{s.index} just after it first reached {c.label}: its frontier"
                         | none => s!"A random moment of #{s.index}",
                       earliest := if !extend && c.moment.isSome then some (s.startNs + after) else none }]
  return (st, list, fillFresh)

/-- main.zig:6893-6918 `returns_earlier`. -/
def returnsEarlier (offsets : List Nat) (returns : List TreeReturn) : JM (List TreeReturn) := do
  if offsets.isEmpty then return returns
  let mut out := []
  for back in returns do
    match back.earliest with
    | none => out := out ++ [back]
    | some earliest =>
      let offset := offsets[(← below "return.offset" offsets.length)]!
      if offset == 0 || back.vtime < earliest + offset then out := out ++ [back]
      else out := out ++ [{ back with vtime := back.vtime - offset, why := back.why ++ s!" Landed {offset} µs before that moment instead." }]
  return out

end Replica.Tree
