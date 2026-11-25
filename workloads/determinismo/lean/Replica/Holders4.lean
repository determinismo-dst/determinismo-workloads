import Replica.Prelude
import Replica.Searching

/-!
# Holders, replicated (src/holders.zig, src/main.zig; platform 3939448)

A timeline's holders are forks of its VM at moments of it (`Owner`, holders.zig:932-1290):

- `spacing` (1003-1006): the timeline's expected length over 64, at least 10 ms (1 s when no
  length is known); `period` (1009-1011): `spacing * 8`;
- `attach` (1017-1022): a periodic hold point armed at `start + period`;
- `behaviors` (1031-1045): at a behavior the tree did not know (not `seen`), past the start: a
  hold point just after it (`max(vtime + 1 µs, start + 1 ms)`), unless one is armed for a new
  behavior already, or the last holder is less than `spacing` before it;
- `reached` (1047-1110): the holder made, the next periodic one armed `period` later; past
  `per_timeline_max` = 8 kept, `drop` (1275-1293) removes the one closest to the one before it
  (never the first or the newest);
- `Registry.take` (589-626): the latest holder of the timeline at or before the moment not taken
  yet (one serves one return); `earliest` (576-585); main.zig:3940-3945 `replay_why`.

The judgment's node for a return (main.zig:6466-6498): a holder taken, replayed on to the moment
(`HolderMaker.make`, 7382-7404, with the timeline's own tape), or a replay from the parent's start.
Time is in µs; the timeline runs from `start` to `start + length`, its behaviors drawn.
-/

namespace Replica.Holders4

open Determinismo

def ms : Nat := 1000
def spacingMin : Nat := 10 * ms
def perTimelineMax : Nat := 8

/-- holders.zig:1003-1006. -/
def spacing (length : Option Nat) : Nat :=
  match length with
  | none => 1000 * ms
  | some l => max spacingMin (l / 64)

def period (sp : Nat) : Nat := sp * (64 / perTimelineMax)

/-- holders.zig:1275-1293 `drop`: the one closest to the one before it (indices 1 to n-2). -/
def drop (kept : Array Nat) : Array Nat := Id.run do
  let mut victim := 1
  let mut gapMin := 1000000000000
  for i in [1:kept.size - 1] do
    let gap := kept[i]! - kept[i - 1]!
    if gap < gapMin then
      gapMin := gap
      victim := i
  return kept.eraseIdx! victim

structure Behavior where
  vtime : Nat
  new : Bool
  deriving Repr, Inhabited, BEq

/-- The Owner over a timeline's events: its kept holders' moments. -/
def holdersOf (start length : Nat) (bs : List Behavior) : Array Nat := Id.run do
  let sp := spacing (some length)
  let per := period sp
  let stop := start + length
  let mut armed : Option Nat := some (start + per)
  let mut armedNew := false
  let mut last : Option Nat := none
  let mut kept : Array Nat := #[]
  let mut pending := bs
  -- Walk virtual time: the next event is a behavior's or the armed hold point's, whichever first.
  let mut guard := 0
  while guard < 10000 do
    guard := guard + 1
    let nextB := pending.head?.map (·.vtime)
    let take := match armed, nextB with
      | some a, some b => if a ≤ b then some true else some false
      | some _, none => some true
      | none, some _ => some false
      | none, none => none
    match take with
    | none => break
    | some true =>
      let a := armed.get!
      if a ≥ stop then break
      -- reached: the holder at `a`, the next periodic one armed.
      last := some a
      armedNew := false
      armed := some (a + per)
      kept := kept.push a
      if kept.size > perTimelineMax then kept := drop kept
    | some false =>
      let b := pending.head!
      pending := pending.tail
      if b.vtime ≥ stop then break
      if armedNew || b.vtime ≤ start || !b.new then continue
      let moment := max (b.vtime + 1) (start + ms)
      if let some l := last then
        if moment < l + sp then continue
      armed := some moment
      armedNew := true
  return kept

/-- Registry.take: the latest at or before `v` not taken; the kept with that one marked. -/
def take (kept : Array Nat) (taken : List Nat) (v : Nat) : Option Nat :=
  let ok := kept.toList.filter fun h => h ≤ v && !taken.contains h
  ok.foldl (fun b h => match b with | some x => some (max x h) | none => some h) none

structure HCfg where
  label : String
  length : Nat := 640 * ms
  behaviors : Nat := 6
  /-- Returns to the timeline in one generation. -/
  returns : Nat := 2
  deriving Inhabited

structure HS where
  decisions : Decisions := {}
  deriving Inhabited

instance : Chaotic HS where
  decisions s := s.decisions
  setDecisions _ d := { decisions := d }

abbrev HM := EStateM Stop HS

structure HRun where
  bs : List Behavior
  kept : Array Nat
  /-- Each return: its moment, the holder it took (none: a replay from the start), and why. -/
  made : List (Nat × Option Nat × String)
  deriving Repr, Inhabited

def runOf (cfg : HCfg) : HM HRun := do
  let start := 0
  let mut bs : List Behavior := []
  let mut t := 0
  for _ in [0:cfg.behaviors] do
    -- The next behavior 0 to 159 ms later (a burst, or a quiet stretch).
    t := t + (← below "behavior.gap_ms" 160) * ms + (← below "behavior.gap_us" 3)
    bs := bs ++ [{ vtime := t, new := (← below "behavior.new" 2) == 1 }]
  let kept := holdersOf start cfg.length bs
  -- The generation's returns to it: just after a new behavior (the frontier, an archive cell).
  let news := bs.filter (·.new)
  let mut taken : List Nat := []
  let mut made := []
  if news.isEmpty then return { bs, kept, made := [] }
  for _ in [0:cfg.returns] do
    let b := news[(← below "return.behavior" news.length)]!
    let v := b.vtime + 1
    match take kept taken v with
    | some h =>
      taken := taken ++ [h]
      made := made ++ [(v, some h, "a holder")]
    | none =>
      let first := kept.toList.foldl (fun m h => min m h) 1000000000000
      let why := if kept.isEmpty then "no holder" else if first > v then "before its first holder" else "its holders before it taken"
      made := made ++ [(v, none, why)]
  return { bs, kept, made }

def promptHolder : String := "a return just after a new behavior starts from a holder made at most `spacing` before it (a hold point there, unless one was made a moment ago)"
def promptSource : String := "holders.zig:1029-1032 (\"The tree returns just after a behavior it did not know ...: a hold point there, unless one was made a moment ago\"); holders.zig:29-35 (\"Holders of a timeline are its length over this apart at least (... one holder per burst)\"; \"so the replays from a holder to a later moment stay short wherever the moment is\")"

def check (cfg : HCfg) (r : HRun) : Option String := Id.run do
  let sp := spacing (some cfg.length)
  for (v, h, why) in r.made do
    if v < ms then continue -- Before the first holder can be, by design (start + 1 ms).
    match h with
    | some x => if v - x > sp then
        return some s!"behaviors {r.bs.map fun b => (b.vtime, b.new)}; holders kept at {r.kept}; a return at {v} µs takes the holder at {x}: a replay of {v - x} µs, spacing {sp}"
    | none => return some s!"behaviors {r.bs.map fun b => (b.vtime, b.new)}; holders kept at {r.kept}; a return at {v} µs: {why}, a replay from the start"
  return none

def judgeH (cfg : HCfg) (src : Source) : Ended :=
  match (runOf cfg).run { decisions := { source := src } } with
  | .ok r s => { taken := s.decisions.taken, violation := (check cfg r).map (promptHolder, ·) }
  | .error _ s => { taken := s.decisions.taken, violation := none }

def storyH (cfg : HCfg) (src : Source) : List String :=
  match (runOf cfg).run { decisions := { source := src } } with
  | .ok r _ => [s!"a timeline of {cfg.length} µs, spacing {spacing (some cfg.length)} µs, period {period (spacing (some cfg.length))} µs",
                s!"behaviors (µs, new): {r.bs.map fun b => (b.vtime, b.new)}",
                s!"holders kept: {r.kept}",
                s!"returns (moment, holder taken, why): {r.made}"]
  | .error _ _ => []

def hworlds : List HCfg :=
  [ { label := "one return, 4 behaviors", behaviors := 4, returns := 1 },
    { label := "two returns, 4 behaviors", behaviors := 4, returns := 2 },
    { label := "one return, 12 behaviors (more than 8 holders)", behaviors := 12, returns := 1 } ]

def searchAll (exhaustRuns seeds : Nat) : IO Unit := do
  say s!"== holder property: {promptHolder}"
  say s!"   source: {promptSource}"
  for cfg in hworlds do
    if let some f ← exhaustSaid s!"{promptHolder} / {cfg.label}" (judgeH cfg) exhaustRuns then
      printFound f (storyH cfg)
    if let some f ← exploreSaid s!"{promptHolder} / {cfg.label}" (judgeH cfg) seeds then
      printFound f (storyH cfg)

end Replica.Holders4
