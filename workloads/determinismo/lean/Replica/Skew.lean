import Replica.Prelude
import Replica.Searching

/-!
# Clock skews and skips, replicated (guest/runtime/faults.zig, platform 3939448)

- A timeline's wall clock start (composer.zig:905-927): CLOCK_REALTIME moved forward once, before
  the drivers and the injector (composer.zig:489-501).
- `clock_skip` (faults.zig:1554-1560, 4310-4320 `clock_shift`): the machine's CLOCK_REALTIME
  moved forward or back by `skip`, back again by the same amount from the clock then at the
  fault's end, or not (permanent: a quarter of them, they stack).
- `clock_skew` (1696-1765, 1767-1773 `skew_begin`, 2826-2846 the strobe's flips, 2290-2293 the
  end): one node's realtime offset in its time namespace (nodes.zig:2504-2510, 386-390), drawn
  `clock_skew_draw`, then `skew_clamp`ed within the node's maximum of every other node's skew
  under way and no more than the maximum below what the clocks remember (`clock_high_ns`, raised by
  `clock_leaves` as a skew leaves a clock); a strobe flips back to its skew only when it fits what
  the clocks remember.

Times are in units of the node's maximum offset divided by 4 (`max` = 4). A node's clock reads
monotonic + the machine's offset + its skew; what hybrid clocks remember is the highest any clock
read so far.
-/

namespace Replica.Skew

open Determinismo

/-- faults.zig:1728-1739 `skew_clamp`. -/
def skewClamp (offset maxNs : Int) (others : List Int) (remembered : Int) : Option Int :=
  let p := others.foldl (fun (lh : Int × Int) o => (max lh.1 (o - maxNs), min lh.2 (o + maxNs)))
    (max (-maxNs) (remembered - maxNs), maxNs)
  if p.1 > p.2 then none else some (max p.1 (min offset p.2))

structure Skew where
  node : Nat
  /-- The drawn offset, clamped at its begin (Applied.skip_ns, forward). -/
  offset : Int
  /-- Applied to the clock now (a strobe's phase). -/
  skewed : Bool
  strobe : Bool
  deriving Repr, Inhabited, BEq

structure KS where
  decisions : Decisions := {}
  now : Int := 0
  /-- The machine's realtime offset (the clock start, skips). -/
  machine : Int := 0
  skews : List Skew := []
  /-- A non-permanent skip under way: its size, signed. -/
  skip : Option Int := none
  /-- clock_high_ns, as monotonic + offset. -/
  clockHigh : Int := 0
  /-- The highest any node's clock read (what hybrid clocks remember). -/
  remembered : Int := 0
  /-- The same without the skews: what the skips alone make the clocks remember. -/
  rememberedSkips : Int := 0
  log : Array String := #[]
  violation : Option String := none
  deriving Inhabited

instance : Chaotic KS where
  decisions s := s.decisions
  setDecisions s d := { s with decisions := d }

abbrev KM := EStateM Stop KS

def maxOff : Int := 4

def clockOf (s : KS) (node : Nat) : Int :=
  s.now + s.machine + (match s.skews.find? (·.node == node) with
    | some k => if k.skewed then k.offset else 0
    | none => 0)

structure KW where
  label : String
  nodes : Nat := 3
  steps : Nat := 6
  skips : Bool := false
  deriving Inhabited

def note (line : String) : KM Unit := modify fun s => { s with log := s.log.push line }

/-- Each step: time goes on a unit, then one fault event. The properties are checked as clocks
read after every step. -/
def run (w : KW) : KM Unit := do
  -- The wall clock start (never back), before any fault.
  let start := 1 + (← below "composer.clock_start" 3)
  modify fun s => { s with machine := s.machine + start }
  for _ in [0:w.steps] do
    modify fun s => { s with now := s.now + 1 }
    let kinds := if w.skips then 5 else 4
    match ← below "world.event" kinds with
    | 0 => -- a skew begins on a node without one
      let node ← below "fault.node" w.nodes
      let s ← get
      if s.skews.any (·.node == node) then pure () else
      let size : Int := Int.ofNat (1 + (← below "fault.clock.skew_ns" 4))
      let forward := (← below "fault.clock.forward" 2) == 0
      let strobe := (← below "fault.clock.strobe" 4) == 0
      let others := s.skews.map (·.offset)
      match skewClamp (if forward then size else -size) maxOff others (s.clockHigh - s.now) with
      | none => note s!"{s.now}: skew on n{node} refused (SkewApart)"
      | some off =>
        modify fun s => { s with skews := s.skews ++ [{ node, offset := off, skewed := true, strobe }] }
        note s!"{s.now}: n{node} skewed {off}{if strobe then " (strobing)" else ""}"
    | 1 => -- a skew ends (clock_leaves when skewed)
      let s ← get
      if s.skews.isEmpty then pure () else
      let k := s.skews[(← below "fault.which" s.skews.length)]!
      let high := if k.skewed then max s.clockHigh (s.now + k.offset) else s.clockHigh
      modify fun s => { s with skews := s.skews.filter (·.node != k.node), clockHigh := high }
      note s!"{s.now}: n{k.node}'s skew ends"
    | 2 => -- a strobe flips (2826-2846)
      let s ← get
      let strobing := s.skews.filter (·.strobe)
      if strobing.isEmpty then pure () else
      let k := strobing[(← below "fault.which" strobing.length)]!
      let fits := k.offset ≥ s.clockHigh - s.now - maxOff
      let high := if k.skewed then max s.clockHigh (s.now + k.offset) else s.clockHigh
      let skewed := !k.skewed && fits
      modify fun s => { s with skews := s.skews.map (fun (x : Skew) => if x.node == k.node then { x with skewed := skewed } else x), clockHigh := high }
      note s!"{s.now}: n{k.node}'s strobe flips {if skewed then "to its skew" else "to 0"}"
    | 3 => pure ()
    | _ => -- a clock skip, or the end of one under way
      let s ← get
      match s.skip with
      | some d =>
        modify fun s => { s with machine := s.machine - d, skip := none }
        note s!"{s.now}: the skip ends: the machine's clock back {d}"
      | none =>
        -- Skips no larger than the maximum: a skip alone never parts clocks past it.
        let size : Int := Int.ofNat (1 + (← below "fault.clock.skip_ns" 4))
        let forward := (← below "fault.clock.forward" 2) == 0
        let permanent := (← below "fault.clock.permanent" 4) == 0
        let d := if forward then size else -size
        modify fun s => { s with machine := s.machine + d, skip := if permanent then none else some d }
        note s!"{s.now}: a clock skip of {d}{if permanent then " (permanent)" else ""}"
    -- Every clock read now: hybrid clocks remember the highest.
    let s ← get
    let readings := (List.range w.nodes).map (clockOf s)
    let high := readings.foldl max s.remembered
    set { s with remembered := high, rememberedSkips := max s.rememberedSkips (s.now + s.machine) }
    let s ← get
    if s.violation.isNone then
      for i in [0:w.nodes] do
        for j in [0:w.nodes] do
          if clockOf s i - clockOf s j > maxOff then
            set { s with violation := some s!"at {s.now}: n{i} reads {clockOf s i}, n{j} {clockOf s j}: {clockOf s i - clockOf s j} apart, the maximum {maxOff}" }
            return
      for i in [0:w.nodes] do
        -- Past the maximum below what the clocks remember, where the skips alone are not.
        let skipsAlone := s.rememberedSkips - (s.now + s.machine)
        if s.remembered - clockOf s i > maxOff && skipsAlone ≤ maxOff then
          set { s with violation := some s!"at {s.now}: n{i} reads {clockOf s i}, {s.remembered - clockOf s i} below the highest any clock read ({s.remembered}), the maximum {maxOff} (the skips alone: {skipsAlone})" }
          return

def skewProp : String × String :=
  ("drawn skews keep every node within its maximum of every other and of what the clocks remember",
   "faults.zig:1700-1709 (skew_clamped: \"a system's maximum clock offset holds between any two nodes ... And within it of the highest any clock has read (clock_high_ns): a hybrid logical clock keeps the latest time it saw\"); docs/ANTITHESIS.md, Per-node clock skew (\"clock_skew_ms_max, 10 s, below a system's documented maximum offset\")")

def judgeK (w : KW) (source : Source) : Ended :=
  match (run w).run { decisions := { source } } with
  | .ok _ s => { taken := s.decisions.taken, violation := s.violation.map (skewProp.1, ·) }
  | .error _ s => { taken := s.decisions.taken, violation := none }

def storyK (w : KW) (source : Source) : List String :=
  match (run w).run { decisions := { source } } with
  | .ok _ s => s.log.toList
  | .error _ _ => []

def searchAll (exhaustRuns seeds : Nat) : IO Unit := do
  say s!"== clock property: {skewProp.1}"
  say s!"   source: {skewProp.2}"
  for w in [({ label := "3 nodes, skews only, 6 steps" } : KW), { label := "2 nodes, skews only, 8 steps", nodes := 2, steps := 8 },
            { label := "2 nodes, skews and clock skips (no larger than the maximum), 6 steps", nodes := 2, skips := true }] do
    if let some f ← exhaustSaid s!"{skewProp.1} / {w.label}" (judgeK w) exhaustRuns then printFound f (storyK w)
    if let some f ← exploreSaid s!"{skewProp.1} / {w.label}" (judgeK w) seeds then printFound f (storyK w)

end Replica.Skew
