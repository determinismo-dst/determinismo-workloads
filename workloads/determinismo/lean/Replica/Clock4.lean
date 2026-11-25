import Replica.Skew

/-!
# A node restarted during its clock skew (guest/runtime/faults.zig, nodes.zig; platform 3939448)

A skew is one node's realtime offset in its time namespace (`clock_offset`, nodes.zig:2504-2510,
written to its main process's `timens_offsets`). A node starts in a namespace of its own
(nodes.zig:385-390, `unshare(CLONE_NEWTIME)`), so one restarted while its skew lasts starts at
offset 0 ("a restarted node's clock starts unskewed, a fresh namespace", faults.zig:1572-1573),
while the fault stays under way in `nodes_faulted` (the condition layer survives the process
layer's faults). Its strobe's next flip on writes the skew to the new namespace again
(2826-2849); its end writes 0 ("A node started again meanwhile has a fresh namespace: this sets
what it has already", 2289-2293). `skew_clamped` (1710-1724) counts every skew under way as the
fault's offset, whatever its node's clock is now; `clock_leaves` raises what the clocks
remember only at a skew's end or a strobe's flip.

The properties (round 3's, now with restarts): every two nodes' clocks stay within the maximum;
no node's clock is more than the maximum below what the clocks remember (what hybrid clocks
keep: a node's own persisted reading too, so a node restarted at 0 after a skew ahead meets the
time it wrote).
-/

namespace Replica.Clock4

open Determinismo
open Replica.Skew

structure CSkew where
  node : Nat
  offset : Int
  skewed : Bool
  strobe : Bool
  deriving Repr, Inhabited, BEq

structure CS where
  decisions : Decisions := {}
  now : Int := 0
  skews : List CSkew := []
  /-- Each node's actual offset (its namespace's), restarts included. -/
  actual : Array Int := #[0, 0, 0]
  clockHigh : Int := 0
  /-- The highest reading any clock made (nodes keep what they read across restarts: a log, a
  hybrid clock persisted). -/
  remembered : Int := 0
  log : Array String := #[]
  violation : Option String := none
  deriving Inhabited

instance : Chaotic CS where
  decisions s := s.decisions
  setDecisions s d := { s with decisions := d }

abbrev KM := EStateM Stop CS

def maxOffset : Int := 4

def kn (line : String) : KM Unit := modify fun s => { s with log := s.log.push line }

def observe : KM Unit := do
  let s ← get
  let readings := s.actual.toList.map (s.now + ·)
  let high := readings.foldl max s.remembered
  modify fun s => { s with remembered := high }
  if s.violation.isSome then return
  for (a, i) in s.actual.toList.zipIdx do
    for (b, j) in s.actual.toList.zipIdx do
      if i < j && (a - b).natAbs > maxOffset.toNat then
        modify fun s => { s with violation := some s!"nodes {i} and {j} at offsets {a} and {b}: {(a - b).natAbs} apart, the maximum {maxOffset}" }
        return
  for (a, i) in s.actual.toList.zipIdx do
    if high - (s.now + a) > maxOffset then
      modify fun s => { s with violation := some s!"node {i} reads {s.now + a}, {high - (s.now + a)} below what the clocks remember ({high}), the maximum {maxOffset}" }
      return

/-- faults.zig:1761-1765 `clock_leaves`. -/
def leaves (offset : Int) : KM Unit := modify fun s => { s with clockHigh := max s.clockHigh (s.now + offset) }

def step (nodes : Nat) : KM Unit := do
  let s ← get
  match (← below "clock.step" 5) with
  | 0 => do
    -- A skew begins on a node with none (skew_begin, skew_clamped).
    let n ← below "clock.node" nodes
    if s.skews.any (·.node == n) then return
    let size := 1 + (← below "clock.size" maxOffset.toNat)
    let forward := (← below "clock.forward" 2) == 1
    let strobe := (← below "clock.strobe" 2) == 1
    let drawn : Int := if forward then size else -size
    let others := (s.skews.filter (·.node != n)).map (·.offset)
    match skewClamp drawn maxOffset others (s.clockHigh - s.now) with
    | none => kn s!"t={s.now}: a skew of node {n} skipped (SkewApart)"
    | some o =>
      modify fun s => { s with skews := s.skews ++ [{ node := n, offset := o, skewed := true, strobe }],
                               actual := s.actual.set! n o }
      kn s!"t={s.now}: node {n} skewed {o}{if strobe then " (strobing)" else ""}"
  | 1 => do
    -- A skew ends (2289-2293): leaves, then 0 in the namespace it has.
    if s.skews.isEmpty then return
    let k ← below "clock.which" s.skews.length
    let sk := s.skews[k]!
    if sk.skewed then leaves sk.offset
    modify fun s => { s with skews := s.skews.eraseIdx k, actual := s.actual.set! sk.node 0 }
    kn s!"t={s.now}: node {sk.node}'s skew ends"
  | 2 => do
    -- A strobe flips (2826-2849): back to its skew only within what the clocks remember.
    let strobing := s.skews.filter (·.strobe)
    if strobing.isEmpty then return
    let sk := strobing[(← below "clock.which" strobing.length)]!
    let fits := sk.offset ≥ s.clockHigh - s.now - maxOffset
    let skewed := !sk.skewed && fits
    if sk.skewed then leaves sk.offset
    modify fun s => { s with skews := s.skews.map (fun x => if x.node == sk.node then { x with skewed } else x),
                             actual := s.actual.set! sk.node (if skewed then sk.offset else 0) }
    kn s!"t={s.now}: node {sk.node}'s strobe flips: {if skewed then s!"at {sk.offset}" else "at 0"}"
  | 3 => do
    -- A node restarts (restart, crash: the process layer): a fresh namespace at 0; its skew's
    -- fault stays under way.
    let n ← below "clock.node" nodes
    modify fun s => { s with actual := s.actual.set! n 0 }
    kn s!"t={s.now}: node {n} restarts: a fresh time namespace, offset 0{if s.skews.any (·.node == n) then " (its skew still under way)" else ""}"
  | _ => modify fun s => { s with now := s.now + 1 }
  observe

def run (nodes steps : Nat) : KM Unit := do
  for _ in [0:steps] do step nodes

def bounds : String := "every two nodes within the maximum, and none more than the maximum below what the clocks remember, restarts during skews included"
def boundsSource : String := "faults.zig:1701-1709 (skew_clamped: \"a system's maximum clock offset holds between any two nodes\"; \"within it of the highest any clock has read\"); faults.zig:1572-1573 (\"a restarted node's clock starts unskewed, a fresh namespace\"); docs/ANTITHESIS.md (per-node clock skew: \"below a system's documented maximum offset\")"

def judgeK (nodes steps : Nat) (src : Source) : Ended :=
  match (run nodes steps).run { decisions := { source := src }, actual := Array.replicate nodes 0 } with
  | .ok _ s => { taken := s.decisions.taken, violation := s.violation.map (bounds, ·) }
  | .error _ s => { taken := s.decisions.taken, violation := none }

def storyK (nodes steps : Nat) (src : Source) : List String :=
  match (run nodes steps).run { decisions := { source := src }, actual := Array.replicate nodes 0 } with
  | .ok _ s => s.log.toList
  | .error _ s => s.log.toList

def searchAll (exhaustRuns seeds : Nat) : IO Unit := do
  say s!"== clock property: {bounds}"
  say s!"   source: {boundsSource}"
  for (nodes, steps) in [(2, 6), (2, 8), (3, 8)] do
    let label := s!"{nodes} nodes, {steps} steps"
    if let some f ← exhaustSaid s!"{bounds} / {label}" (judgeK nodes steps) exhaustRuns then
      printFound f (storyK nodes steps)
    if let some f ← exploreSaid s!"{bounds} / {label}" (judgeK nodes steps) seeds then
      printFound f (storyK nodes steps)

end Replica.Clock4
