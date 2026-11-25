import Jank.R3.Nrepl.ThreadSearch

/-!
# Round 4, nREPL: finishing round 3's World T searches

Round 3 stopped three World T censuses at its 20-minute job bound (T3 ≤1 at 400,000, T7 ≤1 at
1,500,000 and ≤2 at 1,489,000, T9 ≤2 at 853,000). Two tools finish or bound them here:

- `estimate`: Knuth's estimator of a tree's size (a uniformly random root-to-leaf path; the product
  of the branching factors met is an unbiased estimate of the number of leaves), averaged over
  mixed seeds;
- `segment`: a depth-first census that starts at any timeline (a "resume path") and stops at a
  wall-clock deadline, printing the next timeline to start from. Consecutive segments walk the
  tree in the order `Determinismo.nextPath` does, so their union is the complete walk.
-/

namespace Jank.R4.Nrepl.Seg

open Determinismo

/-- The size estimate of one random path: the product of its decisions' option counts. -/
def pathWeight (taken : Array Taken) : Nat :=
  taken.foldl (fun acc t => acc * max 1 t.options) 1

/-- Knuth's estimate averaged over `probes` paths drawn with mixed seeds `first..first+probes-1`:
(mean, min, max) of the per-path products. -/
def estimate (run : Source → Ended) (probes : Nat) (first : Nat := 0) : Nat × Nat × Nat := Id.run do
  let mut total := 0
  let mut lo := 0
  let mut hi := 0
  for i in [0:probes] do
    let o := run { gen := mkStdGen (Determinismo.mixSeed (first + i)) }
    let w := pathWeight o.taken
    total := total + w
    lo := if i == 0 then w else min lo w
    hi := max hi w
  return (if probes == 0 then 0 else total / probes, lo, hi)

/-- A segment's outcome. -/
structure SegOut where
  runs : Nat := 0
  /-- Every timeline from the start path to the end of the tree was run. -/
  complete : Bool := false
  /-- Where the next segment starts (when not complete). -/
  next : Option (Array Nat) := none
  counts : List (String × Nat) := []
  examples : List (String × String) := []
  tapes : List (String × Array Nat) := []
  deriving Inhabited

end Jank.R4.Nrepl.Seg
