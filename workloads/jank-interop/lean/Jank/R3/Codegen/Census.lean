import Determinismo

/-!
# Search helpers this area needed (sdk/lean left as is)

- `mixSeed`: a SplitMix64 finalizer over the seed index (consecutive small `mkStdGen` seeds give
  the same first draws);
- `census`: every timeline of an exhaustive walk (or a range of seeds), violations counted per
  class (the bracketed part of the property name) with the first timeline of each class, instead
  of stopping at the first counterexample;
- `exhaustFrom`: the exhaustive walk restricted to the timelines whose first decisions are a given
  prefix, so a large walk runs as partitions that each complete.
-/

namespace Jank.R3.Codegen

open Determinismo

def mixSeed (i : Nat) : Nat :=
  let z : UInt64 := (UInt64.ofNat i) * 0x9E3779B97F4A7C15
  let z := (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31)).toNat % 2147483562

/-- The class a property name carries in brackets. -/
def bracketClass (property : String) : String :=
  String.ofList (((property.splitOn "[").getLast?.getD "").toList.takeWhile (· != ']'))

structure ClassHit where
  cls : String
  count : Nat
  first : Counterexample

structure Census where
  runs : Nat
  /-- The walk reached its end (every timeline within the bounds). -/
  complete : Bool
  violating : Nat
  classes : List ClassHit

def Census.add (c : Census) (cls : String) (cx : Counterexample) : Census :=
  match c.classes.find? (·.cls == cls) with
  | some _ => { c with classes := c.classes.map fun h => if h.cls == cls then { h with count := h.count + 1 } else h }
  | none => { c with classes := c.classes ++ [{ cls, count := 1, first := cx }] }

/-- Seeds `first .. first+count-1` (mixed, or as `Source.seeded`, round 2's seeds). -/
def censusSeeds (run : Source → Ended) (count : Nat) (first : Nat := 0) (mixed : Bool := true) : Census := Id.run do
  let mut c : Census := { runs := 0, complete := true, violating := 0, classes := [] }
  for i in [0:count] do
    let o := run (if mixed then { gen := mkStdGen (mixSeed (first + i)) } else Source.seeded (first + i))
    c := { c with runs := c.runs + 1 }
    if let some (p, dd) := o.violation then
      c := { c with violating := c.violating + 1 }
      c := c.add (bracketClass p) { taken := o.taken, property := p, detail := dd, runs := i + 1 }
  return c

/-- The path after `taken` within the timelines starting with `prefix` (`none`: the partition is
done). -/
def nextPathWithin (pre : Array Nat) (taken : Array Taken) : Option (Array Nat) := Id.run do
  let mut i := taken.size
  while i > pre.size do
    i := i - 1
    let t := taken[i]!
    if t.value + 1 < t.options then
      return some ((taken.extract 0 i).map (·.value) |>.push (t.value + 1))
  return none

/-- Every timeline starting with `pre`, depth first, up to `maxRuns`, counted per class. -/
def censusFrom (run : Source → Ended) (pre : Array Nat) (maxRuns : Nat) : Census := Id.run do
  let mut c : Census := { runs := 0, complete := false, violating := 0, classes := [] }
  let mut path := pre
  for i in [0:maxRuns] do
    let o := run (Source.path path)
    c := { c with runs := c.runs + 1 }
    if let some (p, dd) := o.violation then
      c := { c with violating := c.violating + 1 }
      c := c.add (bracketClass p) { taken := o.taken, property := p, detail := dd, runs := i + 1 }
    -- a timeline shorter than the prefix (the prefix's last values were out of range) ends it
    if o.taken.size < pre.size then return { c with complete := true }
    match nextPathWithin pre o.taken with
    | none => return { c with complete := true }
    | some p => path := p
  return c

/-- The whole walk as partitions over the first decision's options: each partition must complete
within `maxRuns` for the walk to be complete. -/
def censusPartitioned (run : Source → Ended) (maxRuns : Nat) : Census := Id.run do
  let first := run (Source.path #[])
  let k := match first.taken[0]? with | some t => t.options | none => 1
  let mut total : Census := { runs := 0, complete := true, violating := 0, classes := [] }
  for v in [0:k] do
    let c := censusFrom run #[v] maxRuns
    total := { total with runs := total.runs + c.runs, complete := total.complete && c.complete,
                          violating := total.violating + c.violating }
    for h in c.classes do
      match total.classes.find? (·.cls == h.cls) with
      | some _ => total := { total with classes := total.classes.map fun g => if g.cls == h.cls then { g with count := g.count + h.count } else g }
      | none => total := { total with classes := total.classes ++ [h] }
  return total

end Jank.R3.Codegen
