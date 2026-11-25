import Determinismo

/-!
# Round 3, search widening: the search library this area needs (sdk/lean untouched)

What `Determinismo.Search` lacks for residual searches over big worlds, built here:

- `exhaustUnder`: `exhaust` restricted to the timelines whose decisions start with a given
  prefix, so one world is searched in partitions (by the first decisions' values) that each end
  with `complete` or `found`; the union of a partition family is the whole world.
- `censusUnder`: every timeline of a partition, not stopping at a violation; violations counted per
  class (the property name), with the first example of each class and its decisions.
- `estimate`: Knuth's estimator of a world's number of timelines (the product of option counts
  along uniformly drawn paths, averaged), to size a world before choosing its bounds.
- `exploreMixed`: `explore` over SplitMix64-mixed seeds (consecutive `mkStdGen` seeds draw
  correlated first decisions).
- `prefixes`: the partition family of a world at a given number of leading decisions.
-/

namespace Jank.R3.Search

open Determinismo

/-- SplitMix64's finalizer (as round 2's interop search). -/
def mixSeed (i : Nat) : Nat :=
  let z : UInt64 := (UInt64.ofNat i) * 0x9E3779B97F4A7C15
  let z := (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31)).toNat % 2147483562

def exploreMixed (run : Source → Ended) (count : Nat) (first : Nat := 0) : Option Counterexample := Id.run do
  for i in [0:count] do
    let o := run { gen := mkStdGen (mixSeed (first + i)) }
    if let some (property, detail) := o.violation then
      return some { taken := o.taken, property, detail, runs := i + 1 }
  return none

/-- The path after `taken` that stays under `prefix`: none when every timeline under it is done. -/
def nextPathUnder (taken : Array Taken) (pfx : Nat) : Option (Array Nat) := Id.run do
  let mut i := taken.size
  while i > pfx do
    i := i - 1
    let t := taken[i]!
    if t.value + 1 < t.options then
      return some ((taken.extract 0 i).map (·.value) |>.push (t.value + 1))
  return none

/-- `exhaust` over the timelines that start with `prefix` (a partition of the world). The prefix
must be a valid path: each value below its decision's option count. -/
def exhaustUnder (run : Source → Ended) (prefix_ : Array Nat) (maxRuns : Nat) : Exhausted := Id.run do
  let mut path := prefix_
  for i in [0:maxRuns] do
    let o := run (Source.path path)
    if let some (property, detail) := o.violation then
      return .found { taken := o.taken, property, detail, runs := i + 1 }
    -- A timeline shorter than the prefix ends the partition (the prefix named a decision that
    -- this timeline does not take).
    if o.taken.size < prefix_.size then return .complete (i + 1)
    match nextPathUnder o.taken prefix_.size with
    | none => return .complete (i + 1)
    | some p => path := p
  return .stopped maxRuns

/-- One class of violations seen by a census: how many timelines, the first one's detail and
decisions. -/
structure ClassCount where
  property : String
  count : Nat
  firstDetail : String
  firstTaken : Array Taken
  /-- More examples, kept for the classes named `unexplained…` (up to 12). -/
  more : Array String := #[]

/-- A census of a partition: every timeline, violations counted per property. -/
structure Census where
  runs : Nat := 0
  complete : Bool := false
  classes : Array ClassCount := #[]

def Census.violations (c : Census) : Nat := c.classes.foldl (· + ·.count) 0

def censusUnder (run : Source → Ended) (prefix_ : Array Nat) (maxRuns : Nat) : Census := Id.run do
  let mut path := prefix_
  let mut c : Census := {}
  for _ in [0:maxRuns] do
    let o := run (Source.path path)
    c := { c with runs := c.runs + 1 }
    if let some (p, d) := o.violation then
      match c.classes.findIdx? (·.property == p) with
      | some k => c := { c with classes := c.classes.modify k fun cc =>
          { cc with count := cc.count + 1,
                    more := if p.startsWith "unexplained" && cc.more.size < 12 then cc.more.push d else cc.more } }
      | none => c := { c with classes := c.classes.push { property := p, count := 1, firstDetail := d, firstTaken := o.taken } }
    if o.taken.size < prefix_.size then return { c with complete := true }
    match nextPathUnder o.taken prefix_.size with
    | none => return { c with complete := true }
    | some p => path := p
  return c

/-- Knuth's estimate of the number of timelines: for each of `samples` uniformly drawn timelines,
the product of the option counts of its decisions; their mean. Exact for a tree whose
subtrees at each decision are alike; unbiased for uniform draws in general. Also the mean number
of decisions. -/
def estimate (run : Source → Ended) (samples : Nat) (first : Nat := 0) : Float × Float := Id.run do
  let mut total : Float := 0
  let mut decs : Float := 0
  for i in [0:samples] do
    let o := run { gen := mkStdGen (mixSeed (first + 7919 * i + 1)) }
    let prod := o.taken.foldl (fun acc t => acc * t.options.toFloat) 1.0
    total := total + prod
    decs := decs + o.taken.size.toFloat
  return (total / samples.toFloat, decs / samples.toFloat)

/-- The partitions of a world at its first `k` decisions: every valid prefix of length `k` (or
a shorter complete timeline's own path), in exhaust order. -/
def prefixes (run : Source → Ended) (k : Nat) (maxRuns : Nat := 1000000) : Array (Array Nat) := Id.run do
  -- Walk the tree restricted to the first k decisions.
  let mut out : Array (Array Nat) := #[]
  let mut path : Array Nat := #[]
  for _ in [0:maxRuns] do
    let o := run (Source.path path)
    let cut := o.taken.extract 0 k
    out := out.push (cut.map (·.value))
    match nextPath cut with
    | none => return out
    | some p => path := p
  return out

def describe (c : Counterexample) : String :=
  s!"{c.property} after {c.runs} timelines, {c.taken.size} decisions: {c.detail}"

def indent (s : String) : String := (s.splitOn "\n").map ("    " ++ ·) |> "\n".intercalate

def fmtFloat (f : Float) : String :=
  if f < 1e6 then toString (f.round.toUInt64.toNat)
  else
    let e := (Float.log10 f).floor
    let m := f / (Float.pow 10 e)
    s!"{(m * 100).round / 100}e{e.toUInt64.toNat}"

/-- explore (mixed seeds), shrink; exhaust (under a prefix), shrink. -/
def report (name : String) (run : Source → Ended) (seeds : Nat) (maxRuns : Nat)
    (prefix_ : Array Nat := #[]) : IO Exhausted := do
  let t0 ← IO.monoMsNow
  IO.println s!"== {name}"
  if seeds > 0 then
    match exploreMixed run seeds with
    | some c =>
      IO.println s!"  explore ({seeds} mixed seeds): {describe c}"
      let s := shrink run c
      IO.println s!"  shrunk to {s.taken.size} decisions: {s.detail}"
      IO.println s!"  tape:\n{indent (tape s.taken)}"
    | none => IO.println s!"  explore ({seeds} mixed seeds): nothing"
  let mut res : Exhausted := .stopped 0
  if maxRuns > 0 then
    res := exhaustUnder run prefix_ maxRuns
    let under := if prefix_.isEmpty then "" else s!" under prefix {prefix_.toList}"
    match res with
    | .found c =>
      IO.println s!"  exhaust{under}: found after {c.runs} timelines: {c.detail}"
      let s := shrink run c
      IO.println s!"  shrunk to {s.taken.size} decisions: {s.detail}"
      IO.println s!"  tape:\n{indent (tape s.taken)}"
    | .complete n => IO.println s!"  exhaust{under}: complete, {n} timelines, nothing"
    | .stopped n => IO.println s!"  exhaust{under}: stopped at {n} timelines, nothing"
  let t1 ← IO.monoMsNow
  IO.println s!"  ({(t1 - t0) / 1000} s)"
  return res

def printCensus (name : String) (c : Census) : IO Unit := do
  IO.println s!"== census {name}: {c.runs} timelines{if c.complete then " (complete)" else " (stopped)"}, {c.violations} violate"
  for cc in c.classes do
    IO.println s!"   {cc.property}: {cc.count}; first: {cc.firstDetail}"
    for m in cc.more do IO.println s!"      also: {m}"

end Jank.R3.Search
