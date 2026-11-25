import Determinismo

/-!
# Search helpers for this area (sdk/lean untouched)

- `census`: every timeline within the bounds (as `exhaust`), not stopping at a violation;
  violations counted per property class, with the first example of each (its decisions).
- `exploreMixed`: `explore` over SplitMix64-mixed seeds.
- `report`: explore, then exhaust (or census), shrinking what is found, printed as lines that the
  driver writes to results/r3-immer.txt.
-/

namespace Jank.R3.Immer.Kit

open Determinismo

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

structure Census where
  runs : Nat
  complete : Bool
  /-- class, count, first detail, first decisions -/
  classes : List (String × Nat × String × Array Nat) := []

/-- The path after `taken` that keeps its first `pfx` decisions: none when the partition is done. -/
def nextPathUnder (taken : Array Taken) (pfx : Nat) : Option (Array Nat) := Id.run do
  let mut i := taken.size
  while i > pfx do
    i := i - 1
    let t := taken[i]!
    if t.value + 1 < t.options then
      return some ((taken.extract 0 i).map (·.value) |>.push (t.value + 1))
  return none

/-- A census segment: from `path0` on (in the exhaust order), keeping the first `pfx` decisions,
at most `maxRuns` timelines, counts added to `classes0`; the path to resume from when stopped. -/
def censusFrom (run : Source → Ended) (maxRuns : Nat) (path0 : Array Nat) (pfx : Nat)
    (classes0 : List (String × Nat × String × Array Nat)) : Census × Option (Array Nat) := Id.run do
  let mut path : Array Nat := path0
  let mut classes := classes0
  for i in [0:maxRuns] do
    let o := run (Source.path path)
    if let some (p, d) := o.violation then
      classes := match classes.find? (·.1 == p) with
        | some (_, n, d0, t0) => (p, n + 1, d0, t0) :: classes.filter (·.1 != p)
        | none => (p, 1, d, o.taken.map (·.value)) :: classes
    if o.taken.size < pfx then return ({ runs := i + 1, complete := true, classes }, none)
    match nextPathUnder o.taken pfx with
    | none => return ({ runs := i + 1, complete := true, classes }, none)
    | some q => path := q
  return ({ runs := maxRuns, complete := false, classes }, some path)

/-- Every timeline whose decisions start with `start` (the whole world when `start` is empty). -/
def census (run : Source → Ended) (maxRuns : Nat) (start : Array Nat := #[]) : Census :=
  (censusFrom run maxRuns start start.size []).1

def describe (c : Counterexample) : String :=
  s!"[{c.property}] after {c.runs} timelines, {c.taken.size} decisions: {c.detail}"

def indent (s : String) : String := (s.splitOn "\n").map ("      " ++ ·) |> "\n".intercalate

/-- Explore, then exhaust; each counterexample shrunk. Returns the printed lines. -/
def flushOut : IO Unit := do (← IO.getStdout).flush

def report (name : String) (run : Source → Ended) (seeds : Nat) (maxRuns : Nat) (showTape : Bool := false) : IO Unit := do
  let t0 ← IO.monoMsNow
  IO.println s!"== {name}"
  match exploreMixed run seeds with
  | some c =>
    IO.println s!"  explore ({seeds} seeds): found {describe c}"
    let s := shrink run c
    IO.println s!"    shrunk to {s.taken.size} decisions: {s.detail}"
    if showTape then IO.println s!"    tape:\n{indent (tape s.taken)}"
  | none => IO.println s!"  explore ({seeds} seeds): nothing"
  if maxRuns > 0 then
    match exhaust run maxRuns with
    | .found c =>
      IO.println s!"  exhaust: found {describe c}"
      let s := shrink run c
      IO.println s!"    shrunk to {s.taken.size} decisions: {s.detail}"
    | .complete n => IO.println s!"  exhaust: complete, {n} timelines, nothing"
    | .stopped n => IO.println s!"  exhaust: stopped at {n} timelines, nothing"
  IO.println s!"  ({((← IO.monoMsNow) - t0) / 1000} s)"
  flushOut

def dotted (p : Array Nat) : String := ".".intercalate (p.toList.map toString)

def classSummary (classes : List (String × Nat × String × Array Nat)) : String :=
  if classes.isEmpty then "no violations" else
  ", ".intercalate (classes.reverse.map fun (p, n, _, _) => s!"[{p}] {n}")

/-- A census, printed per class, in segments of `chunk` timelines with a checkpoint line after
each; past `budgetMs` it stops and prints the path to resume from (`ID>path` in the driver), so
no single job runs long and a search is completed across jobs. `start` is a partition (its
decisions are kept); `resume` a path to continue from. -/
def reportCensus (name : String) (run : Source → Ended) (maxRuns : Nat) (start : Array Nat := #[])
    (resume : Option (Array Nat) := none) (budgetMs : Nat := 1080000) (chunk : Nat := 250000) : IO Census := do
  let t0 ← IO.monoMsNow
  let part := if start.isEmpty then "" else s!" [partition: first decisions {start}]"
  let res := match resume with | some r => s!" [resumed from {dotted r}]" | none => ""
  IO.println s!"== {name}{part}{res}"
  flushOut
  let mut path := resume.getD start
  let mut classes : List (String × Nat × String × Array Nat) := []
  let mut runs := 0
  let mut complete := false
  let mut next : Option (Array Nat) := none
  while runs < maxRuns && !complete && next.isNone do
    let (c, nx) := censusFrom run (min chunk (maxRuns - runs)) path start.size classes
    runs := runs + c.runs
    classes := c.classes
    match nx with
    | none => complete := true
    | some q =>
      path := q
      let el := (← IO.monoMsNow) - t0
      IO.println s!"  checkpoint: {runs} timelines, {el / 1000} s, {classSummary classes}"
      flushOut
      if el ≥ budgetMs then next := some q
  let status :=
    if complete then s!"complete, {runs} timelines"
    else if next.isSome then s!"stopped at {runs} timelines (time budget; resumed in the next job)"
    else s!"stopped at {runs} timelines"
  if classes.isEmpty then IO.println s!"  census: {status}, nothing"
  else
    IO.println s!"  census: {status}; violations per class:"
    for (p, n, d, t) in classes.reverse do
      let s := shrink run { taken := (run (Source.path t)).taken, property := p, detail := d, runs := 0 }
      IO.println s!"    [{p}] {n} timelines; shrunk ({s.taken.size} decisions): {s.detail}"
  if let some q := next then IO.println s!"  resume: {dotted q}"
  IO.println s!"  ({((← IO.monoMsNow) - t0) / 1000} s)"
  flushOut
  pure { runs, complete, classes }

end Jank.R3.Immer.Kit
