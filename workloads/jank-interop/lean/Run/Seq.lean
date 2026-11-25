import Jank.Seq.IntRange
import Jank.Seq.Range
import Jank.Seq.Heap
import Jank.Seq.Transducers
import Jank.Seq.Core
import Jank.Seq.Chunked

open Determinismo

namespace Run.Seq

def describe (c : Counterexample) : String :=
  s!"{c.property} after {c.runs} timelines, {c.taken.size} decisions: {c.detail}"

def indent (s : String) : String := (s.splitOn "\n").map ("    " ++ ·) |> "\n".intercalate

def report (name : String) (run : Source → Ended) (seeds : Nat) (maxRuns : Nat) : IO Unit := do
  IO.println s!"== {name}"
  match explore run seeds with
  | some c =>
    IO.println s!"  explore ({seeds} seeds): {describe c}"
    let s := shrink run c
    IO.println s!"  shrunk to {s.taken.size} decisions: {s.detail}"
    IO.println s!"  tape:\n{indent (tape s.taken)}"
  | none => IO.println s!"  explore ({seeds} seeds): nothing"
  match exhaust run maxRuns with
  | .found c =>
    IO.println s!"  exhaust: found after {c.runs} timelines: {c.detail}"
    let s := shrink run c
    if s.taken.size > 0 then
      IO.println s!"  exhaust's counterexample shrunk to {s.taken.size} decisions: {s.detail}\n  tape:\n{indent (tape s.taken)}"
  | .complete n => IO.println s!"  exhaust: complete, {n} timelines, nothing"
  | .stopped n => IO.println s!"  exhaust: stopped at {n} timelines, nothing"

section
open Jank.Seq.IntRange
def intRange : IO Unit := do
  report "integer_range: (range ...) over longs agrees with Clojure" run 3000 200000
  report "integer_range with an exact count() (the fix)" runFixed 3000 200000
  let qs := allQuestions
  let bad := qs.filterMap (·.verdict)
  IO.println s!"  table: {bad.length} of {qs.length} questions deviate"
  let throws := qs.filter fun q => match (walk fuel q.jank).ending with | .throws _ => true | _ => false
  let wrong := qs.filter fun q =>
    let (s, e, st) := q.clj
    let jw := walk fuel q.jank
    let cw := cljWalk s e st fuel
    jw.ending != .throws "integer_range overflow occurred in arithmetic." && jw != cw
  IO.println s!"    walk throws: {throws.length}; walk ends early or differs without a throw: {wrong.length}"
  for d in (bad.take 6) do IO.println s!"    {d}"
  for q in wrong.take 6 do
    IO.println s!"    {q.verdict.getD ""}"
  let ub := qs.filter fun q => match q.jank with | .range r => !(ubNotes r).isEmpty | _ => false
  IO.println s!"    ranges whose count() has a signed overflow (UB in ISO C++): {ub.length}"
  let fixedBad := qs.filter (!·.fixedAgrees)
  IO.println s!"  with an exact count() (the fix): {fixedBad.length} of {qs.length} deviate"
end

section
open Jank.Seq.Range
def range : IO Unit := do
  report "range (a real end): elements agree with Clojure (first 80)" run 3000 100000
  report "range with addP in place of add (the fix)" runFixed 3000 100000
  let qs := allQuestions
  let bad := qs.filterMap (·.verdict 80)
  IO.println s!"  table: {bad.length} of {qs.length} questions deviate"
  for d in bad.take 4 do IO.println s!"    {d}"
  let fixedBad := qs.filter fun q => walkFixed 80 q != cljWalk 80 q.start q.step q.e
  IO.println s!"  with addP in place of add (the fix): {fixedBad.length} of {qs.length} deviate"
end

section
open Jank.Seq.Heap
def heap : IO Unit := do
  report "doseq over a held sequence changes no value" run 3000 100000
  report "doseq stepping by next (the fix)" runFixed 3000 100000
  let ps := allPrograms
  let bad := ps.filterMap (·.verdict)
  IO.println s!"  table: {bad.length} of {ps.length} programs deviate"
  for d in bad.take 8 do IO.println s!"    {d}"
  let fixedBad := ps.filter fun p => match p.jank (fixed := true) with
    | .ok j => !(j == p.clj)
    | .error _ => true
  IO.println s!"  with doseq stepping by next instead of next-in-place (the fix): {fixedBad.length} of {ps.length} deviate"
end

section
open Jank.Seq.Transducers
def transducers : IO Unit := do
  report "transducers: transduce agrees with Clojure" run 5000 300000
  -- Every pipeline of one or two transducers over inputs of length ≤ 3 (values 0..2), each rf.
  let mut total := 0
  let mut bad : Array String := #[]
  let colls : List (List Int) := [[]] ++ ([0, 1, 2].map fun a => [a]) ++
    ([0, 1, 2].flatMap fun a => [0, 1, 2].map fun b => [a, b]) ++
    ([0, 1, 2].flatMap fun a => [0, 1, 2].flatMap fun b => [0, 1, 2].map fun c => [a, b, c])
  let pipes := (xforms.map fun x => [x]) ++ (xforms.flatMap fun x => xforms.map fun y => [x, y])
  for xfs in pipes do
    for coll in colls do
      for stop in [none, some 1, some 2] do
        total := total + 1
        if let some d := ({ xfs, coll, stop } : Question).verdict then bad := bad.push d
  IO.println s!"  table: {bad.size} of {total} (pipeline, input, rf) deviate"
  for d in bad.toList.take 5 do IO.println s!"    {d}"
end

section
open Jank.Seq.Core
def core : IO Unit := do
  report "seq.cpp dispatch (empty, coll?, get-in, find) and byte arrays agree with Clojure" run 3000 100000
  let qs := allQuestions
  let bad := qs.filterMap (·.verdict)
  IO.println s!"  table: {bad.length} of {qs.length} questions deviate"
  for d in bad do IO.println s!"    {d}"
end

section
open Jank.Seq.Chunked
def chunked : IO Unit := do
  report "chunked seqs: (first (map f src)) maps one chunk" run 200 1000
  let mut n := 0
  for total in totals do
    for depth in [1, 2] do
      let c := program .clj total depth
      let j := program .jank total depth
      let sh := fun (r : Except String (Option Int × Nat)) => match r with
        | .ok (v, k) => s!"{v.getD 0}, f called {k} times"
        | .error e => e
      if verdict total depth |>.isSome then n := n + 1
      IO.println s!"    {code total depth}: Clojure {sh c}; jank {sh j}"
  IO.println s!"  table: {n} of {totals.length * 2} programs deviate"
end

def main (args : List String) : IO UInt32 := do
  let only := args.head?
  if only.isNone || only == some "intrange" then intRange
  if only.isNone || only == some "range" then range
  if only.isNone || only == some "heap" then heap
  if only.isNone || only == some "transducers" then transducers
  if only.isNone || only == some "core" then core
  if only.isNone || only == some "chunked" then chunked
  return 0

end Run.Seq

def main (args : List String) : IO UInt32 := Run.Seq.main args
