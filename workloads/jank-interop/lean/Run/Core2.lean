import Determinismo
import Jank.Core.Sorted
import Jank.Core.Destructure
import Jank.Core.NsExtra
import Jank.Core.PrintInf

/-! Round 2, core (second part), replicating jank 7135b7708: sorted collections, `sort` of an empty collection, destructuring
and `defn`, printing and namespace items not covered by fork B/C. -/

open Determinismo

def describe (c : Counterexample) : String :=
  s!"{c.property} after {c.runs} timelines, {c.taken.size} decisions: {c.detail}"

def indent (s : String) : String := (s.splitOn "\n").map ("    " ++ ·) |> "\n".intercalate

def report (name : String) (run : Source → Ended) (seeds : Nat) (maxRuns : Nat) : IO Unit := do
  IO.println s!"== {name}"
  if seeds > 0 then
   match explore run seeds with
   | some c =>
    IO.println s!"  explore ({seeds} seeds): {describe c}"
    let s := shrink run c
    IO.println s!"  shrunk to {s.taken.size} decisions: {s.detail}"
    IO.println s!"  tape:\n{indent (tape s.taken)}"
   | none => IO.println s!"  explore ({seeds} seeds): nothing"
  if maxRuns > 0 then
   match exhaust run maxRuns with
   | .found c =>
    IO.println s!"  exhaust: found after {c.runs} timelines: {c.detail}"
    let s := shrink run c
    IO.println s!"  exhaust's counterexample shrunk to {s.taken.size} decisions: {s.detail}"
    IO.println s!"  tape:\n{indent (tape s.taken)}"
   | .complete n => IO.println s!"  exhaust: complete, {n} timelines, nothing"
   | .stopped n => IO.println s!"  exhaust: stopped at {n} timelines, nothing"

/-- Every timeline of a bounded world, counting the violations by their first word group. -/
def census (run : Source → Ended) (maxRuns : Nat) : Nat × Nat × List String := Id.run do
  let mut path : Array Nat := #[]
  let mut runs := 0
  let mut bad := 0
  let mut firsts : List String := []
  for _ in List.range maxRuns do
    let o := run (Source.path path)
    runs := runs + 1
    if let some (_, d) := o.violation then
      bad := bad + 1
      if firsts.length < 6 then firsts := firsts ++ [d]
    match nextPath o.taken with
    | none => return (runs, bad, firsts)
    | some p => path := p
  return (runs, bad, firsts)

section
open Jank.Core.Sorted
def sorted : IO Unit := do
  report "sorted map: one operation on (sorted-map …) of 0–2 entries" (runBody mapBody) 3000 2000000
  let (runs, bad, firsts) := census (runBody mapBody) 3000000
  IO.println s!"  census: {bad} of {runs} map programs disagree; first ones:"
  for d in firsts do IO.println s!"    {d}"
  report "sorted map without = / find / select-keys (C17, C18 set aside)" (runBody (mapBody [.equal, .find, .selectKeys])) 3000 3000000
  report "sorted set: one operation on (sorted-set …) of 0–2 elements" (runBody setBody) 3000 2000000
  let (runs, bad, firsts) := census (runBody setBody) 3000000
  IO.println s!"  census: {bad} of {runs} set programs disagree; first ones:"
  for d in firsts do IO.println s!"    {d}"
  report "sorted set without = (C17 set aside)" (runBody (setBody [.equal])) 3000 3000000
  let t := mapTable numberKeys
  IO.println s!"== sorted map, numeric keys only (0, 1, 1.0, 2), every program: {t.length} disagree"
  for (code, c, j) in t.take 8 do IO.println s!"    {code}: Clojure {c.code}, jank {j.code}"
  let ops := ["get", "find", "contains?", "dissoc", "assoc", "count", "seq", "conj", "select-keys"]
  for op in ops do
    let n := (t.filter fun (code, _, _) => code.startsWith s!"({op} ").length
    IO.println s!"    {op}: {n}"
  let st := setEqualTable
  IO.println s!"== (= (sorted-set a) (sorted-set b)) over {keyAtoms.length}² pairs: {st.length} disagree"
  for (code, c, j) in st.take 6 do IO.println s!"    {code}: Clojure {c.code}, jank {j.code}"
  let mt := mapEqualTable
  IO.println s!"== (= (sorted-map a :x) (sorted-map b :x)) over {keyAtoms.length}² pairs: {mt.length} disagree"
  for (code, c, j) in mt.take 6 do IO.println s!"    {code}: Clojure {c.code}, jank {j.code}"
  IO.println "== sort of an empty collection (7135b7708: core/seq.cpp 1098/1108; f3d82d654: 1091 and native_vector_sequence.cpp first/next)"
  for (version, sortFn) in [("7135b7708", jankSort), ("f3d82d654", jankSortOld)] do
   for (label, coll) in [("(sort nil)", (none : Option (List Jank.Compare.CV))), ("(sort [])", some [])] do
    let r := sortFn coll
    let first := match jankFirstOfSort r with
      | .ok v => v.code | .throws w => s!"throws {w}" | .ub w => s!"undefined behavior: {w}"
    let next := match jankNextOfSort r with
      | none => "nil"
      | some s => s!"a non-nil seq (index {s.index}, count {nvsCount s})"
    let last := match jankLastOfSort r 100000 with
      | some (.ok v) => v.code
      | some (.throws w) => s!"throws {w}"
      | some (.ub w) => s!"undefined behavior: {w}"
      | none => "does not end in 100000 turns (the index grows past the size)"
    IO.println s!"    [{version}] (first {label}): Clojure {(cljSort coll).head?.map (·.code) |>.getD "nil"}, jank {first}"
    IO.println s!"    [{version}] (next {label}): Clojure nil, jank {next}"
    IO.println s!"    [{version}] (last {label}): Clojure nil, jank {last}"
  let (j, c) := resetMetaProgram
  IO.println "== (reset-meta! (sorted-map) {:x 1}) then [(meta (sorted-map)) (meta (into (sorted-map) {1 2}))]"
  IO.println s!"    Clojure {c}; jank {j}"
  IO.println "== unported sorted-collection functions"
  for (f, at_, ex) in unported do IO.println s!"    {f} ({at_}): throws in jank; {ex}"
end

section
open Jank.Core.Destructure
def destructuring : IO Unit := do
  report "destructuring: (let [form value] …), forms nested twice, values nested twice (explore); once and once (exhaust)" (runBody (bindBody 2 2)) 3000 0
  report "destructuring: forms and values nested once" (runBody (bindBody 1 1)) 0 3000000
  let (runs, bad, firsts) := census (runBody (bindBody 1 1)) 3000000
  IO.println s!"  census: {bad} of {runs} binding programs disagree; first ones:"
  for d in firsts do IO.println s!"    {d}"
  report "destructuring, no trailing (seq m) in keyword arguments (C20 set aside), nested once" (runBody (bindBody 1 1 false)) 3000 3000000
  let t := kwargsTable
  IO.println s!"== ((fn [& \{:as m}] m) args…) over every argument list of length ≤ 3 from 6 values: {t.length} disagree"
  let shw := fun (r : Except String Val) => match r with | .ok v => v.code | .error e => s!"throws ({e})"
  for (args, c, j) in t.take 8 do
    IO.println s!"    (f {" ".intercalate (args.map Val.code)}): Clojure {shw c}, jank {shw j}"
  IO.println "== defn: (defn countdown [n] (if (pos? n) (countdown (dec n)) :done)) (def orig countdown) (defn countdown [n] :redefined) (orig 3)"
  let shv := fun (r : Except String V) => match r with | .ok v => v.code | .error e => s!"throws ({e})"
  IO.println s!"    Clojure {shv (redefProgram .clj)}, jank {shv (redefProgram .jank)}"
end

section
open Jank.Core.NsExtra
def namespaces : IO Unit := do
  report "namespaces: 3 operations (def, ns reload, alias, find-var, ns-resolve, resolve, in-ns)" (runBody 3) 3000 1000000
  let t := table 3
  IO.println s!"== every program of 3 operations ({ops.length ^ 3}): first disagreement, by operation"
  for (op, n, ex) in t do IO.println s!"    {op}: {n} programs; e.g. {ex}"
end

section
open Jank.Core.PrintInf
def printing : IO Unit := do
  let t := table
  IO.println s!"== printing ##Inf/##-Inf/##NaN: {t.length} of {fns.length * values.length} (function, value) pairs differ"
  for (code, c, j) in t do IO.println s!"    {code}: Clojure {repr c}, jank {repr j}"
end

def main : IO UInt32 := do
  let t0 ← IO.monoMsNow
  sorted
  destructuring
  namespaces
  printing
  let t1 ← IO.monoMsNow
  IO.println s!"== total run time: {(t1 - t0) / 1000} s"
  return 0
