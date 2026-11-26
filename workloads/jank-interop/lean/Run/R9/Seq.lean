import Jank.R9.Seq.SortSearch
import Jank.R9.Seq.Lazy
import Jank.R9.Seq.PartitionAll
import Jank.R9.Seq.SortedNaN
import Jank.R9.Seq.LazyState
import Jank.R9.Seq.SortProof

/-! Round 9, area Seq (`jank9-seq`): sorting (jank's std::stable_sort against Clojure's TimSort).

Usage:
  jank9-seq sort            complete searches of every comparator family (lengths and counts)
  jank9-seq predict         the tests' sort programs: Clojure's and jank's results
  jank9-seq pa              the partition-all transducer, complete over small n, inputs, stops
  jank9-seq preorders N     every total preorder on 1..N elements: jank's sort against Clojure's
  jank9-seq preorders-random COUNT SEED   random total preorders of length 2..31
  jank9-seq cases FILE      write the sort validation cases (g++-15 and Clojure check them)
  jank9-seq lazy FILE       write the realization-count cases (Clojure checks its column)
-/

open Jank.R9.Seq.Sort Jank.R9.Seq.SortSearch

/-- Validation cases of the realization models: `kind args | jank | Clojure`. -/
def lazyCases : List String := Id.run do
  let mut out := []
  for n in [1, 2, 5, 31, 32, 33, 40, 64, 65, 100] do
    for k in [1, 2, 31, 32, 33, 50] do
      if k ≤ n then
        for (nm, src) in [("range", Jank.R9.Seq.Lazy.Source.intRange n), ("vector", .vector n), ("list", .list n)] do
          out := s!"map {nm} {n} {k} | {Jank.R9.Seq.Lazy.calls .jank src k} | {Jank.R9.Seq.Lazy.calls .clj src k}" :: out
  for k in [1, 2, 3, 5, 10] do
    out := s!"iterate {k} | {(Jank.R9.Seq.Lazy.jankTake (· + 1) k 0).2} | {(Jank.R9.Seq.Lazy.cljTake (· + 1) k ⟨0, some 0⟩).2}" :: out
  for len in [1, 2, 3, 4, 5, 11, 12, 13, 21, 22, 23, 30] do
    out := s!"mapcat {len} | {Jank.R9.Seq.Lazy.jankApplyRealized len} | {Jank.R9.Seq.Lazy.cljApplyRealized len (some 2)}" :: out
    out := s!"applyfixed {len} | {Jank.R9.Seq.Lazy.jankApplyRealized len} | {Jank.R9.Seq.Lazy.cljApplyRealized len none}" :: out
  let mut seed := 12345
  for _ in [0:60] do
    seed := lcg seed
    let len := 1 + (seed / 65536) % 60
    let mut xs : List Int := []
    for _ in [0:len] do
      seed := lcg seed
      xs := ((seed / 65536) % 3 : Nat) :: xs
    out := s!"dedupe {len} {" ".intercalate (xs.map toString)} | {Jank.R9.Seq.Lazy.jankDedupeFirstRealized xs} | {Jank.R9.Seq.Lazy.cljDedupeFirstRealized xs}" :: out
  return out.reverse

/-- The tests' sort programs: (form, comparator, keys). -/
def sortPrograms : List (String × Option Comp × List Key) := [
  ("(sort [3 ##NaN 1 2])", none, [.num 3, .nan, .num 1, .num 2]),
  ("(sort < [3 ##NaN 1 2])", some .lt, [.num 3, .nan, .num 1, .num 2]),
  ("(sort-by :v [{:v 3} {:v ##NaN} {:v 1} {:v 2}])", none, [.num 3, .nan, .num 1, .num 2]),
  ("(sort [2 ##NaN 1])", none, [.num 2, .nan, .num 1]),
  ("(sort [1 ##NaN 0 0])", none, [.num 1, .nan, .num 0, .num 0]),
  ("(sort [5 4 ##NaN 3 2 1])", none, [.num 5, .num 4, .nan, .num 3, .num 2, .num 1]),
  ("(sort [##NaN 3 2 1])", none, [.nan, .num 3, .num 2, .num 1]),
  ("(sort #(- %1 %2) [4294967296 0])", some .minus, [.num 4294967296, .num 0]),
  ("(sort #(- %1 %2) [3000000000 0])", some .minus, [.num 3000000000, .num 0]),
  ("(sort #(- %1 %2) [0 3000000000 1])", some .minus, [.num 0, .num 3000000000, .num 1]),
  ("(sort-by identity #(- %1 %2) [4294967296 0])", some .minus, [.num 4294967296, .num 0]),
  ("control (sort #(- %1 %2) [3 1 2])", some .minus, [.num 3, .num 1, .num 2]),
  ("control (sort <= [2 1 2 1])", some .le, [.num 2, .num 1, .num 2, .num 1]),
  ("control (sort [3 1 2])", none, [.num 3, .num 1, .num 2])]

def predictSort : IO Unit := do
  for (form, c, ks) in sortPrograms do
    let xs := mk ks
    let j := jankSort c xs
    let cl := (cljSort c xs).getD []
    IO.println s!"{form}: Clojure {keysCode cl} {tagsCode cl}; jank {keysCode j} {tagsCode j}{if tags j == tags cl then " (agree)" else ""}"

def showPA : Option Jank.R9.Seq.PartitionAll.Acc → String
  | some a => toString (repr a.out)
  | none => "throws"

/-- The partition-all transducer: every n in {-1, 0, 1, 2, 3} as a long and {1, 2, 3} as a double,
every input [0 .. len) with len <= 12, every stopping point in {1, 2, 3, 1000}. -/
def paSearch : IO Unit := do
  let ns : List Jank.R9.Seq.PartitionAll.N :=
    [.long (-1), .long 0, .long 1, .long 2, .long 3, .double 1, .double 2, .double 3]
  for n in ns do
    let mut tot := 0
    let mut dif := 0
    let mut first := ""
    for len in [0:13] do
      for stop in [1, 2, 3, 1000] do
        let xs : List Int := (List.range len).map Int.ofNat
        tot := tot + 1
        let j := (Jank.R9.Seq.PartitionAll.jank n stop xs).toOption
        let c := (Jank.R9.Seq.PartitionAll.clj n stop xs).toOption
        if j != c then
          dif := dif + 1
          if first == "" then
            first := s!"len {len} stop {stop}: Clojure {showPA c}, jank {showPA j}"
    let tail := if first == "" then "" else "; first: " ++ first
    IO.println s!"partition-all {repr n}: {tot} runs, {dif} differ{tail}"

def sortSearch : IO Unit := do
  for f in families do
    let mut tot := 0
    let mut dif := 0
    for n in [1:f.maxLen + 1] do
      let t := runFamily f n
      tot := tot + t.total
      dif := dif + t.differ
      IO.println s!"{f.name} length {n}: {t.total} lists, {t.differ} differ{match t.first with | some e => s!"; first: {e}" | none => ""}"
    IO.println s!"== {f.name}: complete to length {f.maxLen}: {tot} lists, {dif} differ{if f.control then " (control)" else ""}"

def main (args : List String) : IO Unit := do
  match args with
  | ["sort"] => sortSearch
  | ["predict"] => predictSort
  | ["pa"] => paSearch
  | ["preorders", n] =>
    for k in [1:n.toNat! + 1] do
      let (t, d) := preorderCensus k
      IO.println s!"every total preorder on {k} elements ({t} lists over {k} values): {d} differ"
  | ["preorders-random", count, seed] =>
    let (t, d) := randomPreorders count.toNat! seed.toNat!
    IO.println s!"random total preorders, lengths 2..31 over 2..32 values, seed {seed}: {t} lists, {d} differ"
  | ["cases", file] =>
    let ls := emitCases
    IO.FS.writeFile file ("\n".intercalate ls ++ "\n")
    IO.println s!"{ls.length} cases written to {file}"
  | ["lazy", file] =>
    IO.FS.writeFile file ("\n".intercalate lazyCases ++ "\n")
    IO.println s!"{lazyCases.length} realization cases written to {file}"
  | _ => IO.println "usage: jank9-seq sort | cases FILE | lazy FILE"
