import Jank.R7.Gen.Num
import Jank.R7.Gen.MinMax
import Jank.R7.Gen.Native
import Jank.R7.Gen.Str

/-!
# Round 7, area G: the strata, their seeds, and the emitted files

One stratum per group and operation. Its seed is `baseSeed + k` (k its position below), mixed by
`Determinismo.mixSeed` inside `choose`; `t` is the number of draws, each emitted on every path of
the draw. The brief's classes (min/max with ##NaN through a fn, `index-of` with negative and
past-the-end starts, `last-index-of` with negative starts) have strata of their own.
-/

namespace Jank.R7.Gen.Plan

open Jank.R7.Gen

def baseSeed : Nat := 70700

structure Stratum where
  group : String
  op : String
  seed : Nat
  candidates : Nat
  failing : Nat
  chosen : Array Draw

def stratum (group op : String) (seed : Nat) (paths : List Path) (ds : Array Draw) (t : Nat) : Stratum :=
  { group, op, seed, candidates := ds.size, failing := (ds.filter (·.fails)).size,
    chosen := choose seed paths ds t }

def strata : Array Stratum := Id.run do
  let mut out := #[]
  let mut k := 0
  for op in Jank.R6.Num.Search.ops do
    let paths := if op.unary then [.literals, .letp, .fn] else Path.all
    out := out.push (stratum "num" (Num.slug op) (baseSeed + k) paths (Num.draws op) 4)
    k := k + 1
  for op in MinMax.ops do
    out := out.push (stratum "minmax" (MinMax.slug op) (baseSeed + k) Path.all (MinMax.draws op) 6)
    k := k + 1
  for op in Jank.R6.Native.Op.all do
    out := out.push (stratum "native" (Native.slug op) (baseSeed + k) Path.all (Native.draws op) 4)
    k := k + 1
  for sl in Str.slugs do
    out := out.push (stratum "str" sl (baseSeed + k) Str.strPaths (Str.mkDraws "str" (Str.casesOf sl)) 5)
    k := k + 1
  for op in ["min", "max"] do
    out := out.push (stratum "brief" s!"nan-{op}" (baseSeed + k) [.fn] (MinMax.nanDraws op) 8)
    k := k + 1
  out := out.push (stratum "brief" "index-of-starts" (baseSeed + k) Str.strPaths (Str.mkDraws "brief" Str.briefIndexOf) 4)
  k := k + 1
  out := out.push (stratum "brief" "last-index-of-negative" (baseSeed + k) Str.strPaths (Str.mkDraws "brief" Str.briefLastIndexOf) 4)
  return out

/-- The chosen draws' items, a form already emitted (two draws sharing their literal path) once. -/
def items (ss : Array Stratum) : Array Item := Id.run do
  let mut seen : Std.HashSet String := {}
  let mut out := #[]
  for s in ss do
    for d in s.chosen do
      for i in d.items do
        if !seen.contains i.form then
          seen := seen.insert i.form
          out := out.push i
  return out

/-- Every stratum's draws before `choose`: the whole universe of each model the strata draw from. -/
def allDraws : Array (String × Nat × List Path × Array Draw) := Id.run do
  let mut out := #[]
  let mut k := 0
  for op in Jank.R6.Num.Search.ops do
    let paths := if op.unary then [.literals, .letp, .fn] else Path.all
    out := out.push (s!"num-{Num.slug op}", baseSeed + k, paths, Num.draws op)
    k := k + 1
  for op in MinMax.ops do
    out := out.push (s!"minmax-{MinMax.slug op}", baseSeed + k, Path.all, MinMax.draws op)
    k := k + 1
  for op in Jank.R6.Native.Op.all do
    out := out.push (s!"native-{Native.slug op}", baseSeed + k, Path.all, Native.draws op)
    k := k + 1
  for sl in Str.slugs do
    out := out.push (s!"str-{sl}", baseSeed + k, Str.strPaths, Str.mkDraws "str" (Str.casesOf sl))
    k := k + 1
  return out

/-- The bulk check: up to `per` draws of each stratum's universe (a seeded shuffle, seed + 1000),
every path, as `name<TAB>assertion<TAB>verdict<TAB>id` lines for the JVM. -/
def bulkFile (per : Nat) : String × Nat := Id.run do
  let mut lines : Array String := #[]
  let mut seen : Std.HashSet String := {}
  for (name, seed, _, ds) in allDraws do
    let (sh, _) := shuffle (rngOf (seed + 1000)) ds
    for d in sh.extract 0 per do
      for i in d.items do
        if !seen.contains i.form then
          seen := seen.insert i.form
          lines := lines.push s!"{name}-{i.path.slug}\t{i.assertion}\t{i.verdict.name}\t{i.id}"
  return ("\n".intercalate lines.toList ++ "\n", lines.size)

def countBy {α : Type} (xs : Array α) (key : α → String) : List (String × Nat) :=
  let m := xs.foldl (fun (m : Std.HashMap String Nat) x => m.insert (key x) (m.getD (key x) 0 + 1)) {}
  m.toList.mergeSort (fun a b => a.1 ≤ b.1)

def jankFile (its : Array Item) : String := Id.run do
  let mut s := header ++ "\n" ++ "\n".intercalate wrappers ++ "\n"
  let mut n := 0
  for i in its do
    n := n + 1
    s := s ++ "\n" ++ deftestText n i
  return s

def tsvFile (its : Array Item) : String := Id.run do
  let mut lines := #["test\tpath\tform\tclojure\tjank_predicted\tverdict\tid"]
  let mut n := 0
  for i in its do
    n := n + 1
    lines := lines.push (tsvLine n i)
  return "\n".intercalate lines.toList ++ "\n"

def summary (ss : Array Stratum) (its : Array Item) : String := Id.run do
  let mut out := #[]
  out := out.push s!"strata: {ss.size}; base seed {baseSeed} (stratum k: seed {baseSeed}+k, mixed by Determinismo.mixSeed); tests: {its.size}"
  out := out.push "\n== Strata: group op | seed | candidate draws (failing somewhere) | draws chosen"
  for s in ss do
    out := out.push s!"  {s.group} {s.op} | {s.seed} | {s.candidates} ({s.failing}) | {s.chosen.size}"
  out := out.push "\n== Tests emitted by group and op (a form shared by two draws once)"
  for (k, v) in countBy its (fun i => s!"{i.group} {i.op}") do
    out := out.push s!"  {k}: {v}"
  out := out.push "\n== Predicted verdicts by group, op and path"
  for (k, v) in countBy its (fun i => s!"{i.group} {i.op} {i.path.slug} {i.verdict.name}") do
    out := out.push s!"  {k}: {v}"
  out := out.push "\n== Predicted verdicts by group and path"
  for (k, v) in countBy its (fun i => s!"{i.group} {i.path.slug} {i.verdict.name}") do
    out := out.push s!"  {k}: {v}"
  out := out.push "\n== Predicted verdicts overall"
  for (k, v) in countBy its (fun i => i.verdict.name) do
    out := out.push s!"  {k}: {v}"
  out := out.push "\n== Predicted failures and throws by explaining id"
  for (k, v) in countBy (its.filter (·.verdict != .pass)) (fun i => s!"{i.id} ({i.verdict.name})") do
    out := out.push s!"  {k}: {v}"
  return "\n".intercalate out.toList ++ "\n"

end Jank.R7.Gen.Plan
