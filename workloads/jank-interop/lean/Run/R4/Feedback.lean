import Jank.R4.Feedback.Numbers
import Jank.R4.Feedback.Control
import Jank.R4.Feedback.Shell
import Jank.R4.Feedback.Pprint

/-! Round 4 driver: the feedback items the coordinator re-ran (S2, S9 and S44 as round 3's tests
wrote them, and the round-4 observations). -/

open Jank.R4.Feedback.Numbers

def printObs (o : Obs) : IO Unit :=
  IO.println s!"{if o.agree then "agree " else "DIFFER"}  {o.form}\n        jank (replica): {o.jank}\n        Clojure:        {o.clj}"

def controlCmd (args : List String) : IO Unit := do
  match args with
  | ["size", samples] =>
    for (name, cfg) in Jank.R4.Feedback.Control.modes do
      let (e, d) := Jank.R4.Feedback.Control.size cfg samples.toNat!
      IO.println s!"== control, {name}, depth 2: {Jank.R4.Feedback.Control.firstOptions cfg} partitions; Knuth estimate {e} timelines ({d} decisions on average, {samples} samples)"
  | ["part", m, lo, hi, bound] =>
    let (name, cfg) := Jank.R4.Feedback.Control.modes[m.toNat!]!
    for k in [lo.toNat!:hi.toNat! + 1] do
      let t0 ← IO.monoMsNow
      let c := Jank.R3.Codegen.censusFrom (Jank.R4.Feedback.Control.runOf cfg) #[k] bound.toNat!
      IO.println s!"== control, {name}, depth 2, partition #{k}: {c.runs} timelines{if c.complete then " (complete)" else " (stopped)"}, {c.violating} violate {c.classes.map (fun h => (h.cls, h.count))}"
      for h in c.classes do
        IO.println s!"   first {h.cls}: {h.first.property}: {h.first.detail}"
      IO.println s!"  ({((← IO.monoMsNow) - t0) / 1000} s)"
      (← IO.getStdout).flush
  | _ => IO.println "usage: control size N | control part MODE LO HI BOUND"

open Jank.R4.Feedback.Shell in
/-- Every argument list `echo a1 [a2]` with each argument a string of length ≤ `len` over
`a`, space, `"`, backslash: jank's argv against Clojure's. Class Q: an argument in which a space
follows an odd number of `"`. -/
def shellArgs (len : Nat) : IO Unit := do
  let alpha := ['a', ' ', '"', '\\']
  let mut strs : List (List Char) := [[]]
  let mut layer : List (List Char) := [[]]
  for _ in [0:len] do
    layer := layer.flatMap fun s => alpha.map (s ++ [·])
    strs := strs ++ layer
  let oddThenSpace := fun (a : List Char) => Id.run do
    let mut q := 0
    for c in a do
      if c == '"' then q := q + 1
      if c == ' ' && q % 2 == 1 then return true
    return false
  let mut total := 0
  let mut differ := 0
  let mut classQ := 0
  let mut residual := 0
  let mut firstQ : Option String := none
  let mut firstR : Option String := none
  let mut qNoDiff := 0
  let mut lone := 0
  let mut loneOutsideQ := 0
  for args in (strs.map ([·])) ++ (strs.flatMap fun a => strs.map fun b => [a, b]) do
    let argv := "echo".toList :: args
    total := total + 1
    let j := jankArgv argv
    let oddQuotes := fun (a : List Char) => (a.filter (· == '"')).length % 2 == 1
    -- an odd quote count leaves `in_quote` flipped for the separator after the argument too
    let inQ := args.any oddThenSpace || (args.dropLast.any oddQuotes)
    if loneQuote argv then
      lone := lone + 1
      if !inQ then loneOutsideQ := loneOutsideQ + 1
    if j != argv then
      differ := differ + 1
      if inQ then
        classQ := classQ + 1
        if firstQ.isNone then firstQ := some s!"{(argv.map String.ofList)} -> {(j.map String.ofList)}"
      else
        residual := residual + 1
        if firstR.isNone then firstR := some s!"{(argv.map String.ofList)} -> {(j.map String.ofList)}"
    else if inQ then qNoDiff := qNoDiff + 1
  IO.println s!"== jank.shell/sh argv: every `echo a1` and `echo a1 a2`, arguments of length ≤ {len} over a, space, \", backslash: {total} lists (complete)"
  IO.println s!"   differ {differ}: class Q (a space after an odd number of quotes, inside an argument or as the separator after it) {classQ}, residual {residual}; Q lists that still agree {qNoDiff}"
  IO.println s!"   a piece that is a lone quote (make_entry's invalid range): {lone}, outside Q {loneOutsideQ}"
  if let some e := firstQ then IO.println s!"   first Q: {e}"
  if let some e := firstR then IO.println s!"   first residual: {e}"

open Jank.R4.Feedback.Shell in
def shellPipes : IO Unit := do
  IO.println "== jank.shell/sh pipes: every reachable interleaving of jank's parent and the child (BFS), cap = pipe capacity"
  let mut cases := 0
  let mut differ := 0
  for cap in [1, 2, 3, 4] do
    let kids : List (Child × Nat) :=
      ((List.range 10).map fun n => (Child.seq n, 0)) ++ ((List.range 10).map fun n => (Child.errOut n, 0))
      ++ ((List.range 10).map fun k => (Child.cat, k)) ++ ((List.range 10).map fun k => (Child.ignore, k))
    let mut row : List String := []
    for (c, k) in kids do
      cases := cases + 1
      let j := jankOutcomes cap c k
      let cl := cljOutcome c k
      if j != [cl] then
        differ := differ + 1
        row := row ++ [s!"{repr c} in={k}: jank {repr j}"]
    IO.println s!"   cap {cap}: {row.length} of {kids.length} differ from Clojure's (done with every byte)"
    for r in row do IO.println s!"     {r}"
  IO.println s!"   {cases} cases (complete), {differ} differ"

open Jank.R4.Feedback.Pprint in
def pprintCensus : IO Unit := do
  let mut firstDiff : Option Nat := none
  let mut diff := 0
  for n in [0:61] do
    let xs := List.range n
    if cljPprint xs != jankPprint xs then
      diff := diff + 1
      if firstDiff.isNone then firstDiff := some n
  IO.println s!"== clojure.pprint/pprint of (vec (range n)), n = 0..60 (complete): {diff} differ; first n = {firstDiff} (flat width {(firstDiff.map fun n => (flat (List.range n)).length)})"
  IO.println s!"   missing in jank: clojure.pprint {missing cljPprintNames jankPprintNames}; clojure.stacktrace {missing cljStacktraceNames jankStacktraceNames}"

def main (args : List String) : IO UInt32 := do
  if args.head? == some "pprint" then
    pprintCensus
    return 0
  if args.head? == some "shell" then
    shellArgs ((args.drop 1).head?.getD "4").toNat!
    shellPipes
    return 0
  if args.head? == some "control" then
    controlCmd args.tail
    return 0
  IO.println "== Round 3's S2/S9 tests as written (jank's `=` is D8's epsilon)"
  for o in round3Tests do printObs o
  IO.println "== Round 4's observations (compare, str)"
  for o in round4Tests do printObs o
  IO.println "== S44: theorems s44_round3_test_meta_kept, s44_round4_cases (checked at build)"
  return 0
