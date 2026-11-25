import Jank.R5.Errors.Model
import Jank.R5.Errors.World
import Jank.R5.Errors.Theorems
import Jank.R5.Errors.Nested
import Jank.R3.Search.Common

/-! Round 5 driver: errors (`jank5-errors <part>`). -/

open Determinismo Jank.R3.Search

def censusAll (name : String) (run : Source → Ended) (maxRuns : Nat) : IO Unit := do
  let t0 ← IO.monoMsNow
  let c := censusUnder run #[] maxRuns
  printCensus name c
  let t1 ← IO.monoMsNow
  IO.println s!"  ({(t1 - t0)} ms)"

def main (args : List String) : IO Unit := do
  match args with
  | ["world"] => censusAll "errors: what a program sees of an error, jank vs Clojure" Jank.R5.Errors.World.run 10000000
  | ["nested"] => censusAll "errors through ≤2 nested contexts (delay, future, module, macro, def)" Jank.R5.Errors.Nested.run 10000000
  | _ => IO.println "usage: jank5-errors world | nested"
