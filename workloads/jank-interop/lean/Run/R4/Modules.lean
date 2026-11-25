import Jank.R4.Modules.Munge
import Jank.R4.Modules.Loader
import Jank.R4.Modules.Load
import Jank.R4.Modules.LoadWorld
import Jank.R4.Modules.Cli
import Jank.R4.Modules.Aot
import Jank.R3.Search.Common

/-! Round 4 driver: modules, AOT and the CLI (`jank4-modules <part> [bound]`). -/

open Determinismo Jank.R3.Search

def censusAll (name : String) (run : Source → Ended) (maxRuns : Nat) : IO Unit := do
  let t0 ← IO.monoMsNow
  let c := censusUnder run #[] maxRuns
  printCensus name c
  let t1 ← IO.monoMsNow
  IO.println s!"  ({(t1 - t0) / 1000} s)"

def main (args : List String) : IO Unit := do
  match args with
  | ["loader", n] => censusAll s!"loader, module paths of ≤{n} elements" (Jank.R4.Modules.loaderRun n.toNat!) 50000000
  | ["load", n] => censusAll s!"require/use/load/refer/alias, ≤{n} top-level forms" (Jank.R4.Modules.LoadWorld.run n.toNat!) 50000000
  | ["runmain"] => censusAll "run-main" Jank.R4.Modules.LoadWorld.rmRun 50000000
  | ["cli", n] => censusAll s!"CLI arguments, ≤{n} tokens" (Jank.R4.Modules.Cli.cliRun n.toNat!) 50000000
  | ["aot"] => censusAll "AOT start-up vs run-main vs clojure -m" Jank.R4.Modules.Aot.run 50000000
  | _ => IO.println "usage: jank4-modules loader N | load N | runmain | cli N | aot"
