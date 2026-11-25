import Jank.R5.Core.Inst
import Jank.R5.Core.InstSearch
import Jank.R5.Core.ChampSub5
import Jank.R5.Core.ChampR55
import Jank.R3.Search.Common

/-! Round 5 driver: core (`jank5-core <part> [bound]`): `#inst` and the CHAMP laws' searches. -/

open Determinismo Jank.R3.Search Jank.R5.Core

def censusAll (name : String) (run : Source → Ended) (maxRuns : Nat) : IO Unit := do
  let t0 ← IO.monoMsNow
  let c := censusUnder run #[] maxRuns
  printCensus name c
  let t1 ← IO.monoMsNow
  IO.println s!"  ({(t1 - t0) / 1000} s)"

def dump (path : String) : IO Unit := do
  let h ← IO.FS.Handle.mk path .write
  let mut n := 0
  for x in InstSearch.allTs do
    h.putStrLn (InstSearch.dumpLine x.text)
    n := n + 1
  h.flush
  IO.println s!"dumped {n} inputs to {path}"

def show1 (s : String) : IO Unit := do
  let j := Inst.jankRead s.toList
  let c := Inst.cljRead s.toList
  IO.println s!"{s}: jank {(j.map Inst.jankPr).getD "read error"} (format {(Inst.jankFormatUsed s.toList).getD 0}, ns {j}, inst-ms {j.map Inst.jankInstMs}); Clojure {(c.map Inst.cljPr).getD "read error"} (inst-ms {c})"

def main (args : List String) : IO Unit := do
  match args with
  | ["inst"] => censusAll "#inst timestamps (field variants)" (InstSearch.runW InstSearch.instCase) 50000000
  | ["raw", n] => censusAll s!"#inst raw strings, length ≤ {n}" (InstSearch.runW (InstSearch.rawCase n.toNat!)) 50000000
  | ["eq"] => censusAll "#inst = below the millisecond" (InstSearch.runW InstSearch.eqCase) 50000000
  | ["dump", path] => dump path
  | "show" :: xs => for s in xs do show1 s
  | _ => IO.println "usage: jank5-core inst | raw N | eq | dump FILE | show TEXT..."
