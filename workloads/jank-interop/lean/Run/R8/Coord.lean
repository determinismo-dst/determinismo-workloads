import Jank.R8.Coord.MinMax
import Jank.R8.Coord.RatioDec

/-! Round 8, coordinator (`jank8-coord`): object `min`/`max` stock, with V56 and Clojure's
(`Jank.R8.Coord.MinMax`), and S3c's ratio-to-decimal conversion (`Jank.R8.Coord.RatioDec`). -/

open Jank.R8.Coord

def showNum : MinMax.Num → String
  | .nan => "##NaN"
  | .val v k => s!"{v}{if k == 1 then ".0" else ""}"

def main : IO Unit := do
  let one := MinMax.Num.val 1 0
  let oneD := MinMax.Num.val 1 1
  let rows : List (String × MinMax.Num × MinMax.Num × MinMax.Num) :=
    [("(min ##NaN 1)", MinMax.stockMin .nan one, MinMax.fixedMin .nan one, MinMax.cljMin .nan one),
     ("(max 1 ##NaN)", MinMax.stockMax one .nan, MinMax.fixedMax one .nan, MinMax.cljMax one .nan),
     ("(max 1 1.0)", MinMax.stockMax one oneD, MinMax.fixedMax one oneD, MinMax.cljMax one oneD),
     ("(min 1.0 1)", MinMax.stockMin oneD one, MinMax.fixedMin oneD one, MinMax.cljMin oneD one)]
  for (form, s, f, c) in rows do
    IO.println s!"{form} through a fn: stock {showNum s}; V56 {showNum f}; Clojure {showNum c}"
  for (n, d) in [((1 : Int), 3), (7, 4), (-1, 8), (7, 3), (3, 1024)] do
    let r := match RatioDec.conv n d with
      | some (m, k) => s!"{m}e-{k}"
      | none => "throws Non-terminating decimal expansion"
    IO.println s!"S3c {n}/{d} -> {r}"
