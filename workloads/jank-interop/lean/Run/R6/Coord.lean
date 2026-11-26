import Jank.R6.Native.Math
import Jank.R6.Num.Search
import Jank.R6.Str.Proofs
import Jank.R6.Coord.NativeKernel

/-! Round 6, coordinator (`jank6-coord`): the brief's observations of the real jank (LG1–LG3, main
7135b7708, whose compiler+runtime is 94d32623's), each put to this round's replica, beside what the
real jank gave. A row says `agrees` when the replica's jank prediction is the observed value.

- LG1 through area P's model (`Jank.R6.Native`): `(count [..])` is `.count n` (a `usize`), a
  literal is `.lit`, and `(long (count [1]))` is a boxed long, `.param 1` (`long` is not inlined:
  core.jank 5773-5776; it returns an object, as a fn parameter is).
- LG2 through area N's model (`Jank.R6.Num`): literals are `.lit`.
- LG3 through area W's model (`Jank.R6.Str`): `jSubs1` on the code points of "é-è" (the theorem
  `lg3_model` proves the same row). -/

open Jank.R6

def row (form observed predicted clj : String) : IO Unit :=
  IO.println s!"{form}\n    real jank {observed}; replica {predicted} ({if observed == predicted then "agrees" else "DIFFERS"}); Clojure {clj}"

def lg1 (form observed : String) (c : Native.Case) : IO Unit :=
  row form observed (c.jank Native.Sw.none).seen.show (c.clj false).show

def lg2 (form observed : String) (op : Num.Search.IOp) (x y : Num.CInt) : IO Unit :=
  let (j, c) := Num.Search.answer op x y .lit .lit
  row form observed (Num.showOut j) (Num.showOut c)

def bytesText (r : Jank.Str.R) : String := reprStr r

def main : IO Unit := do
  IO.println "== LG1 (area P's model)"
  lg1 "(< -1 (count [1]))" "false" { op := .lt, a := .lit (-1), b := .count 1, fnValue := false }
  lg1 "(max (count [1]) -1)" "-1" { op := .max, a := .count 1, b := .lit (-1), fnValue := false }
  lg1 "(min (count [1 2 3]) -1)" "3" { op := .min, a := .count 3, b := .lit (-1), fnValue := false }
  lg1 "(< -1 (long (count [1])))" "true" { op := .lt, a := .lit (-1), b := .param 1, fnValue := false }
  IO.println "== LG2 (area N's model)"
  lg2 "(* -3 9223372036854775807)" "-9223372036854775805" (.bin .mul) (.long (-3)) (.long 9223372036854775807)
  lg2 "(dec -9223372036854775808)" "-9223372036854775809N" .dec (.long (-9223372036854775808)) (.long (-9223372036854775808))
  IO.println "== LG3 (area W's model)"
  let j := Jank.R6.Str.jSubs1 [0xE9, 0x2D, 0xE8] 2
  let c := Jank.R6.Str.cSubs1 [0xE9, 0x2D, 0xE8] 2
  let obs := Jank.Str.R.str (Jank.Str.jstr [0x2D, 0xE8])
  IO.println s!"(subs \"é-è\" 2)\n    real jank \"-è\" = {bytesText obs}; replica {bytesText j} ({if j == obs then "agrees" else "DIFFERS"}); Clojure {bytesText c}"
