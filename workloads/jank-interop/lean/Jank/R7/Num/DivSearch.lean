import Jank.R7.Num.Dec

/-!
# Round 7, numbers: what exact division leaves (a complete search)

For every pair of BigDecimals `⟨u1, s1⟩ / ⟨u2, s2⟩` within the bounds, Clojure's quotient
(`Java.BD.div`: exact, scale `max(s1 − s2, minimal scale)`, else the throw) beside jank with exact
division (`Dec.jDivFixed` on the two values read from Clojure's own text). The search checks the
hypothesis H on every case:

  the two texts agree ⟺ the quotient terminates, Java prints it plainly (scale ≥ 0 and adjusted
  exponent ≥ −6), boost prints it in fixed notation (−4 ≤ order < 128), it has at most 128
  significant digits, and Clojure's scale is the scale jank's text shows: the value's minimal
  scale when that is positive, else 1 (jank prints an integer with ".0").

`jankScale` below is that scale.
-/

namespace Jank.R7.Num.DivSearch

open Jank.R3.Boost Jank.R3.Boost.Dec Jank.R3.Boost.Num Jank.R3.Boost.Java Jank.R7.Num.Dec

def digitsOf (n : Nat) : Nat := (Nat.toDigits 10 n).length

/-- The minimal scale of a nonzero decimal `⟨u, s⟩`; 0 for zero. -/
def minScale (b : BD) : Int := if b.u = 0 then 0 else b.s - tz10 b.u.natAbs

def jankScale (b : BD) : Int := max 1 (minScale b)

/-- Java prints `⟨u, s⟩` plainly: `s ≥ 0` and adjusted exponent `−s + (digits − 1) ≥ −6`. -/
def javaPlain (b : BD) : Bool :=
  b.s ≥ 0 && (-b.s + (digitsOf b.u.natAbs : Int) - 1 ≥ -6)

/-- boost's `str()` is fixed for −4 ≤ order < digits (R3 `jank_str_fixed_iff`); zero prints "0". -/
def jankFixed (b : BD) : Bool :=
  if b.u = 0 then true
  else
    let sig := digitsOf (b.u.natAbs / 10 ^ tz10 b.u.natAbs)
    let order : Int := -b.s + (digitsOf b.u.natAbs : Int) - 1
    order ≥ -4 && order < 128 && sig ≤ 128

def hypothesis (r : BD) : Bool := javaPlain r && jankFixed r && r.s == jankScale r

structure Tally where
  cases : Nat := 0
  nonTerminating : Nat := 0
  agreeBoth : Nat := 0
  textDiffers : Nat := 0
  scaleOnly : Nat := 0
  notationN : Nat := 0
  digits : Nat := 0
  valueDiffers : Nat := 0
  hFails : Nat := 0
  examples : Array String := #[]
  failures : Array String := #[]

def bdText (b : BD) : String := b.toString ++ "M"

def step (t : Tally) (a b : BD) : Tally := Id.run do
  let mut t := { t with cases := t.cases + 1 }
  match BD.div a b with
  | .error _ =>
    -- Clojure throws; the fixed jank throws exactly when the quotient does not terminate.
    t := { t with nonTerminating := t.nonTerminating + 1 }
    return t
  | .ok r =>
    let ja := match rdString (bytes a.toString) with | .ok x => JV.dec x | .error _ => JV.long 0
    let jb := match rdString (bytes b.toString) with | .ok x => JV.dec x | .error _ => JV.long 0
    let j := jDivFixed ja jb
    let cTxt := bdText r
    let (jTxt, jVal) := match j with
      | .num v => (v.prStr, jRat v)
      | .err e => (s!"throws {e}", none)
      | _ => ("?", none)
    let same := jTxt == cTxt
    let h := hypothesis r
    if same then t := { t with agreeBoth := t.agreeBoth + 1 }
    else
      t := { t with textDiffers := t.textDiffers + 1 }
      let valSame := match jVal with | some v => ratEq v r.rat | none => false
      if !valSame then t := { t with valueDiffers := t.valueDiffers + 1 }
      else if !(javaPlain r && jankFixed r) then t := { t with notationN := t.notationN + 1 }
      else t := { t with scaleOnly := t.scaleOnly + 1 }
      if t.examples.size < 12 && (t.cases % 997 == 0 || t.examples.size < 4) then
        t := { t with examples := t.examples.push s!"(/ {bdText a} {bdText b}): Clojure {cTxt}, jank (exact division) {jTxt}" }
    if same != h then
      t := { t with hFails := t.hFails + 1 }
      if t.failures.size < 20 then
        t := { t with failures := t.failures.push s!"(/ {bdText a} {bdText b}): Clojure {cTxt}, jank {jTxt}, H {h}" }
    return t

/-- Every `⟨u1, s1⟩ / ⟨u2, s2⟩` with |u1| ≤ bu1, 1 ≤ |u2| ≤ bu2, scales in [smin, smax]. -/
def search (bu1 bu2 : Nat) (smin smax : Int) : Tally := Id.run do
  let mut t : Tally := {}
  let scales : List Int := (List.range (smax - smin + 1).toNat).map (fun (i : Nat) => smin + (i : Int))
  for i1 in List.range (2 * bu1 + 1) do
    let u1 : Int := (i1 : Int) - bu1
    for s1 in scales do
      for i2 in List.range (2 * bu2 + 1) do
        let u2 : Int := (i2 : Int) - bu2
        if u2 != 0 then
          for s2 in scales do
            t := step t ⟨u1, s1⟩ ⟨u2, s2⟩
  return t

end Jank.R7.Num.DivSearch
