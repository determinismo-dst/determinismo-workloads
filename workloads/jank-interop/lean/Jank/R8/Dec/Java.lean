import Jank.R3.Boost.Java
import Jank.R7.Num.Dec
import Jank.R7.Coord.Decimal

/-!
# Round 8, area D: Java's BigDecimal with its scale, and MathContext rounding, as fixes/R72.diff and
fixes/X6.diff compute them

jank's BigDecimal becomes Java's own representation (type.hpp `native_big_decimal`: an unscaled
`cpp_int` and an `i32` scale; big_decimal.cpp `decimal::*`). This file is the replica of that C++
(`.r8-scratch/dec/cxx/impl.inc`, spliced verbatim into big_decimal.cpp), function by function, over
round 3's `BD` (`u · 10^-s`, Jank.R3.Boost.Java):

- `roundQ`        ↔ `round_quotient` (n / d rounded by a RoundingMode, for a value of a sign);
- `digits`        ↔ `digit_count` (BigDecimal.precision of the unscaled value);
- `round`         ↔ `decimal::round` (Java's doRound: keep `p` digits, carry 10^p → 10^(p-1));
- `exactDiv`      ↔ `exact_quotient` (gcd, strip the 2s and 5s: round 7's `steps`/`resultDigits`,
                    scale `preferred + k`);
- `ctxDiv`        ↔ `context_divide` (BigDecimal.divide(divisor, mc): `p` digits, an exact
                    quotient stripped toward the preferred scale);
- `divToInt`      ↔ `decimal::divide_to_integral_value` (divideToIntegralValue(divisor[, mc]));
- `remainder`     ↔ `decimal::remainder`;
- `cljOp`         ↔ the operators (Numbers.BigDecimalOps with `*math-context*`: add, minus =
                    add(x, negate(y, mc), mc), multiply, divide, quotient, remainder, negate, abs,
                    inc, dec).

Printing is round 3's `BD.toString` (BigDecimal.toString) and hashing round 7's `cljHashDec`
(Numbers.hasheqFrom). Java's semantics are the property: every function here was run against
Clojure 1.12.3 (JDK 23) on the same 225,700 operand cases as the C++ copy (Run/R8/Dec.lean).
-/

namespace Jank.R8.Dec

open Jank.R3.Boost.Java

/-- java.math.RoundingMode. -/
inductive RM where
  | up | down | ceiling | floor | halfUp | halfDown | halfEven | unnecessary
  deriving BEq, Repr, Inhabited, DecidableEq

def RM.ofString : String → RM
  | "UP" => .up | "DOWN" => .down | "CEILING" => .ceiling | "FLOOR" => .floor
  | "HALF_UP" => .halfUp | "HALF_DOWN" => .halfDown | "HALF_EVEN" => .halfEven
  | _ => .unnecessary

/-- java.math.MathContext: precision 0 is unlimited. -/
structure MC where
  p : Nat
  m : RM
  deriving BEq, Repr, Inhabited

def exact : MC := ⟨0, .halfUp⟩

/-- `round_quotient`: `n / d` (`d > 0`) rounded to an integer by the mode, for a value whose sign
is negative when `neg`. -/
def roundQ (n d : Nat) (m : RM) (neg : Bool) : Except String Nat :=
  let q := n / d
  let r := n % d
  if r = 0 then .ok q
  else match m with
    | .up => .ok (q + 1)
    | .down => .ok q
    | .ceiling => .ok (if neg then q else q + 1)
    | .floor => .ok (if neg then q + 1 else q)
    | .halfUp => .ok (if 2 * r ≥ d then q + 1 else q)
    | .halfDown => .ok (if 2 * r > d then q + 1 else q)
    | .halfEven => .ok (if 2 * r > d ∨ (2 * r = d ∧ q % 2 = 1) then q + 1 else q)
    | .unnecessary => .error "Rounding necessary"

/-- `digit_count`: decimal digits of `n` (1 for 0). -/
def digits (n : Nat) : Nat :=
  if h : n < 10 then 1 else digits (n / 10) + 1
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

/-- `decimal::round` (Java's doRound to `mc.p` digits). -/
def round (x : BD) (mc : MC) : Except String BD :=
  if mc.p = 0 then .ok x
  else
    let a := x.u.natAbs
    let dg := digits a
    if dg ≤ mc.p then .ok x
    else
      let drop := dg - mc.p
      match roundQ a (10 ^ drop) mc.m (x.u < 0) with
      | .error e => .error e
      | .ok r =>
        let (r, s) : Nat × Int :=
          if r = 10 ^ mc.p then (10 ^ (mc.p - 1), x.s - drop - 1) else (r, x.s - drop)
        .ok ⟨if x.u < 0 then -(r : Int) else r, s⟩

def nonTerminating : String := "Non-terminating decimal expansion; no exact representable decimal result."

/-- `exact_quotient` (BigDecimal.divide without a context; the divisor is not zero). -/
def exactDiv (x y : BD) : Except String BD :=
  let pref := x.s - y.s
  if x.u = 0 then .ok ⟨0, pref⟩
  else
    let a := x.u.natAbs
    let b := y.u.natAbs
    let g := Nat.gcd a b
    let n := a / g
    let d := b / g
    let st := Jank.R7.Coord.Decimal.steps d
    if st.rest ≠ 1 then .error nonTerminating
    else
      let k := max st.twos st.fives
      let q := Jank.R7.Coord.Decimal.resultDigits n d
      let neg := decide (x.u < 0) != decide (y.u < 0)
      .ok ⟨if neg then -(q : Int) else q, pref + k⟩

/-- `a · 10^t / b` as a numerator and denominator. -/
def nd (a b : Nat) (t : Int) : Nat × Nat :=
  if t ≥ 0 then (a * 10 ^ t.toNat, b) else (a, b * 10 ^ (-t).toNat)

/-- The loop of `context_divide` finding `t` with `10^(p-1) ≤ a · 10^t / b < 10^p`. -/
def findT (a b p : Nat) : Nat → Int → Int
  | 0, t => t
  | f + 1, t =>
    let (n, d) := nd a b t
    let q := n / d
    if q ≥ 10 ^ p then findT a b p f (t - 1)
    else if q < 10 ^ (p - 1) then findT a b p f (t + 1)
    else t

/-- `strip_to_scale`: drop trailing zeros while the scale is above the preferred one. -/
def stripTo (pref : Int) : Nat → Int → Int → BD
  | 0, u, s => ⟨u, s⟩
  | f + 1, u, s =>
    if s > pref ∧ u ≠ 0 ∧ u % 10 = 0 then stripTo pref f (u / 10) (s - 1) else ⟨u, s⟩

/-- `context_divide` (BigDecimal.divide(divisor, mc), `mc.p > 0`, the divisor not zero). -/
def ctxDiv (x y : BD) (mc : MC) : Except String BD :=
  let pref := x.s - y.s
  if x.u = 0 then .ok ⟨0, pref⟩
  else
    let neg := decide (x.u < 0) != decide (y.u < 0)
    let a := x.u.natAbs
    let b := y.u.natAbs
    let p := mc.p
    let t := findT a b p (digits a + digits b + 8) ((p : Int) - digits a + digits b)
    let (n, d) := nd a b t
    let ex := n % d = 0
    match roundQ n d mc.m neg with
    | .error e => .error e
    | .ok u =>
      let (u, s) : Nat × Int := if u = 10 ^ p then (10 ^ (p - 1), pref + t - 1) else (u, pref + t)
      let ui : Int := if neg then -(u : Int) else u
      if ex then .ok (stripTo pref (digits u + 1) ui s) else .ok ⟨ui, s⟩

/-- `decimal::divide` (Numbers.divide's zero check first). -/
def divide (x y : BD) (mc : MC) : Except String BD :=
  if y.u = 0 then .error "Divide by zero"
  else if mc.p = 0 then exactDiv x y else ctxDiv x y mc

/-- `compare_magnitude`. -/
def cmpMag (x y : BD) : Int := BD.cmp x.abs y.abs

/-- `decimal::divide_to_integral_value`. -/
def divToInt (x y : BD) (mc : MC) : Except String BD :=
  if y.u = 0 then .error "Divide by zero"
  else
    let pref := x.s - y.s
    if cmpMag x y < 0 then .ok ⟨0, pref⟩
    else if mc.p = 0 then
      let shift := y.s - x.s
      let (n, d) : Int × Int :=
        if shift ≥ 0 then (x.u * 10 ^ shift.toNat, y.u) else (x.u, y.u * 10 ^ (-shift).toNat)
      let t := Int.tdiv n d
      let sc := max pref (-(Jank.R7.Num.Dec.tz10 t.natAbs : Int))
      .ok (Jank.R7.Num.Dec.atScaleI t sc)
    else do
      let r ← ctxDiv x y ⟨mc.p, .down⟩
      let r ←
        if r.s < 0 then
          if cmpMag (x.sub (r.mul y)) y ≥ 0 then (Except.error "Division impossible" : Except String BD)
          else pure r
        else if r.s > 0 then pure (⟨Int.tdiv r.u (10 ^ r.s.toNat), 0⟩ : BD)
        else pure r
      let pd : Int := (mc.p : Int) - digits r.u.natAbs
      if pref > r.s ∧ pd > 0 then
        let add := min pd (pref - r.s)
        pure ⟨r.u * 10 ^ add.toNat, r.s + add⟩
      else pure (stripTo pref (digits r.u.natAbs + 1) r.u r.s)

/-- `decimal::remainder`: `x - divideToIntegralValue(x, y[, mc]) · y`, exact. -/
def remainder (x y : BD) (mc : MC) : Except String BD := do
  let q ← divToInt x y mc
  return x.sub (q.mul y)

/-- Clojure's operations on BigDecimals in a context (`*math-context*`): Numbers.add/minus/
multiply/divide/quotient/remainder/negate/abs/inc/dec over BigDecimalOps. -/
def cljOp (op : String) (x y : BD) (mc : MC) : Except String String :=
  let num (r : Except String BD) : Except String String := r.map BD.toString
  match op with
  | "+" => num (round (x.add y) mc)
  | "-" => num (do let ny ← round y.neg mc; round (x.add ny) mc)
  | "*" => num (round (x.mul y) mc)
  | "/" => num (divide x y mc)
  | "quot" => num (divToInt x y mc)
  | "rem" => num (remainder x y mc)
  | "neg" => num (round x.neg mc)
  | "abs" => num (round x.abs mc)
  | "inc" => num (round (x.add ⟨1, 0⟩) mc)
  | "dec" => num (round (x.add ⟨-1, 0⟩) mc)
  | "str" => .ok x.toString
  | "hash" => .ok (toString (Jank.R7.Num.Dec.cljHashDec x))
  | "cmp" => .ok (toString (BD.cmp x y))
  | _ => .error "?"

/-- A case operand "<u>E<e>" is `u · 10^e`. -/
def parseOperand (t : String) : Option BD :=
  match t.splitOn "E" with
  | [u, e] => do
    let u ← u.toInt?
    let e ← e.toInt?
    some ⟨u, -e⟩
  | _ => none

/-- The case's answer as the JVM program prints it. -/
def answer (op a b : String) (p : Nat) (m : String) : Option String := do
  let x ← parseOperand a
  let y := (parseOperand b).getD ⟨0, 0⟩
  let mc : MC := ⟨p, RM.ofString m⟩
  match cljOp op x y mc with
  | .ok s => some s
  | .error e => some ("throws " ++ e)

end Jank.R8.Dec
