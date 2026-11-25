import Jank.R3.Boost.Ieee
import Jank.PrintModel

/-!
# Round 3, Boost: the spec side, Java's `BigInteger`/`BigDecimal` and Clojure's `Numbers`

Clojure 1.12's numbers (clojure-ref: Numbers.java, BigInt.java, RT.java, core.clj `bigdec`,
`bigint`, `long`, `double`, LispReader `matchNumber`) over Java's documented `BigDecimal`
semantics (java.math.BigDecimal javadoc): a value is `unscaled × 10^-scale`; `add`/`subtract`
are exact with scale `max(s1, s2)`, `multiply` exact with scale `s1 + s2`; `divide(BigDecimal)`
is exact with preferred scale `s1 − s2` and throws "Non-terminating decimal expansion; no exact
representable decimal result." when the quotient does not terminate; `compareTo` compares
values; `toString` uses scientific notation when the scale is negative or the adjusted exponent
is below −6.
-/

namespace Jank.R3.Boost.Java

/-- A `BigDecimal`: `u × 10^-s`. -/
structure BD where
  u : Int
  s : Int
  deriving BEq, Repr, Inhabited

def pow10 (k : Nat) : Int := (10 : Int) ^ k

/-- `u1·10^-s1` and `u2·10^-s2` on the common scale `max s1 s2`. -/
def align (a b : BD) : Int × Int × Int :=
  let s := max a.s b.s
  (a.u * pow10 (s - a.s).toNat, b.u * pow10 (s - b.s).toNat, s)

def BD.add (a b : BD) : BD := let (x, y, s) := align a b; ⟨x + y, s⟩
def BD.sub (a b : BD) : BD := let (x, y, s) := align a b; ⟨x - y, s⟩
def BD.mul (a b : BD) : BD := ⟨a.u * b.u, a.s + b.s⟩
def BD.neg (a : BD) : BD := ⟨-a.u, a.s⟩
def BD.signum (a : BD) : Int := if a.u > 0 then 1 else if a.u < 0 then -1 else 0
def BD.abs (a : BD) : BD := ⟨a.u.natAbs, a.s⟩

/-- `compareTo`. -/
def BD.cmp (a b : BD) : Int :=
  let (x, y, _) := align a b
  if x < y then -1 else if x > y then 1 else 0

/-- The value as a rational `p / q` (q > 0). -/
def BD.rat (a : BD) : Int × Nat :=
  if a.s ≤ 0 then (a.u * pow10 (-a.s).toNat, 1) else (a.u, (10 ^ a.s.toNat : Nat))

/-- Trailing zeros of `n > 0`. -/
def tz (n : Nat) : Nat := Id.run do
  let mut k := 0
  let mut m := n
  for _ in [0:4000] do
    if m != 0 && m % 10 == 0 then m := m / 10; k := k + 1 else break
  return k

/-- The exact quotient `p / q` (q > 0) as a terminating decimal `c · 10^-sMin` with the
smallest scale, or none. -/
def terminating (p : Int) (q : Nat) : Option (Int × Int) := Id.run do
  let g := Nat.gcd p.natAbs q
  let mut d := q / g
  let mut twos := 0
  let mut fives := 0
  for _ in [0:4000] do
    if d % 2 == 0 && d != 0 then d := d / 2; twos := twos + 1 else break
  for _ in [0:4000] do
    if d % 5 == 0 && d != 0 then d := d / 5; fives := fives + 1 else break
  if d != 1 then return none
  let k := max twos fives
  -- p/q = (p/g)·10^k/(q/g) / 10^k, an integer numerator.
  let num : Int := (p / g) * pow10 k / (q / g : Nat)
  if num == 0 then return some (0, 0)
  let t := tz num.natAbs
  return some (num / pow10 t, (k : Int) - t)

/-- `setScale` without rounding: `v` (a value already exact at scale `s`). -/
def atScale (c : Int) (sMin : Int) (s : Int) : BD :=
  if s ≥ sMin then ⟨c * pow10 (s - sMin).toNat, s⟩ else ⟨c / pow10 (sMin - s).toNat, s⟩

/-- `divide(BigDecimal divisor)` (no MathContext): exact, scale `max(preferred, minimal)`. -/
def BD.div (a b : BD) : Except String BD :=
  if b.u == 0 then .error (if a.u == 0 then "Division undefined" else "Division by zero")
  else
    let pref := a.s - b.s
    if a.u == 0 then .ok ⟨0, pref⟩
    else
      -- a/b = (a.u · 10^b.s) / (b.u · 10^a.s)
      let (pn, qn) : Int × Int :=
        if b.s ≥ a.s then (a.u * pow10 (b.s - a.s).toNat, b.u) else (a.u, b.u * pow10 (a.s - b.s).toNat)
      let (pn, qn) := if qn < 0 then (-pn, -qn) else (pn, qn)
      match terminating pn qn.toNat with
      | none => .error "Non-terminating decimal expansion; no exact representable decimal result."
      | some (c, sMin) => .ok (atScale c sMin (max pref sMin))

/-- `toString()` (layoutChars, scientific). -/
def BD.toString (a : BD) : String :=
  let coeff := (Nat.toDigits 10 a.u.natAbs)
  let n := coeff.length
  let sign := if a.u < 0 then "-" else ""
  let adjusted : Int := -a.s + (n - 1)
  if a.s == 0 then sign ++ String.ofList coeff
  else if a.s > 0 && adjusted ≥ -6 then
    let sc := a.s.toNat
    if n > sc then sign ++ String.ofList (coeff.take (n - sc)) ++ "." ++ String.ofList (coeff.drop (n - sc))
    else sign ++ "0." ++ String.ofList (List.replicate (sc - n) '0') ++ String.ofList coeff
  else
    let body := String.ofList (coeff.take 1) ++ (if n > 1 then "." ++ String.ofList (coeff.drop 1) else "")
    let ex := if adjusted != 0 then "E" ++ (if adjusted > 0 then "+" else "-") ++ Nat.repr adjusted.natAbs else ""
    sign ++ body ++ ex

/-- `doubleValue()`: the nearest double (assumption MPA6). -/
def BD.toDouble (a : BD) : Float :=
  let (p, q) := a.rat
  Ieee.ofRatF (p < 0) p.natAbs q

/-- `toBigInteger()`: truncation toward zero. -/
def BD.toBigInteger (a : BD) : Int :=
  let (p, q) := a.rat
  Int.tdiv p q

/-- `new BigDecimal(String)`: `[+-]? (digits [. digits?] | . digits) ([eE] [+-]? digits)?`. -/
def BD.ofString (cs : List Nat) : Except String BD := Id.run do
  let bad : Except String BD := .error "NumberFormatException"
  let mut s := cs
  let mut neg := false
  if s.head? == some 45 then neg := true; s := s.drop 1
  else if s.head? == some 43 then s := s.drop 1
  let isD := fun (c : Nat) => 48 ≤ c && c ≤ 57
  let intPart := s.takeWhile isD
  s := s.drop intPart.length
  let mut frac : List Nat := []
  let mut dot := false
  if s.head? == some 46 then
    dot := true
    s := s.drop 1
    frac := s.takeWhile isD
    s := s.drop frac.length
  if intPart.isEmpty && frac.isEmpty then return bad
  let mut e : Int := 0
  if s.head? == some 101 || s.head? == some 69 then
    s := s.drop 1
    let mut eneg := false
    if s.head? == some 45 then eneg := true; s := s.drop 1
    else if s.head? == some 43 then s := s.drop 1
    let ed := s.takeWhile isD
    if ed.isEmpty then return bad
    s := s.drop ed.length
    let ev : Int := ed.foldl (fun acc c => acc * 10 + (c - 48 : Nat)) 0
    e := if eneg then -ev else ev
  if !s.isEmpty then return bad
  let _ := dot
  let digits := intPart ++ frac
  let u : Int := digits.foldl (fun acc c => acc * 10 + (c - 48 : Nat)) 0
  let sc : Int := frac.length - e
  -- The scale is an int: out of range throws.
  if sc > 2147483647 || sc < -2147483648 then return bad
  return .ok ⟨if neg then -u else u, sc⟩

/-- `BigDecimal.valueOf(long)`. -/
def BD.ofLong (v : Int) : BD := ⟨v, 0⟩

/-- `Double.toString(d)` (JDK ≥ 19, assumption RB): the shortest decimal, printed by round 2's
`Jank.Print.javaDoubleL`. -/
def javaDoubleString (d : Float) : String :=
  if d.isNaN then "NaN" else if d.isInf then (if d < 0 then "-Infinity" else "Infinity")
  else
    let neg := d.toBits >>> 63 == 1
    if d == 0.0 then (if neg then "-0.0" else "0.0")
    else
      let (c, s) := Jank.Codegen.Float.shortest (d.abs.toBits)
      String.ofList (Jank.Print.javaDoubleL ⟨neg, c, s⟩)

/-- `BigDecimal.valueOf(double)`: `new BigDecimal(Double.toString(d))`. -/
def BD.valueOfDouble (d : Float) : Except String BD :=
  BD.ofString ((javaDoubleString d).toList.map Char.toNat)

/-- `new BigInteger(String)`: `[+-]? digits` (ASCII digits here). -/
def bigIntegerOfString (cs : List Nat) : Except String Int := Id.run do
  if cs.isEmpty then return .error "Zero length BigInteger"
  let mut s := cs
  let mut neg := false
  if s.head? == some 45 then neg := true; s := s.drop 1
  else if s.head? == some 43 then s := s.drop 1
  if s.isEmpty then return .error "Zero length BigInteger"
  if !s.all (fun c => 48 ≤ c && c ≤ 57) then return .error "NumberFormatException"
  let v : Int := s.foldl (fun acc c => acc * 10 + (c - 48 : Nat)) 0
  return .ok (if neg then -v else v)

end Jank.R3.Boost.Java
