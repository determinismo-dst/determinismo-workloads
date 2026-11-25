/-!
# Doubles: how jank prints them into C++, and how C++ reads them back

`string_builder::operator()(double)` (src/cpp/jtl/string_builder.cpp:83-137):

- infinities print `INFINITY` / `-INFINITY`, every NaN prints `NAN` (sign and payload dropped);
- otherwise `std::to_chars(first, last, d)` (the shortest round-trip form), then `.0` is
  appended when the text has neither a `.` nor an `e`.

The code generator puts that text in C++ source (`_jank_small_real({})`, `small_real_ref{ {} }`,
cpp_processor.cpp:197-199 and 298-302). Its meaning is the C++ one: a decimal floating literal is
the nearest double (round to nearest even, as Clang's APFloat does), `-x` negates, `INFINITY` and
`NAN` are `<cmath>`'s float constants converted to double.

Everything here is exact integer arithmetic on the value `m · 2^e` of a double.
-/

namespace Jank.Codegen.Float

/-- A finite double's sign and magnitude `m · 2^e` (IEEE-754 binary64). -/
structure Parts where
  neg : Bool
  m : Nat
  e : Int
  deriving Repr, BEq

def expField (b : UInt64) : Nat := ((b >>> 52) &&& 0x7FF).toNat
def fracField (b : UInt64) : Nat := (b &&& 0xFFFFFFFFFFFFF).toNat
def signBit (b : UInt64) : Bool := (b >>> 63) == 1

def isInf (b : UInt64) : Bool := expField b == 0x7FF && fracField b == 0
def isNaN (b : UInt64) : Bool := expField b == 0x7FF && fracField b != 0

def decode (b : UInt64) : Parts :=
  let ex := expField b
  let fr := fracField b
  if ex == 0 then { neg := signBit b, m := fr, e := -1074 }
  else { neg := signBit b, m := fr + 2 ^ 52, e := (ex : Int) - 1075 }

/-- `p / q` as a pair of naturals for `m · 2^e`. -/
def toRat (m : Nat) (e : Int) : Nat × Nat :=
  if e ≥ 0 then (m * 2 ^ e.toNat, 1) else (m, 2 ^ (-e).toNat)

/-- `2^t ≤ p/q` (p, q > 0). -/
def pow2Le (t : Int) (p q : Nat) : Bool :=
  if t ≥ 0 then q * 2 ^ t.toNat ≤ p else q ≤ p * 2 ^ (-t).toNat

/-- `⌊log2 (p/q)⌋` for `p, q > 0`. -/
def floorLog2 (p q : Nat) : Int :=
  let a : Int := (Nat.log2 p : Int) - (Nat.log2 q : Int)
  if pow2Le a p q then a else a - 1

/-- `10^t ≤ p/q`. -/
def pow10Le (t : Int) (p q : Nat) : Bool :=
  if t ≥ 0 then q * 10 ^ t.toNat ≤ p else q ≤ p * 10 ^ (-t).toNat

def numDigits (n : Nat) : Nat := (toString n).length

/-- `⌊log10 (p/q)⌋` for `p, q > 0`. -/
def floorLog10 (p q : Nat) : Int :=
  let a : Int := (numDigits p : Int) - (numDigits q : Int)
  -- the true value is a-1 or a (p ∈ [10^(dp-1), 10^dp), q likewise)
  if pow10Le a p q then a else a - 1

/-- Round `a / b` to the nearest natural, ties to even. -/
def roundHalfEven (a b : Nat) : Nat :=
  let q := a / b
  let r := a % b
  if 2 * r > b then q + 1 else if 2 * r == b then (if q % 2 == 1 then q + 1 else q) else q

/-- The double nearest to `p / q` (q > 0), ties to even, with subnormals and overflow to
infinity; `neg` sets the sign. This is the correctly rounded conversion C++ (Clang's APFloat,
`std::from_chars`) performs for a decimal floating literal. -/
def ofRat (neg : Bool) (p q : Nat) : UInt64 :=
  let sign : UInt64 := if neg then 0x8000000000000000 else 0
  if p == 0 then sign
  else
    let t := floorLog2 p q
    let e0 : Int := max (t - 52) (-1074)
    -- p / (q · 2^e0)
    let (num, den) := if e0 ≥ 0 then (p, q * 2 ^ e0.toNat) else (p * 2 ^ (-e0).toNat, q)
    let m := roundHalfEven num den
    let (m, e0) := if m ≥ 2 ^ 53 then (m / 2, e0 + 1) else (m, e0)
    if e0 > 971 then sign ||| 0x7FF0000000000000
    else if m < 2 ^ 52 then sign ||| (UInt64.ofNat m)
    else sign ||| (UInt64.ofNat ((e0 + 1075).toNat) <<< 52) ||| UInt64.ofNat (m - 2 ^ 52)

/-- Does the decimal `c · 10^s` read back as the double with bits `b` (positive part)? -/
def roundTrips (c : Nat) (s : Int) (b : UInt64) : Bool :=
  let (p, q) := if s ≥ 0 then (c * 10 ^ s.toNat, 1) else (c, 10 ^ (-s).toNat)
  ofRat false p q == (b &&& 0x7FFFFFFFFFFFFFFF)

/-- Distance `|c·10^s − p/q|` compared as a fraction with a common denominator. -/
def distNum (c : Nat) (s : Int) (p q : Nat) : Nat × Nat :=
  let (cp, cq) := if s ≥ 0 then (c * 10 ^ s.toNat, 1) else (c, 10 ^ (-s).toNat)
  -- |cp/cq - p/q| = |cp*q - p*cq| / (cq*q)
  let a := cp * q
  let b := p * cq
  ((if a ≥ b then a - b else b - a), cq * q)

def strip (c : Nat) (s : Int) : Nat × Int := Id.run do
  let mut c := c
  let mut s := s
  let mut fuel := 400
  while c != 0 && c % 10 == 0 && fuel > 0 do
    c := c / 10
    s := s + 1
    fuel := fuel - 1
  return (c, s)

/-- The shortest significant digits `c` and scale `s` (value `c · 10^s`) that read back as the
finite, nonzero double `b`; among the shortest, the closest to the value, ties to even
(`std::to_chars`, [charconv.to.chars]: "smallest number of characters ... If there are several
such representations, the representation with the smallest difference to the floating-point
argument value is chosen, resolving any remaining ties using rounding according to
round_to_nearest"). -/
def shortest (b : UInt64) : Nat × Int := Id.run do
  let pr := decode b
  let (p, q) := toRat pr.m pr.e
  let n := floorLog10 p q + 1  -- digits before the point: 10^(n-1) ≤ v < 10^n
  for k in List.range 17 do
    let k := k + 1
    let s : Int := n - k
    -- floor(v / 10^s)
    let (np, nq) := if s ≥ 0 then (p, q * 10 ^ s.toNat) else (p * 10 ^ (-s).toNat, q)
    let lo := np / nq
    let cands := [lo, lo + 1].filter fun c => c != 0 && roundTrips c s b
    match cands with
    | [] => pure ()
    | [c] => return strip c s
    | c1 :: c2 :: _ =>
      let (d1, e1) := distNum c1 s p q
      let (d2, e2) := distNum c2 s p q
      -- same denominators
      let _ := e2
      let c := if d1 * e2 < d2 * e1 then c1 else if d2 * e1 < d1 * e2 then c2
               else (if c1 % 2 == 0 then c1 else c2)
      return strip c s
  -- 17 significant digits always round-trip; not reached.
  return strip (p / q) 0

def zeros (n : Nat) : String := String.ofList (List.replicate n '0')

/-- The plain (`%f`-style) shortest form of a positive finite double. When the shortest digits
need no fraction (`s ≥ 0`) the double is an integer and every `%f` representation of the minimal
length is an integer string; the closest is the exact value. -/
def fixedForm (b : UInt64) (c : Nat) (s : Int) : String :=
  if s ≥ 0 then
    let pr := decode b
    let (p, q) := toRat pr.m pr.e
    toString (p / q)
  else
    let d := toString c
    let k := d.length
    let n : Int := k + s
    if n > 0 then
      String.ofList (d.toList.take n.toNat) ++ "." ++ String.ofList (d.toList.drop n.toNat)
    else "0." ++ zeros (-n).toNat ++ d

/-- The scientific (`%e`-style) shortest form: `d[.ddd]e±XX`, at least two exponent digits. -/
def sciForm (c : Nat) (s : Int) : String :=
  let d := toString c
  let k := d.length
  let x : Int := k - 1 + s
  let mant := if k > 1 then String.ofList (d.toList.take 1) ++ "." ++ String.ofList (d.toList.drop 1)
              else d
  let ex := toString x.natAbs
  let ex := if ex.length < 2 then "0" ++ ex else ex
  mant ++ "e" ++ (if x < 0 then "-" else "+") ++ ex

/-- `std::to_chars(first, last, value)` for a finite double: `%f` or `%e` style, whichever is
shorter, a tie going to `%f` ([charconv.to.chars]/2). Zero prints `0` / `-0`. -/
def toChars (b : UInt64) : String :=
  let sign := if signBit b then "-" else ""
  if (b &&& 0x7FFFFFFFFFFFFFFF) == 0 then sign ++ "0"
  else
    let (c, s) := shortest b
    let f := fixedForm b c s
    let e := sciForm c s
    sign ++ (if f.length ≤ e.length then f else e)

/-- `string_builder::operator()(double)` (string_builder.cpp:83-137). -/
def sbF64 (b : UInt64) : String :=
  if isInf b then (if signBit b then "-INFINITY" else "INFINITY")
  else if isNaN b then "NAN"
  else
    let t := toChars b
    if t.contains '.' || t.contains 'e' then t else t ++ ".0"

/-! ## Reading the text back as C++ -/

/-- A C++ decimal floating literal `digits [. digits] [e|E [+|-] digits]` (or an integer literal,
converted to double), correctly rounded; `none` when the text is not one. -/
def parseDecimal (s : List Char) : Option UInt64 := Id.run do
  let digs := s.takeWhile Char.isDigit
  let r := s.drop digs.length
  let (frac, r) := match r with
    | '.' :: q => let f := q.takeWhile Char.isDigit; (f, q.drop f.length)
    | q => ([], q)
  if digs.isEmpty && frac.isEmpty then return none
  let (ex, r) : Int × List Char := match r with
    | c :: q =>
      if c == 'e' || c == 'E' then
        let (neg, q) := match q with | '-' :: q => (true, q) | '+' :: q => (false, q) | q => (false, q)
        let ed := q.takeWhile Char.isDigit
        if ed.isEmpty then ((0 : Int), c :: q)  -- malformed; reported below by the leftover
        else
          let v : Nat := ed.foldl (fun a ch => a * 10 + (ch.toNat - 48)) 0
          ((if neg then -(v : Int) else v), q.drop ed.length)
      else (0, c :: q)
    | [] => (0, [])
  if !r.isEmpty then return none
  let mant : Nat := (digs ++ frac).foldl (fun a ch => a * 10 + (ch.toNat - 48)) 0
  let s10 : Int := ex - frac.length
  let (p, q) := if s10 ≥ 0 then (mant * 10 ^ s10.toNat, 1) else (mant, 10 ^ (-s10).toNat)
  return some (ofRat false p q)

/-- `<cmath>`'s `INFINITY` (a float `+inf`) and `NAN` (a quiet NaN, sign clear) as doubles. -/
def cInfinity : UInt64 := 0x7FF0000000000000
def cNan : UInt64 := 0x7FF8000000000000

/-- The double a C++ expression jank prints for a double denotes: an optional unary `-`, then
`INFINITY`, `NAN` or a floating literal. -/
def cppMeaning (t : String) : Option UInt64 :=
  let (neg, body) := match t.toList with
    | '-' :: r => (true, r)
    | r => (false, r)
  let v := if body == "INFINITY".toList then some cInfinity
    else if body == "NAN".toList then some cNan
    else parseDecimal body
  v.map fun x => if neg then x ^^^ 0x8000000000000000 else x

/-- What the double means to Clojure, for comparing: NaNs are all one value (`##NaN`), every
other double by its bits (so `-0.0` and `0.0` differ, as `(str -0.0)` shows). -/
def sameDouble (a b : UInt64) : Bool :=
  if isNaN a && isNaN b then true else a == b

end Jank.Codegen.Float
