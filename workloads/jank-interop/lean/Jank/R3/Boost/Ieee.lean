import Jank.Codegen.Float

/-!
# Round 3, Boost: IEEE-754 doubles as the C++ code handles them

boost's `cpp_dec_float` and `cpp_int` code converts to and from `double` (`frexp`, `ldexp`,
`floor`, casts, a `std::stringstream >> double`). Lean's `Float` is the IEEE-754 binary64 type
and its operations (`+ - * /`, `floor`, `frExp`, `scaleB`) call the C library, as the C++ does,
so the replicas use `Float` for the double arithmetic boost performs, and exact integer
arithmetic (`Jank.Codegen.Float.ofRat`, correctly rounded) where the C library parses text.
-/

namespace Jank.R3.Boost.Ieee

open Jank.Codegen.Float (ofRat decode)

/-- `strtod` (glibc, C locale) of a decimal `(-1)^neg · mant · 10^exp10`: the nearest double,
ties to even, with overflow to infinity and gradual underflow (glibc's `strtod` rounds
correctly; `std::stringstream >> double` calls it through `num_get`). -/
def strtodDec (neg : Bool) (mant : Nat) (exp10 : Int) : Float :=
  let (p, q) := if exp10 ≥ 0 then (mant * 10 ^ exp10.toNat, 1) else (mant, 10 ^ (-exp10).toNat)
  Float.ofBits (ofRat neg p q)

/-- The exact value of a finite double as a rational `num / den` with its sign. -/
def exact (x : Float) : Bool × Nat × Nat :=
  let pr := decode x.toBits
  let (p, q) := Jank.Codegen.Float.toRat pr.m pr.e
  (pr.neg, p, q)

def isFinite (x : Float) : Bool := !(x.isNaN || x.isInf)

/-- The nearest double to an exact rational (`p / q`, `q > 0`), ties to even. -/
def ofRatF (neg : Bool) (p q : Nat) : Float := Float.ofBits (ofRat neg p q)

/-- The nearest double to an integer, ties to even (Java's `long → double`, `BigInteger.doubleValue`). -/
def ofIntRN (v : Int) : Float := ofRatF (v < 0) v.natAbs 1

/-- `DBL_MIN`, `DBL_MAX`, `DBL_EPSILON`. -/
def dblMin : Float := Float.ofBits 0x0010000000000000
def dblMax : Float := Float.ofBits 0x7FEFFFFFFFFFFFFF
def dblEps : Float := Float.ofBits 0x3CB0000000000000

/-- `static_cast<std::uint64_t>(d)` for `0 ≤ d < 2^64` (truncation). -/
def toU64 (d : Float) : Nat := d.toUInt64.toNat

/-- A double's text as Java's `Double.toString` would compute its digits is in
`Jank.PrintModel`; here only its value matters. -/
def showF (x : Float) : String :=
  if x.isNaN then "NaN" else if x.isInf then (if x < 0 then "-Infinity" else "Infinity")
  else
    let (n, p, q) := exact x
    let (c, s) := if p == 0 then (0, (0 : Int)) else Jank.Codegen.Float.shortest (x.abs.toBits)
    let _ := q
    let body := if c == 0 then "0.0" else s!"{c}e{s}"
    (if n then "-" else "") ++ body

end Jank.R3.Boost.Ieee
