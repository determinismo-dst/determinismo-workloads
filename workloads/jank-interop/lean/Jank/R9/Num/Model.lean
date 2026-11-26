/-!
# Round 9, area N (numbers): models of this round's fixes and of what they replace

jank main 94d32623 (`upstream-r5/compiler+runtime/`). Each definition names the C++ or Java it mirrors.

* Doubles are IEEE-754 bit patterns (`BitVec 64`), as oref.hpp stores them (NaN boxing: a word is a
  real only below `max_real` = 0xFFF8000000000000, oref.hpp 94 and 113).
* `Dec` is R72's `native_big_decimal` (round 8's `fixes/R72.diff`: an unscaled integer and a scale),
  with precision 0 (no `*math-context*` rounding).
* Integers are `Int` with the i64 range checked explicitly, as `__builtin_*_overflow` does.
-/
namespace Jank.R9.Num

/-! ## Doubles (DEC8-1's negation, D9's boxable words) -/

/-- oref.hpp `max_real`: a word below it is a NaN-boxed real. -/
def maxReal : BitVec 64 := 0xFFF8000000000000#64
def signBit : BitVec 64 := 0x8000000000000000#64
def expMask : BitVec 64 := 0x7FF0000000000000#64
def fracMask : BitVec 64 := 0x000FFFFFFFFFFFFF#64

/-- IEEE-754: all exponent bits set and a nonzero fraction. -/
def isNaN64 (x : BitVec 64) : Bool := (x &&& expMask) == expMask && (x &&& fracMask) != 0#64

/-- Java's `-x` on a double (`dneg`, DoubleOps.negate): the sign bit flipped, NaN included. -/
def cljNegBits (x : BitVec 64) : BitVec 64 := x ^^^ signBit

/-- DEC8-1's math.cpp `negate_number` on a `real`/`small_real`: a NaN is returned as it is (a
    flipped quiet NaN is D9's unboxable word on x86-64), anything else is `-data`. -/
def fixNegBits (x : BitVec 64) : BitVec 64 := if isNaN64 x then x else x ^^^ signBit

/-- jank's `##NaN` (number.cpp 512, `static_cast<f64>(NAN)`): the positive quiet NaN. -/
def jankNaN : BitVec 64 := 0x7FF8000000000000#64

/-! ## Longs (LongOps.negate / negateP; the stock `(- 0 x)` in C++ `int` and `i64`) -/

def i64min : Int := -9223372036854775808
def i64max : Int := 9223372036854775807
def i32min : Int := -2147483648
def i32max : Int := 2147483647

inductive NegResult where
  | long (v : Int)
  | bigint (v : Int)
  | throws
  deriving DecidableEq, Repr

/-- Numbers.java LongOps.negate (`promote = false`) and negateP (`promote = true`). -/
def cljNegLong (promote : Bool) (x : Int) : NegResult :=
  if x > i64min then .long (-x) else if promote then .bigint (-x) else .throws

/-- DEC8-1: math.cpp `negate_number` on an `integer` box (i64 data). -/
def fixNegInteger (promote : Bool) (x : Int) : NegResult :=
  if x = i64min then (if promote then .bigint (-x) else .throws) else .long (-x)

/-- DEC8-1 on a `small_integer` box (i32 data): `-static_cast<i64>(data)`. -/
def fixNegSmall (x : Int) : NegResult := .long (-x)

/-- Two's complement wrap to `bits` bits (C++ `-fwrapv`). -/
def wrap (bits : Nat) (v : Int) : Int := (v + 2 ^ (bits - 1)) % 2 ^ bits - 2 ^ (bits - 1)

/-- Stock `(- x)` = `(- 0 x)` = math.hpp `sub(int 0, object)`: `make_box(l - typed_r->data)`, computed
    in C++ `int` for a `small_integer` (i32 data) and in `long` for an `integer` (i64 data). -/
def stockNegSmall (x : Int) : NegResult := .long (wrap 32 (0 - x))
def stockNegInteger (x : Int) : NegResult := .long (wrap 64 (0 - x))

/-! ## BigDecimal (R72's representation) -/

structure Dec where
  u : Int
  s : Int
  deriving DecidableEq, Repr

/-- R72's `exact_add` (impl.inc 168-173): align on the larger scale. -/
def exactAdd (l r : Dec) : Dec :=
  let S := max l.s r.s
  ⟨l.u * 10 ^ (S - l.s).toNat + r.u * 10 ^ (S - r.s).toNat, S⟩

def exactMul (l r : Dec) : Dec := ⟨l.u * r.u, l.s + r.s⟩

/-- R72's `decimal::negate` at precision 0 (BigDecimal.negate): the scale is kept. -/
def negDec (x : Dec) : Dec := ⟨-x.u, x.s⟩

/-- R72's binary minus (Numbers.minus: add(l, negate(r))). -/
def exactSub (l r : Dec) : Dec := exactAdd l (negDec r)

/-- The stock definition `(- x)` = `(- 0 x)` on R72's class: `0 - x`, i.e. add(0, negate(x)). -/
def stockNegDec (x : Dec) : Dec := exactSub ⟨0, 0⟩ x

/-- Value comparison of two decimals (BigDecimal.compareTo), by cross-scaling. -/
def cmpDec (l r : Dec) : Ordering :=
  let S := max l.s r.s
  compare (l.u * 10 ^ (S - l.s).toNat) (r.u * 10 ^ (S - r.s).toNat)

/-! ## R72f: Java's intCompact as a fast path (.r9-scratch/num/bench/fast.inc) -/

def inI64 (x : Int) : Bool := decide (i64min ≤ x) && decide (x ≤ i64max)

/-- fast.inc `mul_pow10`: `v * 10^n` when it fits an i64 (`__builtin_mul_overflow`), 0 for 0. -/
def mulPow10? (v : Int) (n : Nat) : Option Int :=
  if v = 0 then some 0
  else if n > 18 then none
  else if inI64 (v * 10 ^ n) then some (v * 10 ^ n) else none

def fastAdd (l r : Dec) : Option Dec :=
  if inI64 l.u && inI64 r.u then
    let S := max l.s r.s
    match mulPow10? l.u (S - l.s).toNat, mulPow10? r.u (S - r.s).toNat with
    | some x, some y => if inI64 (x + y) then some ⟨x + y, S⟩ else none
    | _, _ => none
  else none

def fastSub (l r : Dec) : Option Dec :=
  if inI64 l.u && inI64 r.u then
    let S := max l.s r.s
    match mulPow10? l.u (S - l.s).toNat, mulPow10? r.u (S - r.s).toNat with
    | some x, some y => if inI64 (x - y) then some ⟨x - y, S⟩ else none
    | _, _ => none
  else none

def fastMul (l r : Dec) : Option Dec :=
  if inI64 l.u && inI64 r.u && inI64 (l.u * r.u) then some ⟨l.u * r.u, l.s + r.s⟩ else none

def fastCmp (l r : Dec) : Option Ordering :=
  if inI64 l.u && inI64 r.u then
    let S := max l.s r.s
    match mulPow10? l.u (S - l.s).toNat, mulPow10? r.u (S - r.s).toNat with
    | some x, some y => some (compare x y)
    | _, _ => none
  else none

/-- The fast path in front of the general one, as fast.inc's operators use it. -/
def withFast {α} (fast : Option α) (general : α) : α := fast.getD general

/-! ## Float rounding (V62: RT.floatCast's `(float) n`) -/

/-- `n / 2^k` rounded to the nearest integer, ties to even (IEEE-754 roundTiesToEven). -/
def rne (n k : Nat) : Nat :=
  let d := 2 ^ k
  let q := n / d
  let r := n % d
  if 2 * r > d ∨ (2 * r = d ∧ q % 2 = 1) then q + 1 else q

def dist (a b : Nat) : Nat := if a ≥ b then a - b else b - a

/-- The bit length of `n` (0 for 0). -/
def bitLen (n : Nat) : Nat := if n = 0 then 0 else Nat.log2 n + 1

/-- A finite double's sign, integer significand and exponent: value = (-1)^s · m · 2^e. -/
structure DecodedD where
  neg : Bool
  m : Nat
  e : Int

/-- IEEE-754 binary64 decoding (finite values; `none` for NaN and the infinities). -/
def decodeD (x : BitVec 64) : Option DecodedD :=
  let E := ((x >>> 52) &&& 0x7FF#64).toNat
  let F := (x &&& fracMask).toNat
  let neg := x.getMsbD 0
  if E = 2047 then none
  else if E = 0 then some ⟨neg, F, -1074⟩
  else some ⟨neg, F + 2 ^ 52, (E : Int) - 1075⟩

/-- Float.MAX_VALUE = (2^24 - 1) · 2^104. -/
def floatMax : Nat := (2 ^ 24 - 1) * 2 ^ 104

/-- `|m · 2^e| > Float.MAX_VALUE`, exactly (RT.floatCast's range check compares doubles; the
    double and Float.MAX_VALUE are both exact here). -/
def aboveFloatMax (m : Nat) (e : Int) : Bool :=
  if e ≥ 0 then decide (m * 2 ^ e.toNat > floatMax)
  else decide (m > floatMax * 2 ^ (-e).toNat)

/-- The model of V62's `float_cast` (RT.floatCast): `none` when it throws, else the float's bits
    (Float.floatToRawIntBits). Rounding is `rne`; subnormals are multiples of 2^-149. -/
def floatCastBits (x : BitVec 64) : Option (BitVec 32) :=
  if isNaN64 x then
    -- (float) of a NaN: the quiet NaN of the same sign and top fraction bits.
    let s : Nat := if x.getMsbD 0 then 2 ^ 31 else 0
    let top := ((x &&& fracMask) >>> 29).toNat
    some (BitVec.ofNat 32 (s + 0x7F800000 + top ||| 0x400000))
  else match decodeD x with
  | none => none  -- an infinity is out of range
  | some ⟨neg, m, e⟩ =>
    let s : Nat := if neg then 2 ^ 31 else 0
    if m = 0 then some (BitVec.ofNat 32 s)
    else if aboveFloatMax m e then none
    else
      -- the value lies in [2^p, 2^(p+1)), p = bitLen m - 1 + e
      let p : Int := (bitLen m : Int) - 1 + e
      if p ≥ -126 then
        -- normal: keep 24 bits; k is how many low bits of m are rounded away
        let k : Int := (bitLen m : Int) - 24
        let q : Nat := if k ≥ 0 then rne m k.toNat else m * 2 ^ (-k).toNat
        some (BitVec.ofNat 32 (s + (((p + 127).toNat) * 2 ^ 23 + q - 2 ^ 23)))
      else
        -- subnormal (or rounding up to the least normal): a multiple of 2^-149
        let k : Int := -149 - e
        let q : Nat := if k ≥ 0 then rne m k.toNat else m * 2 ^ (-k).toNat
        some (BitVec.ofNat 32 (s + q))

/-! ## V60: RT.longCast(double) -/

/-- The model of V60's `long_cast`: NaN is 0; outside [-2^63, 2^63] it throws (`none`); 2^63
    saturates to Long.MAX_VALUE; else truncation toward zero. -/
def longCastBits (x : BitVec 64) : Option Int :=
  if isNaN64 x then some 0
  else match decodeD x with
  | none => none
  | some ⟨neg, m, e⟩ =>
    -- magnitude, truncated toward zero, and whether it exceeds 2^63
    let mag : Nat := if e ≥ 0 then m * 2 ^ e.toNat else m / 2 ^ (-e).toNat
    let exact : Bool := if e ≥ 0 then true else m % 2 ^ (-e).toNat == 0
    let above : Bool := decide (mag > 2 ^ 63) || (decide (mag = 2 ^ 63) && !exact)
    if above then none
    else if mag = 2 ^ 63 then some (if neg then i64min else i64max)
    else some (if neg then -(mag : Int) else mag)

/-- Stock jank's `long` of a double on x86-64 (`static_cast<i64>`, cvttsd2si): truncation when the
    result fits, else the integer indefinite 0x8000000000000000; NaN is 0 (number.cpp 358-366). -/
def stockLongBits (x : BitVec 64) : Int :=
  if isNaN64 x then 0
  else match decodeD x with
  | none => i64min
  | some ⟨neg, m, e⟩ =>
    let mag : Nat := if e ≥ 0 then m * 2 ^ e.toNat else m / 2 ^ (-e).toNat
    let v : Int := if neg then -(mag : Int) else mag
    if i64min ≤ v ∧ v ≤ i64max then v else i64min

end Jank.R9.Num
