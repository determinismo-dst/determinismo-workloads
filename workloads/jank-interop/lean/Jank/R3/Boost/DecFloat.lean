import Jank.R3.Boost.CppInt

/-!
# Round 3, Boost: `cpp_dec_float<100>` as jank uses it

jank's `native_big_decimal` is `number<cpp_dec_float<100>, et_off>` (include/cpp/jank/type.hpp:35).
With `Digits10 = 100`, `ExponentType = std::int32_t`, `Allocator = void` (fwd.hpp:98): 16 limbs
of 8 decimal digits (`cpp_dec_float_elem_number = 100/8 + 1 + 3`, cpp_dec_float.hpp:120), most
significant first; the value is `Σ data[i] · 10^(exp − 8i)` with `exp` a multiple of 8 and
`0 < data[0] < 10^8` when nonzero; `max_exp10 = 2^26` (cpp_dec_float.hpp:106); `prec_elem` limits
how many limbs a multiplication reads.

Every function below is a line-by-line replica of deps/boost-multiprecision (2b3ab082)
include/boost/multiprecision/cpp_dec_float.hpp (and detail/number_base.hpp,
detail/default_ops.hpp, detail/generic_interconvert.hpp, detail/functions/pow.hpp where named).
C++ `/` and `%` on signed values truncate (`Int.tdiv`, `Int.tmod`).
-/

namespace Jank.R3.Boost.Dec

open Jank.R3.Boost

def elemDigits : Nat := 8
def mask : Nat := 100000000
def elemNumber : Nat := 16
def maxDigits10 : Nat := 128
def maxExp10 : Int := 67108864
def minExp10 : Int := -67108864

inductive FpClass where
  | finite | inf | nan
  deriving BEq, Repr, Inhabited

structure CDF where
  data : Array Nat
  exp : Int
  neg : Bool
  fpclass : FpClass
  precElem : Nat
  deriving BEq, Repr, Inhabited

/-- int32 wrap-around (a cast of a wider value to `exponent_type`). -/
def wrap32 (v : Int) : Int :=
  let m := v % 4294967296
  if m ≥ 2147483648 then m - 4294967296 else m

def zeros (n : Nat) : Array Nat := Array.replicate n 0

/-- `from_lst(lst, e, n)` (cpp_dec_float.hpp:153-166): the rest of the array is zero. -/
def fromLst (lst : List Nat) (e : Int := 0) (n : Bool := false) : CDF :=
  { data := (lst ++ List.replicate (elemNumber - lst.length) 0).toArray, exp := e, neg := n,
    fpclass := .finite, precElem := elemNumber }

def zero : CDF := fromLst [0]
def one : CDF := fromLst [1]
def two : CDF := fromLst [2]
def half : CDF := fromLst [mask / 2] (-8)
def nanV : CDF := { data := zeros 16, exp := 0, neg := false, fpclass := .nan, precElem := 16 }
def infV : CDF := { data := zeros 16, exp := 0, neg := false, fpclass := .inf, precElem := 16 }
def maxV : CDF := fromLst [1] maxExp10
def minV : CDF := fromLst [1] minExp10
/-- `eps()` (cpp_dec_float.hpp:305-319): 10^(1 + 13·8 − 100) at exponent −104, i.e. 10^-99. -/
def eps : CDF := fromLst [100000] (-104)

def CDF.d (x : CDF) (i : Nat) : Nat := x.data.getD i 0
def CDF.isnan (x : CDF) : Bool := x.fpclass == .nan
def CDF.isinf (x : CDF) : Bool := x.fpclass == .inf
def CDF.isfinite (x : CDF) : Bool := x.fpclass == .finite
def CDF.iszero (x : CDF) : Bool := x.fpclass == .finite && x.d 0 == 0

/-- `negate()` (433): zero keeps its sign. -/
def CDF.negate (x : CDF) : CDF := if x.iszero then x else { x with neg := !x.neg }

/-- `from_unsigned_long_long` (2519-2552). -/
def fromULL (u : Nat) : CDF := Id.run do
  let mut x : CDF := { data := zeros 16, exp := 0, neg := false, fpclass := .finite, precElem := 16 }
  if u == 0 then return x
  let mut temp : Array Nat := #[]
  let mut uu := u
  while uu != 0 do
    temp := temp.push (uu % mask)
    uu := uu / mask
  let i := temp.size
  if i > 1 then x := { x with exp := ((i - 1) * elemDigits : Nat) }
  let rev := temp.reverse
  let mut data := x.data
  for k in [0:min i elemNumber] do
    data := data.set! k rev[k]!
  return { x with data := data }

/-- `operator=(long long)` (345-359) and the signed constructor (198-215). -/
def ofLL (v : Int) : CDF := if v < 0 then (fromULL v.natAbs).negate else fromULL v.toNat

/-- `compare_ranges(a, b, count)` (2556-2585). -/
def compareRanges (a b : Array Nat) (count : Nat := elemNumber) : Int := Id.run do
  for i in [0:count] do
    let l := a.getD i 0
    let r := b.getD i 0
    if l != r then return (if l > r then 1 else -1)
  return 0

/-- `compare(v)` (1377-1460). -/
def CDF.compare (u v : CDF) : Int :=
  if !u.isfinite || !v.isfinite then
    if u.isnan || v.isnan then (if u.isnan then 1 else -1)
    else if u.isinf && v.isinf then (if u.neg == v.neg then 0 else if u.neg then -1 else 1)
    else if u.isinf then (if u.neg then -1 else 1)
    else (if v.neg then 1 else -1)
  else if u.iszero then (if v.iszero then 0 else if v.neg then 1 else -1)
  else if v.iszero then (if u.neg then -1 else 1)
  else if u.neg != v.neg then (if u.neg then -1 else 1)
  else if u.exp != v.exp then
    let c : Int := if u.exp < v.exp then 1 else -1
    if u.neg then c else -c
  else
    let c := compareRanges u.data v.data
    if !u.neg then c else -c

/-- `eval_add_n` (2587-2605): returns the carry and `u + v` limb by limb. -/
def addN (u v : Array Nat) (count : Nat) : Nat × Array Nat := Id.run do
  let mut r := u
  let mut carry := 0
  let mut j := count
  while j > 0 do
    j := j - 1
    let t := u.getD j 0 + v.getD j 0 + carry
    carry := if t ≥ mask then 1 else 0
    r := r.set! j (if carry != 0 then t - mask else t)
  return (carry, r)

/-- `eval_subtract_n` (2607-2634). -/
def subN (u v : Array Nat) (count : Nat) : Nat × Array Nat := Id.run do
  let mut r := u
  let mut borrow : Int := 0
  let mut j := count
  while j > 0 do
    j := j - 1
    let mut t : Int := (u.getD j 0 : Int) - (v.getD j 0 : Int) - borrow
    if t < 0 then t := t + mask; borrow := 1 else borrow := 0
    r := r.set! j t.toNat
  return (borrow.toNat, r)

/-- `[0]*k ++ a[0 .. 16−k)`: a limb array shifted down by `k` limbs (the low limbs are lost). -/
def shiftDown (a : Array Nat) (k : Nat) : Array Nat :=
  (zeros k ++ a.extract 0 (elemNumber - k)).extract 0 elemNumber

/-- `operator+=` (758-937). -/
def CDF.add (u v : CDF) : CDF := Id.run do
  if u.isnan then return u
  if u.isinf then
    if v.isinf && u.neg != v.neg then return nanV
    return u
  if u.iszero then return v
  if v.isnan || v.isinf then return v
  let maxDelta : Int := ((elemNumber - 1) * elemDigits : Nat)
  let ofsExp := u.exp - v.exp
  if v.iszero || ofsExp > maxDelta then return u
  if ofsExp < -maxDelta then return v
  let ofs : Int := Int.tdiv ofsExp elemDigits
  let mut x := u
  if u.neg == v.neg then
    if ofs ≥ 0 then
      let nData := shiftDown v.data ofs.toNat
      let (carry, r) := addN x.data nData elemNumber
      x := { x with data := r }
      if carry != 0 then
        x := { x with data := (#[carry] ++ x.data.extract 0 (elemNumber - 1)), exp := x.exp + elemDigits }
    else
      let nData := shiftDown x.data (-ofs).toNat
      let (carry, r) := addN nData v.data elemNumber
      x := { x with data := r, exp := v.exp }
      if carry != 0 then
        x := { x with data := (#[carry] ++ x.data.extract 0 (elemNumber - 1)), exp := x.exp + elemDigits }
  else
    if ofs > 0 || (ofs == 0 && compareRanges x.data v.data > 0) then
      let nData := shiftDown v.data ofs.toNat
      let (_, r) := subN x.data nData elemNumber
      x := { x with data := r }
    else
      let uData := if ofs != 0 then shiftDown x.data (-ofs).toNat else x.data
      let (_, r) := subN v.data uData elemNumber
      x := { x with data := r, exp := v.exp, neg := v.neg }
    -- Justify.
    match (List.range elemNumber).find? (fun i => x.d i != 0) with
    | none => x := { x with neg := false, exp := 0 }
    | some sj =>
      if sj != 0 then
        x := { x with data := (x.data.extract sj elemNumber ++ zeros sj),
                      exp := x.exp - (sj * elemDigits : Nat) }
  if x.iszero then return zero
  if x.exp ≥ maxExp10 then
    let n := x.neg
    let y := { x with neg := false }
    if y.compare maxV > 0 then return { infV with neg := n }
    return x
  return x

/-- `operator-=` (940-948): `*this − v = −(−*this + v)`. -/
def CDF.sub (u v : CDF) : CDF := ((u.negate).add v).negate

/-- `eval_multiply_n_by_n_to_2n` (2636-2676): the 2n-limb schoolbook product of the first `n`
limbs of `a` and `b`, written from the least significant limb up. -/
def mulN (a b : Array Nat) (n : Nat) : Array Nat := Id.run do
  let mut r : Array Nat := zeros (2 * n)
  let mut ir := 2 * n  -- the next index written is ir - 1
  let mut carry := 0
  let mut j := n - 1
  while j ≥ 1 do
    let mut sum := carry
    let mut i := n - 1
    while i ≥ j do
      sum := sum + a.getD i 0 * b.getD ((n - 1) - (i - j)) 0
      if i == 0 then break
      i := i - 1
    carry := sum / mask
    ir := ir - 1
    r := r.set! ir (sum - carry * mask)
    j := j - 1
  let mut jj : Int := (n : Int) - 1
  while jj ≥ 0 do
    let mut sum := carry
    let mut i : Int := jj
    while i ≥ 0 do
      sum := sum + a.getD (jj - i).toNat 0 * b.getD i.toNat 0
      i := i - 1
    carry := sum / mask
    ir := ir - 1
    r := r.set! ir (sum - carry * mask)
    jj := jj - 1
  ir := ir - 1
  r := r.set! ir carry
  return r

/-- `eval_mul_dispatch_multiplication_method` (school branch, 609-643): only the first
`prec` limbs of `data` are written. -/
def mulDispatch (x : CDF) (v : CDF) (prec : Nat) : CDF := Id.run do
  let result := mulN x.data v.data prec
  let mut data := x.data
  let mut exp := x.exp
  if result.getD 0 0 != 0 then
    exp := exp + elemDigits
    for k in [0:prec] do data := data.set! k (result.getD k 0)
  else
    for k in [0:min prec elemNumber] do data := data.set! k (result.getD (k + 1) 0)
  return { x with data := data, exp := exp }

/-- `operator*=` (950-1012). -/
def CDF.mul (u v : CDF) : CDF := Id.run do
  let resNeg := u.neg != v.neg
  let x0 := { u with neg := false }
  let uInf := x0.isinf
  let vInf := v.isinf
  let uZero := x0.iszero
  let vZero := v.iszero
  if x0.isnan || v.isnan || (uInf && vZero) || (vInf && uZero) then return nanV
  if uInf || vInf then return (if resNeg then infV.negate else infV)
  if uZero || vZero then return zero
  let mightOverflow := x0.exp + v.exp ≥ maxExp10
  let mightUnderflow := x0.exp + v.exp ≤ minExp10
  let x1 := { x0 with exp := x0.exp + v.exp }
  let precMul := min x1.precElem v.precElem
  let mut x := mulDispatch x1 v precMul
  if mightOverflow && x.compare maxV > 0 then x := infV
  if mightUnderflow && x.compare minV < 0 then return zero
  return { x with neg := resNeg }

/-- `isone()` (1463-1484). -/
def CDF.isone (x : CDF) : Bool :=
  if !x.neg && x.isfinite then
    if x.d 0 == 1 && x.exp == 0 then (List.range elemNumber).all fun i => i == 0 || x.d i == 0
    else if x.d 0 == mask - 1 && x.exp == -(elemDigits : Int) then
      (List.range elemNumber).all fun i => x.d i == mask - 1
    else false
  else false

/-- `isint()` (1487-1515). -/
def CDF.isint (x : CDF) : Bool :=
  if x.fpclass != .finite then false
  else if x.iszero then true
  else if x.exp < 0 then false
  else
    let off := (Int.tdiv x.exp elemDigits).toNat + 1
    if off ≥ elemNumber then true
    else (List.range elemNumber).all fun i => i < off || x.d i == 0

/-- `precision(prec_digits)` (496-503). -/
def CDF.precision (x : CDF) (p : Nat) : CDF :=
  let elems := p / elemDigits + (if p % elemDigits != 0 then 1 else 0)
  { x with precElem := min elemNumber (max elems 2) }

/-- `order()` (505-554): the exponent of the leading digit. -/
def CDF.order (x : CDF) : Int :=
  if !x.isfinite || x.d 0 == 0 then 0
  else x.exp + ((Nat.toDigits 10 (x.d 0)).length - 1 : Nat)

/-- `extract_parts(mantissa, exponent)` (1517-1559). -/
def CDF.extractParts (x : CDF) : Float × Int := Id.run do
  let mut exponent := x.exp
  let mut p10 : Nat := 1
  let mut test := x.d 0
  for _ in [0:12] do
    test := test / 10
    if test == 0 then break
    p10 := p10 * 10
    exponent := exponent + 1
  -- max_elem_in_double_count = 15/8 + 1 + 1 = 3.
  let mut mantissa : Float := (x.d 0).toFloat
  let mut scale : Float := 1.0
  for i in [1:3] do
    scale := scale / (mask.toFloat)
    mantissa := mantissa + (x.d i).toFloat * scale
  mantissa := mantissa / p10.toFloat
  if x.neg then mantissa := -mantissa
  return (mantissa, exponent)

/-- `cpp_dec_float(const double mantissa, const exponent_type exponent)` (2402-2455). -/
def ctorDE (mantissa : Float) (exponent : Int) : CDF := Id.run do
  let base : CDF := { data := zeros 16, exp := 0, neg := false, fpclass := .finite, precElem := 16 }
  let tiny := Ieee.dblMin * (1.0 + Ieee.dblEps)
  if mantissa.abs < tiny then return base
  let bNeg := mantissa < 0.0
  let mut d := if !bNeg then mantissa else -mantissa
  let mut e := exponent
  for _ in [0:400] do
    if d > 10.0 then d := d / 10.0; e := e + 1 else break
  for _ in [0:400] do
    if d < 1.0 then d := d * 10.0; e := e - 1 else break
  let mut shift : Int := Int.tmod e elemDigits
  for _ in [0:9] do
    let c := Int.tmod shift elemDigits
    shift := shift - 1
    if c != 0 then d := d * 10.0; e := e - 1 else break
  let mut data := zeros 16
  for i in [0:3] do
    let n := (Ieee.toU64 d) % 4294967296
    data := data.set! i n
    d := d - n.toFloat
    d := d * mask.toFloat
  return { base with data := data, exp := e, neg := bNeg }

/-- `calculate_inv()` (1221-1286). -/
def CDF.calculateInv (x0 : CDF) : CDF := Id.run do
  let bNeg := x0.neg
  let s := { x0 with neg := false }
  if s.iszero then return (if bNeg then infV.negate else infV)
  if s.isnan then return s
  if s.isinf then return zero
  if s.isone then return (if bNeg then s.negate else s)
  let mut x := s
  let (dd, ne) := x.extractParts
  let mut me := ctorDE (1.0 / dd) (-ne)
  let mut digits : Nat := 12
  while digits ≤ maxDigits10 do
    me := me.precision ((digits + 10) * 2)
    x := x.precision ((digits + 10) * 2)
    let mut t := me
    t := t.mul x
    t := t.sub two
    t := t.negate
    me := me.mul t
    digits := digits * 2
  return { me with neg := bNeg, precElem := elemNumber }

/-- `operator/=` (1014-1045). -/
def CDF.div (u v : CDF) : CDF :=
  if u.iszero && v.isnan then v
  else if u.iszero && v.iszero then nanV
  else
    let identical := u.isfinite && u.fpclass == v.fpclass && u.exp == v.exp &&
      compareRanges u.data v.data == 0
    if identical then (if u.neg != v.neg then one.negate else one)
    else u.mul v.calculateInv

/-- `pow_imp(result, t, p, false_type)` (detail/functions/pow.hpp:28-72). -/
def powImp (t : CDF) (p : Nat) : CDF := Id.run do
  let mut result := if p % 2 != 0 then t else fromULL 1
  let mut p2 := p
  let mut x := t
  let mut fuel := 70
  while fuel > 0 do
    fuel := fuel - 1
    p2 := p2 / 2
    if p2 == 0 then break
    x := x.mul x
    if p2 % 2 != 0 then result := result.mul x
  return result

/-- An exact decimal `c · 10^k` (`c` > 0) in the normalized limb form `from_lst` lists use,
truncated past 16 limbs. -/
def ofDecimal (neg : Bool) (c : Nat) (k : Int) : CDF :=
  if c == 0 then zero else
  let len := (Nat.toDigits 10 c).length
  let order : Int := k + len - 1
  let e : Int := (order - (Int.emod order 8))
  -- M = c · 10^(k − e + 120), the 16 limbs below 10^128.
  let sh : Int := k - e + 120
  let m : Nat := if sh ≥ 0 then c * 10 ^ sh.toNat else c / 10 ^ (-sh).toNat
  let data := (List.range 16).map fun i => (m / mask ^ (15 - i)) % mask
  { data := data.toArray, exp := e, neg := neg, fpclass := .finite, precElem := 16 }

/-- `pow2(p)` (2887-3158): the table for −128 ≤ p ≤ 127 holds 2^p exactly (checked against
the header's `from_lst` lines by `pow2TableMatchesHeader` in the driver); otherwise `pow_imp`
of `half()` or `two()`. -/
def pow2 (p : Int) : CDF :=
  if p < -128 then powImp half (-p).toNat
  else if p ≤ 127 then
    if p ≥ 0 then ofDecimal false (2 ^ p.toNat) 0
    else ofDecimal false (5 ^ (-p).toNat) p
  else powImp two p.toNat

/-- `operator=(Float)` (2457-2516): `frexp`, then 30 bits at a time (`shift = int digits − 1`),
then `*this *= pow2(e)`. -/
def ofDouble (a : Float) : CDF := Id.run do
  if a == 0.0 then return zero
  if a == 1.0 then return one
  if a.isInf then return (if a < 0.0 then infV.negate else infV)
  if a.isNaN then return nanV
  let mut x := zero
  let (f0, e0) := a.frExp
  let mut f := f0
  let mut e := e0
  for _ in [0:40] do
    if f == 0.0 then break
    f := Float.scaleB f 30
    let term := f.floor
    e := e - 30
    x := x.mul (pow2 30)
    if term > 0.0 then x := x.add (fromULL (Ieee.toU64 term))
    else x := x.sub (fromULL (Ieee.toU64 (-term)))
    f := f - term
  if e != 0 then x := x.mul (pow2 e)
  return x

/-! ## Strings -/

/-- `std::string::find_first_not_of(set, from)`. -/
def findFirstNotOf (s : List Nat) (set : List Nat) (from_ : Nat) : Option Nat :=
  ((List.range s.length).filter (· ≥ from_)).find? fun i => !set.contains (s.getD i 0)

def digitsSet : List Nat := (List.range 10).map (· + 48)

/-- glibc `atoll`: `strtoll(s, NULL, 10)`, saturating at the `long long` range. -/
def atoll (s : List Nat) : Int := Id.run do
  let mut cs := s.dropWhile fun c => c == 32 || (9 ≤ c && c ≤ 13)
  let mut neg := false
  if cs.head? == some 45 then neg := true; cs := cs.drop 1
  else if cs.head? == some 43 then cs := cs.drop 1
  let ds := cs.takeWhile CppInt.isDec
  let v : Int := ds.foldl (fun acc c => acc * 10 + (c - 48 : Nat)) 0
  let v := if neg then -v else v
  return max CppInt.i64min (min CppInt.i64max v)

/-- `std::stol` of a string of digits (rd_string only passes digits; an empty one throws
`invalid_argument`). -/
def stol (s : List Nat) : Option Nat :=
  if s.isEmpty || !s.all CppInt.isDec then none
  else some (s.foldl (fun acc c => acc * 10 + (c - 48)) 0)

def insertAt (s : List Nat) (i : Nat) (t : List Nat) : List Nat := s.take i ++ t ++ s.drop i
def eraseAt (s : List Nat) (i n : Nat) : List Nat := s.take i ++ s.drop (i + n)
def findC (s : List Nat) (c : Nat) : Option Nat := s.findIdx? (· == c)

def codes (s : String) : List Nat := s.toList.map Char.toNat

/-- The standalone exponent check (2111-2112): after an optional sign, only digits may follow
the `e` at `pos` (`str[pos + 1]` past the end is the terminating NUL). -/
def expPartRejected (str : List Nat) (pos : Nat) : Bool :=
  let nx := str.getD (pos + 1) 0
  let from_ := if nx == 43 || nx == 45 then pos + 2 else pos + 1
  (findFirstNotOf str digitsSet from_).isSome

/-- `rd_string(const char*)` (2084-2394), standalone build (`BOOST_MP_STANDALONE`: the exponent
is checked for digits and read with `std::atoll`). Every exception inside is rethrown as
`Unable to parse the string "…" as a floating point value.` (2380-2389). -/
def rdString (s0 : List Nat) : Except String CDF := Id.run do
  let s1 := CppInt.cstr s0
  let fail : Except String CDF :=
    .error s!"Unable to parse the string \"{String.ofList (s1.map Char.ofNat)}\" as a floating point value."
  let mut x : CDF := { data := zeros 16, exp := 0, neg := false, fpclass := .finite, precElem := 16 }
  let mut str := s1
  let mut exp : Int := 0
  -- The exponent.
  let pe := match findC str 101 with
    | some p => some p
    | none => findC str 69
  if let some pos := pe then
    if expPartRejected str pos then return fail
    exp := wrap32 (atoll (str.drop (pos + 1)))
    str := str.take pos
  -- The sign.
  let mut neg := false
  if !str.isEmpty then
    if str.head! == 45 then neg := true; str := str.drop 1
    else if str.head! == 43 then str := str.drop 1
  if str == codes "inf" || str == codes "INF" || str == codes "infinity" || str == codes "INFINITY" then
    return .ok (if neg then infV.negate else infV)
  if str.length ≥ 3 && (str.take 3 == codes "nan" || str.take 3 == codes "NAN" || str.take 3 == codes "NaN") then
    return .ok nanV
  -- Leading zeros.
  match str.findIdx? (· != 48) with
  | none => if !str.isEmpty then return .ok zero
  | some i => if i != 0 then str := str.drop i
  -- The decimal point.
  match findC str 46 with
  | some pos =>
    if findFirstNotOf str digitsSet 0 != some pos then return fail
    if (findFirstNotOf str digitsSet (pos + 1)).isSome then return fail
    -- Trailing zeros.
    let rev := str.reverse
    match rev.findIdx? (· != 48) with
    | some k => if k != 0 then str := str.take (str.length - k)
    | none => pure ()
    if str == [46] then return .ok zero
    if str.head! == 46 then
      let itNonZero := (str.drop 1).findIdx? (· != 48) |>.map (· + 1) |>.getD str.length
      let deltaExp : Nat := if str.getD 1 0 == 48 then itNonZero - 1 else 0
      str := str.drop itNonZero
      str := insertAt str 1 [46]
      exp := wrap32 (exp - (deltaExp + 1 : Nat))
  | none =>
    if (findFirstNotOf str digitsSet 0).isSome then return fail
    str := str ++ [46]
  -- Shift the point so that the exponent is a multiple of 8.
  let nExpRem : Int := Int.tmod exp elemDigits
  let nShift : Int := if nExpRem != 0 then (if exp < 0 then nExpRem + elemDigits else nExpRem) else 0
  let pos := (findC str 46).getD 0
  let posPlusOne := pos + 1
  if (str.length : Int) - posPlusOne < nShift then
    str := str ++ List.replicate (nShift - ((str.length : Int) - posPlusOne)).toNat 48
  if nShift != 0 then
    str := insertAt str (posPlusOne + nShift.toNat) [46]
    str := eraseAt str pos 1
    exp := wrap32 (exp - nShift)
  -- At most 8 digits before the point.
  let pos := (findC str 46).getD 0
  let posPlusOne := pos + 1
  if pos > elemDigits then
    let nRemIsZero := if pos % elemDigits == 0 then 1 else 0
    let n := pos / elemDigits - nRemIsZero
    str := insertAt str (pos - n * elemDigits) [46]
    str := eraseAt str posPlusOne 1
    exp := wrap32 (exp + (n * elemDigits : Nat))
  -- Pad the decimals to a multiple of 8.
  let pos := (findC str 46).getD 0
  let posPlusOne := pos + 1
  let nDec := str.length - 1 - pos
  let nRem := nDec % elemDigits
  let nCnt := if nRem != 0 then elemDigits - nRem else 0
  if nCnt != 0 then str := str ++ List.replicate nCnt 48
  -- At most 120 decimals.
  let maxDec := (elemNumber - 1) * elemDigits
  if str.length - pos > maxDec then str := str.take (posPlusOne + maxDec)
  -- The limbs.
  let mut data := zeros 16
  match stol (str.take pos) with
  | none => return fail
  | some v => data := data.set! 0 v
  let iEnd := (str.length - posPlusOne) / elemDigits
  for i in [0:iEnd] do
    let chunk := (str.drop (posPlusOne + i * elemDigits)).take elemDigits
    match stol chunk with
    | none => return fail
    | some v => data := data.set! (i + 1) v
  x := { x with data := data, exp := exp, neg := neg }
  if x.exp > maxExp10 then
    x := if neg then infV.negate else infV
  if x.exp ≤ minExp10 then
    if x.exp == minExp10 then
      let test := { x with exp := 0 }
      if test.isone then x := zero
    else x := zero
  return .ok x

/-- I/O flags used by the calls jank makes (`str()`, and `str(18, scientific)` inside
`extract_double`). -/
structure Flags where
  scientific : Bool := false
  fixed : Bool := false
  showpoint : Bool := false
  showpos : Bool := false

/-- number_base.hpp:1394: fixed notation, else scientific. -/
def fixedStyle (f : Flags) (myExp digits : Int) : Bool :=
  f.fixed || (!f.scientific && myExp ≥ -4 && myExp < digits)

/-- `format_float_string(str, my_exp, digits, f, iszero)` (detail/number_base.hpp:1313-1466). -/
def formatFloatString (s0 : List Char) (myExp : Int) (digits0 : Int) (f : Flags) (iszero : Bool) : String := Id.run do
  let mut str := s0
  let neg := str.head? == some '-'
  if neg then str := str.drop 1
  let mut digits := digits0
  if digits == 0 && !f.fixed then digits := max str.length 16
  if iszero || str.isEmpty || str.all (· == '0') then
    str := ['0']
    if f.scientific || f.fixed then
      if f.showpoint || digits > 0 then
        str := str ++ ['.']
        if digits > 0 then str := str ++ List.replicate digits.toNat '0'
      if f.scientific then str := str ++ "e+00".toList
    else
      if f.showpoint then
        str := str ++ ['.']
        if digits > 1 then str := str ++ List.replicate (digits - 1).toNat '0'
    if neg then str := '-' :: str else if f.showpos then str := '+' :: str
    return String.ofList str
  if !f.fixed && !f.scientific && !f.showpoint then
    str := (str.reverse.dropWhile (· == '0')).reverse
    if str.isEmpty then str := ['0']
  else if !f.fixed || myExp ≥ 0 then
    let mut chars : Int := digits - str.length
    if f.scientific then chars := chars + 1
    if chars > 0 then str := str ++ List.replicate chars.toNat '0'
  if fixedStyle f myExp digits then
    if 1 + myExp > str.length then
      str := str ++ List.replicate (1 + myExp - str.length).toNat '0'
      if f.showpoint || (f.fixed && digits > 0) then str := str ++ ['.']
    else if myExp + 1 < str.length then
      if myExp < 0 then
        str := List.replicate (-1 - myExp).toNat '0' ++ str
        str := ['0', '.'] ++ str
      else
        str := str.take (myExp + 1).toNat ++ ['.'] ++ str.drop (myExp + 1).toNat
    else if f.showpoint || (f.fixed && digits > 0) then str := str ++ ['.']
    if f.fixed then
      match str.findIdx? (· == '.') with
      | some p =>
        let l : Int := digits - ((str.length : Int) - (p + 1))
        if l > 0 then str := str ++ List.replicate l.toNat '0'
      | none => pure ()
  else
    if f.showpoint || str.length > 1 then str := str.take 1 ++ ['.'] ++ str.drop 1
    str := str ++ ['e']
    let mut e := (toString myExp.natAbs).toList
    if e.length < 2 then e := List.replicate (2 - e.length) '0' ++ e
    e := (if myExp < 0 then '-' else '+') :: e
    str := str ++ e
  if neg then str := '-' :: str else if f.showpos then str := '+' :: str
  return String.ofList str

def pad8 (n : Nat) : List Char :=
  let s := (toString n).toList
  List.replicate (8 - s.length) '0' ++ s

/-- `str(number_of_digits, f)` (1882-2081) for non-fixed formats (jank calls `str()`, boost's
`extract_double` calls `str(18, scientific)`). -/
def CDF.str (x : CDF) (numberOfDigits0 : Int := 0) (f : Flags := {}) : String := Id.run do
  if x.isinf then
    return if x.neg then "-inf" else if f.showpos then "+inf" else "inf"
  if x.isnan then return "nan"
  let orgDigits := numberOfDigits0
  let mut myExp := x.order
  let mut nd := numberOfDigits0
  if !f.fixed && nd == 0 then nd := maxDigits10
  if f.fixed then nd := nd + myExp + 1
  else if f.scientific then nd := nd + 1
  let nElems := min (nd.toNat / elemDigits + 2) elemNumber
  let mut str : List Char := (toString (x.d 0)).toList
  for i in [1:nElems] do
    str := str ++ pad8 (x.d i)
  -- (number_of_digits == 0 and < 0 occur only for `fixed`.)
  if str.length > nd.toNat then
    let ndn := nd.toNat
    let round := (str.getD ndn '0').toNat - 48
    let mut needRoundUp : Bool := round ≥ 5
    if round == 5 then
      let ix := if ndn == 0 then 0 else (str.getD (ndn - 1) '0').toNat - 48
      if ix % 2 == 0 then
        if (str.drop (ndn + 1)).all (· == '0') then
          let allZeros := (List.range elemNumber).all fun i => i < nElems || x.d i == 0
          if allZeros then needRoundUp := false
    str := str.take ndn
    if needRoundUp then
      if !str.isEmpty then
        let mut arr := str.toArray
        let mut ix := arr.size - 1
        while ix != 0 && arr[ix]! == '9' do
          arr := arr.set! ix '0'
          ix := ix - 1
        if ix == 0 then
          if arr[0]! == '9' then
            arr := arr.set! 0 '1'
            myExp := myExp + 1
          else arr := arr.set! 0 (Char.ofNat (arr[0]!.toNat + 1))
        else arr := arr.set! ix (Char.ofNat (arr[ix]!.toNat + 1))
        str := arr.toList
      else
        str := ['1']; myExp := myExp + 1
  if x.neg then str := '-' :: str
  return formatFloatString str myExp orgDigits f x.iszero

/-! ## Conversions -/

def doubleMin : CDF := ofDouble Ieee.dblMin
def doubleMax : CDF := ofDouble Ieee.dblMax
def llMax : CDF := ofLL CppInt.i64max
def llMin : CDF := ofLL CppInt.i64min

def CDF.abs (x : CDF) : CDF := if x.neg then x.negate else x

/-- `extract_double()` (1562-1601): zero below `double_min()`, infinity above `double_max()`,
else `str(digits10 + 3, scientific)` read back by a `std::stringstream` (glibc `strtod`). -/
def CDF.extractDouble (x : CDF) : Float :=
  if !x.isfinite then
    if x.isnan then (0.0 / 0.0 : Float) else (if !x.neg then (1.0/0.0 : Float) else (-1.0/0.0 : Float))
  else
    let xx := x.abs
    if x.iszero || xx.compare doubleMin < 0 then 0.0
    else if xx.compare doubleMax > 0 then (if !x.neg then (1.0/0.0 : Float) else (-1.0/0.0 : Float))
    else
      let s := x.str 18 { scientific := true }
      -- "[-]d.dddddddddddddddddde±XX": 19 significant digits.
      let cs := s.toList
      let neg := cs.head? == some '-'
      let body := if neg then cs.drop 1 else cs
      let (mant, rest) := body.span (· != 'e')
      let ds := mant.filter (· != '.')
      let m : Nat := ds.foldl (fun a c => a * 10 + (c.toNat - 48)) 0
      let ecs := rest.drop 1
      let eneg := ecs.head? == some '-'
      let ev : Nat := (ecs.drop 1).foldl (fun a c => a * 10 + (c.toNat - 48)) 0
      let e10 : Int := (if eneg then -(ev : Int) else ev) - (ds.length - 1 : Nat)
      Ieee.strtodDec neg m e10

/-- `extract_integer_part()` (1850-1880). -/
def CDF.extractIntegerPart (x : CDF) : CDF :=
  if !x.isfinite then x
  else if x.exp < 0 then zero
  else
    let firstClear := (Int.tdiv x.exp elemDigits).toNat + 1
    if firstClear < elemNumber then
      { x with data := x.data.extract 0 firstClear ++ zeros (elemNumber - firstClear) }
    else x

/-- `extract_signed_long_long()` (1677-1720): truncation, saturating at the `long long` range. -/
def CDF.extractSignedLL (x : CDF) : Int := Id.run do
  if x.exp < 0 then return 0
  let bNeg := x.neg
  if !bNeg && x.compare llMax > 0 then return CppInt.i64max
  if bNeg && x.compare llMin < 0 then return CppInt.i64min
  let mut xn := x.extractIntegerPart
  if xn.neg then xn := xn.negate
  let mut v : Nat := xn.d 0
  let imax := min (Int.tdiv xn.exp elemDigits).toNat (elemNumber - 1)
  for i in [1:imax + 1] do
    v := (v * mask + xn.d i) % 2 ^ 64
  if !bNeg then return (BitVec.ofNat 64 v).toInt
  else return -(v : Int)

/-- `hash()` (259-266) with boost's `hash_combine` (detail/hash.hpp:36-42): `std::hash` of a
`uint32_t` limb, of the `int` exponent (sign-extended to `size_t`), of `bool` and of
`size_t` are the identity (libstdc++). -/
def CDF.hash (x : CDF) : UInt64 := Id.run do
  let comb := fun (seed h : UInt64) => seed ^^^ (h + (0x9e3779b9 : UInt64) + (seed <<< 6) + (seed >>> 2))
  let mut r : UInt64 := 0
  for i in [0:x.precElem] do r := comb r (UInt64.ofNat (x.d i))
  r := comb r (UInt64.ofInt x.exp)
  r := comb r (if x.neg then 1 else 0)
  r := comb r (match x.fpclass with | .finite => 0 | .inf => 1 | .nan => 2)
  return r

/-- `eval_floor` (3338-3352). -/
def CDF.floor (x : CDF) : CDF :=
  if !x.isfinite || x.isint then x
  else (if x.neg then x.sub one else x).extractIntegerPart

/-- `eval_ceil` (3354-3368). -/
def CDF.ceil (x : CDF) : CDF :=
  if !x.isfinite || x.isint then x
  else (if !x.neg then x.add one else x).extractIntegerPart

/-- `eval_fmod(result, a, b)` (detail/default_ops.hpp:1260-1321). -/
def fmod (a b : CDF) : CDF := Id.run do
  if a.iszero then return a
  if !a.isfinite then return nanV
  if b.iszero || b.isnan then return nanV
  let mut result := a.div b
  let sgn := fun (y : CDF) => if y.iszero then (0 : Int) else if y.neg then -1 else 1
  let mut n := if sgn result < 0 then result.ceil else result.floor
  n := n.mul b
  result := a.sub n
  if sgn result != 0 then
    if sgn result == sgn b then
      if result.compare b ≥ 0 then result := result.sub b
    else
      let nb := b.negate
      if result.compare nb ≥ 0 then result := result.sub nb
  return result

/-- `eval_ldexp(result, x, e)` (3407-3436) for the shifts `generic_interconvert` passes
(multiples of 64). -/
def ldexp (x : CDF) (e : Int) : CDF :=
  if e == 0 then x
  else if -63 < e && e < 0 then x  -- div_unsigned_long_long: not reached by jank's calls
  else if 0 < e && e < 63 then x   -- mul_unsigned_long_long: not reached by jank's calls
  else if e < minExp10 / 2 && x.order > 0 then x  -- not reached
  else x.mul (pow2 e)

/-- `generic_interconvert(float ← integer)` (detail/generic_interconvert.hpp:35-81): limb by
limb, each one `ldexp`-shifted and added. This is how `native_big_decimal{cpp_int}` and
`big_decimal(native_big_integer)` (through `val.real()`) build a decimal. -/
def ofCppInt (v : Int) : CDF := Id.run do
  let isNeg := v < 0
  let mut t := v.natAbs
  let mut to := fromULL (t % 2 ^ 64)
  t := t / 2 ^ 64
  let mut shift : Nat := 64
  let mut fuel := 100000
  while t != 0 && fuel > 0 do
    fuel := fuel - 1
    let l := ldexp (fromULL (t % 2 ^ 64)) shift
    t := t / 2 ^ 64
    to := to.add l
    shift := shift + 64
  return if isNeg then to.negate else to

/-- `scalbn(val, e)` (eval_scalbn, 3398-3405): multiply by `cpp_dec_float(1.0, e)`. -/
def scalbn (x : CDF) (e : Int) : CDF := x.mul (ctorDE 1.0 e)

/-- `detail::lltrunc` (standalone, detail/functions/trunc.hpp:52-64): floor or ceil, then
`convert_to<long long>`; past `LLONG_MAX` it throws `std::domain_error`. -/
def lltrunc (x : CDF) : Except String Int :=
  let t := if !x.neg && !x.iszero then x.floor else x.ceil
  if t.isnan then .ok 0
  else if t.compare llMax > 0 then .error "arg cannot be converted into a long long"
  else .ok t.extractSignedLL

/-- `generic_interconvert_float2int` radix 10 (detail/generic_interconvert.hpp:533-557): one
decimal digit at a time from `ilogb`. This is `convert_to<native_big_integer>()`. -/
def toCppInt (x : CDF) : Except String Int := Id.run do
  if x.iszero then return .ok 0
  if !x.isfinite then return .error "arg cannot be converted into a long long"
  let mut e := x.order
  let mut val := scalbn x (-e)
  let mut num : Int := 0
  let mut fuel := 200000
  while e ≥ 0 && fuel > 0 do
    fuel := fuel - 1
    match lltrunc val with
    | .error m => return .error m
    | .ok ll =>
      -- `val -= ll`: eval_subtract(cpp_dec_float&, long long) (3216-3226).
      val := if ll < 0 then val.add (fromULL ll.natAbs) else val.sub (fromULL ll.toNat)
      val := scalbn val 1
      num := num * 10 + ll
      e := e - 1
  return .ok num

/-- `number < double` and friends: `compare(const V&)` (468-474) builds the double's decimal
with `operator=(double)`. -/
def compareDouble (x : CDF) (d : Float) : Int := x.compare (ofDouble d)

end Jank.R3.Boost.Dec
