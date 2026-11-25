import Jank.R3.Boost.DecFloat
import Jank.R3.Boost.Java
import Jank.Hash

/-!
# Round 3, Boost: jank's number objects over the boost replica, beside Clojure's `Numbers`

jank side (paths under upstream-main/compiler+runtime):

- core/math.hpp `add`/`sub`/`mul`/`div`/`lt`/`lte`/`min`/`max` (68-990): `make_box(typed_l->data
  OP typed_r->data)` on the two objects' `data` (`i64`, `f64`, `native_big_integer`,
  `native_big_decimal`, `ratio_data`); the C++ operator chosen for each pair of types is the one
  overload resolution finds: boost's for boost/boost and boost/arithmetic pairs
  (detail/no_et_ops.hpp, detail/number_compare.hpp; mixed arithmetic converts the arithmetic
  operand with the backend's constructor, default_ops.hpp:283-292, 361-366, 561-583), jank's
  big_decimal.hpp/.cpp for decimal/big-integer pairs (through `str()`), big_integer.hpp's
  templates for big-integer/floating pairs (through `to_f64`), and ratio.hpp/.cpp for ratios.
  A `cpp_int < double` has no boost operator (`double → cpp_int` is a restricted conversion,
  traits/is_restricted_conversion.hpp:17-41), so it resolves to jank's
  `operator<(native_big_integer const &, native_big_decimal const &)` with the double converted
  to `cpp_dec_float` (big_decimal.cpp:78-86).
- core/math.cpp `rem` (204-304), `quot` (321-345), `is_equiv` (469-489), `to_big_integer`
  (747-783), `to_big_decimal` (790-839); math.hpp `to_int` (1411), `to_real` (1440).
- obj/big_integer.cpp, obj/big_decimal.cpp, obj/ratio.cpp: constructors, `equal`, `to_string`,
  `to_code_string`, `to_hash`, `compare`, `to_integer`, `to_real`.

Clojure side: Numbers.java `ops(x).combine(ops(y))` (LongOps, DoubleOps, RatioOps, BigIntOps,
BigDecimalOps), `Numbers.divide`/`quotient`/`remainder` (182-206), `toBigDecimal` (298-321),
`compare` (268), `min`/`max` (4124, 4217), `equal` (247: same category and `equiv`); RT.longCast,
RT.doubleCast; core.clj `bigdec`, `bigint`.
-/

namespace Jank.R3.Boost.Num

open Jank.R3.Boost Jank.R3.Boost.Dec Jank.R3.Boost.Java

/-! ## Values -/

/-- A jank number object: `integer`/`small_integer` (`i64`), `real` (`f64`), `big_integer`,
`big_decimal`, `ratio` (normalized: denominator > 1). -/
inductive JV where
  | long (v : Int)
  | dbl (x : Float)
  | big (v : Int)
  | dec (d : CDF)
  | ratio (n : Int) (d : Int)
  deriving Inhabited

/-- A Clojure number: Long, Double, BigInt, BigDecimal, Ratio. -/
inductive CV where
  | long (v : Int)
  | dbl (x : Float)
  | big (v : Int)
  | dec (d : BD)
  | ratio (n : Int) (d : Int)
  deriving Inhabited

inductive Res (α : Type) where
  | num (v : α)
  | bool (b : Bool)
  | int (i : Int)
  | str (s : String)
  | err (msg : String)
  deriving Inhabited

abbrev JR := Res JV
abbrev CR := Res CV

/-! ## Printing -/

def dblOf (x : Float) : Jank.Print.Dbl :=
  let neg := x.toBits >>> 63 == 1
  if x == 0.0 then ⟨neg, 0, 0⟩
  else let (c, s) := Jank.Codegen.Float.shortest (x.abs.toBits); ⟨neg, c, s⟩

/-- real.cpp `to_string` (291-312): `Infinity`, `-Infinity`, `NaN`, else string_builder's
`to_chars` + `.0` (round 2's `Jank.Print.jankDoubleL`). -/
def jankDblStr (x : Float) : String :=
  if x.isInf then (if x < 0.0 then "-Infinity" else "Infinity")
  else if x.isNaN then "NaN"
  else String.ofList (Jank.Print.jankDoubleL (dblOf x))

/-- big_decimal.cpp `to_string` (157): string_builder.cpp:240-249, `str()` then `.0` without a `.`. -/
def decStr (d : CDF) : String :=
  let s := d.str
  if s.contains '.' then s else s ++ ".0"

def JV.str : JV → String
  | .long v => toString v
  | .dbl x => jankDblStr x
  | .big v => CppInt.str v
  | .dec d => decStr d
  | .ratio n d => CppInt.str n ++ "/" ++ CppInt.str d

/-- `to_code_string`: big_integer.cpp:143 adds `N`, big_decimal.cpp:169-175 `M`,
real.cpp:314-335 `##Inf`/`##-Inf`/`##NaN`. -/
def JV.prStr : JV → String
  | .dbl x => if x.isInf then (if x < 0.0 then "##-Inf" else "##Inf") else if x.isNaN then "##NaN" else jankDblStr x
  | .big v => CppInt.str v ++ "N"
  | .dec d => decStr d ++ "M"
  | v => v.str

def CV.str : CV → String
  | .long v => toString v
  | .dbl x => javaDoubleString x
  | .big v => toString v
  | .dec d => d.toString
  | .ratio n d => toString n ++ "/" ++ toString d

def CV.prStr : CV → String
  | .dbl x => if x.isInf then (if x < 0.0 then "##-Inf" else "##Inf") else if x.isNaN then "##NaN" else javaDoubleString x
  | .big v => toString v ++ "N"
  | .dec d => d.toString ++ "M"
  | v => v.str

def JV.kind : JV → String
  | .long _ => "long" | .dbl _ => "double" | .big _ => "BigInt" | .dec _ => "BigDecimal" | .ratio .. => "Ratio"
def CV.kind : CV → String
  | .long _ => "long" | .dbl _ => "double" | .big _ => "BigInt" | .dec _ => "BigDecimal" | .ratio .. => "Ratio"

def JR.show : JR → String
  | .num v => v.prStr | .bool b => toString b | .int i => toString i | .str s => s!"\"{s}\"" | .err m => s!"throws ({m})"
def CR.show : CR → String
  | .num v => v.prStr | .bool b => toString b | .int i => toString i | .str s => s!"\"{s}\"" | .err m => s!"throws ({m})"

/-! ## Exact values (for comparing results) -/

/-- An exact rational for a finite value: `(p, q)` with `q > 0`. -/
def _root_.Jank.R3.Boost.Dec.CDF.rat (x : CDF) : Option (Int × Nat) :=
  if !x.isfinite then none
  else
    let m : Nat := (List.range 16).foldl (fun acc i => acc * mask + x.d i) 0
    -- value = m · 10^(exp − 120)
    let e := x.exp - 120
    let p : Int := if x.neg then -(m : Int) else m
    if e ≥ 0 then some (p * (10 : Int) ^ e.toNat, 1) else some (p, 10 ^ (-e).toNat)

/-- `cpp_dec_float` as a `BigDecimal` with its exact value (unscaled digits, no trailing zeros
dropped: the scale is the 120 limb digits after `exp`). -/
def _root_.Jank.R3.Boost.Dec.CDF.toBD (x : CDF) : Option BD :=
  if !x.isfinite then none
  else
    let m : Nat := (List.range 16).foldl (fun acc i => acc * mask + x.d i) 0
    some ⟨if x.neg then -(m : Int) else m, 120 - x.exp⟩

def ratEq (a b : Int × Nat) : Bool := a.1 * b.2 == b.1 * a.2

/-! ## Reading BigDecimals and BigInts -/

def bytes (s : String) : List Nat := s.toUTF8.toList.map (·.toNat)

/-- `big_decimal(jtl::immutable_string const &)` (big_decimal.cpp:128): `rd_string(c_str())`. -/
def decOfString (s : List Nat) : Except String CDF := rdString s

/-- `big_integer::init` (big_integer.cpp:33-58): empty throws; a trailing `N` is dropped; then
boost's `assign(std::string)`. -/
def bigInit (s : List Nat) : Except String Int :=
  if s.isEmpty then .error "The `big_integer` constructor requires a non-empty string."
  else
    let t := if s.getLast? == some 78 then s.dropLast else s
    match CppInt.assignString t with
    | .ok v => .ok v
    | .error e => .error s!"The `big_integer` constructor could not parse the string: {e}."

/-- `big_integer(s, radix, is_negative)` (big_integer.cpp:66-108). -/
def bigCreate (s : List Nat) (radix : Int) (neg : Bool) : Except String Int := do
  let v ← if radix == 10 then bigInit s
    else if radix == 8 then bigInit (48 :: s)
    else if radix == 16 then bigInit (48 :: 120 :: s)
    else pure (s.reverse.foldl (fun (acc : Int × Int) (c0 : Nat) =>
        let c : Nat := if 65 ≤ c0 && c0 ≤ 90 then c0 + 32 else c0
        let dv : Int := if 48 ≤ c && c ≤ 57 then (c : Int) - 48 else (c : Int) - 97 + 10
        (acc.1 + acc.2 * dv, acc.2 * radix)) ((0 : Int), (1 : Int))).1
  return if neg then -v else v

/-! ## jank: ratios (ratio.cpp) -/

/-- `ratio_data(n, d)` (ratio.cpp:47-64). -/
def ratioData (n d : Int) : Except String (Int × Int) :=
  if d == 0 then .error "Ratio denominator cannot be zero."
  else
    let g : Int := Int.ofNat (Int.gcd n d)
    let n' := Int.tdiv n g
    let d' := Int.tdiv d g
    .ok (if d < 0 then (-n', -d') else (n', d'))

/-- `ratio::create` (ratio.cpp:87-101). -/
def ratioCreate (n d : Int) : Except String JV := do
  let (n', d') ← ratioData n d
  if d' == 1 then
    return if CppInt.fitsI64 n' then .long n' else .big n'
  return .ratio n' d'

/-- `make_box<ratio>(ratio_data(n, d))`: always a ratio object. -/
def ratioBox (n d : Int) : Except String JV := do
  let (n', d') ← ratioData n d
  return .ratio n' d'

/-- `to_native_big_decimal(ratio_data)` (ratio.cpp:12-16). -/
def ratioToDec (n d : Int) : CDF :=
  match rdString (bytes (CppInt.str n)), rdString (bytes (CppInt.str d)) with
  | .ok a, .ok b => a.div b
  | _, _ => nanV

/-- `native_big_decimal(r.str())`, jank's bridge from a big integer to a decimal (big_decimal.cpp:7-105). -/
def bigToDec (v : Int) : CDF :=
  match rdString (bytes (CppInt.str v)) with
  | .ok a => a
  | .error _ => nanV

/-! ## jank: arithmetic (core/math.hpp) -/

inductive AOp where
  | add | sub | mul | div
  deriving BEq, Repr, Inhabited

def AOp.sym : AOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/"

def fop : AOp → Float → Float → Float
  | .add, a, b => a + b | .sub, a, b => a - b | .mul, a, b => a * b | .div, a, b => a / b

def dop : AOp → CDF → CDF → CDF
  | .add, a, b => a.add b | .sub, a, b => a.sub b | .mul, a, b => a.mul b | .div, a, b => a.div b

/-- `number<cpp_dec_float> OP V` for an arithmetic `V` already converted to the backend
(`T vv(v); t = a; t OP= vv`). -/
def decOpR (op : AOp) (a : CDF) (bv : CDF) : CDF := dop op a bv

/-- `V OP number<cpp_dec_float>` (no_et_ops.hpp:61-160): `+` and `*` swap the operands;
`-` computes `b − a` and negates it (default_ops.hpp:367-372); `/` converts `a` first. -/
def decOpL (op : AOp) (av : CDF) (b : CDF) : CDF :=
  match op with
  | .add => b.add av
  | .mul => b.mul av
  | .sub => (b.sub av).negate
  | .div => av.div b

/-- `to_f64` of a big integer (big_integer.cpp:215-231). -/
def bigF (v : Int) : Float := CppInt.toDouble v

def jArith (op : AOp) : JV → JV → JR
  -- cpp_int with cpp_int or an integer: exact (expression templates evaluate into a cpp_int).
  | .big a, .big b | .big a, .long b | .long a, .big b =>
    match op with
    | .add => .num (.big (a + b))
    | .sub => .num (.big (a - b))
    | .mul => .num (.big (a * b))
    | .div => if b == 0 then .err "Division by zero." else .num (.big (Int.tdiv a b))
  -- big_integer.hpp:55-109: through `to_f64`.
  | .big a, .dbl b => .num (.dbl (fop op (bigF a) b))
  | .dbl a, .big b => .num (.dbl (fop op a (bigF b)))
  -- cpp_dec_float with an arithmetic value.
  | .dec a, .long b => .num (.dec (decOpR op a (ofLL b)))
  | .long a, .dec b => .num (.dec (decOpL op (ofLL a) b))
  | .dec a, .dbl b => .num (.dec (decOpR op a (ofDouble b)))
  | .dbl a, .dec b => .num (.dec (decOpL op (ofDouble a) b))
  | .dec a, .dec b => .num (.dec (dop op a b))
  -- big_decimal.cpp:7-45: the big integer through `str()`.
  | .dec a, .big b => .num (.dec (dop op a (bigToDec b)))
  | .big a, .dec b => .num (.dec (dop op (bigToDec a) b))
  -- ratio.cpp:510-548.
  | .dec a, .ratio n d => .num (.dec (dop op a (ratioToDec n d)))
  | .ratio n d, .dec b => .num (.dec (dop op (ratioToDec n d) b))
  -- ratio.cpp:410-448.
  | .ratio n d, .big r =>
    let res := match op with
      | .add => ratioBox (n + r * d) d
      | .sub => ratioBox (n - r * d) d
      | .mul => ratioCreate (n * r) d
      | .div => ratioBox n (d * r)
    match res with | .ok v => .num v | .error e => .err e
  | .big l, .ratio n d =>
    let res := match op with
      | .add => ratioBox (n + l * d) d
      | .sub => ratioBox (l * d - n) d
      | .mul => ratioCreate (n * l) d
      | .div => ratioCreate (l * d) n
    match res with | .ok v => .num v | .error e => .err e
  | _, _ => .err "not modeled (no boost type)"

/-! ## jank: comparisons -/

/-- boost's `<` on two `cpp_dec_float` numbers: false when either is NaN
(number_compare.hpp `is_unordered_comparison`). -/
def dlt (a b : CDF) : Bool := !(a.isnan || b.isnan) && a.compare b < 0
def dle (a b : CDF) : Bool := !(a.isnan || b.isnan) && a.compare b ≤ 0

/-- `typed_l->data < typed_r->data` for each pair. -/
def jLt : JV → JV → Option Bool
  | .big a, .big b | .big a, .long b | .long a, .big b => some (a < b)
  | .big a, .dbl b => some (dlt (bigToDec a) (ofDouble b))
  | .dbl a, .big b => some (dlt (ofDouble a) (bigToDec b))
  | .dec a, .long b => some (dlt a (ofLL b))
  | .long a, .dec b => some (dlt (ofLL a) b)
  | .dec a, .dbl b => some (if b.isNaN then false else dlt a (ofDouble b))
  | .dbl a, .dec b => some (if a.isNaN then false else dlt (ofDouble a) b)
  | .dec a, .dec b => some (dlt a b)
  | .dec a, .big b => some (dlt a (bigToDec b))
  | .big a, .dec b => some (dlt (bigToDec a) b)
  | .dec a, .ratio n d => some (dlt a (ratioToDec n d))
  | .ratio n d, .dec b => some (dlt (ratioToDec n d) b)
  | .ratio n d, .big r => some (n < r * d)
  | .big l, .ratio n d => some (l * d < n)
  | _, _ => none

def jLe : JV → JV → Option Bool
  | .big a, .big b | .big a, .long b | .long a, .big b => some (a ≤ b)
  | .big a, .dbl b => some (dle (bigToDec a) (ofDouble b))
  | .dbl a, .big b => some (dle (ofDouble a) (bigToDec b))
  | .dec a, .long b => some (dle a (ofLL b))
  | .long a, .dec b => some (dle (ofLL a) b)
  | .dec a, .dbl b => some (if b.isNaN then false else dle a (ofDouble b))
  | .dbl a, .dec b => some (if a.isNaN then false else dle (ofDouble a) b)
  | .dec a, .dec b => some (dle a b)
  | .dec a, .big b => some (dle a (bigToDec b))
  | .big a, .dec b => some (dle (bigToDec a) b)
  | .dec a, .ratio n d => some (dle a (ratioToDec n d))
  | .ratio n d, .dec b => some (dle (ratioToDec n d) b)
  | .ratio n d, .big r => some (n ≤ r * d)
  | .big l, .ratio n d => some (l * d ≤ n)
  | _, _ => none

/-- `compare` (big_integer.cpp:177-187, big_decimal.cpp:182-190, number.cpp, ratio.cpp:149-164):
`(o < this) − (this < o)`; ratio against a decimal is `to_native_big_decimal(*this).compare(o)`. -/
def jCompare (a b : JV) : Option Int :=
  match a, b with
  | .ratio n d, .dec y => some ((ratioToDec n d).compare y)
  | _, _ => do
    let x ← jLt b a
    let y ← jLt a b
    return (if x then 1 else 0) - (if y then 1 else 0)

/-- jank `=` (`equal`): big_integer.cpp:116-131, number.cpp:95-116, big_decimal.cpp:146-155
(`abs(a − b) < numeric_limits<f64>::epsilon()`), ratio.cpp:139-147. -/
def jEqual : JV → JV → Bool
  | .big a, .big b | .big a, .long b | .long a, .big b | .long a, .long b => a == b
  | .dec a, .dec b =>
    let diff := (a.sub b).abs
    !diff.isnan && diff.compare (ofDouble Ieee.dblEps) < 0
  | .ratio n d, .ratio n' d' => n == n' && d == d'
  | .dbl a, .dbl b => a == b
  | _, _ => false

/-- `to_real` (math.hpp:1440-1462 and each object's `to_real`). -/
def JV.toReal : JV → Float
  | .long v => Ieee.ofIntRN v
  | .dbl x => x
  | .big v => bigF v
  | .dec d => d.extractDouble
  | .ratio n d => bigF n / bigF d

/-- `is_equiv` (math.cpp:469-489): both through `to_real`. -/
def jEquiv (a b : JV) : Bool := a.toReal == b.toReal

/-- jank `hash` (`to_hash`): hash.cpp `integer` for longs (round 1 `Jank.Hash.integer`),
big_integer.cpp:155-170, big_decimal.cpp:177-180 (`std::hash<native_big_decimal>` →
`hash()`, truncated to `uhash`), ratio.cpp:133-137. -/
def jHash : JV → UInt32
  | .long v => Jank.Hash.integer (UInt64.ofInt v)
  | .big v => CppInt.bigHash v
  | .dec d => d.hash.toUInt32
  | .ratio n d => Jank.Hash.combine (CppInt.bigHash n) (CppInt.bigHash d)
  | .dbl x => Jank.Hash.real x.toBits

/-! ## jank: conversions -/

/-- `(long x)`: `to_int` → `to_integer`. -/
def jLong : JV → JR
  | .long v => .int v
  | .big v => if CppInt.fitsI64 v then .int v else .err s!"The value `{v}` is out of range for `i64` conversion."
  | .dec d => .int d.extractSignedLL
  | .ratio n d =>
    let q := Int.tdiv n d
    if CppInt.fitsI64 q then .int q else .err "out of range for `i64` conversion"
  -- number.cpp:358-366: NaN is 0, else `static_cast<i64>(data)` (UB out of range).
  | .dbl x =>
    if x.isNaN then .int 0
    else if x.isInf || x.abs ≥ 9223372036854775808.0 then .err "UB: out-of-range double to i64 cast"
    else .int (if x < 0.0 then -((-x).floor.toUInt64.toNat : Int) else (x.floor.toUInt64.toNat : Int))

/-- `(double x)`: `to_real`. -/
def jDouble (v : JV) : JR := .num (.dbl v.toReal)

/-- `(bigdec x)`: `to_big_decimal` (math.cpp:790-839). -/
def jBigdec : JV → JR
  | .long v => .num (.dec (ofDouble (Ieee.ofIntRN v)))
  | .dbl x =>
    if x.isNaN then .err "`##NaN` cannot be converted to a `big_decimal`."
    else if x.isInf then .err "`##Inf` cannot be converted to a `big_decimal`."
    else .num (.dec (ofDouble x))
  | .big v => .num (.dec (ofCppInt v))
  | .dec d => .num (.dec d)
  | .ratio n d => .num (.dec ((ofCppInt n).div (bigToDec d)))

/-- `(bigint x)`: `to_big_integer` (math.cpp:747-783). -/
def jBigint : JV → JR
  | .long v => .num (.big v)
  | .big v => .num (.big v)
  | .dbl x => match toCppInt (ofDouble x) with | .ok v => .num (.big v) | .error e => .err e
  | .dec d => match toCppInt d with | .ok v => .num (.big v) | .error e => .err e
  | .ratio n d =>
    let q := Int.tdiv n d
    if CppInt.fitsI64 q then .num (.big q) else .err "out of range for `i64` conversion"

def jBigintStr (s : List Nat) : JR := match bigInit s with | .ok v => .num (.big v) | .error e => .err e
def jBigdecStr (s : List Nat) : JR := match decOfString s with | .ok d => .num (.dec d) | .error e => .err e

/-- `quot` (math.cpp:321-345): both through `to_real`, then `static_cast<i64>` (an out-of-range
cast is UB: reported as an error). -/
def jQuot (a b : JV) : JR :=
  let x := a.toReal
  let y := b.toReal
  if y == 0.0 then .err "Division by zero is not permitted."
  else
    let q := x / y
    if q.isNaN || q.isInf || q.abs ≥ 9223372036854775808.0 then .err "UB: out-of-range double to i64 cast"
    else .int (if q < 0.0 then -((-q).floor.toUInt64.toNat : Int) else (q.floor.toUInt64.toNat : Int))

/-- `rem` (math.cpp:204-304) for the pairs with a boost type. -/
def jRem : JV → JV → JR
  | a, b =>
    let isF := match a, b with | .dbl _, _ | _, .dbl _ => true | _, _ => false
    let isR := match a, b with | .ratio .., _ | _, .ratio .. => true | _, _ => false
    let isD := match a, b with | .dec _, _ | _, .dec _ => true | _, _ => false
    if isF then
      let l := a.toReal
      let r := b.toReal
      if r == 0.0 then .err "Division by zero is not permitted."
      else if l.isNaN || l.isInf || r.isNaN then .err "not permitted"
      else if r.isInf then .num (.dbl (0.0/0.0))
      else .num (.dbl (l - r * (l / r).floor))  -- std::fmod: see MPA note; only finite |l/r| < 2^53 used
    else if isR then
      -- A non-ratio operand becomes `ratio_data{native_big_integer(data), 1}`:
      -- a decimal is truncated by convert_to<cpp_int> (generic_interconvert).
      let asRatio : JV → Except String (Int × Int) := fun
        | .ratio n d => .ok (n, d)
        | .long v => .ok (v, 1)
        | .big v => .ok (v, 1)
        | .dec x => match toCppInt x with | .ok v => .ok (v, 1) | .error e => .error e
        | .dbl _ => .error "unreachable"
      match asRatio a, asRatio b with
      | .ok (ln, ld), .ok (rn, rd) =>
        match ratioData ln ld, ratioData rn rd with
        | .ok (ln, ld), .ok (rn, rd) =>
          if rn == 0 then .err "Division by zero is not permitted."
          else
            let q := Int.tdiv (ln * rd) (ld * rn)
            let num := ln * rd - q * rn * ld
            let den := ld * rd
            if Int.tmod num den == 0 then .num (.big (Int.tdiv num den))
            else match ratioBox num den with | .ok v => .num v | .error e => .err e
        | .error e, _ | _, .error e => .err e
      | .error e, _ | _, .error e => .err e
    else if isD then
      let toD : JV → CDF := fun
        | .dec x => x | .long v => ofLL v | .big v => ofCppInt v | _ => nanV
      let l := toD a
      let r := toD b
      if r.compare zero == 0 && !r.isnan then .err "Division by zero is not permitted."
      else
        let res := fmod l.abs r.abs
        .num (.dec (if dlt l zero then res.negate else res))
    else
      match a, b with
      | .big x, .big y | .big x, .long y | .long x, .big y =>
        if y == 0 then .err "Division by zero is not permitted." else .num (.big (Int.tmod x y))
      | _, _ => .err "not modeled"

/-! ## Clojure -/

inductive Cat where
  | long | dbl | ratio | big | dec
  deriving BEq, Repr

def CV.cat : CV → Cat
  | .long _ => .long | .dbl _ => .dbl | .big _ => .big | .dec _ => .dec | .ratio .. => .ratio

/-- `ops(x).combine(ops(y))`. -/
def combine (a b : Cat) : Cat :=
  if a == .dbl || b == .dbl then .dbl
  else if a == .dec || b == .dec then .dec
  else if a == .ratio || b == .ratio then .ratio
  else if a == .big || b == .big then .big
  else .long

/-- `doubleValue()`: Long → double (nearest), BigInt → nearest, BigDecimal → nearest,
Ratio → `decimalValue(MathContext.DECIMAL64).doubleValue()` (16 digits, HALF_EVEN). -/
def CV.toDouble : CV → Float
  | .long v => Ieee.ofIntRN v
  | .dbl x => x
  | .big v => Ieee.ofIntRN v
  | .dec d => d.toDouble
  | .ratio n d =>
    -- round n/d to 16 significant digits, half even
    let neg := n < 0
    let p := n.natAbs
    let q := d.natAbs
    let digitsOf := fun (k : Nat) => (Nat.toDigits 10 k).length
    -- exponent so that p/q·10^sh has 16 digits before the point
    let e : Int := (digitsOf p : Int) - (digitsOf q : Int)
    let sh : Int := 16 - e
    let (num, den) := if sh ≥ 0 then (p * 10 ^ sh.toNat, q) else (p, q * 10 ^ (-sh).toNat)
    let c0 := Jank.Codegen.Float.roundHalfEven num den
    -- normalize to at most 16 digits
    let (c, sh) := if digitsOf c0 > 16 then
        (Jank.Codegen.Float.roundHalfEven num (den * 10), sh - 1) else (c0, sh)
    let (c, sh) := if digitsOf c > 16 then (c / 10, sh - 1) else (c, sh)
    Ieee.strtodDec neg c (-sh)

/-- `Numbers.toBigDecimal` (298-321). -/
def toBD : CV → Except String BD
  | .dec d => .ok d
  | .long v => .ok (BD.ofLong v)
  | .big v => .ok ⟨v, 0⟩
  | .ratio n d => BD.div ⟨n, 0⟩ ⟨d, 0⟩
  | .dbl _ => .error "toBigDecimal(double): not reached"

def ratioOf : CV → Int × Int
  | .ratio n d => (n, d)
  | .long v | .big v => (v, 1)
  | _ => (0, 1)

/-- `Numbers.divide(BigInteger n, BigInteger d)`: BigInt when integral, else a Ratio. -/
def cljDivide (n d : Int) : Except String CV :=
  if d == 0 then .error "Divide by zero"
  else
    let g : Int := Int.ofNat (Int.gcd n d)
    if g == 0 then .ok (.big 0)
    else
      let n := n / g
      let d := d / g
      if d == 1 then .ok (.big n)
      else if d == -1 then .ok (.big (-n))
      else .ok (.ratio (if d < 0 then -n else n) (if d < 0 then -d else d))

/-- `Numbers.add/minus/multiply/divide(Object, Object)` for the pairs with a BigInt, BigDecimal
or Ratio. Division by zero throws "Divide by zero" (Numbers.java:189). -/
def cArith (op : AOp) (a b : CV) : CR :=
  let isZero := match b with
    | .long v | .big v => v == 0 | .dbl x => x == 0.0 | .dec d => d.u == 0 | .ratio n _ => n == 0
  if op == .div && (match a with | .dbl x => x.isNaN | _ => false) then .num a
  else if op == .div && (match b with | .dbl x => x.isNaN | _ => false) then .num b
  else if op == .div && isZero then .err "Divide by zero"
  else
  match combine a.cat b.cat with
  | .dbl => .num (.dbl (fop op a.toDouble b.toDouble))
  | .dec =>
    match toBD a, toBD b with
    | .ok x, .ok y =>
      match op with
      | .add => .num (.dec (x.add y))
      | .sub => .num (.dec (x.add y.neg))
      | .mul => .num (.dec (x.mul y))
      | .div => match x.div y with | .ok r => .num (.dec r) | .error e => .err e
    | .error e, _ | _, .error e => .err e
  | .ratio =>
    let (xn, xd) := ratioOf a
    let (yn, yd) := ratioOf b
    let r := match op with
      | .add => cljDivide (yn * xd + xn * yd) (yd * xd)
      | .sub => cljDivide ((-yn) * xd + xn * yd) (yd * xd)
      | .mul => cljDivide (yn * xn) (yd * xd)
      | .div => cljDivide (yd * xn) (yn * xd)
    match r with | .ok v => .num v | .error e => .err e
  | .big =>
    let x := match a with | .long v | .big v => v | _ => 0
    let y := match b with | .long v | .big v => v | _ => 0
    match op with
    | .add => .num (.big (x + y))
    | .sub => .num (.big (x - y))
    | .mul => .num (.big (x * y))
    | .div => match cljDivide x y with | .ok v => .num v | .error e => .err e
  | .long => .err "not modeled (longs)"

/-- `Ops.lt` of the combined ops. -/
def cLt (a b : CV) : Option Bool :=
  match combine a.cat b.cat with
  | .dbl => some (a.toDouble < b.toDouble)
  | .dec => match toBD a, toBD b with
    | .ok x, .ok y => some (x.cmp y < 0)
    | _, _ => none
  | .ratio =>
    let (xn, xd) := ratioOf a
    let (yn, yd) := ratioOf b
    some (xn * yd < yn * xd)
  | .big | .long =>
    let x := match a with | .long v | .big v => v | _ => 0
    let y := match b with | .long v | .big v => v | _ => 0
    some (x < y)

def cLe (a b : CV) : Option Bool :=
  match combine a.cat b.cat with
  | .dbl => some (a.toDouble ≤ b.toDouble)
  | .dec => match toBD a, toBD b with
    | .ok x, .ok y => some (x.cmp y ≤ 0)
    | _, _ => none
  | .ratio =>
    let (xn, xd) := ratioOf a
    let (yn, yd) := ratioOf b
    some (xn * yd ≤ yn * xd)
  | .big | .long =>
    let x := match a with | .long v | .big v => v | _ => 0
    let y := match b with | .long v | .big v => v | _ => 0
    some (x ≤ y)

/-- `Numbers.compare` (268): `lt` both ways. A Ratio/BigDecimal pair whose ratio does not
terminate throws. -/
def cCompare (a b : CV) : Option Int := do
  let x ← cLt a b
  let y ← cLt b a
  return if x then -1 else if y then 1 else 0

/-- `Numbers.equiv` (`==`). -/
def cEquiv (a b : CV) : Option Bool :=
  match combine a.cat b.cat with
  | .dbl => some (a.toDouble == b.toDouble)
  | .dec => match toBD a, toBD b with
    | .ok x, .ok y => some (x.cmp y == 0)
    | _, _ => none
  | _ => do
    let l ← cLe a b
    let g ← cLe b a
    return l && g

/-- `Numbers.equal` (`=`): same category and `equiv`. Categories: INTEGER (Long, BigInt),
FLOATING, DECIMAL, RATIO. -/
def cEqual (a b : CV) : Option Bool :=
  let catOf : CV → Nat := fun | .long _ | .big _ => 0 | .dbl _ => 1 | .dec _ => 2 | .ratio .. => 3
  if catOf a != catOf b then some false else cEquiv a b

def cLong : CV → CR
  | .long v => .int v
  | .big v => if CppInt.fitsI64 v then .int v else .err "Value out of range for long"
  | .ratio n d => let q := Int.tdiv n d; if CppInt.fitsI64 q then .int q else .err "Value out of range for long"
  | v =>
    let x := v.toDouble
    if x < -9223372036854775808.0 || x > 9223372036854775807.0 then .err "Value out of range for long"
    else if x.isNaN then .int 0
    else .int (if x < 0.0 then -((-x).floor.toUInt64.toNat : Int) else (x.floor.toUInt64.toNat : Int))

def cDouble (v : CV) : CR := .num (.dbl v.toDouble)

/-- core.clj `bigdec` (3673-3685). -/
def cBigdec : CV → CR
  | .dec d => .num (.dec d)
  | .dbl x => match BD.valueOfDouble x with | .ok d => .num (.dec d) | .error e => .err e
  | .ratio n d => match BD.div ⟨n, 0⟩ ⟨d, 0⟩ with | .ok r => .num (.dec r) | .error e => .err e
  | .big v => .num (.dec ⟨v, 0⟩)
  | .long v => .num (.dec ⟨v, 0⟩)

/-- core.clj `bigint` (3645-3657). -/
def cBigint : CV → CR
  | .big v => .num (.big v)
  | .dec d => .num (.big d.toBigInteger)
  | .dbl x => match BD.valueOfDouble x with | .ok d => .num (.big d.toBigInteger) | .error e => .err e
  | .ratio n d => .num (.big (Int.tdiv n d))
  | .long v => .num (.big v)

def cBigintStr (s : List Nat) : CR := match bigIntegerOfString s with | .ok v => .num (.big v) | .error e => .err e
def cBigdecStr (s : List Nat) : CR := match BD.ofString s with | .ok d => .num (.dec d) | .error e => .err e

/-- BigDecimal `divideToIntegralValue` value, then `remainder` = x − q·y (values; the scale
follows max(s1, s2) when q is exact). -/
def cRem (a b : CV) : CR :=
  let isZero := match b with
    | .long v | .big v => v == 0 | .dbl x => x == 0.0 | .dec d => d.u == 0 | .ratio n _ => n == 0
  if isZero then .err "Divide by zero"
  else match combine a.cat b.cat with
  | .dbl =>
    let x := a.toDouble
    let y := b.toDouble
    .num (.dbl (x - y * (if x / y < 0.0 then -((-(x / y)).floor) else (x / y).floor)))
  | .dec =>
    match toBD a, toBD b with
    | .ok x, .ok y =>
      let (p, q) := x.rat
      let (p', q') := y.rat
      -- integer part of x/y toward zero
      let qi := Int.tdiv (p * q') (q * p')
      .num (.dec (x.sub ((⟨qi, 0⟩ : BD).mul y)))
    | .error e, _ | _, .error e => .err e
  | .ratio =>
    let (xn, xd) := ratioOf a
    let (yn, yd) := ratioOf b
    let q := Int.tdiv (xn * yd) (xd * yn)
    -- Numbers.minus(x, Numbers.multiply(q, y)) with q a BigInt
    match cljDivide (xn * yd - q * yn * xd) (xd * yd) with
    | .ok v => .num v | .error e => .err e
  | _ =>
    let x := match a with | .long v | .big v => v | _ => 0
    let y := match b with | .long v | .big v => v | _ => 0
    .num (.big (Int.tmod x y))

/-- `quot`: BigDecimalOps.quotient = divideToIntegralValue (a BigDecimal); BigInt/Ratio → BigInt;
DoubleOps → `Numbers.quotient(double, double)`. -/
def cQuot (a b : CV) : CR :=
  let isZero := match b with
    | .long v | .big v => v == 0 | .dbl x => x == 0.0 | .dec d => d.u == 0 | .ratio n _ => n == 0
  if isZero then .err "Divide by zero"
  else match combine a.cat b.cat with
  | .dbl =>
    let q := a.toDouble / b.toDouble
    .num (.dbl (if q < 0.0 then -((-q).floor) else q.floor))
  | .dec =>
    match toBD a, toBD b with
    | .ok x, .ok y =>
      let (p, q) := x.rat
      let (p', q') := y.rat
      .num (.dec ⟨Int.tdiv (p * q') (q * p'), 0⟩)
    | .error e, _ | _, .error e => .err e
  | .ratio =>
    let (xn, xd) := ratioOf a
    let (yn, yd) := ratioOf b
    .num (.big (Int.tdiv (xn * yd) (xd * yn)))
  | _ =>
    let x := match a with | .long v | .big v => v | _ => 0
    let y := match b with | .long v | .big v => v | _ => 0
    .num (.big (Int.tdiv x y))

/-! ## Comparing outcomes -/

/-- Same number: same kind and the same value (BigDecimals by value; doubles by bits, NaN = NaN). -/
def sameNum : JV → CV → Bool
  | .long a, .long b | .big a, .big b => a == b
  | .dbl a, .dbl b => (a.isNaN && b.isNaN) || a.toBits == b.toBits
  | .ratio n d, .ratio n' d' => n == n' && d == d'
  | .dec a, .dec b =>
    match a.rat with
    | some r => ratEq r b.rat
    | none => false
  | _, _ => false

/-- Same value, maybe another kind (`==`-equal). -/
def sameValue : JV → CV → Bool
  | .dbl a, .dbl b => (a.isNaN && b.isNaN) || a == b
  | j, c =>
    let jr : Option (Int × Nat) := match j with
      | .long v | .big v => some (v, 1)
      | .dec d => d.rat
      | .ratio n d => some (n, d.toNat)
      | .dbl x => if Ieee.isFinite x then let (n, p, q) := Ieee.exact x; some (if n then -(p : Int) else p, q) else none
    let cr : Option (Int × Nat) := match c with
      | .long v | .big v => some (v, 1)
      | .dec d => some d.rat
      | .ratio n d => some (n, d.toNat)
      | .dbl x => if Ieee.isFinite x then let (n, p, q) := Ieee.exact x; some (if n then -(p : Int) else p, q) else none
    match jr, cr with
    | some a, some b => ratEq a b
    | _, _ => false

end Jank.R3.Boost.Num
