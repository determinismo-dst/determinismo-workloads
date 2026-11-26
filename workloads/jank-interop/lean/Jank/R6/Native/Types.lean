/-!
# Round 6, native values: C++'s arithmetic types and conversions as jank's emitted code sees them

jank at 94d32623 (upstream-r5/compiler+runtime). A native C++ number reaches a Clojure operation
when the analyzer types an expression natively and core.jank's `:inline` metadata expands the
operation into a call of a `jank::runtime` template (core/math.hpp). This file is the C++ side:
the types (x86-64 Linux, LP64), [conv.prom], [conv.rank], the usual arithmetic conversions
([expr.arith.conv]), `std::common_type` for arithmetic types, conversions ([conv.integral] as
C++20 defines them: modulo 2^N; [conv.fpint]: truncation, undefined out of range), and the built-in
operators `<`, `<=`, `+`, `-`, `*`, `/` on converted operands. jank compiles with `-fwrapv`
(round 3's Flags), so a signed overflow wraps.

Types (include/cpp/jtl/primitive.hpp 9-27): i8 = signed char, u8 = unsigned char, i16 = short,
u16 = unsigned short, i32 = int, u32 = unsigned int (= uhash), i64 = long long, u64 = usize =
unsigned long long, f32 = float, f64 = double. An integer literal is `int` when it fits 32 bits,
else `long` (analyze/cpp_util.cpp literal_type 628-648; on Windows `long long`). `char` is signed
on x86-64 (on AArch64 Linux it is unsigned: noted where it matters).
-/

namespace Jank.R6.Native

/-- A C++ arithmetic type of the universe. -/
inductive NT where
  | bool | char | schar | uchar | short | ushort | int | uint | long | ulong | llong | ullong
  | float | double
  deriving Repr, BEq, DecidableEq, Inhabited

namespace NT

def all : List NT :=
  [.bool, .char, .schar, .uchar, .short, .ushort, .int, .uint, .long, .ulong, .llong, .ullong,
   .float, .double]

def name : NT → String
  | .bool => "bool" | .char => "char" | .schar => "signed char (i8)" | .uchar => "unsigned char (u8)"
  | .short => "short (i16)" | .ushort => "unsigned short (u16)" | .int => "int (i32)"
  | .uint => "unsigned int (u32, uhash)" | .long => "long" | .ulong => "unsigned long"
  | .llong => "long long (i64)" | .ullong => "unsigned long long (u64, usize)"
  | .float => "float (f32)" | .double => "double (f64)"

def isFloating : NT → Bool
  | .float | .double => true
  | _ => false

def isIntegral (t : NT) : Bool := !t.isFloating

/-- bool and the character types: `std::is_integral` holds for them, Clojure has no number there. -/
def isNonNumber : NT → Bool
  | .bool | .char => true
  | _ => false

def bits : NT → Nat
  | .bool => 1 | .char | .schar | .uchar => 8 | .short | .ushort => 16 | .int | .uint => 32
  | .long | .ulong | .llong | .ullong => 64 | .float => 32 | .double => 64

/-- Signedness of an integral type (x86-64: `char` is signed). -/
def signed : NT → Bool
  | .char | .schar | .short | .int | .long | .llong => true
  | _ => false

/-- [conv.rank]. -/
def rank : NT → Nat
  | .bool => 0 | .char | .schar | .uchar => 1 | .short | .ushort => 2 | .int | .uint => 3
  | .long | .ulong => 4 | .llong | .ullong => 5 | _ => 0

def minV (t : NT) : Int :=
  if t == .bool then 0 else if t.signed then -(2 ^ (t.bits - 1) : Nat) else 0

def maxV (t : NT) : Int :=
  if t == .bool then 1 else if t.signed then (2 ^ (t.bits - 1) - 1 : Nat) else (2 ^ t.bits - 1 : Nat)

/-- [conv.prom]: bool, the character types and short types promote to int (int holds them all). -/
def promote (t : NT) : NT := if t.isIntegral && t.rank < 3 then .int else t

def toUnsigned : NT → NT
  | .int => .uint | .long => .ulong | .llong => .ullong | .char | .schar => .uchar
  | .short => .ushort | t => t

end NT

/-- The usual arithmetic conversions ([expr.arith.conv]/1): the type both operands of a binary
arithmetic or relational operator are converted to. -/
def uac (a b : NT) : NT :=
  if a == .double || b == .double then .double
  else if a == .float || b == .float then .float
  else
    let a := a.promote
    let b := b.promote
    if a == b then a
    else if a.signed == b.signed then (if a.rank ≥ b.rank then a else b)
    else
      let (u, s) := if a.signed then (b, a) else (a, b)
      if u.rank ≥ s.rank then u
      else if s.bits > u.bits then s
      else s.toUnsigned

/-- `std::common_type_t<A, B>` for arithmetic A, B: `decay_t<decltype(false ? a : b)>`, which is the
type itself when both are the same ([expr.cond]/7), else the usual arithmetic conversions. -/
def commonType (a b : NT) : NT := if a == b then a else uac a b

/-- A native value: an integral value in its type's range, or a floating value (a `float`'s
value is a float rounded to binary32, kept as the double it widens to). -/
inductive NV where
  | i (t : NT) (v : Int)
  | f (t : NT) (x : Float)
  deriving Inhabited

def NV.ival : NV → Int
  | .i _ v => v
  | .f _ _ => 0

def NV.ty : NV → NT
  | .i t _ => t
  | .f t _ => t

def NV.show : NV → String
  | .i .bool v => if v == 0 then "false" else "true"
  | .i .char v => s!"char {v}"
  | .i t v => s!"{v} ({t.name})"
  | .f t x => s!"{x} ({t.name})"

/-- Reduce an integer into type t ([conv.integral]: modulo 2^N for every integer type since C++20;
bool: `!= 0`). -/
def wrapTo (t : NT) (v : Int) : Int :=
  if t == .bool then (if v == 0 then 0 else 1)
  else if t.signed then (BitVec.ofInt t.bits v).toInt
  else ((BitVec.ofInt t.bits v).toNat : Int)

/-- Round a double to binary32 and back. -/
def toF32 (x : Float) : Float := x.toFloat32.toFloat

/-- Truncation toward zero of a finite double below 2^63 in magnitude. -/
def truncF (f : Float) : Int :=
  let a := f.abs.floor
  let n : Int := (a.toUInt64.toNat : Int)
  if f < 0 then -n else n

/-- A C++ conversion's outcome: a value, or undefined behavior ([conv.fpint] out of range). -/
inductive Conv where
  | ok (v : NV)
  | ub (why : String)
  deriving Inhabited

/-- C++'s conversion of a native value to type t (implicit conversion, `static_cast`). -/
def NV.conv (n : NV) (t : NT) : Conv :=
  match n with
  | .i _ v =>
    if t.isFloating then
      let x := Float.ofInt v
      .ok (.f t (if t == .float then toF32 x else x))
    else .ok (.i t (wrapTo t v))
  | .f _ x =>
    if t.isFloating then .ok (.f t (if t == .float then toF32 x else x))
    else if t == .bool then .ok (.i .bool (if x == 0.0 then 0 else 1))
    else if x.isNaN || x.isInf then .ub s!"double to {t.name}"
    else
      let n := truncF x
      if t.minV ≤ n && n ≤ t.maxV then .ok (.i t n) else .ub s!"double to {t.name}"

/-- Both operands after the usual arithmetic conversions (no floating→integral conversion happens
here, so no undefined behavior). -/
def NV.toUac (a b : NV) : NV × NV :=
  let t := uac a.ty b.ty
  let c := fun (n : NV) => match n.conv t with | .ok v => v | .ub _ => n
  (c a, c b)

/-- Mathematical order of two converted values of one type. -/
def nvLtSame : NV → NV → Bool
  | .i _ a, .i _ b => decide (a < b)
  | .f _ a, .f _ b => a < b
  | _, _ => false

def nvLeSame : NV → NV → Bool
  | .i _ a, .i _ b => decide (a ≤ b)
  | .f _ a, .f _ b => a ≤ b
  | _, _ => false

/-- The built-in `l < r` on two arithmetic operands ([expr.rel]: usual arithmetic conversions). -/
def cppLt (l r : NV) : Bool := let (a, b) := NV.toUac l r; nvLtSame a b
def cppLe (l r : NV) : Bool := let (a, b) := NV.toUac l r; nvLeSame a b

inductive BinOp where
  | add | sub | mul | div
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The outcome of a built-in arithmetic operator: a value of the converted type, or undefined
behavior (integer division by zero, or `INT_MIN / -1`: x86's `idiv` traps). -/
def cppArith (op : BinOp) (l r : NV) : Conv :=
  let (a, b) := NV.toUac l r
  match a, b with
  | .i t x, .i _ y =>
    match op with
    | .add => .ok (.i t (wrapTo t (x + y)))
    | .sub => .ok (.i t (wrapTo t (x - y)))
    | .mul => .ok (.i t (wrapTo t (x * y)))
    | .div =>
      if y == 0 then .ub "integer division by zero"
      else if t.signed && x == t.minV && y == -1 then .ub "INT_MIN / -1"
      else .ok (.i t (wrapTo t (x.tdiv y)))
  | .f t x, .f _ y =>
    let r := match op with
      | .add => x + y | .sub => x - y | .mul => x * y | .div => x / y
    .ok (.f t (if t == .float then toF32 r else r))
  | _, _ => .ub "mixed"

/-- `std::min(a, b)` is `(b < a) ? b : a`; `std::max(a, b)` is `(a < b) ? b : a` ([alg.min.max]). -/
def stdMin (a b : NV) : NV := if nvLtSame b a then b else a
def stdMax (a b : NV) : NV := if nvLtSame a b then b else a

/-- A double's exact decimal expansion, cut at 17 significant digits (from its IEEE bits). -/
def showF (x : Float) : String :=
  if x.isNaN then "##NaN" else if x.isInf then (if x > 0 then "##Inf" else "##-Inf") else
  let b : Nat := x.toBits.toNat
  let neg := b / 2 ^ 63 == 1
  let ex : Nat := (b / 2 ^ 52) % 2048
  let fr : Nat := b % 2 ^ 52
  let (m, e) : Nat × Int := if ex == 0 then (fr, -1074) else (fr + 2 ^ 52, (ex : Int) - 1075)
  let sgn := if neg then "-" else ""
  if e ≥ 0 then s!"{sgn}{m * 2 ^ e.toNat}.0" else
  let d := 2 ^ (-e).toNat
  let q := m / d
  let digits := Id.run do
    let mut r := m % d
    let mut out := ""
    let mut sig := (toString q).length - (if q == 0 then 1 else 0)
    let mut started := q != 0
    for _ in [0:400] do
      if r == 0 || sig ≥ 17 then break
      r := r * 10
      let dg := r / d
      r := r % d
      out := out.push (Char.ofNat (48 + dg))
      if dg != 0 then started := true
      if started then sig := sig + 1
    return out
  s!"{sgn}{q}.{if digits.isEmpty then "0" else digits}"

/-! ## Facts about the conversions (kernel-checked) -/

theorem uac_ullong_int : uac .ullong .int = .ullong := by decide
theorem uac_ullong_long : uac .ullong .long = .ullong := by decide
theorem uac_ullong_llong : uac .ullong .llong = .ullong := by decide
theorem uac_uint_int : uac .uint .int = .uint := by decide
theorem uac_uint_llong : uac .uint .llong = .llong := by decide
theorem uac_uchar_int : uac .uchar .int = .int := by decide
theorem uac_bool_int : uac .bool .int = .int := by decide
theorem commonType_ullong_int : commonType .ullong .int = .ullong := by decide
theorem commonType_int_double : commonType .int .double = .double := by decide

/-- Every pairing of an unsigned type of rank ≥ int with a signed type of no higher rank converts
the signed operand to unsigned: the whole set of type pairs where a negative operand changes
value under `<`, `min`, `max` and `/`. -/
theorem uac_unsigned_wins :
    ∀ u ∈ [NT.uint, .ulong, .ullong], ∀ s ∈ [NT.char, .schar, .short, .int, .long, .llong],
      s.rank ≤ u.rank → (uac u s).signed = false ∧ (uac s u).signed = false := by
  decide

/-- The only signed-meets-unsigned pairs that stay signed: a narrower unsigned meeting a wider signed. -/
theorem uac_signed_survives :
    (uac .uint .long).signed = true ∧ (uac .uint .llong).signed = true ∧
    (uac .uchar .int).signed = true ∧ (uac .ushort .int).signed = true := by
  decide

end Jank.R6.Native
