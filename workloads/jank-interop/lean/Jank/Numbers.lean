import Std.Tactic.BVDecide
import Determinismo

/-!
# jank's numbers, as the C++ computes them, beside Clojure's

jank (commit f3d82d654) represents a number as an `object_ref` (oref.hpp): a NaN-boxed 64-bit
word holding either a double, an inline 32-bit integer (`small_integer`, tag 0xFFF9), or a pointer
to a heap object (`integer` for longs outside i32, `big_integer`, `ratio`, `big_decimal`).
`make_box(i)` (core/make_box.hpp) boxes an integral value as a small integer when it fits i32,
else as a heap `integer`.

Arithmetic is generic C++ (core/math.hpp, core/math.cpp): `visit_number_like` dispatches on the
two operands' types and evaluates `typed_l->data OP typed_r->data`, where `data` is `i32` for a
small integer (oref.hpp, `oref<obj::small_integer>::data`), `i64` for `integer`, `f64` for reals.
The C++ usual arithmetic conversions then decide the width of the operation: two small integers
are added, subtracted, multiplied and divided as 32-bit `int`s.

jank documents (book/src/differences-from-clojure.md, "Math"): "Signed integer overflow is well
defined", "Division by integer `0` is undefined behavior", "Division by floating point `0.0` is
well defined". We model signed overflow as two's complement wrapping (BitVec), as documented.

The Clojure side (`Clj`) follows clojure.lang.Numbers (1.12): longs are 64-bit; `+ - * inc dec`
throw on overflow; `+' -' *'` promote to BigInt; `/` of integers gives a Ratio or an integer;
`quot` truncates (a double for double operands); `==` compares longs exactly.
-/

namespace Jank.Numbers

/-! ## Values -/

/-- A jank number object (the cases `visit_number_like` dispatches on, visit.hpp). Ratios are
kept normalized (ratio.cpp, `ratio_data` constructor divides by the gcd, sign on the numerator). -/
inductive JNum where
  /-- `obj::small_integer`: inline i32 (oref.hpp `integer_nan_tag`). -/
  | small (v : BitVec 32)
  /-- `obj::integer`: heap i64. -/
  | int (v : BitVec 64)
  /-- `obj::big_integer`: boost cpp_int. -/
  | big (v : Int)
  /-- `obj::ratio`: normalized numerator / denominator (denominator > 1). -/
  | ratio (n : Int) (d : Nat)
  /-- `obj::small_real` / `obj::real`: a double (always NaN-boxed inline). -/
  | real (v : Float)
  deriving Inhabited

/-- A Clojure number (the classes clojure.lang.Numbers categorizes). -/
inductive CNum where
  | long (v : Int)          -- java.lang.Long, |v| < 2^63
  | bigint (v : Int)        -- clojure.lang.BigInt
  | ratio (n : Int) (d : Nat)
  | double (v : Float)
  deriving Inhabited

def i32min : Int := -2147483648
def i32max : Int := 2147483647
def i64min : Int := -9223372036854775808
def i64max : Int := 9223372036854775807

/-- `make_box(T i)` for an integral `i` (core/make_box.hpp): a small integer when it fits i32,
else a heap `integer`. -/
def makeBoxI64 (v : BitVec 64) : JNum :=
  if i32min ≤ v.toInt ∧ v.toInt ≤ i32max then .small (v.truncate 32) else .int v

/-- What a jank integer means (its mathematical value). -/
def JNum.intValue? : JNum → Option Int
  | .small v => some v.toInt
  | .int v => some v.toInt
  | .big v => some v
  | _ => none

/-- A jank number as the Clojure number it stands for (jank's small and heap integers are both
Clojure longs). -/
def JNum.toClj : JNum → CNum
  | .small v => .long v.toInt
  | .int v => .long v.toInt
  | .big v => .bigint v
  | .ratio n d => .ratio n d
  | .real f => .double f

/-- The jank number reading a long literal (the reader boxes with `make_box`). -/
def JNum.ofInt (i : Int) : JNum :=
  if i32min ≤ i ∧ i ≤ i32max then .small (BitVec.ofInt 32 i)
  else if i64min ≤ i ∧ i ≤ i64max then .int (BitVec.ofInt 64 i) else .big i

instance : Repr JNum where
  reprPrec n _ := match n with
    | .small v => s!"{v.toInt}"
    | .int v => s!"{v.toInt}"
    | .big v => s!"{v}N"
    | .ratio n d => s!"{n}/{d}"
    | .real f => toString f

instance : Repr CNum where
  reprPrec n _ := match n with
    | .long v => s!"{v}"
    | .bigint v => s!"{v}N"
    | .ratio n d => s!"{n}/{d}"
    | .double f => toString f

/-- Value equality of results across the two sides (a long and a jank integer of the same value
are the same; doubles by bits so that -0.0 and 0.0 are told apart). -/
def sameResult : Except String JNum → Except String CNum → Bool
  | .error _, .error _ => true
  | .ok j, .ok c =>
    match j.toClj, c with
    | .long a, .long b => a == b
    | .bigint a, .bigint b => a == b
    | .ratio a b, .ratio c d => a == c && b == d
    | .double a, .double b => a.toBits == b.toBits
    | _, _ => false
  | _, _ => false

/-! ## jank: integer arithmetic (core/math.hpp `add`, `sub`, `mul`, `div`)

`add(object_ref, object_ref)` → `make_box(typed_l->data + typed_r->data)`. For two small
integers both `data` are `i32`: the sum is a 32-bit `int` (wrapping, per jank's "signed integer
overflow is well defined"), then `make_box<int>` keeps it small. With one `integer` operand the
other converts to `i64`. -/

inductive Op where | add | sub | mul
  deriving Repr, BEq

def bvOp {w : Nat} : Op → BitVec w → BitVec w → BitVec w
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b

/-- core/math.hpp `add`/`sub`/`mul` (object_ref, object_ref), integer operands only. -/
def jankIntOp (op : Op) : JNum → JNum → Except String JNum
  -- i32 OP i32: an `int` result (C++ [expr.arith.conv]); make_box<int> → small.
  | .small a, .small b => .ok (.small (bvOp op a b))
  -- i32 OP i64 / i64 OP i32 / i64 OP i64: computed in i64, make_box<i64>.
  | .small a, .int b => .ok (makeBoxI64 (bvOp op (a.signExtend 64) b))
  | .int a, .small b => .ok (makeBoxI64 (bvOp op a (b.signExtend 64)))
  | .int a, .int b => .ok (makeBoxI64 (bvOp op a b))
  -- with a big integer: boost cpp_int arithmetic, exact.
  | x, y => match x.intValue?, y.intValue? with
    | some a, some b => .ok (.big (match op with | .add => a + b | .sub => a - b | .mul => a * b))
    | _, _ => .error "outside this model"

/-- core/math.cpp `promoting_add`/`promoting_sub`/`promoting_mul` for integer operands:
`__builtin_*_overflow(l_val, r, &res)` with `i64 res`; on overflow, `promoting_add` and
`promoting_mul` box `native_big_integer(l) OP r` (exact), but `promoting_sub` boxes
`make_box<obj::big_integer>(l_val - typed_r->data)`: the difference computed in i64 (wrapped),
its unused `native_big_integer const l` notwithstanding. -/
def jankPromotingOp (op : Op) (x y : JNum) : Except String JNum :=
  match x, y with
  | .big _, _ | _, .big _ =>
    match x.intValue?, y.intValue? with
    | some a, some b => .ok (.big (match op with | .add => a + b | .sub => a - b | .mul => a * b))
    | _, _ => .error "outside this model"
  | _, _ =>
    match x.intValue?, y.intValue? with
    | some a, some b =>
      let exact : Int := match op with | .add => a + b | .sub => a - b | .mul => a * b
      -- __builtin_*_overflow computes the exact result and reports whether it fits i64.
      if i64min ≤ exact ∧ exact ≤ i64max then .ok (makeBoxI64 (BitVec.ofInt 64 exact))
      else match op with
        | .sub => .ok (.big (BitVec.ofInt 64 (a - b)).toInt)  -- l_val - r in i64: wrapped
        | _ => .ok (.big exact)
    | _, _ => .error "outside this model"

/-- core/math.hpp `div` (object_ref, object_ref) for integer operands: `typed_l->data /
typed_r->data`, C++ integer division (truncation). Division by 0 is documented as undefined;
INT_MIN / -1 of two small integers overflows `int` (a SIGFPE on x86-64). -/
def jankIntDiv : JNum → JNum → Except String JNum
  | .small a, .small b =>
    if b == 0 then .error "UB: integer division by 0 (documented)"
    else if a == BitVec.ofInt 32 i32min && b == -1 then .error "UB: INT_MIN / -1 in int (SIGFPE on x86-64)"
    else .ok (.small (a.sdiv b))
  | x, y => match x, y with
    | .small _, .int _ | .int _, .small _ | .int _, .int _ =>
      let a := match x with | .small v => v.signExtend 64 | .int v => v | _ => 0
      let b := match y with | .small v => v.signExtend 64 | .int v => v | _ => 0
      if b == 0 then .error "UB: integer division by 0 (documented)"
      else if a == BitVec.ofInt 64 i64min && b == -1 then .error "UB: LLONG_MIN / -1"
      else .ok (makeBoxI64 (a.sdiv b))
    | _, _ => .error "outside this model"

/-! ## Clojure: clojure.lang.Numbers -/

namespace Clj

/-- A long result, or the `ArithmeticException("integer overflow")` LongOps throws. -/
def longOrOverflow (v : Int) : Except String CNum :=
  if i64min ≤ v ∧ v ≤ i64max then .ok (.long v) else .error "ArithmeticException: integer overflow"

/-- `+ - *` (Numbers.add/minus/multiply): LongOps throws on overflow, BigInt is exact. -/
def intOp (op : Op) : CNum → CNum → Except String CNum
  | .long a, .long b => longOrOverflow (match op with | .add => a + b | .sub => a - b | .mul => a * b)
  | .long a, .bigint b | .bigint a, .long b | .bigint a, .bigint b =>
    .ok (.bigint (match op with | .add => a + b | .sub => a - b | .mul => a * b))
  | _, _ => .error "outside this model"

/-- `+' -' *'` (Numbers.addP/minusP/multiplyP): the exact value, a BigInt when it leaves long. -/
def promotingOp (op : Op) : CNum → CNum → Except String CNum
  | .long a, .long b =>
    let v := match op with | .add => a + b | .sub => a - b | .mul => a * b
    if i64min ≤ v ∧ v ≤ i64max then .ok (.long v) else .ok (.bigint v)
  | .long a, .bigint b | .bigint a, .long b | .bigint a, .bigint b =>
    .ok (.bigint (match op with | .add => a + b | .sub => a - b | .mul => a * b))
  | _, _ => .error "outside this model"

/-- `/` of integers (Numbers.divide → BigInt division → Ratio, or an integer when it divides). -/
def intDiv : CNum → CNum → Except String CNum
  | x, y =>
    let get : CNum → Option Int := fun | .long v => some v | .bigint v => some v | _ => none
    match get x, get y with
    | some a, some b =>
      if b == 0 then .error "ArithmeticException: Divide by zero"
      else
        let g := Int.gcd a b
        let n := a / g * (if b < 0 then -1 else 1)
        let d := (b / g).natAbs
        if d == 1 then
          -- Numbers.divide: a BigInt result normalized back to a Long when it fits.
          if i64min ≤ n ∧ n ≤ i64max then .ok (.long n) else .ok (.bigint n)
        else .ok (.ratio n d)
    | _, _ => .error "outside this model"

end Clj

/-! ## Search: every operator over a set of interesting operands -/

/-- Integer operands worth drawing: around 0, around the i32 and i64 boundaries. -/
def interesting : List Int :=
  [0, 1, -1, 2, 3, 7, -7, 65536, 100000, i32max, i32max - 1, i32min, i32min + 1,
   2147483648, -2147483649, 4294967296, i64max, i64min, i64max - 1, i64min + 1]

/-- One arithmetic question: an operator and two operands. -/
inductive Question where
  | arith (op : Op) (a b : Int)
  | promoting (op : Op) (a b : Int)
  | divide (a b : Int)
  deriving Repr

def Question.jank : Question → Except String JNum
  | .arith op a b => jankIntOp op (.ofInt a) (.ofInt b)
  | .promoting op a b => jankPromotingOp op (.ofInt a) (.ofInt b)
  | .divide a b => jankIntDiv (.ofInt a) (.ofInt b)

def Question.clj : Question → Except String CNum
  | .arith op a b => Clj.intOp op (JNum.ofInt a).toClj (JNum.ofInt b).toClj
  | .promoting op a b => Clj.promotingOp op (JNum.ofInt a).toClj (JNum.ofInt b).toClj
  | .divide a b => Clj.intDiv (JNum.ofInt a).toClj (JNum.ofInt b).toClj

/-- Whether jank's answer is one its documentation allows: equal to Clojure's, or Clojure threw
for an overflow ("signed integer overflow is well defined": any wrapped value), or a documented
UB (integer division by 0). -/
def Question.allowed (q : Question) : Bool :=
  match q.clj, q.jank with
  | .error e, _ => e == "ArithmeticException: integer overflow" || e == "ArithmeticException: Divide by zero"
  | c, j => sameResult j c

def Question.program : Question → String
  | .arith op a b => s!"({match op with | .add => "+" | .sub => "-" | .mul => "*"} {a} {b})"
  | .promoting op a b => s!"({match op with | .add => "+'" | .sub => "-'" | .mul => "*'"} {a} {b})"
  | .divide a b => s!"(/ {a} {b})"

def showE {α : Type} [Repr α] : Except String α → String
  | .ok v => reprStr v
  | .error e => s!"throws ({e})"

/-- The world for the arithmetic search: a question drawn by decisions. -/
structure ArithWorld where
  decisions : Determinismo.Decisions := {}

instance : Determinismo.Chaotic ArithWorld where
  decisions w := w.decisions
  setDecisions w d := { w with decisions := d }

open Determinismo in
def drawQuestion : EStateM Stop ArithWorld Question := do
  let kind ← decide (σ := ArithWorld) "num.kind" 3
  let op := match ← decide (σ := ArithWorld) "num.op" 3 with | 0 => Op.add | 1 => .sub | _ => .mul
  let a := interesting.getD (← decide (σ := ArithWorld) "num.a" interesting.length) 0
  let b := interesting.getD (← decide (σ := ArithWorld) "num.b" interesting.length) 0
  pure (match kind with | 0 => .arith op a b | 1 => .promoting op a b | _ => .divide a b)

open Determinismo in
def arithBody : EStateM Stop ArithWorld Unit := do
  let q ← drawQuestion
  unless q.allowed do
    violate (σ := ArithWorld) "jank arithmetic = Clojure's (up to documented differences)"
      s!"{q.program}: Clojure {showE q.clj}, jank {showE q.jank}"

open Determinismo in
def runArith (source : Source) : Ended :=
  match arithBody.run { decisions := { source } } with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }
  | .error (.nodeDown _) w => { taken := w.decisions.taken, violation := none }

/-- Every question of one kind (for a table of all deviations, not only the first). -/
def allQuestions : List Question :=
  let ops := [Op.add, .sub, .mul]
  (ops.flatMap fun op => interesting.flatMap fun a => interesting.map fun b => Question.arith op a b)
  ++ (ops.flatMap fun op => interesting.flatMap fun a => interesting.map fun b => Question.promoting op a b)
  ++ (interesting.flatMap fun a => interesting.map fun b => Question.divide a b)

/-! ## Theorems on the fixed-width arithmetic -/

/-- Two small integers' `+` in jank is the true sum exactly when the 32-bit `int` addition does
not overflow: the deviation from Clojure is precisely the i32-overflowing sums (all of which are
far inside the i64 range Clojure computes in). -/
theorem small_add_exact_iff (a b : BitVec 32) :
    ((a + b).signExtend 64 = a.signExtend 64 + b.signExtend 64) ↔ ¬ BitVec.saddOverflow a b := by
  bv_decide

/-- Any two i32 values' true sum fits i64: Clojure never throws for them, so every 32-bit
overflow of jank's `+` is a wrong answer, not a documented wrap. -/
theorem small_add_fits_i64 (a b : BitVec 32) :
    ¬ BitVec.saddOverflow (a.signExtend 64) (b.signExtend 64) := by
  bv_decide

/-- `promoting_add` on two small integers: `__builtin_add_overflow` into an `i64` never
overflows, so `+'` is exact on them (it is `+` that is wrong). -/
theorem promoting_add_small_exact (a b : BitVec 32) :
    ¬ BitVec.saddOverflow (a.signExtend 64) (b.signExtend 64) := small_add_fits_i64 a b

/-- `promoting_sub`'s overflow branch boxes `l_val - r` computed in i64: whenever it is taken
(an i64 overflow), the big integer it returns differs from the true difference. -/
theorem promoting_sub_overflow_wrong (a b : BitVec 64) (h : BitVec.ssubOverflow a b) :
    (a - b).signExtend 65 ≠ a.signExtend 65 - b.signExtend 65 := by
  bv_decide

/-- jank's `rem` on integers (core/math.cpp `rem`, last branch): `div == -1` returns 0, else
C++ `%`. It equals Java's `%` (BitVec.srem, which gives 0 for MIN % -1) for every i64 pair. -/
def jankRemI64 (a b : BitVec 64) : BitVec 64 := if b == -1 then 0 else a.srem b

theorem jank_rem_eq_java (a b : BitVec 64) : jankRemI64 a b = a.srem b := by
  unfold jankRemI64; bv_decide

/-- `bit-shift-left` (core/math.cpp `bit_shift_left`: `l_data << r_data`): for shift counts
0..63 it is Java's `x << n`. For n ≥ 64 or n < 0 the C++ shift is undefined behavior; Java masks
the count with 63. (Stated, not a deviation we report: x86-64 and AArch64 also mask by 63.) -/
theorem shift_in_range_java (x : BitVec 64) (n : BitVec 64) (h : n < 64) :
    x <<< n = x <<< (n &&& 63) := by
  bv_decide

/-! ## Doubles: `quot`, `==`, `abs`, `bigdec` -/

/-- How `static_cast<i64>(double)` behaves out of range (C++: undefined). -/
inductive Platform where
  /-- cvttsd2si: the "integer indefinite" 0x8000000000000000. -/
  | x86_64
  /-- fcvtzs: saturating. -/
  | aarch64
  deriving Repr, BEq

def castF64ToI64 (p : Platform) (f : Float) : BitVec 64 :=
  if f.isNaN then (if p == .x86_64 then BitVec.ofInt 64 i64min else 0)
  else if f ≥ 9223372036854775808.0 || f < -9223372036854775808.0 then
    (if p == .x86_64 then BitVec.ofInt 64 i64min else (f.toInt64).toBitVec)
  else (f.toInt64).toBitVec

/-- `to_real` of a jank number (number.hpp `to_real`; i64 → f64 rounds to nearest). -/
def JNum.toReal : JNum → Float
  | .small v => Float.ofInt v.toInt
  | .int v => Float.ofInt v.toInt
  | .big v => Float.ofInt v
  | .ratio n d => Float.ofInt n / Float.ofNat d
  | .real f => f

/-- core/math.cpp `quot`: both operands `to_real`, divided as doubles, `static_cast<i64>`, boxed
as an integer, whatever the operand types. -/
def jankQuot (p : Platform) (x y : JNum) : Except String JNum :=
  let l := x.toReal
  let r := y.toReal
  if r == 0.0 then .error "throws (a string: Division by zero is not permitted.)"
  else .ok (makeBoxI64 (castF64ToI64 p (l / r)))

/-- Clojure `quot` of doubles (Numbers.quotient(double, double)): the truncated quotient as a
double. -/
def cljQuotDouble (a b : Float) : Except String CNum :=
  if b == 0.0 then .error "ArithmeticException: Divide by zero"
  else let q := a / b
       .ok (.double (if q < 0.0 then -(Float.floor (-q)) else Float.floor q))

/-- Clojure `quot` (Numbers.quotient): longs → `x / y` (Java truncation); a double operand →
the truncated quotient as a double. -/
def cljQuot : CNum → CNum → Except String CNum
  -- LongOps.quotient: `x.longValue() / y.longValue()`, Java's wrapping long division.
  | .long a, .long b => if b == 0 then .error "ArithmeticException: Divide by zero"
      else .ok (.long ((BitVec.ofInt 64 a).sdiv (BitVec.ofInt 64 b)).toInt)
  | .double a, .double b => cljQuotDouble a b
  | .long a, .double b => cljQuotDouble (Float.ofInt a) b
  | .double a, .long b => cljQuotDouble a (Float.ofInt b)
  | _, _ => .error "outside this model"

/-- core/math.cpp `is_equiv` (`==`): both `to_real`, compared as doubles. -/
def jankEquiv (x y : JNum) : Bool := x.toReal == y.toReal

/-- Clojure `==` (Numbers.equiv): two longs compare as longs; a double makes it a double
comparison. -/
def cljEquiv : CNum → CNum → Bool
  | .long a, .long b => a == b
  | .bigint a, .long b | .long a, .bigint b | .bigint a, .bigint b => a == b
  | .double a, .double b => a == b
  | .long a, .double b => Float.ofInt a == b
  | .double a, .long b => a == Float.ofInt b
  | _, _ => false

/-- core/math.hpp `abs` (object_ref): `typed_l->data < 0ll ? make_box(-1ll * data) : make_box(data)`.
For -0.0, `-0.0 < 0` is false: -0.0 is returned as is. -/
def jankAbsReal (f : Float) : Float := if f < 0.0 then -1.0 * f else f

/-- Clojure `abs` (Numbers.abs → Math.abs(double)): "If a is a double and zero => +0.0". -/
def cljAbsReal (f : Float) : Float := Float.abs f

/-- core/math.cpp `to_big_decimal` for an integer: `make_box<obj::big_decimal>(typed_o->to_real())`:
the long goes through a double. The decimal's integral value: -/
def jankBigdecOfLong (v : Int) : Int := (Float.ofInt v).toInt64.toInt

/-- Clojure `bigdec` of a long: `BigDecimal.valueOf(long)`, exact. -/
def cljBigdecOfLong (v : Int) : Int := v

/-! ## BigDecimal `=` (big_decimal.cpp `big_decimal::equal`)

    return abs(data - typed_o->data) < std::numeric_limits<f64>::epsilon();

Two big decimals are `=` in jank when they differ by less than 2^-52. Clojure (Numbers.equal →
BigDecimalOps.equiv): `compareTo == 0`, the exact values. A decimal here is `n / 10^scale`. -/

structure Dec where
  n : Int
  scale : Nat
  deriving Repr, BEq

def Dec.code (d : Dec) : String :=
  let s := toString d.n.natAbs
  let s := if s.length ≤ d.scale then String.mk (List.replicate (d.scale + 1 - s.length) '0') ++ s else s
  let intPart := s.take (s.length - d.scale)
  let frac := s.drop (s.length - d.scale)
  (if d.n < 0 then "-" else "") ++ intPart ++ (if d.scale == 0 then "" else "." ++ frac) ++ "M"

/-- |a - b| < 2^-52, exactly: |a.n·10^b.s − b.n·10^a.s| · 2^52 < 10^(a.s + b.s). -/
def jankDecEq (a b : Dec) : Bool :=
  let diff := (a.n * 10 ^ b.scale - b.n * 10 ^ a.scale).natAbs
  diff * 2 ^ 52 < 10 ^ (a.scale + b.scale)

def cljDecEq (a b : Dec) : Bool := a.n * 10 ^ b.scale == b.n * 10 ^ a.scale

/-- `(= 1M 1.0000000000000000001M)`. -/
theorem bigdec_eq_epsilon :
    jankDecEq ⟨1, 0⟩ ⟨10000000000000000001, 19⟩ = true ∧
    cljDecEq ⟨1, 0⟩ ⟨10000000000000000001, 19⟩ = false := by decide

/-- Not transitive: 0M = 0.00000000000000015M = 0.0000000000000003M, but 0M ≠ 0.0000000000000003M. -/
theorem bigdec_eq_not_transitive :
    jankDecEq ⟨0, 0⟩ ⟨15, 17⟩ = true ∧ jankDecEq ⟨15, 17⟩ ⟨3, 16⟩ = true ∧
    jankDecEq ⟨0, 0⟩ ⟨3, 16⟩ = false := by decide

/-! ## NaN boxing (oref.hpp) -/

/-- "Anything below this is an encoded real value." -/
def maxReal : BitVec 64 := 0xFFF8000000000000
def integerNanTag : BitVec 64 := 0xFFF9000000000000
def integerValueMask : BitVec 64 := 0x00000000FFFFFFFF
def pointerNanTag : BitVec 64 := 0xFFFA000000000000
def pointerValueMask : BitVec 64 := 0x0000FFFFFFFFFFFF

/-- oref.hpp `detail::is_tagged_small_real`. -/
def isTaggedSmallReal (b : BitVec 64) : Bool := b < maxReal
/-- oref.hpp `detail::is_tagged_small_int`. -/
def isTaggedSmallInt (b : BitVec 64) : Bool := (b &&& ~~~integerValueMask) == integerNanTag
/-- oref.hpp `detail::is_tagged_pointer`. -/
def isTaggedPointer (b : BitVec 64) : Bool := (b &&& ~~~pointerValueMask) == pointerNanTag
/-- oref.hpp `detail::as_pointer` (the debug assertion compiled out in release). -/
def asPointer (b : BitVec 64) : BitVec 64 := b &&& pointerValueMask

/-- oref.hpp `detail::tag<T>(f64 d)`: `std::bit_cast<T>(d)`, no canonicalization. -/
def tagReal (bits : BitVec 64) : BitVec 64 := bits

/-- What `oref<object>::get_type()` does with a word: a small int, a small real, else a read of
`ptr()->type` at `as_pointer(word)`. -/
inductive Decoded where
  | smallInt | smallReal | heapObjectAt (address : BitVec 64)
  deriving Repr, DecidableEq

def decode (b : BitVec 64) : Decoded :=
  if isTaggedSmallInt b then .smallInt
  else if isTaggedSmallReal b then .smallReal
  else .heapObjectAt (asPointer b)

/-- IEEE-754 binary64: a NaN (exponent all ones, mantissa nonzero). -/
def isNaN64 (b : BitVec 64) : Bool :=
  (b &&& 0x7FF0000000000000) == 0x7FF0000000000000 && (b &&& 0x000FFFFFFFFFFFFF) != 0

/-- The default NaN an invalid operation (∞-∞, 0·∞, 0/0, sqrt(-1)) produces: x86-64 SSE's
"QNaN floating-point indefinite" has the sign bit set; AArch64's default NaN does not. -/
def defaultNaN : Platform → BitVec 64
  | .x86_64 => 0xFFF8000000000000
  | .aarch64 => 0x7FF8000000000000

/-- Every double is decoded as a real, except exactly the NaNs whose sign and quiet bits are set:
those are read as pointers. -/
theorem real_decoded_iff (b : BitVec 64) :
    decode (tagReal b) = .smallReal ↔ b < maxReal := by
  have hInt : isTaggedSmallInt b = true → ¬ b < maxReal := by
    unfold isTaggedSmallInt maxReal integerNanTag integerValueMask
    intro h; simp only [beq_iff_eq] at h; bv_decide
  unfold decode tagReal
  by_cases hi : isTaggedSmallInt b = true
  · simp only [hi, if_true]
    constructor
    · intro h; cases h
    · intro h; exact absurd h (hInt hi)
  · by_cases hr : isTaggedSmallReal b = true
    · simp only [hi, hr, if_true, if_false, Bool.false_eq_true]
      unfold isTaggedSmallReal at hr
      simpa using hr
    · simp only [hi, hr, if_false, Bool.false_eq_true]
      unfold isTaggedSmallReal at hr
      constructor
      · intro h; cases h
      · intro h; simp_all

/-- The only doubles not decoded as reals are NaNs (with the sign bit set). -/
theorem misdecoded_are_negative_nans (b : BitVec 64) (h : ¬ b < maxReal) :
    isNaN64 b = true ∧ b.msb = true := by
  unfold isNaN64 maxReal at *
  bv_decide

/-- On x86-64 the default NaN is decoded as a heap object at address 0: `get_type()` reads
`ptr()->type` through a null pointer. On AArch64 it is a real. -/
theorem x86_default_nan_is_null_object :
    decode (tagReal (defaultNaN .x86_64)) = .heapObjectAt 0 := by
  decide

theorem arm_default_nan_is_real :
    decode (tagReal (defaultNaN .aarch64)) = .smallReal := by
  decide

/-- A small integer round-trips through its tag (oref.hpp `tag(i32)`, `as_integer`). -/
def tagInt (v : BitVec 32) : BitVec 64 := integerNanTag ||| ((v.zeroExtend 64) &&& integerValueMask)
def asInteger (b : BitVec 64) : BitVec 32 := (b &&& integerValueMask).truncate 32

theorem small_int_roundtrip (v : BitVec 32) :
    decode (tagInt v) = .smallInt ∧ asInteger (tagInt v) = v := by
  have h : isTaggedSmallInt (tagInt v) = true := by
    unfold isTaggedSmallInt tagInt integerNanTag integerValueMask
    simp only [beq_iff_eq]; bv_decide
  constructor
  · simp [decode, h]
  · unfold asInteger tagInt integerNanTag integerValueMask; bv_decide

/-! ## parse-long / parse-double (core/math.cpp `parse_long`, `parse_double`)

jank: `std::stoll(s, &parsed_upto)` / `std::stod`, nil on an exception or when
`parsed_upto != size`. `strtoll` skips leading `isspace` characters, takes an optional sign
and decimal digits; it throws `invalid_argument` with no digits and `out_of_range` outside i64.

Clojure 1.12 `parse-long`: "Parse string of decimal digits with optional leading - or + and return
a Long value, or nil if parse fails" (`Long/valueOf`, no whitespace). -/

def isCSpace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == Char.ofNat 11 || c == Char.ofNat 12

/-- `std::stoll(str, &idx)` then the `idx != size` check: the parsed value, or none. -/
def jankParseLong (s : String) : Option Int :=
  let cs := s.toList
  let rest := cs.dropWhile isCSpace
  let (neg, rest) := match rest with
    | '-' :: r => (true, r) | '+' :: r => (false, r) | r => (false, r)
  let digits := rest.takeWhile Char.isDigit
  if digits.isEmpty then none  -- std::invalid_argument → nil
  else
    let mag : Int := digits.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0
    let v := if neg then -mag else mag
    if v < i64min || v > i64max then none  -- std::out_of_range → nil
    else
      -- parsed_upto counts the skipped whitespace, the sign and the digits.
      let consumed := (cs.length - rest.length) + digits.length
      if consumed != cs.length then none else some v

/-- Clojure `parse-long`: `[+-]?[0-9]+` within the long range. -/
def cljParseLong (s : String) : Option Int :=
  let cs := s.toList
  let (neg, rest) := match cs with
    | '-' :: r => (true, r) | '+' :: r => (false, r) | r => (false, r)
  if rest.isEmpty || !rest.all Char.isDigit then none
  else
    let mag : Int := rest.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0
    let v := if neg then -mag else mag
    if v < i64min || v > i64max then none else some v

/-- `std::stod` + the full-consumption check, as an acceptance test on a small alphabet: leading
whitespace, a sign, then "inf"/"infinity"/"nan" (any case) or decimal digits with an optional
fraction and exponent; out of the double range (overflow or underflow, ERANGE) → nil. Values are
not modeled, only which strings give a number and whether it is finite. -/
inductive Parsed where | none | finite | infinite | nan
  deriving BEq

instance : Repr Parsed where
  reprPrec p _ := match p with
    | .none => "nil" | .finite => "a finite double" | .infinite => "##Inf" | .nan => "##NaN"

def lower (c : Char) : Char := c.toLower

def decimalShape (cs : List Char) : Option (List Char × Int) :=
  -- digits [. digits] [e [sign] digits]; returns the rest and the decimal exponent of the
  -- leading digit (to tell overflow), or none when no digit at all.
  let intDigits := cs.takeWhile Char.isDigit
  let r1 := cs.drop intDigits.length
  let (fracDigits, r2) := match r1 with
    | '.' :: r => let f := r.takeWhile Char.isDigit; (f, r.drop f.length)
    | r => ([], r)
  if intDigits.isEmpty && fracDigits.isEmpty then none
  else
    let (expo, r3) := match r2 with
      | e :: r =>
        if lower e == 'e' then
          let (neg, r') := match r with | '-' :: q => (true, q) | '+' :: q => (false, q) | q => (false, q)
          let ds := r'.takeWhile Char.isDigit
          if ds.isEmpty then ((0 : Int), r2)
          else
            let m : Int := ds.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0
            ((if neg then -m else m), r'.drop ds.length)
        else ((0 : Int), r2)
      | [] => ((0 : Int), [])
    let allZero := (intDigits ++ fracDigits).all (· == '0')
    let lead : Int := if allZero then 0 else
      -- position of the first nonzero digit relative to the decimal point
      let iz := intDigits.dropWhile (· == '0')
      if !iz.isEmpty then iz.length - 1 else
        -(((fracDigits.takeWhile (· == '0')).length : Int) + 1)
    some (r3, if allZero then 0 else lead + expo)

def jankParseDouble (s : String) : Parsed :=
  let cs := s.toList
  let r := cs.dropWhile isCSpace
  let r := match r with | '-' :: q => q | '+' :: q => q | q => q
  let low := r.map lower
  if low == "infinity".toList || low == "inf".toList then .infinite
  else if low == "nan".toList then .nan
  else match decimalShape r with
    | none => .none
    | some (rest, mag) =>
      if !rest.isEmpty then .none
      else if mag > 308 || mag < -324 then .none  -- ERANGE → std::out_of_range → nil
      else .finite

/-- Clojure `parse-double` (`Double/valueOf` grammar, java.lang.Double#valueOf): whitespace
trimmed on both ends, an optional sign, "NaN" or "Infinity" (exact case), or a decimal with an
optional format suffix f/F/d/D; overflow gives Infinity, underflow 0.0. -/
def cljParseDouble (s : String) : Parsed :=
  let cs := (s.toList.dropWhile (· ≤ ' ')).reverse.dropWhile (· ≤ ' ') |>.reverse
  let r := match cs with | '-' :: q => q | '+' :: q => q | q => q
  if r == "Infinity".toList then .infinite
  else if r == "NaN".toList then .nan
  else
    let r := match r.reverse with
      | c :: q => if c == 'd' || c == 'D' || c == 'f' || c == 'F' then q.reverse else r
      | [] => r
    match decimalShape r with
    | none => .none
    | some (rest, mag) =>
      if !rest.isEmpty then .none
      else if mag > 308 then .infinite else .finite

end Jank.Numbers
