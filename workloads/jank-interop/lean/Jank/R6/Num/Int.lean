import Jank.Numbers

/-!
# Round 6, numbers: integer overflow on every path (LG2, D1, R25, D3, R5)

Extends round 1's `Jank.Numbers.jankIntOp` (which saw only objects reaching math.hpp) with the
C++ type each operand has when a Clojure form reaches `core/math.hpp`, as decided by the reader
and the analyzer at 94d32623 (paths under upstream-r5/compiler+runtime/):

- a literal that fits i32 is a C++ `int`; one outside i32 a C++ `long` (analyze/cpp_util.cpp
  `literal_type` 630-643, 652-658; emitted as `auto tN(<digits>);`, codegen/cpp_processor.cpp
  `gen(cpp_literal)` 1278-1285, `lift_constant` 131-149);
- a `let`-bound local keeps its init's C++ type (analyze/processor.cpp `analyze_let` 2370-2421;
  a `loop` binding too, `mutable_type` only erases typed objects, cpp_util.cpp 1064-1089);
- `+ - * /` with two arguments inline to `cpp/jank.runtime.add` etc. (clojure/core.jank
  1371-1434, `:inline-arities #{2}`); any other arity, and any call through a fn value, runs the
  fn body, whose parameters are `object_ref`s;
- an `object_ref` integer is a `small_integer` (`i32 data`) when it fits i32, else an `integer`
  (`i64 data`) (core/make_box.hpp 89-101; visit.hpp `visit_number_like` 463-498);
- the literal `-9223372036854775808` is read as a `big_integer` (round 2's R5: read/lex.cpp
  1145-1156 runs `strtoll` on the digits after `-`, which overflows).

math.hpp then computes `l OP r` in the C++ type the usual arithmetic conversions give: `int OP
int` is 32-bit, anything with a `long` is 64-bit, both wrapping (`-fwrapv`, round 3), and a
`cpp_int` operand makes it exact. `inc`/`dec` check with `__builtin_*_overflow` (math.hpp
1186-1340); `+' -' *' inc' dec'` are math.cpp `promoting_*` (50-175, 352-403).

Clojure (clojure-ref Numbers.java, 1.12): with both operands primitive longs (literals or
let-bound literals) the compiler calls `Numbers.add/minus/multiply(long, long)` = `Math.addExact`
etc. (1921-1985), which throw `ArithmeticException("long overflow")`; with any Object operand
(a fn parameter) it calls `add/minus/multiply(Object, Object)` (154-178), where `minus` is
`add(x, negate(y))` and `LongOps.negate` is `Math.negateExact` (651-654): it throws when
`y = Long/MIN_VALUE` even if `x - y` fits. Checked on Clojure 1.12.0
(.r6-scratch/num/probe/probe1.out).
-/

namespace Jank.R6.Num

open Jank.Numbers (Op i64min i64max i32min i32max)

/-! ## Values and paths -/

/-- A Clojure integer value: a Long or a BigInt. -/
inductive CInt where
  | long (v : Int)
  | big (v : Int)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- How an operand reaches the call. -/
inductive Src where
  /-- Written as a literal in the call, or a `let`-bound local initialized by a literal. -/
  | lit
  /-- A literal passed through a fn parameter (an object; the reader's R5 still applies). -/
  | fnLit
  /-- A value computed at run time and passed through a fn parameter (an object). -/
  | fnVal
  deriving Repr, BEq, DecidableEq, Inhabited

def Src.isObj : Src → Bool
  | .lit => false
  | _ => true

/-- The C++ data an integer operand has inside math.hpp. -/
inductive Rep where
  /-- C++ `int`: an `int`-typed literal or local, or a `small_integer` object's data. -/
  | i32 (v : Int)
  /-- C++ `long`: a `long`-typed literal or local, or an `integer` object's data. -/
  | i64 (v : Int)
  /-- `native_big_integer` (boost `cpp_int`) of a `big_integer` object. -/
  | big (v : Int)
  deriving Repr, BEq, DecidableEq, Inhabited

def Rep.val : Rep → Int
  | .i32 v | .i64 v | .big v => v

def inI32 (v : Int) : Bool := decide (i32min ≤ v) && decide (v ≤ i32max)
def inI64 (v : Int) : Bool := decide (i64min ≤ v) && decide (v ≤ i64max)

/-- What jank's reader, analyzer and `make_box` make of a Clojure integer reaching math.hpp. -/
def jRep : CInt → Src → Rep
  | .big v, _ => .big v
  | .long v, .lit => if v == i64min then .big v else if inI32 v then .i32 v else .i64 v
  | .long v, .fnLit => if v == i64min then .big v else if inI32 v then .i32 v else .i64 v
  | .long v, .fnVal => if inI32 v then .i32 v else .i64 v

/-- A result as a program sees it: its kind and value. -/
inductive R where
  | long (v : Int)
  | big (v : Int)
  deriving Repr, BEq, DecidableEq, Inhabited

abbrev Out := Except String R

def R.val : R → Int
  | .long v | .big v => v

def showR : R → String
  | .long v => toString v
  | .big v => s!"{v}N"

def showOut : Out → String
  | .ok r => showR r
  | .error e => s!"throws ({e})"

def exact : Op → Int → Int → Int
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b

/-- C++ two's complement wrapping at width `w` (`-fwrapv`): the value's `bmod`. -/
def wrap (w : Nat) (z : Int) : Int := z.bmod (2 ^ w)

/-! ## jank -/

/-- math.hpp `add`/`sub`/`mul` (71-520) on two integer operands, whatever overload is reached
(native/native `l OP r`, native/object and object/object `make_box(l OP typed_r->data)`): the
operation happens in the C++ type of the operands. -/
def jArith (op : Op) : Rep → Rep → R
  | .i32 a, .i32 b => .long (wrap 32 (exact op a b))
  | .big a, b => .big (exact op a b.val)
  | a, .big b => .big (exact op a.val b)
  | a, b => .long (wrap 64 (exact op a.val b.val))

/-- `(- x)`: the 1-arity of `-` is `(- 0 x)` (core.jank 1393-1394): `0 - x` in x's C++ type
(`int 0 - int` or `small 0 - small` are both 32-bit). -/
def jNeg (x : Rep) : R := jArith .sub (.i32 0) x

/-- math.hpp `inc`/`dec` (1186-1340): fixed integers through `__builtin_add/sub_overflow(data,
1ll, &i64)`, which throws the string "Overflow on increment." (both); a `cpp_int` is exact. -/
def jIncDec (up : Bool) : Rep → Out
  | .big v => .ok (.big (if up then v + 1 else v - 1))
  | x =>
    let r := if up then x.val + 1 else x.val - 1
    if inI64 r then .ok (.long r) else .error "Overflow on increment."

/-- math.cpp `promoting_inc`/`promoting_dec` (352-403): exact; a BigInt only on overflow. -/
def jIncDecP (up : Bool) : Rep → R
  | .big v => .big (if up then v + 1 else v - 1)
  | x =>
    let r := if up then x.val + 1 else x.val - 1
    if inI64 r then .long r else .big r

/-- math.cpp `promoting_add`/`promoting_mul` (50-100, 136-169) are exact; `promoting_sub`
(102-134) boxes `l_val - typed_r->data` computed in i64 on overflow (round 1's D3). -/
def jArithP (op : Op) : Rep → Rep → R
  | .big a, b => .big (exact op a b.val)
  | a, .big b => .big (exact op a.val b)
  | a, b =>
    let r := exact op a.val b.val
    if inI64 r then .long r
    else match op with
      | .sub => .big (wrap 64 r)
      | _ => .big r

/-- math.hpp `abs` (994-1040), object branch: `data < 0ll ? make_box(-1ll * data) : ...`; an i32
is widened by `-1ll *`, an i64 wraps at Long/MIN_VALUE. The native branch is `std::abs(i64)`. -/
def jAbs : Rep → R
  | .i32 v => .long (if v < 0 then -v else v)
  | .i64 v => .long (if v < 0 then wrap 64 (-v) else v)
  | .big v => .big (if v < 0 then -v else v)

/-- math.cpp `rem` (226-304), integer branches: `div == 0` throws, `div == -1` gives 0, else C++
`%` (truncating); a `cpp_int` operand gives `cpp_int %` (a BigInt). -/
def jRem : Rep → Rep → Out
  | a, b =>
    match a, b with
    | .big _, _ | _, .big _ =>
      if b.val == 0 then .error "Division by zero is not permitted."
      else .ok (.big (a.val.tmod b.val))
    | _, _ =>
      if b.val == 0 then .error "Division by zero is not permitted."
      else if b.val == -1 then .ok (.long 0)
      else .ok (.long (a.val.tmod b.val))

/-! ## Clojure 1.12 (Numbers.java) -/

/-- Whether Clojure compiles the call to the primitive `(long, long)` overload: both operands
are long literals or let-bound long literals. -/
def staticPath (x y : CInt) (sx sy : Src) : Bool :=
  match x, y with
  | .long _, .long _ => sx == .lit && sy == .lit
  | _, _ => false

def longOrThrow (r : Int) : Out := if inI64 r then .ok (.long r) else .error "long overflow"

/-- `+ - *`: `Math.addExact`/`subtractExact`/`multiplyExact` on the static path; on the Object
path `LongOps.add/multiply` (the same checks) and `minus = add(x, negate(y))`; BigIntOps exact. -/
def cArith (op : Op) (x y : CInt) (static : Bool) : Out :=
  match x, y with
  | .long a, .long b =>
    if static then longOrThrow (exact op a b)
    else match op with
      | .sub => if b == i64min then .error "long overflow" else longOrThrow (a - b)
      | _ => longOrThrow (exact op a b)
  | _, _ =>
    match op, y with
    | .sub, .long b => if b == i64min then .error "long overflow"
                       else .ok (.big (exact op (match x with | .long v | .big v => v) b))
    | _, _ =>
      let a := match x with | .long v | .big v => v
      let b := match y with | .long v | .big v => v
      .ok (.big (exact op a b))

def CInt.val : CInt → Int
  | .long v | .big v => v

/-- `(- x)`: `Math.negateExact` / `LongOps.negate`; BigInt negates. -/
def cNeg : CInt → Out
  | .long v => if v == i64min then .error "long overflow" else .ok (.long (-v))
  | .big v => .ok (.big (-v))

/-- `inc`/`dec`: `Math.incrementExact`/`decrementExact`, BigIntOps.inc/dec. -/
def cIncDec (up : Bool) : CInt → Out
  | .long v => longOrThrow (if up then v + 1 else v - 1)
  | .big v => .ok (.big (if up then v + 1 else v - 1))

/-- `inc'`/`dec'`: `incP`/`decP`. -/
def cIncDecP (up : Bool) : CInt → Out
  | .long v => let r := if up then v + 1 else v - 1
               .ok (if inI64 r then .long r else .big r)
  | .big v => .ok (.big (if up then v + 1 else v - 1))

/-- `+' *'` (addP, multiplyP) and `-'` (minusP): on the static path `minusP(long, long)` is
exact (a Long when it fits); on the Object path `minusP(x, y)` = `addP(x, negateP(y))`, and
`negateP(Long/MIN_VALUE)` is a BigInt, so the result is then a BigInt even when it fits. -/
def cArithP (op : Op) (x y : CInt) (static : Bool) : Out :=
  match x, y with
  | .long a, .long b =>
    let r := exact op a b
    let lp := if inI64 r then R.long r else R.big r
    match op with
    | .sub => if !static && b == i64min then .ok (.big r) else .ok lp
    | _ => .ok lp
  | _, _ => .ok (.big (exact op x.val y.val))

/-- `abs`: `Math.abs(long)` (Long/MIN_VALUE stays, as the docstring says); BigInt abs. -/
def cAbs : CInt → R
  | .long v => .long (if v < 0 then wrap 64 (-v) else v)
  | .big v => .big (if v < 0 then -v else v)

/-- `rem`: `LongOps.remainder` (`x % y`: MIN % -1 is 0), BigIntOps.remainder. -/
def cRem (x y : CInt) : Out :=
  if y.val == 0 then .error "Divide by zero"
  else match x, y with
    | .long a, .long b => .ok (.long (a.tmod b))
    | _, _ => .ok (.big (x.val.tmod y.val))

/-! ## Outcomes -/

/-- How two outcomes compare. -/
inductive Verdict where
  | agree
  /-- jank returns a value where Clojure throws. -/
  | valueVsThrow
  /-- jank throws where Clojure returns. -/
  | throwVsValue
  /-- different values. -/
  | wrongValue
  /-- the same value as a long in one and a BigInt in the other (`pr-str`, `hash` tell). -/
  | wrongKind
  deriving Repr, BEq, DecidableEq, Inhabited

def verdict (j c : Out) : Verdict :=
  match j, c with
  | .error _, .error _ => .agree
  | .ok _, .error _ => .valueVsThrow
  | .error _, .ok _ => .throwVsValue
  | .ok a, .ok b =>
    if a = b then .agree else if a.val = b.val then .wrongKind else .wrongValue

/-! ## The fix (fixes/LG2.diff): checked arithmetic in i64 for every fixed-width pair -/

/-- The fixed `add`/`sub`/`mul`: `__builtin_*_overflow(l, r, &i64)` on every pair of fixed
integers (i32 or i64), throwing on overflow; `cpp_int` unchanged. -/
def jArithFixed (op : Op) : Rep → Rep → Out
  | .big a, b => .ok (.big (exact op a b.val))
  | a, .big b => .ok (.big (exact op a.val b))
  | a, b =>
    let r := exact op a.val b.val
    if inI64 r then .ok (.long r) else .error "integer overflow"

/-- The fixed reader (fixes/R5.diff): `-9223372036854775808` is an `integer`. -/
def jRepFixed : CInt → Src → Rep
  | .big v, _ => .big v
  | .long v, _ => if inI32 v then .i32 v else .i64 v

/-! ## Lemmas: C++ fixed-width arithmetic is `wrap` -/

theorem bmod64_eq_iff (z : Int) : z.bmod (2 ^ 64) = z ↔ -(2 ^ 63 : Int) ≤ z ∧ z < 2 ^ 63 := by
  simp only [Int.bmod]
  constructor
  · intro h; split at h <;> omega
  · intro h; split <;> omega

theorem bmod32_eq_iff (z : Int) : z.bmod (2 ^ 32) = z ↔ -(2 ^ 31 : Int) ≤ z ∧ z < 2 ^ 31 := by
  simp only [Int.bmod]
  constructor
  · intro h; split at h <;> omega
  · intro h; split <;> omega

theorem wrap64_eq_iff (z : Int) : wrap 64 z = z ↔ inI64 z = true := by
  unfold wrap inI64 i64min i64max
  rw [bmod64_eq_iff]; simp; omega

theorem wrap32_eq_iff (z : Int) : wrap 32 z = z ↔ inI32 z = true := by
  unfold wrap inI32 i32min i32max
  rw [bmod32_eq_iff]; simp; omega

/-- C++ `int OP int` with `-fwrapv` (BitVec 32) is `wrap 32` of the exact result. -/
theorem cpp_int_op (op : Op) (a b : BitVec 32) :
    (Jank.Numbers.bvOp op a b).toInt = wrap 32 (exact op a.toInt b.toInt) := by
  cases op <;> simp [Jank.Numbers.bvOp, exact, wrap, BitVec.toInt_add, BitVec.toInt_sub,
    BitVec.toInt_mul]

/-- C++ `long OP long` (and `int OP long` after the `int` is sign-extended) is `wrap 64`. -/
theorem cpp_long_op (op : Op) (a b : BitVec 64) :
    (Jank.Numbers.bvOp op a b).toInt = wrap 64 (exact op a.toInt b.toInt) := by
  cases op <;> simp [Jank.Numbers.bvOp, exact, wrap, BitVec.toInt_add, BitVec.toInt_sub,
    BitVec.toInt_mul]

theorem cpp_int_long_op (op : Op) (a : BitVec 32) (b : BitVec 64) :
    (Jank.Numbers.bvOp op (a.signExtend 64) b).toInt = wrap 64 (exact op a.toInt b.toInt) := by
  rw [cpp_long_op, BitVec.toInt_signExtend_of_le (by omega)]

theorem inI32_iff (v : Int) : inI32 v = true ↔ -2147483648 ≤ v ∧ v ≤ 2147483647 := by
  unfold inI32 i32min i32max
  by_cases h1 : -2147483648 ≤ v <;> by_cases h2 : v ≤ 2147483647 <;> simp [h1, h2]

theorem inI64_iff (v : Int) :
    inI64 v = true ↔ -9223372036854775808 ≤ v ∧ v ≤ 9223372036854775807 := by
  unfold inI64 i64min i64max
  by_cases h1 : -9223372036854775808 ≤ v <;> by_cases h2 : v ≤ 9223372036854775807 <;> simp [h1, h2]

/-- Every exact `+ - *` of two i32 values fits i64 (so Clojure never throws on them). -/
theorem i32_exact_fits_i64 (op : Op) (a b : Int) (ha : inI32 a = true) (hb : inI32 b = true) :
    inI64 (exact op a b) = true := by
  rw [inI32_iff] at ha hb
  rw [inI64_iff]
  cases op
  · simp only [exact]; omega
  · simp only [exact]; omega
  · simp only [exact]
    have hx : a.natAbs ≤ 2147483648 := by omega
    have hy : b.natAbs ≤ 2147483648 := by omega
    have hxy : (a * b).natAbs ≤ 2147483648 * 2147483648 := by
      rw [Int.natAbs_mul]; exact Nat.mul_le_mul hx hy
    omega

theorem jRepFixed_val (v : Int) (src : Src) : (jRepFixed (.long v) src).val = v := by
  simp only [jRepFixed]; split <;> rfl

theorem jRepFixed_not_big (v : Int) (src : Src) (w : Int) : jRepFixed (.long v) src ≠ .big w := by
  simp only [jRepFixed]; split <;> simp

theorem jArithFixed_fixed (op : Op) (ra rb : Rep) (hra : ∀ w, ra ≠ .big w) (hrb : ∀ w, rb ≠ .big w) :
    jArithFixed op ra rb =
      (if inI64 (exact op ra.val rb.val) then .ok (.long (exact op ra.val rb.val))
       else .error "integer overflow") := by
  cases ra <;> cases rb <;> simp_all [jArithFixed, Rep.val]

theorem jArithP_fixed (op : Op) (ra rb : Rep) (hra : ∀ w, ra ≠ .big w) (hrb : ∀ w, rb ≠ .big w) :
    jArithP op ra rb =
      (let r := exact op ra.val rb.val
       if inI64 r then .long r else match op with | .sub => .big (wrap 64 r) | _ => .big r) := by
  cases ra <;> cases rb <;> simp_all [jArithP, Rep.val]

/-! ## Theorems: where jank's `+ - *` depart from Clojure, for every input -/

/-- ★ Two `int` operands (literals, let-bound literals, `small_integer` objects, in any mix):
jank's result is wrong exactly when the true result leaves i32, and then Clojure returns the true
value (D1, R25): a wrong value, never a throw. -/
theorem i32_pair_verdict (op : Op) (a b : Int) (ha : inI32 a = true) (hb : inI32 b = true) :
    verdict (.ok (jArith op (.i32 a) (.i32 b))) (longOrThrow (exact op a b)) =
      (if inI32 (exact op a b) then .agree else .wrongValue) := by
  have hfit := i32_exact_fits_i64 op a b ha hb
  simp only [jArith, longOrThrow, hfit, ite_true, verdict]
  by_cases h : inI32 (exact op a b) = true
  · have hw := (wrap32_eq_iff (exact op a b)).mpr h
    simp [h, hw]
  · have hw : wrap 32 (exact op a b) ≠ exact op a b := fun e => h ((wrap32_eq_iff _).mp e)
    simp [h, R.val, hw]

/-- ★ LG2: at least one `long` operand (a literal or local outside i32, or an `integer` object),
the other fixed: jank returns the 64-bit wrapped value, always; Clojure's static path throws
exactly when the true result leaves i64. So jank departs exactly on i64 overflow, and always as
"a value where Clojure throws". -/
theorem i64_pair_verdict (op : Op) (ra rb : Rep)
    (hfix : (match ra, rb with | .big _, _ | _, .big _ => false | .i32 _, .i32 _ => false | _, _ => true) = true) :
    verdict (.ok (jArith op ra rb)) (longOrThrow (exact op ra.val rb.val)) =
      (if inI64 (exact op ra.val rb.val) then .agree else .valueVsThrow) := by
  have hj : jArith op ra rb = .long (wrap 64 (exact op ra.val rb.val)) := by
    cases ra <;> cases rb <;> simp_all [jArith, Rep.val]
  rw [hj]
  by_cases h : inI64 (exact op ra.val rb.val) = true
  · have hw := (wrap64_eq_iff _).mpr h
    simp [longOrThrow, h, hw, verdict]
  · simp [longOrThrow, h, verdict]

/-- ★ The fixed arithmetic (checked, in i64, for every pair of fixed integers) is Clojure's
static path for every pair of fixed integer operands and every operation. -/
theorem fixed_eq_static (op : Op) (ra rb : Rep)
    (hfix : (match ra, rb with | .big _, _ | _, .big _ => false | _, _ => true) = true) :
    verdict (jArithFixed op ra rb) (longOrThrow (exact op ra.val rb.val)) = .agree := by
  have : jArithFixed op ra rb =
      (if inI64 (exact op ra.val rb.val) then .ok (.long (exact op ra.val rb.val))
       else .error "integer overflow") := by
    cases ra <;> cases rb <;> simp_all [jArithFixed, Rep.val]
  rw [this]
  by_cases h : inI64 (exact op ra.val rb.val) = true <;> simp [h, longOrThrow, verdict]

/-- ★ Clojure's Object `-` (a fn parameter on either side) throws for `y = Long/MIN_VALUE` even
when `x - y` fits (`x < 0`); the fixed jank returns `x - y` there. Exactly those pairs separate
the fixed jank from Clojure's Object path for `-`. -/
theorem fixed_vs_object_sub (a b : Int) :
    verdict (jArithFixed .sub (jRepFixed (.long a) .fnVal) (jRepFixed (.long b) .fnVal))
        (cArith .sub (.long a) (.long b) false) =
      (if b = i64min ∧ inI64 (a - b) = true then .valueVsThrow else .agree) := by
  rw [jArithFixed_fixed _ _ _ (jRepFixed_not_big a _) (jRepFixed_not_big b _),
    jRepFixed_val, jRepFixed_val]
  simp only [exact]
  by_cases hm : b = i64min
  · subst hm
    by_cases h : inI64 (a - i64min) = true <;> simp [h, cArith, verdict]
  · by_cases h : inI64 (a - b) = true <;> simp [h, cArith, hm, longOrThrow, verdict]

/-- ★ jank's `inc`/`dec` throw exactly when Clojure's do, with the same value otherwise, for every
fixed integer (the checked builtins); only R5's BigInt literal makes them depart. -/
theorem incdec_fixed_agree (up : Bool) (v : Int) (src : Src)
    (hnot : jRep (.long v) src ≠ .big v) :
    verdict (jIncDec up (jRep (.long v) src)) (cIncDec up (.long v)) = .agree := by
  have hval : (jRep (.long v) src).val = v := by
    cases src <;> simp only [jRep] <;> split <;> (try split) <;> rfl
  have hfixed : ∀ w, jRep (.long v) src ≠ .big w := by
    intro w h
    have h2 := congrArg Rep.val h
    rw [hval] at h2; simp only [Rep.val] at h2
    subst h2; exact hnot h
  have key : ∀ x : Rep, (∀ w, x ≠ .big w) →
      jIncDec up x = (if inI64 (if up then x.val + 1 else x.val - 1) then
        .ok (.long (if up then x.val + 1 else x.val - 1)) else .error "Overflow on increment.") := by
    intro x hx; cases x <;> simp_all [jIncDec, Rep.val]
  rw [key _ hfixed, hval]
  cases up
  · by_cases h : inI64 (v - 1) = true <;> simp [h, cIncDec, longOrThrow, verdict]
  · by_cases h : inI64 (v + 1) = true <;> simp [h, cIncDec, longOrThrow, verdict]

/-- ★ `abs` agrees with Clojure on every fixed integer, including Long/MIN_VALUE (both wrap). -/
theorem abs_fixed_agree (v : Int) (src : Src) (hnot : jRep (.long v) src ≠ .big v) :
    jAbs (jRep (.long v) src) = cAbs (.long v) := by
  have hi32 : ∀ w, inI32 w = true → wrap 64 (-w) = -w := by
    intro w hw; rw [inI32_iff] at hw; rw [wrap64_eq_iff, inI64_iff]; omega
  have fixed : ∀ x : Rep, (x = .i32 v ∧ inI32 v = true) ∨ x = .i64 v → jAbs x = cAbs (.long v) := by
    intro x hx
    rcases hx with ⟨rfl, h⟩ | rfl
    · simp only [jAbs, cAbs]; rw [hi32 v h]
    · rfl
  apply fixed
  by_cases hm : v = i64min
  · subst hm
    cases src <;> simp [jRep] at hnot ⊢ <;> simp [inI32, i32min, i32max, i64min]
  · have hb : (v == i64min) = false := by simp [hm]
    cases src <;> simp only [jRep, hb] <;> by_cases h : inI32 v = true <;> simp [h]

/-- ★ `+'` and `*'` are exact for every pair of fixed integers, and agree with Clojure's static
and Object paths. -/
theorem promoting_add_mul_agree (op : Op) (hop : op ≠ .sub) (a b : Int) (src : Src)
    (static : Bool) :
    verdict (.ok (jArithP op (jRepFixed (.long a) src) (jRepFixed (.long b) src)))
        (cArithP op (.long a) (.long b) static) = .agree := by
  rw [jArithP_fixed _ _ _ (jRepFixed_not_big a _) (jRepFixed_not_big b _),
    jRepFixed_val, jRepFixed_val]
  cases op
  · by_cases h : inI64 (exact .add a b) = true <;> simp [cArithP, h, verdict]
  · exact absurd rfl hop
  · by_cases h : inI64 (exact .mul a b) = true <;> simp [cArithP, h, verdict]

/-- ★ `-'` (D3, re-proved over the exact model): for fixed operands jank's value is wrong exactly
when the true difference leaves i64. -/
theorem promoting_sub_wrong_iff (a b : Int) (src : Src) :
    (jArithP .sub (jRepFixed (.long a) src) (jRepFixed (.long b) src)).val ≠ a - b ↔
      inI64 (a - b) = false := by
  rw [jArithP_fixed _ _ _ (jRepFixed_not_big a _) (jRepFixed_not_big b _),
    jRepFixed_val, jRepFixed_val]
  simp only [exact]
  by_cases h : inI64 (a - b) = true
  · simp [h, R.val]
  · have hw : wrap 64 (a - b) ≠ a - b := fun e => h ((wrap64_eq_iff _).mp e)
    simp [h, R.val, hw]

end Jank.R6.Num
