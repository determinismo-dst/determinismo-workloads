/-!
# Round 7, native values: which plain programs make x86-64's default NaN, and what jank does with it

D9 (round 1; confirmed on the real jank: d09 and d09b end with signal 11) is the cause: an
`object_ref` holds a double as its raw bits (oref.hpp `tag(f64)` 194, a `bit_cast`), and a word
counts as a real only below `max_real` = 0xFFF8000000000000 (oref.hpp 94, `is_tagged_small_real`
113). x86-64 SSE's default NaN ("QNaN floating-point indefinite") is exactly 0xFFF8000000000000 for
binary64 (0xFFC00000 for binary32). That word is neither a real, nor a tagged integer (0xFFF9…),
nor a tagged pointer (0xFFFA…); `get_type()` (oref.hpp 386-398) reads `ptr()->type`, and
`as_pointer` (142) masks the word to address 0: a null read, SIGSEGV.

Round 1 reached it through fn parameters. This file follows every producer a plain program has:

- **Inlined literals and `let`** (new paths). A double literal is emitted as `auto tN(<text>);`
  (codegen/cpp_processor.cpp `gen(cpp_literal_ref)` 1278-1285) with the text from
  `lift_constant` 132-150 → jtl string_builder `operator()(double)` (string_builder.cpp 83-135):
  a finite value by `std::to_chars`, `##Inf` as `INFINITY`, `##-Inf` as `-INFINITY`, `##NaN` as
  `NAN`. `INFINITY` and `NAN` are `float` constants (C's <math.h>: `__builtin_inff()`,
  `__builtin_nanf("")`), so `auto` makes a `float`: the analyzer's `double` (cpp_util.cpp
  `literal_type` 670-693) is not what Clang compiles. math.hpp's both-primitive templates then run
  the C++ operator at run time (the default runtime optimization level is -O0:
  util/cli.cpp 205, jit/processor_dynamic.cpp 281-298), so `(/ 0.0 0.0)` is `divsd` → the default
  NaN, and `(- ##Inf ##Inf)` is `subss` → 0xFFC00000, widened by `make_box(float)`
  (make_box.hpp 79-85: `static_cast<f64>`, `cvtss2sd` keeps the sign) to 0xFFF8000000000000.
  Boxing it (`convert<f64>::into_object` → `make_box` → `small_real_ref` → `oref<object>`'s
  constructor 284-289 → `tag(f64)`) keeps the bits; the first `get_type()` crashes. Clojure: these
  are `Numbers` primitive double operations, ##NaN, no exception.
- **Fn values** (round 1's path): two real objects → `typed_l->data OP typed_r->data` (f64).
- **`parse-double`** of "-NaN" (new producer): math.cpp `parse_double` 712-736 → `std::stod` →
  glibc `strtod`, which negates its quiet NaN: 0xFFF8000000000000. Clojure 1.12.3:
  `(parse-double "-NaN")` is ##NaN.
- **jank.math with fixes/V24.diff** (new producer; stock jank cannot load jank.math, V24): `sqrt`,
  `pow`, `tan` of objects → `make_box(std::sqrt(l.to_real()))` etc. (math.hpp 1043-1176); glibc's
  `sqrt(-1.0)` is `sqrtsd` (the default NaN), `pow(-1.0, 0.5)` returns `__math_invalid` =
  `(x - x) / (x - x)` = 0/0, `tan(±inf)` returns `x - x`: the default NaN each. Clojure's
  clojure.math: ##NaN each.

A NaN that keeps a NaN operand's bits (`(+ ##NaN 1)`, `(- 0 ##NaN)`) is positive (x86 returns the
first NaN operand, quieted), so it decodes as a real: only invalid operations on non-NaN operands,
and `strtod`'s negated NaN, make the bad word.
-/

namespace Jank.R7.Native.Nan

/-- oref.hpp 94, 101, 108. -/
def maxReal : Nat := 0xFFF8000000000000
def intTag : Nat := 0xFFF9000000000000
def ptrTag : Nat := 0xFFFA000000000000

/-- What `get_type()` sees in a word: a real, a tagged integer, or a pointer read at
`as_pointer(word)` = the low 48 bits (no check in a release build: `jank_debug_assert`). -/
inductive Decoded where
  | real
  | smallInt
  | pointer (addr : Nat)
  deriving DecidableEq, Repr

def decode (w : Nat) : Decoded :=
  if w < maxReal then .real
  else if w / 2 ^ 32 == intTag / 2 ^ 32 then .smallInt
  else .pointer (w % 2 ^ 48)

/-- x86-64 SSE's default NaN, binary64 and binary32; C's `NAN` / `quiet_NaN()`. -/
def defaultNaN64 : Nat := 0xFFF8000000000000
def defaultNaN32 : Nat := 0xFFC00000
def posNaN64 : Nat := 0x7FF8000000000000

/-- `cvtss2sd` of a binary32 NaN: the sign kept, the payload shifted up 29 bits, quiet bit set. -/
def widenNaN32 (f : Nat) : Nat :=
  (f / 2 ^ 31) * 2 ^ 63 + 0x7FF * 2 ^ 52 + 2 ^ 51 + ((f % 2 ^ 22) * 2 ^ 29)

/-- glibc `strtod("-NaN")`: the quiet NaN with its sign bit set. -/
def strtodNegNaN : Nat := 2 ^ 63 + posNaN64

/-- A double's bits are a NaN: exponent all ones, a nonzero fraction. -/
def isNaN64 (w : Nat) : Bool := (w / 2 ^ 52) % 2048 == 2047 && w % 2 ^ 52 != 0

/-- The programs (each written inside a deftest). -/
inductive Prog where
  | divZeroZero      -- (/ 0.0 0.0)
  | subInfInf        -- (- ##Inf ##Inf)
  | mulZeroInf       -- (* 0.0 ##Inf)
  | addInfNegInf     -- (+ ##Inf ##-Inf)
  | parseNegNaN      -- (parse-double "-NaN")
  | mathSqrtNeg      -- (jank.math/sqrt -1.0), with fixes/V24.diff
  | mathPowNegHalf   -- (jank.math/pow -1.0 0.5), with fixes/V24.diff
  | mathTanInf       -- (jank.math/tan ##Inf), with fixes/V24.diff
  deriving DecidableEq, Repr

inductive Path where
  | literals | letBound | fnValue
  deriving DecidableEq, Repr

def Prog.code : Prog → Path → String
  | .divZeroZero, .literals => "(NaN? (/ 0.0 0.0))"
  | .divZeroZero, .letBound => "(let [x 0.0] (NaN? (/ x x)))"
  | .divZeroZero, .fnValue => "(NaN? (apply / [0.0 0.0]))"
  | .subInfInf, .literals => "(NaN? (- ##Inf ##Inf))"
  | .subInfInf, .letBound => "(let [x ##Inf] (NaN? (- x x)))"
  | .subInfInf, .fnValue => "(NaN? (apply - [##Inf ##Inf]))"
  | .mulZeroInf, .literals => "(NaN? (* 0.0 ##Inf))"
  | .mulZeroInf, .letBound => "(let [x 0.0 y ##Inf] (NaN? (* x y)))"
  | .mulZeroInf, .fnValue => "(NaN? (apply * [0.0 ##Inf]))"
  | .addInfNegInf, .literals => "(NaN? (+ ##Inf ##-Inf))"
  | .addInfNegInf, .letBound => "(let [x ##Inf y ##-Inf] (NaN? (+ x y)))"
  | .addInfNegInf, .fnValue => "(NaN? (apply + [##Inf ##-Inf]))"
  | .parseNegNaN, _ => "(NaN? (parse-double \"-NaN\"))"
  | .mathSqrtNeg, _ => "(NaN? (jank.math/sqrt -1.0))"
  | .mathPowNegHalf, _ => "(NaN? (jank.math/pow -1.0 0.5))"
  | .mathTanInf, _ => "(NaN? (jank.math/tan ##Inf))"

/-- The operands' C++ types on the inlined and `let` paths: a finite double literal is a `double`,
`##Inf`/`##-Inf` a `float` (the `INFINITY` macro). The operation runs in their common type. -/
def Prog.inFloat : Prog → Bool
  | .subInfInf | .addInfNegInf => true
  | _ => false

/-- The bits jank boxes, at runtime optimization level `opt` (0 by default). At -O1 and above
LLVM folds the constant operation on the inlined and `let` paths; APFloat's invalid result is the
positive quiet NaN (assumption PA7-2), which decodes as a real. -/
def jankBits (opt : Nat) (p : Prog) (path : Path) : Nat :=
  match p with
  | .parseNegNaN => strtodNegNaN
  | .mathSqrtNeg | .mathPowNegHalf | .mathTanInf => defaultNaN64
  | _ =>
    match path with
    | .fnValue => defaultNaN64
    | _ => if opt ≥ 1 then posNaN64 else if p.inFloat then widenNaN32 defaultNaN32 else defaultNaN64

/-- What the program gives: Clojure "true" for every one (run on 1.12.3, except `(apply / [0.0
0.0])`, where `Numbers.divide(Object, Object)` throws "Divide by zero": D2's area). -/
inductive Outcome where
  | value (s : String)
  /-- SIGSEGV: `get_type()` reads the object at this address (0: null). -/
  | crash (addr : Nat)
  | throws (s : String)
  deriving DecidableEq, Repr

def jankOutcome (opt : Nat) (p : Prog) (path : Path) : Outcome :=
  match decode (jankBits opt p path) with
  | .real => .value "true"
  | .smallInt => .value "a misread integer"
  | .pointer a => .crash a

def cljOutcome (p : Prog) (path : Path) : Outcome :=
  if p == .divZeroZero && path == .fnValue then .throws "ArithmeticException: Divide by zero" else .value "true"

/-- fixes/D9.diff (round 6): `tag(f64)` stores a word at or above `max_real` as the positive
quiet NaN. -/
def canon (w : Nat) : Nat := if w ≥ maxReal then posNaN64 else w

/-! ## Facts (kernel-checked) -/

theorem default_nan_is_null : decode defaultNaN64 = .pointer 0 := by decide
theorem widened_float_nan : widenNaN32 defaultNaN32 = defaultNaN64 := by decide
theorem strtod_neg_nan : strtodNegNaN = defaultNaN64 := by decide
theorem positive_nan_is_real : decode posNaN64 = .real := by decide

/-- ★ Every double below 2^64 whose sign bit is clear, and every non-NaN double, decodes as a
real: the bad words are exactly negative quiet NaNs. -/
theorem nonneg_real (w : Nat) (h : w < 2 ^ 63) : decode w = .real := by
  have : w < maxReal := by unfold maxReal; omega
  simp [decode, this]

theorem non_nan_real (w : Nat) (hw : w < 2 ^ 64) (h : (w / 2 ^ 52) % 2048 ≠ 2047) :
    decode w = .real := by
  have : w < maxReal := by unfold maxReal; omega
  simp [decode, this]

/-- ★ The misdecoded words are NaNs with the sign and quiet bits set. -/
theorem misdecoded_are_negative_quiet_nans (w : Nat) (hw : w < 2 ^ 64) (h : ¬ w < maxReal) :
    w / 2 ^ 63 = 1 ∧ (w / 2 ^ 52) % 2048 = 2047 ∧ (w / 2 ^ 51) % 2 = 1 := by
  unfold maxReal at h; omega

/-- ★ fixes/D9.diff makes every word decode as a real. -/
theorem canon_real (w : Nat) : decode (canon w) = .real := by
  unfold canon
  split
  · decide
  · rename_i h; simp [decode]; unfold maxReal at *; omega

/-- Every program on every path crashes at -O0 (the default), where Clojure answers. -/
theorem every_program_crashes_at_O0 (p : Prog) (path : Path) :
    jankOutcome 0 p path = .crash 0 := by
  cases p <;> cases path <;> decide

/-- At -O1 and above the inlined and `let` forms of the four operations agree (LLVM folds them to
the positive NaN); the fn-value path and the three other producers crash at every level. -/
theorem folded_literals_agree (opt : Nat) (h : 1 ≤ opt) :
    jankOutcome opt .divZeroZero .literals = .value "true" ∧
    jankOutcome opt .subInfInf .letBound = .value "true" ∧
    jankOutcome opt .subInfInf .fnValue = .crash 0 ∧
    jankOutcome opt .parseNegNaN .literals = .crash 0 := by
  have h1 : opt ≥ 1 := h
  simp only [jankOutcome, jankBits, h1, ite_true]
  decide

end Jank.R7.Native.Nan
