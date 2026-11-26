import Jank.R6.Native.Math

/-!
# Round 7, native values: the one-operand templates `zero?`, `abs`, `inc`, `dec`

Extends round 6's `Jank.R6.Native.jankBin` (two operands) with core/math.hpp's one-operand
templates, on round 6's operands (`Opd`) and sources (`Src`), so the walk covers every native type
a plain program produces with every inlined one-operand operation.

jank (include/cpp/jank/runtime/core/math.hpp at 94d32623):
- `is_zero` 1340-1382: `primitive_number<L> && !is_same<L, bool>` → `l == 0ll` (a `char` counts:
  `(zero? (aget (char-array 1) 0))` is true); a `bool` → `!valid_boxed_math<bool>` → throws
  `std::runtime_error` "Can't check if a bool is zero."; an object → `visit_number_like`
  (`data == 0ll`; a boolean or character object throws "not a number", visit.hpp 507).
- `abs` 992-1040: integral (bool and char included) → `std::abs(static_cast<i64>(l))`; floating →
  `std::abs(static_cast<f64>(l))`; an object → `data < 0ll ? make_box(-1ll * data) : make_box(data)`
  (so -0.0 and NaN stay: D6).
- `inc` 1184-1260 / `dec` 1262-1338: integral → `__builtin_add_overflow(l, 1ll, &res)` into `i64`
  (throws the string "Overflow on increment."); floating → `l + 1` in the operand's own type (a
  `float` stays a `float`); an object → the same with its `data`.
core.jank inlines each (`zero?` 1680, `abs` 1818, `inc` 1646, `dec` 1655); through a fn value the
argument is boxed first (`convert<T>::into_object`).

Clojure (Numbers.java): `isZero`, `abs`, `inc`, `dec` take long, double or Object; a char or a
boolean reaches `Object` and `ops(x).isZero((Number) x)` throws ClassCastException (run on 1.12.3:
`(zero? (aget (char-array 1) 0))` throws "java.lang.Character cannot be cast to class
java.lang.Number"). A float widens to double. `inc`/`dec` of a long throw "integer overflow".
-/

namespace Jank.R7.Native

open Jank.R6.Native

inductive UOp where
  | zero | abs | inc | dec
  deriving Repr, BEq, DecidableEq, Inhabited

def UOp.all : List UOp := [.zero, .abs, .inc, .dec]

def UOp.sym : UOp → String
  | .zero => "zero?" | .abs => "abs" | .inc => "inc" | .dec => "dec"

/-- `std::abs` of an `i64` (wraps at the minimum, as x86's `neg`). -/
def absI64 (v : Int) : Int := wrapTo .llong (if v < 0 then -v else v)

/-- One math.hpp one-operand template on an operand. -/
def jankUnary (op : UOp) (o : Opd) : JR :=
  match op, o with
  -- is_zero
  | .zero, .prim (.i .bool _) => .threwNative "Can't check if a bool is zero."
  | .zero, .prim (.i _ v) => .prim (.i .bool (if v == 0 then 1 else 0))
  | .zero, .prim (.f _ x) => .prim (.i .bool (if x == 0.0 then 1 else 0))
  | .zero, .obj (.num (.i _ v)) => .prim (.i .bool (if v == 0 then 1 else 0))
  | .zero, .obj (.num (.f _ x)) => .prim (.i .bool (if x == 0.0 then 1 else 0))
  | .zero, .obj (.ratio p _) => .prim (.i .bool (if p == 0 then 1 else 0))
  | .zero, .obj _ => .threwNative "not a number"
  -- abs
  | .abs, .prim (.i _ v) => .prim (.i .llong (absI64 v))
  | .abs, .prim (.f _ x) => .prim (.f .double x.abs)
  | .abs, .obj (.num (.i _ v)) => .obj (makeBox (.i .llong (absI64 v)))
  | .abs, .obj (.num (.f _ x)) => .obj (makeBox (.f .double (if x < 0.0 then -x else x)))
  | .abs, .obj (.ratio p q) => .obj (.ratio (if p < 0 then -p else p) q)
  | .abs, .obj _ => .threwNative "not a number"
  -- inc / dec
  | .inc, .prim (.i _ v) => if inI64' (v + 1) then .prim (.i .llong (v + 1)) else .threwObj "Overflow on increment."
  | .dec, .prim (.i _ v) => if inI64' (v - 1) then .prim (.i .llong (v - 1)) else .threwObj "Overflow on decrement."
  | .inc, .prim (.f t x) => .prim (.f t (if t == .float then toF32 (x + 1.0) else x + 1.0))
  | .dec, .prim (.f t x) => .prim (.f t (if t == .float then toF32 (x - 1.0) else x - 1.0))
  | .inc, .obj (.num (.i _ v)) => if inI64' (v + 1) then .obj (makeBox (.i .llong (v + 1))) else .threwObj "Overflow on increment."
  | .dec, .obj (.num (.i _ v)) => if inI64' (v - 1) then .obj (makeBox (.i .llong (v - 1))) else .threwObj "Overflow on decrement."
  | .inc, .obj (.num (.f _ x)) => .obj (makeBox (.f .double (x + 1.0)))
  | .dec, .obj (.num (.f _ x)) => .obj (makeBox (.f .double (x - 1.0)))
  | .inc, .obj (.ratio p q) => .obj (.ratio (p + q) q)
  | .dec, .obj (.ratio p q) => .obj (.ratio (p - q) q)
  | _, .obj _ => .threwNative "not a number"

/-- The inlined call (`(zero? x)` → `cpp/jank.runtime.is_zero x`) and the call through a fn value
(the argument boxed by `convert<T>::into_object`). -/
def jankUnaryInline (op : UOp) (o : Opd) : JR := jankUnary op o

def jankUnaryFn (op : UOp) (o : Opd) : JR :=
  jankUnary op (match o with | .prim n => .obj (intoObject n) | o => o)

/-- Clojure 1.12's Numbers on one value. -/
def cljUnary (op : UOp) (a : CV) : CR :=
  if !a.isNum then .threw "ClassCastException"
  else match op, a with
  | .zero, .long v => .val (.bool (v == 0))
  | .zero, .dbl x _ => .val (.bool (x == 0.0))
  | .zero, .ratio _ _ => .val (.bool false)
  | .abs, .long v => .val (.long (absI64 v))
  | .abs, .dbl x _ => .val (.dbl x.abs)
  | .abs, .ratio p q => .val (.ratio (if p < 0 then -p else p) q)
  | .inc, .long v => if inI64 (v + 1) then .val (.long (v + 1)) else .threw "ArithmeticException: integer overflow"
  | .dec, .long v => if inI64 (v - 1) then .val (.long (v - 1)) else .threw "ArithmeticException: integer overflow"
  | .inc, .dbl x _ => .val (.dbl (x + 1.0))
  | .dec, .dbl x _ => .val (.dbl (x - 1.0))
  | .inc, .ratio p q => .val (ratioNorm (p + q) q)
  | .dec, .ratio p q => .val (ratioNorm (p - q) q)
  | _, _ => .threw "ClassCastException"

/-- The source switches of round 6 that change a source's own value, so a unary disagreement can
be put to its cause: P6 (hash is unsigned), P7 (float is a double), R122 (bytes unsigned). -/
def srcSw : Sw := { hashSigned := true, floatF32 := true, bytesSigned := true }

structure UCase where
  op : UOp
  a : Src
  fnValue : Bool

def UCase.form (c : UCase) : String :=
  let call := if c.fnValue then s!"(apply {c.op.sym} [{c.a.code}])" else s!"({c.op.sym} {c.a.code})"
  match c.a.paramArg with
  | some x => s!"((fn [x] {call}) {x})"
  | none => call

def UCase.jank (sw : Sw) (c : UCase) : JR :=
  if c.fnValue then jankUnaryFn c.op (c.a.jank sw) else jankUnaryInline c.op (c.a.jank sw)

def UCase.clj (c : UCase) : CR := cljUnary c.op c.a.clj

def UCase.deviates (sw : Sw) (c : UCase) : Bool := !agrees (c.jank sw).seen c.clj

def unaryCases : List UCase := Id.run do
  let mut out := #[]
  for fv in [false, true] do
    for op in UOp.all do
      for a in sources do
        out := out.push { op, a, fnValue := fv }
  return out.toList

/-! ## For every input -/

/-- `(zero? (aget (char-array …) 0))`, inlined: for every `char` value jank returns a boolean
(`c == 0`), where Clojure throws ClassCastException. -/
theorem zero_of_char_returns (c : Int) :
    ∃ b, jankUnaryInline .zero (.prim (.i .char c)) = .prim (.i .bool b) ∧
      cljUnary .zero (.char c) = .threw "ClassCastException" :=
  ⟨_, rfl, rfl⟩

/-- The same for `abs`, `inc`, `dec` of a char (P9's cause, round 6's V64, in the one-operand
templates): a number for every `char` below 2^63, where Clojure throws. -/
theorem abs_inc_dec_of_char_return (c : Int) (h : -128 ≤ c ∧ c ≤ 127) :
    (∃ v, jankUnaryInline .abs (.prim (.i .char c)) = .prim (.i .llong v)) ∧
    (∃ v, jankUnaryInline .inc (.prim (.i .char c)) = .prim (.i .llong v)) ∧
    (∃ v, jankUnaryInline .dec (.prim (.i .char c)) = .prim (.i .llong v)) ∧
    cljUnary .abs (.char c) = .threw "ClassCastException" := by
  refine ⟨⟨_, rfl⟩, ?_, ?_, rfl⟩
  · have : inI64' (c + 1) = true := by simp [inI64']; omega
    exact ⟨c + 1, by simp [jankUnaryInline, jankUnary, this]⟩
  · have : inI64' (c - 1) = true := by simp [inI64']; omega
    exact ⟨c - 1, by simp [jankUnaryInline, jankUnary, this]⟩

/-- Through a fn value the char is a character object and `is_zero` throws a `std::runtime_error`
("not a number"), which `thrown?` cannot see (V7's class): both sides throw. -/
theorem zero_of_char_fn_value (c : Int) :
    jankUnaryFn .zero (.prim (.i .char c)) = .threwNative "not a number" := rfl

end Jank.R7.Native
