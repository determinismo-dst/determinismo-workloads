import Jank.Interop.Spec
import Std.Tactic.BVDecide

/-!
# Theorems about the interop replica

Fixed-width facts are proved with `bv_decide` on the bit patterns the C++ computes; facts about
the model's functions on given inputs by `decide`/`rfl` (kernel evaluation). No `sorry`, no
`native_decide`.
-/

namespace Jank.Interop.Theorems

/-- `convert<int>::from_object` of a heap `obj::integer` is `static_cast<int>(o.to_integer())`
(builtin.hpp:238 at 7135b7708; `integer::to_integer` is the i64 data),
the low 32 bits: the value comes back exactly iff it lies in [INT32_MIN, INT32_MAX]. A loop local
typed `int` therefore keeps a `recur` value modulo 2^32 (I2). -/
theorem int_from_object_exact_iff (v : BitVec 64) :
    (v.truncate 32).signExtend 64 = v ↔
      (BitVec.sle 0xFFFFFFFF80000000#64 v ∧ BitVec.sle v 0x000000007FFFFFFF#64) := by
  bv_decide

/-- `int + int` on two integer literals (the analyzer types both `int`, cpp_util.cpp:634) is the
true sum exactly when the 32-bit addition does not overflow; every true sum of two i32 values fits
i64, so each overflow is a wrong long, not a documented wrap (I1). -/
theorem literal_add_exact_iff (a b : BitVec 32) :
    ((a + b).signExtend 64 = a.signExtend 64 + b.signExtend 64) ↔ ¬ BitVec.saddOverflow a b := by
  bv_decide

theorem literal_mul_exact_iff (a b : BitVec 32) :
    ((a * b).signExtend 64 = a.signExtend 64 * b.signExtend 64) ↔ ¬ BitVec.smulOverflow a b := by
  bv_decide

/-- `make_box<T>(i)` for `T = unsigned int` (make_box.hpp:95): after the usual arithmetic
conversions both comparisons are unsigned (`INT32_MIN` becomes 0x80000000), and no value passes
both: an unsigned value is never boxed small. -/
theorem makeBox_u32_never_small (i : BitVec 32) :
    ¬ (0x80000000#32 ≤ i ∧ i ≤ 0x7FFFFFFF#32) := by
  bv_decide

/-- The same for 64-bit unsigned types (`INT32_MIN` converts to 0xFFFFFFFF80000000). -/
theorem makeBox_u64_never_small (i : BitVec 64) :
    ¬ (0xFFFFFFFF80000000#64 ≤ i ∧ i ≤ 0x000000007FFFFFFF#64) := by
  bv_decide

/-- `convert<unsigned long>::into_object` is `make_box(static_cast<i64>(o))` (builtin.hpp:223): a
value with its top bit set (≥ 2^63) becomes a negative long (I5). -/
theorem u64_into_object_negative (x : BitVec 64) (h : x.msb = true) : BitVec.slt x 0#64 := by
  bv_decide

/-- ... and only those: below 2^63 the long is the value. -/
theorem u64_into_object_exact_iff (x : BitVec 64) : BitVec.sle 0#64 x ↔ x.msb = false := by
  bv_decide

/-- Integral round trip `from_object(into_object(t)) = t` for `unsigned int` (into: `static_cast<i64>`,
a heap integer above INT32_MAX; from: `static_cast<unsigned>` of the i64 or of the tagged i32). -/
theorem u32_roundtrip (x : BitVec 32) :
    (x.zeroExtend 64).truncate 32 = x ∧ ((x.zeroExtend 64).truncate 32).truncate 32 = x := by
  bv_decide

/-- The analyzer gives every integer literal that fits i32 the C++ type `int` (cpp_util.cpp:657). -/
theorem literal_type_small_int (v : BitVec 32) :
    CppUtil.literalType (.smallInteger v) false = .b .int := rfl

/-- `is_pointer_to_void_conversion` (cpp_util.cpp:962) accepts `const void *` → `int *`, a cast
`static_cast` may not make (it casts away constness, [expr.static.cast] p13) (I6). -/
theorem pointer_to_void_ignores_cv :
    CppUtil.isPointerToVoidConversion (.ptr (.cv true false (.b .void))) (.ptr (.b .int)) = true := by
  decide

/-- ... and function pointers: `void (*)()` → `void *`, which no `static_cast` makes. -/
theorem pointer_to_void_accepts_function_pointers :
    CppUtil.isPointerToVoidConversion (.ptr (.fn (.b .void) [])) (.ptr (.b .void)) = true := by
  decide

def summary : IO Unit := do
  IO.println "== theorems (proved at build time; no sorry, no native_decide)"
  for n in ["int_from_object_exact_iff", "literal_add_exact_iff", "literal_mul_exact_iff",
            "makeBox_u32_never_small", "makeBox_u64_never_small", "u64_into_object_negative",
            "u64_into_object_exact_iff", "u32_roundtrip", "literal_type_small_int",
            "pointer_to_void_ignores_cv", "pointer_to_void_accepts_function_pointers"] do
    IO.println s!"  {n}"
  IO.println "== checked by evaluation (string-valued model functions do not reduce in the kernel)"
  let c1 := CppUtil.getQualifiedTypeName world0 (.ptr (.cv true false (.record "base")))
  let c2 := CppUtil.getQualifiedTypeName world0 (.ptr (.record "base"))
  let c3 := CppUtil.getQualifiedTypeName world0 (.ptr (.fn (.record "base") [.b .int]))
  IO.println s!"  box names: `const base *` → {c1}, `base *` → {c2}, `base (*)(int)` → {c3}"
  IO.println s!"  convert<char>::from_object of \\é keeps byte {(charDataBytes "é").headD 0} of {charDataBytes "é"}"

end Jank.Interop.Theorems
