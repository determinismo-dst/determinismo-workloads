import Jank.R3.Interop.Census

/-!
# Theorems about the round-3 CppInterOp replica (no `sorry`, no `native_decide`)

Most are for every input: every builtin kind, every platform, every element type, every chain of
DSL modifiers.
-/

namespace Jank.R3.Interop.Theorems

open Jank.Interop
open Jank.R3.Interop.Clang
open Jank.R3.Interop.CppInterOp

/-! ## The DSL's integer modifiers -/

inductive Mod where
  | signed | unsigned | short | long
  deriving Repr, DecidableEq

/-- The builtin a modifier gives (CppInterOp.cpp:3131-3335 on an unqualified builtin). -/
def applyMod (p : Platform) : Mod → Builtin → Builtin
  | .signed, k => (builtin? (getSignedType p (.b k))).getD k
  | .unsigned, k => (builtin? (getUnsignedType p (.b k))).getD k
  | .short, k => (builtin? (getShortType p (.b k))).getD k
  | .long, k => (builtin? (getLongType p (.b k))).getD k

def notLongLong (k : Builtin) : Prop := k ≠ .llong ∧ k ≠ .ullong

instance (k : Builtin) : Decidable (notLongLong k) := inferInstanceAs (Decidable (_ ∧ _))

/-- No modifier turns a type that is not `long long`/`unsigned long long` into one: `GetLongType`
of `long` is `long` (CppInterOp.cpp:3301), of `long long` is `long`. -/
theorem applyMod_keeps_notLongLong (c : Bool) (m : Mod) (k : Builtin) (h : notLongLong k) :
    notLongLong (applyMod { charSigned := c } m k) := by
  cases c <;> cases m <;> cases k <;> simp_all [notLongLong, applyMod] <;> decide

/-- For every chain of DSL modifiers over every builtin base other than `long long`, on every
platform, the result is never `long long` or `unsigned long long`: the DSL cannot name
`long long` (the book's `(:long (:long int))` is `long`). Round 2 checked chains of length ≤ 2. -/
theorem dsl_never_long_long (c : Bool) (ms : List Mod) (k : Builtin) (h : notLongLong k) :
    notLongLong (ms.foldr (fun m acc => applyMod { charSigned := c } m acc) k) := by
  induction ms with
  | nil => simpa using h
  | cons m ms ih => exact applyMod_keeps_notLongLong c m _ ih

/-- `(:long (:long cpp/int))` is `long` on every platform. -/
theorem long_long_int_is_long (c : Bool) :
    applyMod { charSigned := c } .long (applyMod { charSigned := c } .long .int) = .long := by
  cases c <;> decide

/-- `(:signed cpp/char)` is plain `char` where `char` is signed (x86-64): `Char_S` comes back
unchanged (CppInterOp.cpp:3174). -/
theorem signed_char_is_char_x86 : applyMod x86_64 .signed .char = .char := by decide

/-- `(:unsigned cpp/char)` is plain `char` where `char` is unsigned (AArch64 Linux): `Char_U` is
"already unsigned" (CppInterOp.cpp:3199). -/
theorem unsigned_char_is_char_aarch64 : applyMod linuxAArch64 .unsigned .char = .char := by decide

/-- ... while the other platform gives the distinct C++ type each time. -/
theorem signed_char_aarch64 : applyMod linuxAArch64 .signed .char = .schar := by decide
theorem unsigned_char_x86 : applyMod x86_64 .unsigned .char = .uchar := by decide

/-- `GetShortType`/`GetLongType` return `bool` unchanged, on every platform. -/
theorem short_long_bool (c : Bool) :
    applyMod { charSigned := c } .short .bool = .bool ∧ applyMod { charSigned := c } .long .bool = .bool := by
  cases c <;> decide

/-! ## Type kinds -/

/-- `IsIntegral` is false for every enumeration (C++ `Type::isIntegralType`, Type.cpp:2160);
round 2's IA3 said true. -/
theorem isIntegral_enum (n : String) : CppInterOp.isIntegral (.enum n) = false := rfl

/-- `IsBuiltin` is false for every enumeration (round 2's I assumption, confirmed): an `if` on an
enum value takes the non-builtin path (R89). -/
theorem isBuiltin_enum (n : String) : CppInterOp.isBuiltin (.enum n) = false := rfl

/-- `GetPointeeType` of an array is its element type, for every element type and size
(CppInterOp.cpp:3015); round 2's IA11 answered null, the premise of R87. -/
theorem getPointeeType_array (e : CType) (n : Option Nat) :
    getPointeeType (.array e n) = e := rfl

/-- `GetScopeFromType` of a function pointer is null for every signature (round 2 gave the return
type's class). -/
theorem getScopeFromType_fnptr (x : XWorld) (r : CType) (ps : List CType) :
    getScopeFromType x (.ptr (.fn r ps)) = none := rfl

/-- `IsImplicitlyConvertible(from, T&)` is false for every source and every referenced type: the
synthesized prvalue reaches `TryImplicitConversion`, which has no standard conversion to a
reference type (SemaOverload.cpp:2663) and, for a non-class source, no user-defined one. -/
theorem isImplicitlyConvertible_to_lref (p : Platform) (x : XWorld) (k : Builtin) (t : CType) :
    CppInterOp.isImplicitlyConvertible p x (.b k) (.lref t) = false := rfl

theorem isImplicitlyConvertible_to_rref (p : Platform) (x : XWorld) (k : Builtin) (t : CType) :
    CppInterOp.isImplicitlyConvertible p x (.b k) (.rref t) = false := rfl

/-- `IsCStyleConvertible` from any floating type is false, for every target (CppInterOp.cpp:679:
"conservatively say no"). -/
theorem isCStyleConvertible_floating (p : Platform) (x : XWorld) (d : CType) :
    CppInterOp.isCStyleConvertible p x (.b .float) d = false ∧
    CppInterOp.isCStyleConvertible p x (.b .double) d = false ∧
    CppInterOp.isCStyleConvertible p x (.b .ldouble) d = false := ⟨rfl, rfl, rfl⟩

/-- ... and from `std::nullptr_t`, for every target. -/
theorem isCStyleConvertible_nullptr (p : Platform) (x : XWorld) (d : CType) :
    CppInterOp.isCStyleConvertible p x (.b .nullptr) d = false := rfl

/-- `GetFunctionTypeFromPointerToMember` on a pointer to a const object gives the object
parameter `C *`, for every class, return type and parameter list: the pointee's `const` is lost
(CppInterOp.cpp:2900 tests the pointer's own qualifiers). -/
theorem pm_const_pointee_dropped (cls : String) (r : CType) (ps : List CType) :
    getFunctionTypeFromPointerToMember (.memPtr cls (.fn r ps)) (.ptr (.cv true false (.record cls))) =
      .fn r (.ptr (.record cls) :: ps) := rfl

/-- `GetCommonType` of two operands of one small integer type is `int` (both promoted by
`UsualArithmeticConversions`), not the type itself as `?:` gives (round 2's AN). -/
theorem getCommonType_small_same (x : XWorld) :
    getCommonType x86_64 x (.b .bool) (.b .bool) = .b .int ∧
    getCommonType x86_64 x (.b .short) (.b .short) = .b .int ∧
    getCommonType x86_64 x (.b .char) (.b .char) = .b .int := ⟨rfl, rfl, rfl⟩

/-- `GetCommonType` of an lvalue reference and an arithmetic type is null (a reference type is
not arithmetic), for every builtin. -/
theorem getCommonType_ref_null (x : XWorld) (k : Builtin) (t : CType) :
    getCommonType x86_64 x (.lref t) (.b k) = .null := by
  cases k <;> rfl

end Jank.R3.Interop.Theorems
