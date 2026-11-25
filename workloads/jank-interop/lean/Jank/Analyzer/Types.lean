import Jank.Analyzer.Expr

/-!
# C++ types as the analyzer sees them

The analyzer manipulates Clang types (`jtl::ptr<void>`) through `cpp_util` and `cppinterop`
(`src/cpp/jank/analyze/cpp_util.cpp`, `cppinterop.cpp` at jank 7135b7708, owned by the interop agent; the parts the
analyzer's non-interop paths call are modeled here). The universe is the types jank code without
explicit interop produces: the untyped `object_ref`, typed `oref<T>`s, `bool`, `int`, `long`,
`double`, `char const[n]` and `void`. Clang queries (`Cpp::GetCommonType`,
`Cpp::IsImplicitlyConvertible`, `Cpp::IsConstructible`, `Cpp::GetBuiltinOperatorType`) are
unreadable library code: modeled by their documented C++ meaning (assumptions in the report).
-/

namespace Jank.Analyzer

/-- A canonical C++ type of the universe. -/
inductive CT where
  /-- `jank::runtime::object_ref` (`oref<object>`). -/
  | objectRef
  /-- `jank::runtime::oref<obj::T>`, by `T` (`nil`, `integer`, `small_integer`, `keyword`, ...). -/
  | typed (t : String)
  | bool
  /-- `int`: 32-bit signed. -/
  | int
  /-- `long`: 64-bit signed (LP64). -/
  | long
  | double
  /-- `char const[n]`. -/
  | cstr (n : Nat)
  | void
  /-- Anything else (opaque). -/
  | other (spelling : String)
  deriving Repr, BEq, DecidableEq, Inhabited

def CT.spelling : CT → String
  | .objectRef => "jank::runtime::object_ref"
  | .typed t => s!"jank::runtime::obj::{t}_ref"
  | .bool => "bool"
  | .int => "int"
  | .long => "long"
  | .double => "double"
  | .cstr n => s!"char const[{n}]"
  | .void => "void"
  | .other s => s

def CT.toCpp (t : CT) : CppType := .named t.spelling

def CppType.toCT : CppType → CT
  | .null => .other "<null>"
  | .named s =>
    if s == "jank::runtime::object_ref" then .objectRef
    else if s == "bool" then .bool
    else if s == "int" then .int
    else if s == "long" then .long
    else if s == "double" then .double
    else if s == "void" then .void
    else if s.startsWith "jank::runtime::obj::" && s.endsWith "_ref" then
      .typed (((s.drop 20).dropEnd 4).toString)
    else if s.startsWith "char const[" && s.endsWith "]" then
      .cstr (((s.drop 11).dropEnd 1).toString.toNat!)
    else .other s

theorem CT.roundtrip_basic :
    (CT.objectRef.toCpp.toCT = .objectRef) ∧ (CT.int.toCpp.toCT = .int) ∧
    (CT.double.toCpp.toCT = .double) ∧ (CT.bool.toCpp.toCT = .bool) := by
  decide

/-- `cpp_util::is_untyped_object` (cpp_util.cpp:969). -/
def isUntypedObject : CT → Bool
  | .objectRef => true
  | _ => false

/-- `cpp_util::is_typed_object_ref` (cpp_util.cpp:1002; `is_typed_object` before 7135b7708): an `oref<T>` specialization other than
`object_ref`. -/
def isTypedObject : CT → Bool
  | .typed _ => true
  | _ => false

/-- The 7135b7708 name of `isTypedObject`. -/
abbrev isTypedObjectRef := isTypedObject

/-- `cpp_util::is_untyped_object_ref` (cpp_util.cpp:977): exactly `object_ref` (not `object*`). -/
def isUntypedObjectRef : CT → Bool
  | .objectRef => true
  | _ => false

/-- `cpp_util::is_any_object` (cpp_util.cpp:1012). -/
def isAnyObject (t : CT) : Bool := isUntypedObject t || isTypedObject t

/-- `cpp_util::is_any_object_ref` (cpp_util.cpp:1017). -/
def isAnyObjectRef (t : CT) : Bool := isUntypedObjectRef t || isTypedObjectRef t

/-- `cpp_util::is_bool` (cpp_util.cpp:920). -/
def isBool (t : CT) : Bool := t == .bool

/-- `cppinterop::is_builtin` (Clang `Type::isBuiltinType`): void, bool and arithmetic. -/
def isBuiltin : CT → Bool
  | .bool | .int | .long | .double | .void => true
  | _ => false

def isArithmetic : CT → Bool
  | .bool | .int | .long | .double => true
  | _ => false

/-- `cpp_util::is_c_string` (cpp_util.cpp:1056). -/
def isCString : CT → Bool
  | .cstr _ => true
  | _ => false

def isVoid (t : CT) : Bool := t == .void

/-- `cpp_util::is_primitive` (cpp_util.cpp:1025): builtin, pointer, array or enum. -/
def isPrimitive (t : CT) : Bool := isBuiltin t || isCString t

/-- `cpp_util::is_trait_convertible` (cpp_util.cpp:1717): `jank::runtime::convert<T>` is complete.
convert/builtin.hpp specializes it for objects, typed objects, void, nullptr, bool, char, integral,
floating and C strings. -/
def isTraitConvertible : CT → Bool
  | .other s => s == "char const*"
  | _ => true

/-- `cpp_util::mutable_type` (cpp_util.cpp:1064). -/
def mutableType (t : CT) : CT :=
  if isTypedObject t then .objectRef
  else if isCString t then .objectRef
  else if isVoid t then .objectRef
  else t

/-- `cpp_util::select_most_native_type` (cpp_util.cpp:1100). -/
def selectMostNativeType (left right : CT) : CT × CT :=
  if !isAnyObject left then (left, right)
  else if !isAnyObject right then (right, left)
  else if isTypedObject left then (left, right)
  else if isTypedObject right then (right, left)
  else (left, right)

/-- `cpp_util::non_void_type` (cpp_util.cpp:1157). -/
def nonVoidType (t : CT) : CT := if isVoid t then .typed "nil" else t

/-- Integer conversion rank for the usual arithmetic conversions. -/
def arithRank : CT → Nat
  | .bool => 0 | .int => 1 | .long => 2 | .double => 3 | _ => 0

/-- `cppinterop::get_common_type` (cppinterop.cpp:151, `Cpp::GetCommonType`): the type of `c ? a : b`. Arithmetic:
the usual arithmetic conversions (bool promotes to int). `oref<T>` converts to `object_ref` and
`nil_ref` to any `oref<T>`. None otherwise. (Assumption A3.) -/
def getCommonType (a b : CT) : Option CT :=
  if a == b then some a
  else if isArithmetic a && isArithmetic b then
    let r := max (arithRank a) (arithRank b)
    some (if r ≤ 1 then .int else if r == 2 then .long else .double)
  else match a, b with
    | .objectRef, .typed _ => some .objectRef
    | .typed _, .objectRef => some .objectRef
    | .typed "nil", .typed t => some (.typed t)
    | .typed t, .typed "nil" => some (.typed t)
    | .cstr _, .cstr _ => some (.other "char const*")
    | _, _ => none

/-- Two equal array types still decay in `c ? a : b`. -/
def getCommonType' (a b : CT) : Option CT :=
  if isCString a && isCString b then some (.other "char const*") else getCommonType a b

/-- `cppinterop::is_implicitly_convertible` (cppinterop.cpp:157, `Cpp::IsImplicitlyConvertible`): standard
conversions between arithmetic types, array-to-pointer-to-bool, `oref<T>` → `object_ref`,
`nil_ref` → `oref<T>`. -/
def cppImplicitlyConvertible (f t : CT) : Bool :=
  f == t
  || (isArithmetic f && isArithmetic t)
  || (isCString f && t == .bool)
  || (isTypedObject f && t == .objectRef)
  || (f == .typed "nil" && isTypedObject t)

/-- `cpp_util::is_implicitly_convertible` (cpp_util.cpp:927). -/
def isImplicitlyConvertible (f t : CT) : Bool :=
  f == t || cppImplicitlyConvertible f t

/-- `cpp_util::is_implicitly_assignable` (cpp_util.cpp:943, new in 7135b7708): implicitly
convertible, and for a class type that is not a jank object also `Cpp::IsAssignable`. The universe
has no such class type, so it is `isImplicitlyConvertible`. -/
def isImplicitlyAssignable (f t : CT) : Bool :=
  if !isImplicitlyConvertible f t then false
  else if isAnyObject t then true
  else match t with
    | .other _ => false
    | _ => true

/-- `cppinterop::is_constructible` (cppinterop.cpp:169, `Cpp::IsConstructible`): `T(x)` is well formed. -/
def cppIsConstructible (to fr : CT) : Bool :=
  to == fr || (isArithmetic to && isArithmetic fr) || (to == .bool && isCString fr)
  || (isTypedObject fr && to == .objectRef) || (fr == .typed "nil" && isTypedObject to)

/-- `cpp_util::implicit_conversion_action`. -/
inductive ConvAction where
  | none | intoObject | fromObject | cast | unknown
  deriving Repr, BEq, DecidableEq, Inhabited

/-- `cpp_util::determine_implicit_conversion` (cpp_util.cpp:2004), over the universe (no
references, no cv-qualifiers, no class hierarchy, no pointers). -/
def determineImplicitConversion (exprType expectedType : CT) : ConvAction :=
  if exprType == expectedType || (isUntypedObject exprType && isUntypedObject expectedType) then .none
  else if isUntypedObject expectedType && isTypedObject exprType then .none
  else if isTypedObject expectedType && isUntypedObject exprType then .fromObject
  else if isAnyObject expectedType && isTraitConvertible exprType then .intoObject
  else if isAnyObject exprType && isTraitConvertible expectedType then .fromObject
  else if cppIsConstructible expectedType exprType then .cast
  else .unknown

/-- `cpp_util::branch_common_type` (cpp_util.hpp:115, new in 7135b7708). -/
structure BranchCommonType where
  type : CT
  thenNeedsConversion : Bool
  elseNeedsConversion : Bool
  deriving Repr, BEq, DecidableEq

/-- `cpp_util::find_branch_common_type` (cpp_util.cpp:1908, new in 7135b7708; used by
`analyze_if` and, per branch against the default, by `analyze_case`): from the `then` type and the
`else` type (`object_ref` when absent), whether the branches are accepted, which get boxed, and the
common type. The final types are not those of the converted expressions: a converted branch counts
as `object_ref` (cpp_util.cpp:1942). -/
def findBranchCommonType (thenType : CT) (elseType? : Option CT) (hasRecur : Bool) :
    Except String BranchCommonType :=
  let elseType := elseType?.getD .objectRef
  let isThenObject := isAnyObject thenType
  let isElseObject := isAnyObject elseType
  let isThenConvertible := isTraitConvertible thenType
  let isElseConvertible := isTraitConvertible elseType
  let commonType := getCommonType' thenType elseType
  let isSameType := thenType == elseType
  let isCompatible := isImplicitlyAssignable thenType elseType || isImplicitlyAssignable elseType thenType
    || commonType.isSome
  if isSameType || isCompatible || ((isElseObject && isThenConvertible) || (isThenObject && isElseConvertible))
     || (isThenConvertible && isElseConvertible) || hasRecur then
    let thenNeedsConversion := !isSameType && (isElseObject || !isCompatible) && isThenConvertible && isElseConvertible
    let elseNeedsConversion := !isSameType && (isThenObject || !isCompatible) && isElseConvertible && isThenConvertible
    let finalThenType := if thenNeedsConversion then CT.objectRef else thenType
    let finalElseType := match elseType? with
      | some t => if !elseNeedsConversion then t else CT.objectRef
      | none => CT.objectRef
    let (chosen0, otherType) := selectMostNativeType (nonVoidType finalElseType) (nonVoidType finalThenType)
    let finalIsSameType := finalThenType == finalElseType && !isCString finalThenType
    let finalCommonType := getCommonType' finalThenType finalElseType
    let chosen :=
      if isTypedObjectRef chosen0 && isAnyObject otherType && chosen0 != otherType then CT.objectRef
      else if !finalIsSameType && finalCommonType.isSome then finalCommonType.get!
      else if !isAnyObject chosen0 && !isAnyObject otherType && isCompatible
              && isImplicitlyConvertible chosen0 otherType then otherType
      else chosen0
    .ok { type := chosen, thenNeedsConversion, elseNeedsConversion }
  else
    .error s!"Mismatched branch types `{thenType.spelling}` and `{elseType.spelling}`. Each branch must have the same type, a common type, or a trait conversion."

/-- The result of `Cpp::GetBuiltinOperatorType` for `=` (assignment): the builtin candidates
`T& operator=(T&, U)` exist for arithmetic `T`, `U`. -/
def builtinAssignOk (l r : CT) : Bool := isArithmetic l && isArithmetic r

/-- `cpp_util::literal_type` (cpp_util.cpp:603): the type of a literal, unboxed or boxed. -/
def literalType (o : Obj) (isBoxed : Bool) : CT :=
  match o with
  | .nil => .typed "nil"
  | .boolean _ => if !isBoxed then .bool else .typed "boolean"
  | .integer v =>
    if !isBoxed then
      -- `static_cast<i32>(i) == i`
      if (v.truncate 32).signExtend 64 == v then .int else .long
    else .typed "integer"
  | .smallInteger _ => if !isBoxed then .int else .typed "small_integer"
  | .character _ => .typed "character"
  | .real _ => if !isBoxed then .double else .typed "real"
  | .smallReal _ => if !isBoxed then .double else .typed "small_real"
  | .symbol .. => .typed "symbol"
  | .keyword .. => .typed "keyword"
  | .persistentString s => if !isBoxed then .cstr (s.utf8ByteSize + 1) else .typed "persistent_string"
  | .persistentList .. => .typed "persistent_list"
  | .persistentVector .. => .typed "persistent_vector"
  | .persistentHashSet .. => .typed "persistent_hash_set"
  | .persistentArrayMap .. => .typed "persistent_array_map"
  | .persistentHashMap .. => .typed "persistent_hash_map"
  | .var .. => .typed "var"
  | .opaque .rePattern _ => .typed "re_pattern"
  | _ => .objectRef

/-- A literal is analyzed as `primitive_literal` exactly when its unboxed type is an object
(processor.cpp:3241). -/
def literalIsPrimitive (o : Obj) : Bool := isAnyObject (literalType o false)

/-- Numbers, booleans and strings become `cpp_literal`s (native C++ values). -/
theorem numbers_are_cpp_literals (b : Bool) (v : BitVec 32) (r : UInt64) :
    literalIsPrimitive (.boolean b) = false ∧ literalIsPrimitive (.smallInteger v) = false
    ∧ literalIsPrimitive (.smallReal r) = false := by
  simp [literalIsPrimitive, literalType, isAnyObject, isUntypedObject, isTypedObject]

/-- `if` with an `int` branch and a `bool` branch has common type `int`. -/
theorem common_bool_int : getCommonType .bool .int = some .int ∧ getCommonType .int .bool = some .int := by
  decide

theorem common_int_double : getCommonType .int .double = some .double := by decide

/-- A loop local bound to an `int` literal stays `int` (no type erasure). -/
theorem mutable_int : mutableType .int = .int ∧ mutableType .double = .double ∧ mutableType .bool = .bool := by
  decide

end Jank.Analyzer
