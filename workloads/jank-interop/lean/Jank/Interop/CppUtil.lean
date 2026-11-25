import Jank.Interop.Expr

/-!
# `src/cpp/jank/analyze/cpp_util.cpp`, replicated

One definition per function of cpp_util.cpp (and the enum helper of cpp_util.hpp), in file order,
each citing its line. Static locals (`static auto const type{ ... }`) are plain values. Functions
that drive Clang's parser (`resolve_literal_type`, `resolve_literal_value`, `register_rtti`) are
modeled by what they return for the inputs the searched programs use.
-/

namespace Jank.Interop.CppUtil

open Jank.Analyzer (Obj ExprPosition ExprKind CppValueKind ConversionPolicy LoopKind ObjectType)
open CppInterop (Scope)

/-- cpp_util.cpp:reset_sfinae_state:31 (parses "1" to clear Clang's state; no model effect). -/
def resetSfinaeState : Unit := ()

/-- cpp_util.cpp:instantiate_if_needed:37: a template specialization or templated function is
instantiated (CppInterOp reports failure as `true`); a templated function's return type's scope
too. -/
def instantiateIfNeeded (w : World) (scope : Scope) : Except String Unit :=
  if scope.isNone then .ok ()
  else
    let scope := CppInterop.getUnderlyingScope w scope
    if CppInterop.isTemplateSpecialization scope || CppInterop.isTemplatedFunction scope then
      if CppInterop.isBodylessFunctionTemplateSpecialization scope then .ok ()
      else if CppInterop.instantiateTemplate scope then
        let _ := resetSfinaeState
        .error "Unable to instantiate template."
      else .ok ()
    else .ok ()

/-- cpp_util.cpp:instantiate:83. -/
def instantiate (w : World) (scope : Scope) (args : List CType) : Except String Scope :=
  match CppInterop.instantiateTemplateWith w scope args with
  | none => .error "Unable to instantiate template."
  | some d => .ok (some d)

/-- cpp_util.cpp:char_type:487: `resolve_literal_type("char")`, the exact `char` (not the
`signed char` Clang may canonicalize it to). -/
def charType : CType := .b .char

/-- cpp_util.cpp:resolve_type:113. -/
def resolveType (w : World) (sym : String) : CType :=
  if sym == "char" then charType else CppInterop.getType w sym

/-- cpp_util.cpp:resolve_scope:135: `a.b.c` looked up segment by segment; the last segment may
be an overload set, whose first function is returned. -/
def resolveScope (w : World) (sym : String) : Except String Scope := do
  let parts := sym.splitOn "."
  let rec go (scope : Scope) : List String → Except String Scope
    | [] => .ok scope
    | [last] => do
      instantiateIfNeeded w scope
      match CppInterop.getNamed w last scope with
      | some d => do instantiateIfNeeded w (some d); .ok (some d)
      | none =>
        match CppInterop.getFunctionsUsingName w scope last with
        | [] =>
          let n := CppInterop.getQualifiedName scope
          if n.isEmpty then .error s!"Unable to find `{last}` within the global namespace."
          else .error s!"Unable to find `{last}` within namespace `{n}`."
        | f :: _ => do instantiateIfNeeded w (some (.function f)); .ok (some (.function f))
    | seg :: rest =>
      match CppInterop.getUnderlyingScope w (CppInterop.getNamed w seg scope) with
      | none =>
        let n := CppInterop.getQualifiedName scope
        if n.isEmpty then .error s!"Unable to find `{seg}` within the global namespace."
        else .error s!"Unable to find `{seg}` within namespace `{n}` while trying to resolve `{sym}`."
      | some d => go (some d) rest
  go CppInterop.getGlobalScope parts

/-- cpp_util.cpp:resolve_literal_type:207: `using alias = <literal>;` parsed by Clang. -/
def resolveLiteralType (w : World) (literal : String) : Except String CType :=
  match CppInterop.getType w literal with
  | .null => .error "Unable to parse C++ literal."
  | t => .ok t

/-- The C++ value expressions a program may name through `resolve_literal_value` (macros and
other non-declarations), with their type and value. -/
def literalValues : List (String × CType × CVal) :=
  [("UINT64_MAX", .b .ulong, .int .ulong (2 ^ 64 - 1)),
   ("SIZE_MAX", .b .ulong, .int .ulong (2 ^ 64 - 1)),
   ("ULLONG_MAX", .b .ullong, .int .ullong (2 ^ 64 - 1)),
   ("UINT32_MAX", .b .uint, .int .uint (2 ^ 32 - 1)),
   ("INT_MAX", .b .int, .int .int 2147483647),
   ("INT64_MIN", .b .long, .int .long (-(2 ^ 63))),
   ("LDBL_EPSILON", .b .ldouble, .ldbl 1 (-63)),
   ("ONE_PLUS_LDBL_EPS", .b .ldouble, .ldbl (2 ^ 63 + 1) (-63)),
   ("FLT_TRUE_MIN", .b .float, .flt .float 1.401298464324817e-45)]

/-- cpp_util.hpp:literal_value_result. -/
structure LiteralValueResult where
  fnScope : FnDecl
  retType : CType
  functionCode : String
  deriving Repr, Inhabited

/-- cpp_util.cpp:resolve_literal_value:261: wraps the text in
`[[gnu::always_inline]] inline decltype(auto) f(){ return (<literal>\n); }` and compiles it. -/
def resolveLiteralValue (literal : String) : Except String LiteralValueResult :=
  match literalValues.find? (·.1 == literal) with
  | some (_, t, _) =>
    let alias := s!"jank_literal_{literal}"
    .ok { fnScope := { name := alias, ret := t }, retType := t,
          functionCode := s!"#ifndef JANK_DEFINED_{alias} ... decltype(auto) {alias}()\{ return ({literal}); } #endif" }
  | none => .error "Unable to parse C++ literal."

/-- cpp_util.cpp:find_adl_scopes:318: each starter and all its parents. -/
def findAdlScopes (starters : List Scope) : List Scope :=
  starters.flatMap fun s =>
    match s with
    | none => []
    | some _ =>
      let rec parents (s : Scope) (fuel : Nat) : List Scope :=
        match fuel, CppInterop.getParentScope s with
        | 0, _ => []
        | _, none => []
        | f + 1, some q => some q :: parents (some q) f
      s :: parents s 16

/-- cpp_util.cpp:get_qualified_name_helper:338. -/
def getQualifiedNameHelper (scope : Scope) (truncated : Bool) : String :=
  let res := if truncated then CppInterop.getTruncatedName scope else CppInterop.getQualifiedCompleteName scope
  if res == "<unnamed>" then CppInterop.getTypeAsString (CppInterop.getTypeFromScope scope) else res

/-- cpp_util.cpp:get_qualified_name:359. -/
def getQualifiedName (scope : Scope) : String := getQualifiedNameHelper scope false

/-- cpp_util.cpp:untyped_object_ptr_type:472: `jank::runtime::object *`. -/
def untypedObjectPtrType : CType := .ptr objectT
/-- cpp_util.cpp:untyped_object_ref_type:480. -/
def untypedObjectRefType : CType := objectRef

/-- cpp_util.cpp:get_qualified_type_name_helper:364: `object *` is named `object_ref`; a typedef
by its declaration's name; an unnamed enum by its integer type; a type with a scope by the scope's
name, plus `*` when the type is a pointer; anything else Clang's spelling. -/
partial def getQualifiedTypeNameHelper (w : World) (type : CType) (truncated : Bool) : String :=
  if type == untypedObjectPtrType then "jank::runtime::object_ref"
  else match type with
  | .null => "<null>"
  | .b .nullptr => "std::nullptr_t"
  -- An alias declared inside a class (e.g. `std::vector<int>::size_type`) is spelled by its
  -- canonical type (7135b7708, cpp_util.cpp:388-397); any other alias by its declaration's name.
  | .alias n t =>
    let parent := "::".intercalate ((n.splitOn "::").dropLast)
    if (w.findClass parent).isSome then getQualifiedTypeNameHelper w t.canonical truncated else n
  | _ =>
    match CppInterop.getScopeFromType w type with
    | some d =>
      let name := getQualifiedNameHelper (some d) truncated
      if CppInterop.isPointerType type then name ++ "*" else name
    | none =>
      if truncated then CppInterop.getTypeAsTruncatedString type else CppInterop.getTypeAsString type

/-- The type the emitted text `get_qualified_type_name(t)` denotes when Clang compiles it: the
scope's type (plus `*` for a pointer) when the type has a scope, else the type itself. Under IA7
`const C *`, `volatile C *` and `C (*)(...)` all print as `C*`, `object *` as `object_ref`. -/
def typeOfName (w : World) (type : CType) : CType :=
  if type == untypedObjectPtrType then objectRef
  else match type with
  | .null | .b .nullptr | .alias .. => type
  | _ =>
    match CppInterop.getScopeFromType w type with
    | some d =>
      let base := CppInterop.getTypeFromScope (some d)
      if CppInterop.isPointerType type then .ptr base else base
    | none => type

/-- cpp_util.cpp:get_qualified_type_name:431. -/
def getQualifiedTypeName (w : World) (type : CType) : String := getQualifiedTypeNameHelper w type false
/-- cpp_util.cpp:get_qualified_truncated_type_name:436. -/
def getQualifiedTruncatedTypeName (w : World) (type : CType) : String := getQualifiedTypeNameHelper w type true

/-- cpp_util.cpp:register_rtti:443: evaluates `&typeid(T)` and defines the RTTI symbol (no model
effect; it throws `codegen_internal_failure` when Clang fails). -/
def registerRtti (_ : CType) : Unit := ()

/-- cpp_util.cpp:bool_type:496. -/
def boolType : CType := .b .bool
/-- cpp_util.cpp:int_type:502. -/
def intType : CType := .b .int
/-- cpp_util.cpp:long_type:508. -/
def longType : CType := .b .long
/-- cpp_util.cpp:long_long_type:514: `get_type("long")` (used on WIN32 only). -/
def longLongType : CType := .b .long
/-- cpp_util.cpp:double_type:520. -/
def doubleType : CType := .b .double
/-- cpp_util.cpp:c_string_type:526: `const char[size + 1]`. -/
def cStringType (size : Nat) : CType := .array (.cv true false charType) (some (size + 1))
/-- cpp_util.cpp:nil_ref_type:533. -/
def nilRefType : CType := typedRef "nil"
/-- cpp_util.cpp:var_type:540. -/
def varType : CType := typedRef "var"
/-- cpp_util.cpp:integer_ref_type:547. -/
def integerRefType : CType := typedRef "integer"
/-- cpp_util.cpp:persistent_list_ref_type:554. -/
def persistentListRefType : CType := typedRef "persistent_list"
/-- cpp_util.cpp:persistent_vector_ref_type:561. -/
def persistentVectorRefType : CType := typedRef "persistent_vector"
/-- cpp_util.cpp:persistent_array_map_ref_type:568. -/
def persistentArrayMapRefType : CType := typedRef "persistent_array_map"
/-- cpp_util.cpp:persistent_hash_map_ref_type:575. -/
def persistentHashMapRefType : CType := typedRef "persistent_hash_map"
/-- cpp_util.cpp:persistent_hash_set_ref_type:582. -/
def persistentHashSetRefType : CType := typedRef "persistent_hash_set"
/-- cpp_util.cpp:jit_function_ref_type:589. -/
def jitFunctionRefType : CType := typedRef "jit_function"
/-- cpp_util.cpp:jit_closure_ref_type:596. -/
def jitClosureRefType : CType := typedRef "jit_closure"

/-- `runtime::to_i64` of an integer object. -/
def objToI64 : Obj → Int
  | .smallInteger v => v.toInt
  | .integer v => v.toInt
  | _ => 0

/-- cpp_util.cpp:literal_type:603: the C++ type the analyzer gives a literal. Unboxed: booleans
are `bool`; integers `int` when `static_cast<i32>(i) == i`, else `long` (non-WIN32); small
integers `int`; reals `double`; strings `const char[n + 1]`. Boxed (or any other object): the
typed `oref`, or `object_ref` by default. -/
def literalType (o : Obj) (isBoxed : Bool) : CType :=
  match o with
  | .nil => typedRef "nil"
  | .boolean _ => if !isBoxed then boolType else typedRef "boolean"
  | .integer v =>
    if !isBoxed then
      let i := v.toInt
      if (BitVec.ofInt 32 i).toInt == i then intType else longType
    else typedRef "integer"
  | .smallInteger _ => if !isBoxed then intType else typedRef "small_integer"
  | .character _ => typedRef "character"
  | .real _ => if !isBoxed then doubleType else typedRef "real"
  | .smallReal _ => if !isBoxed then doubleType else typedRef "small_real"
  | .symbol .. => typedRef "symbol"
  | .keyword .. => typedRef "keyword"
  | .persistentString s => if !isBoxed then cStringType s.utf8ByteSize else typedRef "persistent_string"
  | .persistentList .. => typedRef "persistent_list"
  | .persistentVector .. => typedRef "persistent_vector"
  | .persistentHashSet .. => typedRef "persistent_hash_set"
  | .persistentArrayMap .. => typedRef "persistent_array_map"
  | .persistentHashMap .. => typedRef "persistent_hash_map"
  | .var .. => varType
  | _ => untypedObjectRefType

/-- cpp_util.cpp:literal_codegen_type:864: an `integer` that fits i32 is a `small_integer_ref`,
else an `integer_ref`; a small hash map an array map; otherwise `literal_type`. -/
def literalCodegenType (o : Obj) (isBoxed : Bool) : CType :=
  match o with
  | .integer v =>
    let i := v.toInt
    if (BitVec.ofInt 32 i).toInt == i then typedRef "small_integer" else typedRef "integer"
  | .persistentHashMap _ kvs => if kvs.length ≤ 8 then typedRef "persistent_array_map" else typedRef "persistent_hash_map"
  | o => literalType o isBoxed

/-- cpp_util.cpp:is_member_function:902. -/
def isMemberFunction (f : FnDecl) : Bool :=
  CppInterop.isMethod f && !CppInterop.isConstructor f && !CppInterop.isDestructor f
/-- cpp_util.cpp:is_non_static_member_function:908. -/
def isNonStaticMemberFunction (f : FnDecl) : Bool := isMemberFunction f && !CppInterop.isStaticMethod f

/-- cpp_util.cpp:is_nullptr:913. -/
def isNullptr (type : CType) : Bool := type.canonical == (CType.b .nullptr)

/-- cpp_util.cpp:is_bool:920. -/
def isBool (type : CType) : Bool :=
  CppInterop.getCanonicalType (CppInterop.getTypeWithoutCv (CppInterop.getNonReferenceType type)) == boolType

/-- cpp_util.cpp:is_implicitly_convertible:927: same canonical non-reference types (or the source
equal to the cv-free target, or derived), else Clang's answer. -/
def isImplicitlyConvertible (p : Platform) (w : World) (src dst : CType) : Bool :=
  let fromNoRef := (CppInterop.getNonReferenceType src).canonical
  let toNoRef := (CppInterop.getNonReferenceType dst).canonical
  if fromNoRef == toNoRef || fromNoRef == CppInterop.getTypeWithoutCv toNoRef ||
     CppInterop.isTypeDerivedFrom w fromNoRef toNoRef then true
  else CppInterop.isImplicitlyConvertible p w src dst

/-- cpp_util.cpp:is_pointer_to_void_conversion:962: both pointers, and either points to `void`
(cv and the other pointee unexamined). -/
def isPointerToVoidConversion (src dst : CType) : Bool :=
  (CppInterop.isPointerType src && CppInterop.isPointerType dst) &&
  (CppInterop.isVoid (CppInterop.getPointeeType src) || CppInterop.isVoid (CppInterop.getPointeeType dst))

/-- cpp_util.cpp:is_untyped_object:969. -/
def isUntypedObject (type : CType) : Bool :=
  let canType := CppInterop.getCanonicalType (CppInterop.getTypeWithoutCv (CppInterop.getNonReferenceType type))
  canType == untypedObjectPtrType.canonical || canType == untypedObjectRefType.canonical

/-- cpp_util.cpp:is_untyped_object_ref:977 (7135b7708): exactly `object_ref`. -/
def isUntypedObjectRef (type : CType) : Bool :=
  let canType := CppInterop.getCanonicalType (CppInterop.getTypeWithoutCv (CppInterop.getNonReferenceType type))
  canType == untypedObjectRefType.canonical

/-- cpp_util.cpp:base_type:984. -/
partial def baseType (type : CType) : CType :=
  let t := CppInterop.getNonReferenceType type
  let rec strip (t : CType) : CType := if CppInterop.isPointerType t then strip (CppInterop.getPointeeType t) else t
  strip t

/-- cpp_util.cpp:oref_template:994. -/
def orefTemplate : String := "jank::runtime::oref"

/-- cpp_util.cpp:is_typed_object_ref:1002 (named `is_typed_object` at f3d82d654): not untyped,
and the type's scope a specialization of `oref`. -/
def isTypedObjectRef (w : World) (type : CType) : Bool :=
  let canType := CppInterop.getCanonicalType (CppInterop.getTypeWithoutCv (CppInterop.getNonReferenceType type))
  let scope := CppInterop.getUnderlyingScope w (CppInterop.getScopeFromType w canType)
  !isUntypedObject canType && scope.isSome && CppInterop.isTemplateSpecializationOf scope orefTemplate

/-- cpp_util.cpp:is_any_object:1012: `object *`, `object_ref` or a typed `oref`. -/
def isAnyObject (w : World) (type : CType) : Bool := isUntypedObject type || isTypedObjectRef w type

/-- cpp_util.cpp:is_any_object_ref:1017 (7135b7708): `object_ref` or a typed `oref` (not
`object *`). -/
def isAnyObjectRef (w : World) (type : CType) : Bool := isUntypedObjectRef type || isTypedObjectRef w type

/-- cpp_util.cpp:is_implicitly_assignable:943 (7135b7708): implicitly convertible, and for a class
target that is not a jank object, `to = from` assignable (`Cpp::IsAssignable`). -/
def isImplicitlyAssignable (p : Platform) (w : World) (src dst : CType) : Bool :=
  if !isImplicitlyConvertible p w src dst then false
  else
    let toNoRef := (CppInterop.getNonReferenceType dst).canonical
    let toScope := CppInterop.getScopeFromType w toNoRef
    if isAnyObject w dst || toScope.isNone || !CppInterop.isClass toScope then true
    else CppInterop.isAssignable p w toNoRef src

/-- cpp_util.cpp:is_primitive:1025: builtins, pointers, arrays, enums. -/
def isPrimitive (type : CType) : Bool :=
  CppInterop.isBuiltin type || CppInterop.isPointerType type || CppInterop.isArrayType type ||
  CppInterop.isEnumType type

/-- cpp_util.cpp:is_constructible:1033: Clang's answer, or a reference to the very type of a value. -/
def isConstructible (p : Platform) (w : World) (dst src : CType) : Bool :=
  if CppInterop.isConstructible p w dst src then true
  else if CppInterop.isReferenceType dst && !CppInterop.isReferenceType src then
    (CppInterop.getNonReferenceType dst).canonical == src.canonical
  else false

/-- cpp_util.cpp:is_c_string:1056. -/
def isCString (type : CType) : Bool :=
  CppInterop.isArrayType type &&
  (CppInterop.getTypeWithoutCv (CppInterop.getArrayElementType type)).canonical == charType

/-- cpp_util.cpp:mutable_type:1064: typed objects and C strings become `object_ref`; a const
(possibly referenced) type its cv-free self; void `object_ref`. -/
def mutableType (w : World) (type : CType) : CType :=
  if isTypedObjectRef w type then untypedObjectRefType
  else if isCString type then untypedObjectRefType
  else if CppInterop.isConstType (CppInterop.getNonReferenceType type) then
    CppInterop.getTypeWithoutCv (CppInterop.getNonReferenceType type)
  else if CppInterop.isVoid (CppInterop.getNonReferenceType type) then untypedObjectRefType
  else type

/-- cpp_util.cpp:select_most_native_type:1099. -/
def selectMostNativeType (w : World) (left right : CType) : CType × CType :=
  let isLeftAny := isAnyObject w left
  let isRightAny := isAnyObject w right
  let isLeftTyped := isTypedObjectRef w left
  let isRightTyped := isTypedObjectRef w right
  if !isLeftAny then (left, right)
  else if !isRightAny then (right, left)
  else if isLeftTyped then (left, right)
  else if isRightTyped then (right, left)
  else (left, right)

/-- The `get_type` of each expression struct (expression.cpp:59 for the base: `object_ref`;
local_reference.cpp: the binding's type; primitive_literal.cpp: `literal_type(data, true)`;
cpp_literal.cpp:27: `literal_type(data, false)`; cpp_delete/cpp_raw: void; cpp_member_call: the
function's return type; cpp_new.cpp:38: the array type itself, else a pointer to the type;
if.cpp:56; let.cpp:53 and do.cpp:64: the last body form's). -/
partial def getType (e : IExpr) : CType :=
  match e.data with
  | .primitiveLiteral d => literalType d true
  | .cppLiteral d => literalType d false
  | .localReference b _ => b.type
  | .varDeref _ | .call .. | .recur _ => untypedObjectRefType
  | .if_ t .. => t
  | .let_ _ body _ => match body.getLast? with | some x => getType x | none => untypedObjectRefType
  | .cppRaw _ | .cppDelete _ => CppInterop.getVoidType
  | .cppType _ t => t
  | .cppValue _ t _ _ => t
  | .cppConversion t .. => t
  | .cppUnsafeCast t _ => t
  | .cppCall t .. => t
  | .cppConstructorCall t .. => t
  | .cppMemberCall _ f _ => CppInterop.getFunctionReturnType f
  | .cppMemberAccess t .. => t
  | .cppBuiltinOperatorCall _ _ t => t
  | .cppBox _ => typedRef "opaque_box"
  | .cppUnbox t _ => t
  | .cppNew t _ => if CppInterop.isArrayType t then t else CppInterop.getPointerType t

/-- cpp_util.cpp:expression_type:1051 ("TODO: Remove entirely."). -/
def expressionType (e : IExpr) : CType := getType e

/-- cpp_util.cpp:expression_scope:1127: a cpp_value's scope, else null. -/
def expressionScope (e : IExpr) : Scope :=
  match e.data with
  | .cppValue _ _ s _ => s
  | _ => none

/-- cpp_util.cpp:non_void_expression_type:1146. -/
def nonVoidExpressionType (e : IExpr) : CType :=
  let t := expressionType e
  if CppInterop.isVoid t then untypedObjectRefType else t

/-- cpp_util.cpp:non_void_type:1157. -/
def nonVoidType (t : CType) : CType := if CppInterop.isVoid t then nilRefType else t

/-- cpp_util.cpp:is_trait_convertible:1717: `convert<T>` instantiates to a complete type, for the
canonical, cv-free, non-reference `T` (the `requires` clauses of convert/builtin.hpp). -/
def isTraitConvertible (w : World) (type : CType) : Bool := (convertSpec w type).isSome

/-- cpp_util.cpp:find_best_arg_types_with_conversions:1166: for each argument, every
arity-matching, non-deleted candidate (7135b7708: deleted ones skipped, templates no longer
skipped) whose parameter is not implicitly convertible but where an object/native pair is trait
convertible marks a needed conversion. A second such candidate for the same argument is an
ambiguity, unless its parameter type is the same (or `T&&` beside an earlier `T const &`, which
then defers to overload resolution; an earlier `T&&` beside a later `T const &` keeps the `T&&`,
1230-1268). The argument's type becomes that parameter type. -/
def findBestArgTypesWithConversions (p : Platform) (w : World) (fns : List FnDecl)
    (argTypes : List CType) (isMemberCall : Bool) : Except String (List CType) := do
  let memberOffset := if isMemberCall then 1 else 0
  let argCount := argTypes.length - memberOffset
  let matching := fns.filter fun f =>
    !CppInterop.isFunctionDeleted f &&
    CppInterop.getFunctionRequiredArgs f ≤ argCount && argCount ≤ CppInterop.getFunctionNumArgs f
  let mut converted := argTypes.toArray
  for argIdx in List.range argCount do
    let argType := CppInterop.getNonReferenceType (argTypes.getD (argIdx + memberOffset) .null)
    let isArgObj := isUntypedObject argType || isTypedObjectRef w argType
    let mut needed : Option Nat := none
    for (f, fnIdx) in matching.zipIdx do
      let paramType := CppInterop.getFunctionArgType f argIdx
      if paramType.isNull then continue
      if isImplicitlyConvertible p w (argTypes.getD (argIdx + memberOffset) .null) paramType then continue
      let isParamObj := isUntypedObject paramType || isTypedObjectRef w paramType
      if !isArgObj && !isParamObj then continue
      let traitType := if isArgObj then paramType else argType
      if isTraitConvertible w traitType then
        let mut apply := true
        if let some prevIdx := needed then
          let prevParam := CppInterop.getFunctionArgType (matching.getD prevIdx default) argIdx
          let sameType := paramType.canonical == prevParam.canonical
          let sameWithoutRef := (CppInterop.getTypeWithoutCv (CppInterop.getNonReferenceType paramType)).canonical ==
            CppInterop.getTypeWithoutCv (CppInterop.getNonReferenceType prevParam).canonical
          if sameType || (sameWithoutRef && CppInterop.isRvalueReferenceType paramType &&
              CppInterop.getValueCategory prevParam == 1) then
            pure ()
          else if sameWithoutRef && CppInterop.isRvalueReferenceType prevParam &&
                  CppInterop.getValueCategory paramType == 1 then
            apply := false
          else
            throw "No matching overload was found. When considering automatic trait conversions, this call is ambiguous."
        if apply then needed := some fnIdx
        converted := converted.set! (argIdx + memberOffset) paramType
  return converted.toList

/-- cpp_util.cpp:candidate_rank_tier:1290. -/
inductive CandidateRankTier where
  | viable | deleted | accessViolation | conversionFailure | constMismatch | templateFailure
  | arityMismatch
  deriving Repr, BEq, Inhabited

def CandidateRankTier.ord : CandidateRankTier → Nat
  | .viable => 0 | .deleted => 1 | .accessViolation => 2 | .conversionFailure => 3
  | .constMismatch => 4 | .templateFailure => 5 | .arityMismatch => 6

/-- cpp_util.cpp:candidate_rank:1301 and ranked_fn:1229. -/
structure RankedFn where
  fn : FnDecl
  tier : CandidateRankTier
  conversionScore : Nat := 0
  arityDelta : Nat := 0
  viable : Bool := false
  deriving Repr, Inhabited

/-- cpp_util.cpp:rank_candidate:1315. -/
def rankCandidate (p : Platform) (w : World) (f : FnDecl) (argTypes : List CType) (isMemberCall : Bool) : RankedFn :=
  let argCount := if isMemberCall && !argTypes.isEmpty then argTypes.length - 1 else argTypes.length
  let req := CppInterop.getFunctionRequiredArgs f
  let n := CppInterop.getFunctionNumArgs f
  let arityMismatch := argCount < req || (!CppInterop.isFunctionVariadic f && !CppInterop.isFunctionVariadicTemplate f && n < argCount)
  let info := CppInterop.getOverloadCandidateInfo p w f argTypes
  if CppInterop.isFunctionDeleted f then { fn := f, tier := .deleted, viable := info.viable }
  else if CppInterop.isPrivateMethod f || CppInterop.isProtectedMethod f then
    { fn := f, tier := .accessViolation, viable := info.viable }
  else if arityMismatch then
    { fn := f, tier := .arityMismatch, arityDelta := if argCount < req then req - argCount else argCount - req,
      viable := info.viable }
  else if isMemberCall && !argTypes.isEmpty && !CppInterop.isConstMethod f &&
          !CppInterop.isConstType (argTypes.headD .null) then
    { fn := f, tier := .constMismatch, viable := info.viable }
  else if info.viable then { fn := f, tier := .viable, viable := true }
  else if info.isTemplateInstantiationFailure then { fn := f, tier := .templateFailure }
  else
    let score := info.conversions.foldl (fun acc c => acc + match c with
      | none => 3 | some .userDefined => 2 | some .exact => 0 | some _ => 1) 0
    { fn := f, tier := .conversionFailure, conversionScore := score }

/-- `error::candidate`: the reason a candidate is listed. -/
structure Candidate where
  signature : String
  reason : String
  viable : Bool
  deriving Repr, Inhabited

/-- cpp_util.cpp:resolve_candidate:1388 (by reason). -/
def resolveCandidateReason (f : FnDecl) (reason : String) (viable : Bool) : Candidate :=
  { signature := CppInterop.getFunctionSignature f, reason, viable }

/-- cpp_util.cpp:resolve_candidate_impl:1400 (the per-argument conversion detail is reduced to
its reason). -/
def resolveCandidateImpl (f : FnDecl) (viable : Bool) : Candidate :=
  resolveCandidateReason f (if viable then "This candidate is ambiguous." else "See details below.") viable

/-- cpp_util.cpp:resolve_candidate:1477 (for a ranked candidate). -/
def resolveCandidate (r : RankedFn) (argTypes : List CType) (isMemberCall : Bool) : Candidate :=
  let f := r.fn
  if CppInterop.isFunctionDeleted f then resolveCandidateReason f "This function is deleted." false
  else if CppInterop.isPrivateMethod f then resolveCandidateReason f "This member function is private." false
  else if CppInterop.isProtectedMethod f then resolveCandidateReason f "This member function is protected." false
  else
    let req := CppInterop.getFunctionRequiredArgs f
    let n := CppInterop.getFunctionNumArgs f
    let argCount := if isMemberCall && !argTypes.isEmpty then argTypes.length - 1 else argTypes.length
    if argCount < req || (!CppInterop.isFunctionVariadic f && n < argCount) then
      resolveCandidateReason f s!"This function requires {req} argument(s), but {argCount} provided." false
    -- 7135b7708 (cpp_util.cpp:1514-1516): the invoking object is const; f3d82d654 tested `!is_const_type`.
    else if isMemberCall && CppInterop.isMethod f && !argTypes.isEmpty && !CppInterop.isConstMethod f &&
            CppInterop.isConstType (argTypes.headD .null) then
      resolveCandidateReason f "This member function is non-const, but the invoking object is const." false
    else resolveCandidateImpl f r.viable

/-- cpp_util.cpp:resolve_candidates:1538: ranked, stable-sorted by tier, arity delta, score. -/
def resolveCandidates (p : Platform) (w : World) (fns : List FnDecl) (argTypes : List CType) (isMemberCall : Bool) : List Candidate :=
  let ranked := fns.map fun f => rankCandidate p w f argTypes isMemberCall
  let lt (a b : RankedFn) : Bool :=
    if a.tier.ord != b.tier.ord then a.tier.ord < b.tier.ord
    else if a.tier == .arityMismatch && a.arityDelta != b.arityDelta then a.arityDelta < b.arityDelta
    else a.conversionScore < b.conversionScore
  let sorted := ranked.mergeSort (fun a b => lt a b || !(lt b a))
  sorted.map fun r => resolveCandidate r argTypes isMemberCall

/-- cpp_util.cpp:find_best_overload:1573: Clang's best match; more than one is an ambiguity; a
deleted, private or protected match an error. Arguments that named a template get the matched
parameter type (`arg_types` is an out parameter: returned). -/
def findBestOverload (p : Platform) (w : World) (fns : List FnDecl) (argTypes : List CType)
    (argScopes : List Scope) : Except String (Option FnDecl × List CType) :=
  if fns.isEmpty then .ok (none, argTypes)
  else
    match CppInterop.bestOverloadMatch p w fns argTypes with
    | [] => .ok (none, argTypes)
    | [m] =>
      if CppInterop.isFunctionDeleted m then .error s!"The `{m.name}` function cannot be called, since it's deleted."
      else if CppInterop.isPrivateMethod m then .error s!"The `{m.name}` function is private. It can only be accessed if it's public."
      else if CppInterop.isProtectedMethod m then .error s!"The `{m.name}` function is protected. It can only be accessed if it's public."
      else
        let member := if isNonStaticMemberFunction m then 1 else 0
        let argTypes' := (List.range argTypes.length).map fun i =>
          if i ≥ member && (CppInterop.isTemplate (argScopes.getD i none)) then
            CppInterop.getFunctionArgType m (i - member) else argTypes.getD i .null
        .ok (some m, argTypes')
    | ms => .error s!"This call is ambiguous between {ms.length} different overloads."

/-- cpp_util.cpp:find_aggregate_match_with_conversions:1635. -/
def findAggregateMatchWithConversions (p : Platform) (w : World) (aggregateTypes argTypes : List CType) :
    Option (List CType) := Id.run do
  if aggregateTypes.length != argTypes.length then return none
  let mut converted := argTypes.toArray
  for i in List.range argTypes.length do
    let argType := CppInterop.getNonReferenceType (argTypes.getD i .null)
    let isArgObj := isAnyObject w argType
    let paramType := aggregateTypes.getD i .null
    if paramType.isNull then continue
    if isImplicitlyConvertible p w (argTypes.getD i .null) paramType then continue
    let isParamObj := isAnyObject w paramType
    if !isArgObj && !isParamObj then continue
    let traitType := if isArgObj then paramType else argType
    if isTraitConvertible w traitType then converted := converted.set! i paramType
    else return none
  return some converted.toList

/-- cpp_util.cpp:get_function_return_type:1682. -/
def getFunctionReturnTypeOfExpr (e : IExpr) : CType :=
  match e.data with
  | .cppValue _ t scope _ =>
    let t := CppInterop.getNonReferenceType t
    if CppInterop.isFunctionPointerType t then CppInterop.getFunctionReturnTypeFromType t
    else match scope with
      | some (.function f) => CppInterop.getFunctionReturnType f
      | _ => .null
  | _ => .null

/-- cpp_util.cpp:get_function_parameter_type:1699. -/
def getFunctionParameterType (e : IExpr) (i : Nat) : CType :=
  match e.data with
  | .cppValue _ t scope _ =>
    let t := CppInterop.getNonReferenceType t
    if CppInterop.isFunctionPointerType t then CppInterop.getFunctionArgTypeFromType t i
    else match scope with
      | some (.function f) => CppInterop.getFunctionArgType f i
      | _ => .null
  | _ => .null

/-- cpp_util.cpp:offset_to_typed_object_base:1736 (the `base` member's offset, 0). -/
def offsetToTypedObjectBase (_ : CType) : Nat := 0

/-- cpp_util.cpp:match_operator:1749. -/
def matchOperator (name : String) : Option Cxx.Op :=
  let table : List (String × Cxx.Op) :=
    [("+", .plus), ("-", .minus), ("*", .star), ("/", .slash), ("%", .percent), ("++", .plusPlus),
     ("--", .minusMinus), ("==", .equalEqual), ("!=", .exclaimEqual), (">", .greater), ("<", .less),
     (">=", .greaterEqual), ("<=", .lessEqual), ("<=>", .spaceship), ("!", .exclaim),
     ("&&", .ampAmp), ("||", .pipePipe), ("~", .tilde), ("&", .amp), ("|", .pipe), ("^", .caret),
     ("<<", .lessLess), (">>", .greaterGreater), ("=", .equal), ("+=", .plusEqual),
     ("-=", .minusEqual), ("*=", .starEqual), ("/=", .slashEqual), ("%=", .percentEqual),
     ("&=", .ampEqual), ("|=", .pipeEqual), ("^=", .caretEqual), ("<<=", .lessLessEqual),
     (">>=", .greaterGreaterEqual), ("aget", .subscript), ("()", .call)]
  table.lookup name

/-- cpp_util.cpp:operator_name:1799. -/
def operatorName (op : Cxx.Op) : Option String :=
  let table : List (Cxx.Op × String) :=
    [(.plus, "+"), (.minus, "-"), (.star, "*"), (.slash, "/"), (.percent, "%"), (.plusPlus, "++"),
     (.minusMinus, "--"), (.equalEqual, "=="), (.exclaimEqual, "!="), (.greater, ">"), (.less, "<"),
     (.greaterEqual, ">="), (.lessEqual, "<="), (.spaceship, "<=>"), (.exclaim, "!"),
     (.ampAmp, "&&"), (.pipePipe, "||"), (.tilde, "~"), (.amp, "&"), (.pipe, "|"), (.caret, "^"),
     (.lessLess, "<<"), (.greaterGreater, ">>"), (.equal, "="), (.plusEqual, "+="),
     (.minusEqual, "-="), (.starEqual, "*="), (.slashEqual, "/="), (.percentEqual, "%="),
     (.ampEqual, "&="), (.pipeEqual, "|="), (.caretEqual, "^="), (.lessLessEqual, "<<="),
     (.greaterGreaterEqual, ">>="), (.subscript, "aget"), (.call, "()")]
  table.lookup op

/-- cpp_util.cpp:ensure_convertible:1848. -/
def ensureConvertible (w : World) (e : IExpr) : Except String Unit :=
  let t := expressionType e
  if !isAnyObject w t && !isTraitConvertible w t then
    .error s!"This function returns a native object of type `{CppInterop.getTypeAsString t}` that is not convertible to a jank runtime object."
  else .ok ()

/-- cpp_util.cpp:aggregate_initialization_types_impl:1862: bases' members first, recursively;
members of an anonymous union (flattened by Clang) contribute only the first (7135b7708,
1874-1890; the model's world has no unions, `CppInterop.isUnion`). -/
partial def aggregateInitializationTypesImpl (w : World) (scope : Scope) : List CType :=
  let n := CppInterop.getNumBases scope
  let bases := (List.range n).flatMap fun i => aggregateInitializationTypesImpl w (CppInterop.getBaseClass w scope i)
  let owner := CppInterop.getQualifiedName scope
  let (_, members) := (CppInterop.getDatamembers scope).foldl (fun (lastUnion, acc) (m : FieldDecl) =>
      let parent := CppInterop.getParentScope (some (.field owner m))
      if parent.isSome && parent != scope && CppInterop.isUnion parent then
        if parent == lastUnion then (lastUnion, acc) else (parent, acc ++ [m.type])
      else (none, acc ++ [m.type])) ((none : Scope), [])
  bases ++ members

/-- cpp_util.cpp:aggregate_initialization_types:1900. -/
def aggregateInitializationTypes (w : World) (scope : Scope) : List CType := aggregateInitializationTypesImpl w scope

/-- cpp_util.hpp:branch_common_type (7135b7708). -/
structure BranchCommonType where
  type : CType
  thenNeedsConversion : Bool := false
  elseNeedsConversion : Bool := false
  deriving Repr, Inhabited

/-- cpp_util.cpp:find_branch_common_type:1907 (7135b7708; the branch reconciliation `analyze_if`
did inline at f3d82d654, now shared with `analyze_case`). Compatibility is
`is_implicitly_assignable` either way or a common type; a branch is boxed when the types differ,
both are trait convertible, and the other side is an object or the two are incompatible. -/
def findBranchCommonType (p : Platform) (w : World) (thenExpr : IExpr) (elseOpt : Option IExpr)
    (hasRecur : Bool) : Except String BranchCommonType :=
  let thenType := expressionType thenExpr
  let elseType := match elseOpt with | some e => expressionType e | none => untypedObjectRefType
  let isThenObject := isAnyObject w thenType
  let isElseObject := isAnyObject w elseType
  let isThenConvertible := isTraitConvertible w thenType
  let isElseConvertible := isTraitConvertible w elseType
  let commonType := CppInterop.getCommonType p w thenType elseType
  let isSameType := thenType.canonical == elseType.canonical
  let isCompatible := isImplicitlyAssignable p w thenType elseType ||
    isImplicitlyAssignable p w elseType thenType || !commonType.isNull
  if isSameType || isCompatible || ((isElseObject && isThenConvertible) || (isThenObject && isElseConvertible)) ||
     (isThenConvertible && isElseConvertible) || hasRecur then
    let thenNeeds := !isSameType && (isElseObject || !isCompatible) && isThenConvertible && isElseConvertible
    let elseNeeds := !isSameType && (isThenObject || !isCompatible) && isElseConvertible && isThenConvertible
    let finalThen := if thenNeeds then untypedObjectRefType else getType thenExpr
    let finalElse := match elseOpt with
      | some e => if !elseNeeds then getType e else untypedObjectRefType
      | none => untypedObjectRefType
    let (chosen0, other) := selectMostNativeType w (nonVoidType finalElse) (nonVoidType finalThen)
    let finalIsSame := finalThen.canonical == finalElse.canonical && !CppInterop.isArrayType finalThen
    let finalCommon := CppInterop.getCommonType p w finalThen finalElse
    let chosen :=
      if isTypedObjectRef w chosen0 && isAnyObject w other && chosen0.canonical != other.canonical then untypedObjectRefType
      else if !finalIsSame && !finalCommon.isNull then finalCommon
      else if !isAnyObject w chosen0 && !isAnyObject w other && isCompatible &&
              isImplicitlyConvertible p w chosen0 other then other
      else chosen0
    .ok { type := chosen, thenNeedsConversion := thenNeeds, elseNeedsConversion := elseNeeds }
  else
    .error s!"Mismatched branch types `{getQualifiedTypeName w thenType}` and `{getQualifiedTypeName w elseType}`. Each branch must have the same type, a common type, or a trait conversion."

/-- cpp_util.hpp:implicit_conversion_action. -/
inductive ImplicitConversionAction where
  | unknown | none | intoObject | fromObject | cast
  deriving Repr, BEq, DecidableEq, Inhabited

/-- cpp_util.hpp:implicit_conversion_action_str. -/
def implicitConversionActionStr : ImplicitConversionAction → String
  | .none => "none" | .intoObject => "into_object" | .fromObject => "from_object" | .cast => "cast"
  | .unknown => "unknown"

/-- cpp_util.cpp:determine_implicit_conversion:2003. -/
partial def determineImplicitConversion (p : Platform) (w : World) (exprType0 expected : CType) :
    ImplicitConversionAction :=
  let exprType := CppInterop.getNonReferenceType exprType0
  let can (t : CType) := t.canonical
  if can exprType == can expected ||
     can exprType == can (CppInterop.getTypeWithConst expected) ||
     can (CppInterop.getTypeWithConst exprType) == can (CppInterop.getNonReferenceType expected) ||
     CppInterop.isTypeDerivedFrom w (can exprType) (can expected) ||
     (isUntypedObject exprType && isUntypedObject expected) then .none
  else if isUntypedObject expected && isTypedObjectRef w exprType then .none
  else if isTypedObjectRef w expected && isUntypedObject exprType then .fromObject
  else if isAnyObject w expected && isTraitConvertible w exprType then .intoObject
  else if isAnyObject w exprType && isTraitConvertible w expected then .fromObject
  else if CppInterop.isTypeDerivedFrom w (CppInterop.getUnderlyingType exprType) (CppInterop.getUnderlyingType expected) ||
          (can exprType == can (CppInterop.getNonReferenceType expected) &&
            !CppInterop.isReferenceType exprType && CppInterop.isReferenceType expected) ||
          (isNullptr exprType && (CppInterop.isPointerType expected || CppInterop.isArrayType expected)) ||
          (CppInterop.isArrayType exprType && CppInterop.isArrayType expected &&
            CppInterop.getArrayElementType exprType == CppInterop.getArrayElementType expected) then .none
  else if (CppInterop.isPointerType exprType || CppInterop.isArrayType exprType) &&
          (CppInterop.isPointerType expected || CppInterop.isArrayType expected) then
    let ep := CppInterop.getPointeeType exprType
    let xp := CppInterop.getPointeeType expected
    if CppInterop.isVoid ep || CppInterop.isVoid xp then .none
    else match determineImplicitConversion p w ep xp with
      | .none => .none
      | _ => .unknown
  else if CppInterop.isConstructible p w expected exprType then .cast
  else .unknown

end Jank.Interop.CppUtil
