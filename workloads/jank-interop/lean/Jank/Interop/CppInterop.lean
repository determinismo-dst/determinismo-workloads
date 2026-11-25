import Jank.Interop.Convert

/-!
# `src/cpp/jank/analyze/cppinterop.cpp`, replicated

Every function of cppinterop.cpp is a lock of the interpreter mutex (a `std::recursive_mutex`,
jit/processor.hpp:102, so the nested locks in cpp_util.cpp are fine) and one call into CppInterOp.
Each Lean definition below is that call, answered by the model of `Cxx.lean`/`Facts.lean`. A
scope (`clang_decl`) is a `Decl`; the null scope is `none`.

The world (`World`) is what Clang's AST holds: jank's runtime types, a few std types and the
program's `cpp/raw` declarations (`world0`).
-/

namespace Jank.Interop.CppInterop

open Cxx


abbrev Scope := Option Decl

/-- Namespaces Clang knows in this model. -/
def namespaces : List String := ["std", "jank", "jank::runtime", "jank::runtime::obj"]

/-- Every named declaration, by qualified name (`get_named` / `GetScopeFromCompleteName`). -/
def lookupQualified (w : World) (q : String) : Scope :=
  if namespaces.contains q then some (.namespace_ q)
  else if q == "std::string" then some (.typedef_ "std::string" stdString)
  else if q == "size_t" || q == "std::size_t" then some (.typedef_ "size_t" sizeT)
  else if q == "std::nullptr_t" then some (.typedef_ "std::nullptr_t" (.b .nullptr))
  else if q == "std::vector" then some (.class_ { name := "std::vector", complete := false })
  else if q.startsWith "jank::runtime::obj::" && q.endsWith "_ref" then
    let v := (q.drop "jank::runtime::obj::".length).dropRight 4
    if typedRefs.contains v.toString then some (.typedef_ q (typedRef v.toString)) else none
  else match w.findClass q with
    | some c => some (.class_ c)
    | none => match w.findEnum q with
      | some e => some (.enum_ e)
      | none =>
        let consts := w.enums.flatMap fun e =>
          e.constants.filterMap fun (n, v) =>
            if (!e.isScoped && n == q) || (e.name ++ "::" ++ n == q) then some (Decl.enumConstant e.name n v) else none
        match consts with
        | c :: _ => some c
        | [] => none

def declName : Decl → String
  | .namespace_ n => n
  | .class_ c => c.name
  | .enum_ e => e.name
  | .enumConstant e n _ => e ++ "::" ++ n
  | .function f => f.name
  | .variable n _ _ _ => n
  | .typedef_ n _ => n
  | .field o f => o ++ "::" ++ f.name

/-- cppinterop.cpp:mangle_rtti:37 → `Cpp::MangleRTTI` (the Itanium `_ZTI` name). -/
def mangleRtti (t : CType) : String := s!"_ZTI{reprStr t.canonical}"
/-- cppinterop.cpp:enable_debug_output:43 (no effect on the model). -/
def enableDebugOutput (_ : Bool) : Unit := ()
/-- cppinterop.cpp:dump:49 (prints the scope; no effect on the model). -/
def dump (_ : Scope) : Unit := ()
/-- cppinterop.cpp:is_union:55 (7135b7708) → `Cpp::IsUnion` (the model's world declares no
unions). -/
def isUnion : Scope → Bool | _ => false
/-- cppinterop.cpp:is_namespace:61. -/
def isNamespace : Scope → Bool | some (.namespace_ _) => true | _ => false
/-- cppinterop.cpp:is_class:67. -/
def isClass : Scope → Bool | some (.class_ c) => c.complete || true | _ => false
/-- cppinterop.cpp:is_class_template:73 (`std::vector` without arguments). -/
def isClassTemplate : Scope → Bool | some (.class_ c) => c.name == "std::vector" | _ => false
/-- cppinterop.cpp:is_function:79. -/
def isFunction : Scope → Bool | some (.function f) => f.template == .none | _ => false
/-- cppinterop.cpp:is_function_pointer_type:85. -/
def isFunctionPointerType (t : CType) : Bool := Cxx.isFunctionPointer t
/-- cppinterop.cpp:is_inline_friend_function:91. -/
def isInlineFriendFunction (_ : Scope) : Bool := false
/-- cppinterop.cpp:is_complete:97. -/
def isComplete : Scope → Bool
  | some (.class_ c) => c.complete
  | some _ => true
  | none => false
/-- cppinterop.cpp:is_builtin:103 → `Cpp::IsBuiltin`. -/
def isBuiltin (t : CType) : Bool := Cxx.isBuiltin t
/-- cppinterop.cpp:is_integral:109 → `Cpp::IsIntegral`. -/
def isIntegral (t : CType) : Bool := Cxx.isIntegral t
/-- cppinterop.cpp:is_void:115. -/
def isVoid (t : CType) : Bool := Cxx.isVoid t
/-- cppinterop.cpp:get_void_type:121. -/
def getVoidType : CType := .b .void
/-- cppinterop.cpp:is_template:127. -/
def isTemplate : Scope → Bool
  | some (.function f) => f.template != .none
  | s => isClassTemplate s
/-- cppinterop.cpp:is_template_specialization:133 (`std::vector<int>`, jank's `oref<T>`s). -/
def isTemplateSpecialization : Scope → Bool
  | some (.class_ c) => c.name == "std::vector<int>" || c.orefOf.isSome || c.name == objectRefName
  | _ => false
/-- cppinterop.cpp:is_template_specialization_of:139 (only `oref` is asked about). -/
def isTemplateSpecializationOf (spec : Scope) (templ : String) : Bool :=
  match spec with
  | some (.class_ c) => templ == "jank::runtime::oref" && (c.orefOf.isSome || c.name == objectRefName)
  | _ => false
/-- cppinterop.cpp:is_typedefed:145. -/
def isTypedefed : Scope → Bool | some (.typedef_ ..) => true | _ => false
/-- cppinterop.cpp:get_common_type:151 → `Cpp::GetCommonType`. -/
def getCommonType (p : Platform) (w : World) (a b : CType) : CType := Cxx.commonType p w a b
/-- cppinterop.cpp:is_implicitly_convertible:157. -/
def isImplicitlyConvertible (p : Platform) (w : World) (src dst : CType) : Bool := Cxx.isImplicitlyConvertible p w src dst
/-- cppinterop.cpp:is_c_style_convertible:163. -/
def isCStyleConvertible (p : Platform) (w : World) (src dst : CType) : Bool := Cxx.isCStyleConvertible p w src dst
/-- cppinterop.cpp:is_constructible:169. -/
def isConstructible (p : Platform) (w : World) (dst src : CType) : Bool := Cxx.isConstructible p w dst src
/-- cppinterop.cpp:is_assignable:175 (7135b7708) → `Cpp::IsAssignable` (`std::is_assignable<to,
from>`, IA20): `to` an lvalue of a non-const type implicitly convertible from `from` (the model's
classes have one implicit copy assignment; no ambiguous `operator=` sets). -/
def isAssignable (p : Platform) (w : World) (dst src : CType) : Bool :=
  !Cxx.isConst (Cxx.nonRef dst) && Cxx.isImplicitlyConvertible p w src (Cxx.nonRef dst)
/-- cppinterop.cpp:is_trivially_destructible:181 (builtins, pointers, enums). -/
def isTriviallyDestructible (w : World) (t : CType) : Bool := !Cxx.isRecord t || (convertSpec w t).isSome
/-- cppinterop.cpp:is_enum_scope:187. -/
def isEnumScope : Scope → Bool | some (.enum_ _) => true | _ => false
/-- cppinterop.cpp:is_enum_constant:193. -/
def isEnumConstant : Scope → Bool | some (.enumConstant ..) => true | _ => false
/-- cppinterop.cpp:is_enum_type:199. -/
def isEnumType (t : CType) : Bool := Cxx.isEnum t
/-- cppinterop.cpp:has_type_qualifier:205. -/
def hasTypeQualifier (t : CType) (volatile : Bool) : Bool :=
  if volatile then t.canonical.topVolatile else t.canonical.topConst
/-- cppinterop.cpp:is_variable:211. -/
def isVariable : Scope → Bool | some (.variable ..) => true | some (.field ..) => true | _ => false
/-- cppinterop.cpp:get_name:217. -/
def getName : Scope → String
  | some d => ((declName d).splitOn "::").getLast!
  | none => ""
/-- cppinterop.cpp:get_qualified_name:223. -/
def getQualifiedName : Scope → String | some d => declName d | none => ""
/-- cppinterop.cpp:get_qualified_complete_name:229. -/
def getQualifiedCompleteName : Scope → String := getQualifiedName
/-- cppinterop.cpp:get_truncated_name:235. -/
def getTruncatedName : Scope → String := getName
/-- cppinterop.cpp:get_qualified_complete_name_with_template_args:241. -/
def getQualifiedCompleteNameWithTemplateArgs : Scope → String := getQualifiedName
/-- cppinterop.cpp:get_global_scope:247 (the translation unit). -/
def getGlobalScope : Scope := some (.namespace_ "")
/-- cppinterop.cpp:get_underlying_scope:253 (a typedef to a class: the class). -/
def getUnderlyingScope (w : World) : Scope → Scope
  | some (.typedef_ n t) =>
    match t.canonical with
    | .record r => match w.findClass r with | some c => some (.class_ c) | none => some (.typedef_ n t)
    | .enum e => match w.findEnum e with | some x => some (.enum_ x) | none => some (.typedef_ n t)
    | _ => some (.typedef_ n t)
  | s => s
/-- cppinterop.cpp:get_scope_from_complete_name:259. -/
def getScopeFromCompleteName (w : World) (q : String) : Scope := lookupQualified w q
/-- cppinterop.cpp:get_named:265: a direct member `name` of `parent`. An overload set (more than
one function) is not a single declaration: none (IA6). -/
def getNamed (w : World) (name : String) (parent : Scope) : Scope :=
  let q := match parent with
    | some (.namespace_ "") | none => name
    | some d => declName d ++ "::" ++ name
  match lookupQualified w q with
  | some d => some d
  | none =>
    match w.functions.filter (·.name == q) with
    | [f] => some (.function f)
    | _ => none
/-- cppinterop.cpp:get_parent_scope:271. -/
def getParentScope (s : Scope) : Scope :=
  match s with
  | some (.namespace_ "") | none => none
  | some d =>
    match (declName d).splitOn "::" with
    | [_] => some (.namespace_ "")
    | parts => some (.namespace_ ("::".intercalate (parts.dropLast)))
/-- cppinterop.cpp:get_scope_from_type:277 → `Cpp::GetScopeFromType` (IA7): the canonical type,
one pointer or array level stripped, qualifiers stripped; a function type gives its return type's
class; an enum its declaration; a class its declaration; anything else none. -/
def getScopeFromType (w : World) (t : CType) : Scope :=
  let c := t.canonical.unqual
  let c := match c with | .ptr u | .array u _ => u.canonical.unqual | u => u
  let c := match c with | .fn r _ => r.canonical.unqual | u => u
  match c with
  | .record n => (w.findClass n).map Decl.class_
  | .enum n => (w.findEnum n).map Decl.enum_
  | _ => none
/-- cppinterop.cpp:get_num_bases:283. -/
def getNumBases : Scope → Nat | some (.class_ c) => c.bases.length | _ => 0
/-- cppinterop.cpp:get_base_class:289. -/
def getBaseClass (w : World) (s : Scope) (i : Nat) : Scope :=
  match s with
  | some (.class_ c) => (c.bases[i]?).bind fun b => (w.findClass b).map Decl.class_
  | _ => none
/-- cppinterop.cpp:has_usable_copy_constructor:295. -/
def hasUsableCopyConstructor (_ : Scope) : Bool := true
/-- cppinterop.cpp:has_usable_move_constructor:301. -/
def hasUsableMoveConstructor (_ : Scope) : Bool := true
/-- cppinterop.cpp:has_deleted_move_constructor:307. -/
def hasDeletedMoveConstructor (_ : Scope) : Bool := false
/-- cppinterop.cpp:get_functions_using_name:313: the overload set `name` in `scope`. -/
def getFunctionsUsingName (w : World) (scope : Scope) (name : String) : List FnDecl :=
  let q := match scope with
    | some (.namespace_ "") | none => name
    | some d => declName d ++ "::" ++ name
  w.functions.filter (·.name == q)
/-- cppinterop.cpp:get_function_return_type:319. -/
def getFunctionReturnType (f : FnDecl) : CType := f.ret
/-- cppinterop.cpp:get_function_num_args:325. -/
def getFunctionNumArgs (f : FnDecl) : Nat := f.params.length
/-- cppinterop.cpp:get_function_required_args:331. -/
def getFunctionRequiredArgs (f : FnDecl) : Nat := f.required
/-- cppinterop.cpp:get_function_arg_type:337 (null past the last parameter). -/
def getFunctionArgType (f : FnDecl) (i : Nat) : CType := f.params.getD i .null
/-- cppinterop.cpp:get_function_signature:343. -/
def getFunctionSignature (f : FnDecl) : String := s!"{reprStr f.ret} {f.name}({reprStr f.params})"
/-- cppinterop.cpp:get_function_source_info:349. -/
def getFunctionSourceInfo (_ : FnDecl) : String := "<cpp/raw>"
/-- cppinterop.cpp:get_function_return_type_from_type:355. -/
def getFunctionReturnTypeFromType (t : CType) : CType :=
  match t.canonical.unqual with
  | .ptr (.fn r _) | .fn r _ => r
  | _ => .null
/-- cppinterop.cpp:get_function_num_args_from_type:361. -/
def getFunctionNumArgsFromType (t : CType) : Nat :=
  match t.canonical.unqual with
  | .ptr (.fn _ ps) | .fn _ ps => ps.length
  | _ => 0
/-- cppinterop.cpp:get_function_arg_type_from_type:367. -/
def getFunctionArgTypeFromType (t : CType) (i : Nat) : CType :=
  match t.canonical.unqual with
  | .ptr (.fn _ ps) | .fn _ ps => ps.getD i .null
  | _ => .null
/-- cppinterop.cpp:is_function_variadic:373. -/
def isFunctionVariadic (f : FnDecl) : Bool := f.isVariadic
/-- cppinterop.cpp:is_function_variadic_template:379. -/
def isFunctionVariadicTemplate (_ : FnDecl) : Bool := false
/-- cppinterop.cpp:is_function_deleted:385. -/
def isFunctionDeleted (f : FnDecl) : Bool := f.isDeleted
/-- cppinterop.cpp:is_function_type_const:391. -/
def isFunctionTypeConst (_ : CType) : Bool := false
/-- cppinterop.cpp:is_templated_function:397. -/
def isTemplatedFunction : Scope → Bool | some (.function f) => f.template != .none | _ => false
/-- cppinterop.cpp:is_bodyless_function_template_specialization:403. -/
def isBodylessFunctionTemplateSpecialization (_ : Scope) : Bool := false
/-- cppinterop.cpp:lookup_constructors:409. -/
def lookupConstructors (w : World) (_name : String) (parent : Scope) : List FnDecl :=
  match getUnderlyingScope w parent with
  | some (.class_ c) => (w.findClass c.name).map (·.ctors) |>.getD c.ctors
  | _ => []
/-- cppinterop.cpp:is_method:418. -/
def isMethod (f : FnDecl) : Bool := f.isMethod || f.isCtor
/-- cppinterop.cpp:is_protected_method:424. -/
def isProtectedMethod (f : FnDecl) : Bool := f.isProtected
/-- cppinterop.cpp:is_private_method:430. -/
def isPrivateMethod (f : FnDecl) : Bool := f.isPrivate
/-- cppinterop.cpp:is_constructor:436. -/
def isConstructor (f : FnDecl) : Bool := f.isCtor
/-- cppinterop.cpp:is_destructor:442. -/
def isDestructor (_ : FnDecl) : Bool := false
/-- cppinterop.cpp:is_static_method:448. -/
def isStaticMethod (f : FnDecl) : Bool := f.isMethod && f.isStatic
/-- cppinterop.cpp:get_datamembers:454 (non-static fields, declaration order). -/
def getDatamembers : Scope → List FieldDecl
  | some (.class_ c) => c.fields.filter (!·.isStatic)
  | _ => []
/-- cppinterop.cpp:get_static_datamembers:462. -/
def getStaticDatamembers : Scope → List FieldDecl
  | some (.class_ c) => c.fields.filter (·.isStatic)
  | _ => []
/-- cppinterop.cpp:lookup_datamember:470 (non-static fields only). -/
def lookupDatamember (name : String) (parent : Scope) : Option FieldDecl :=
  (getDatamembers parent).find? (·.name == name)
/-- cppinterop.cpp:lookup_methods:476. -/
def lookupMethods (w : World) (name : String) (parent : Scope) : List FnDecl :=
  match parent with
  | some (.class_ c) => (((w.findClass c.name).map (·.methods) |>.getD c.methods).filter (·.name == name)).map
      fun f => { f with owner := c.name }
  | _ => []
/-- cppinterop.cpp:get_variable_offset:482 (the `base` member of an `obj::X` is at offset 0). -/
def getVariableOffset (_ : FieldDecl) : Int := 0
/-- cppinterop.cpp:is_protected_variable:488. -/
def isProtectedVariable (f : FieldDecl) : Bool := f.isProtected
/-- cppinterop.cpp:is_private_variable:494. -/
def isPrivateVariable (f : FieldDecl) : Bool := f.isPrivate
/-- cppinterop.cpp:is_static_variable:500. -/
def isStaticVariable : Scope → Bool
  | some (.variable _ _ s _) => s
  | some (.field _ f) => f.isStatic
  | _ => false
/-- cppinterop.cpp:is_non_static_variable:506. -/
def isNonStaticVariable : Scope → Bool | some (.field _ f) => !f.isStatic | _ => false
/-- cppinterop.cpp:is_const_type:512. -/
def isConstType (t : CType) : Bool := Cxx.isConst t
/-- cppinterop.cpp:is_pointer_type:518. -/
def isPointerType (t : CType) : Bool := Cxx.isPointer t
/-- cppinterop.cpp:is_pointer_to_member_type:524. -/
def isPointerToMemberType (t : CType) : Bool := Cxx.isMemberPointer t
/-- cppinterop.cpp:is_pointer_to_member_variable_type:530. -/
def isPointerToMemberVariableType (t : CType) : Bool :=
  match t.canonical.unqual with | .memPtr _ u => !Cxx.isFunctionType u | _ => false
/-- cppinterop.cpp:is_pointer_to_member_function_type:536. -/
def isPointerToMemberFunctionType (t : CType) : Bool :=
  match t.canonical.unqual with | .memPtr _ u => Cxx.isFunctionType u | _ => false
/-- cppinterop.cpp:get_parent_type_from_pointer_to_member:542. -/
def getParentTypeFromPointerToMember (t : CType) : CType :=
  match t.canonical.unqual with | .memPtr c _ => .record c | _ => .null
/-- cppinterop.cpp:get_function_type_from_pointer_to_member:548. -/
def getFunctionTypeFromPointerToMember (t : CType) (_ : CType) : CType :=
  match t.canonical.unqual with | .memPtr _ u => u | _ => .null
/-- cppinterop.cpp:is_array_type:554. -/
def isArrayType (t : CType) : Bool := Cxx.isArray t
/-- cppinterop.cpp:is_sized_array_type:560. -/
def isSizedArrayType (t : CType) : Bool := Cxx.isSizedArray t
/-- cppinterop.cpp:get_array_size:566. -/
def getArraySize (t : CType) : Nat :=
  match t.canonical.unqual with | .array _ (some n) => n | _ => 0
/-- cppinterop.cpp:get_array_element_type:572. -/
def getArrayElementType (t : CType) : CType := Cxx.arrayElem t
/-- cppinterop.cpp:get_array_type:578 (unsized). -/
def getArrayType (t : CType) : CType := .array t none
/-- cppinterop.cpp:get_array_type:584 (sized). -/
def getArrayTypeSized (t : CType) (n : Nat) : CType := .array t (some n)
/-- cppinterop.cpp:get_function_type:590. -/
def getFunctionType (r : CType) (ps : List CType) : CType := .fn r ps
/-- cppinterop.cpp:get_pointee_type:596. -/
def getPointeeType (t : CType) : CType := Cxx.pointee t
/-- cppinterop.cpp:get_pointer_type:602. -/
def getPointerType (t : CType) : CType := .ptr t
/-- cppinterop.cpp:get_pointer_to_member_type:608. -/
def getPointerToMemberType (owner : String) (f : FieldDecl) : CType := .memPtr owner f.type
/-- cppinterop.cpp:get_lvalue_reference_type:614 (reference collapsing). -/
def getLvalueReferenceType (t : CType) : CType :=
  match t.canonical with | .lref u | .rref u => .lref u | _ => .lref t
/-- cppinterop.cpp:get_rvalue_reference_type:620. -/
def getRvalueReferenceType (t : CType) : CType :=
  match t.canonical with | .lref u => .lref u | .rref u => .rref u | _ => .rref t
/-- cppinterop.cpp:is_reference_type:626. -/
def isReferenceType (t : CType) : Bool := Cxx.isReference t
/-- cppinterop.cpp:is_rvalue_reference_type:632. -/
def isRvalueReferenceType (t : CType) : Bool := Cxx.isRvalueReference t
/-- cppinterop.cpp:get_value_category:638 (`value_category`: none, lvalue, rvalue). -/
def getValueCategory (t : CType) : Nat :=
  match t.canonical with | .lref _ => 1 | .rref _ => 2 | _ => 0
/-- cppinterop.cpp:get_non_reference_type:644. -/
def getNonReferenceType (t : CType) : CType := Cxx.nonRef t
/-- cppinterop.cpp:get_underlying_type:650. -/
def getUnderlyingType (t : CType) : CType := Cxx.underlyingType t
/-- cppinterop.cpp:get_type_without_cv:656. -/
def getTypeWithoutCv (t : CType) : CType := Cxx.withoutCv t
/-- cppinterop.cpp:get_type_with_const:662. -/
def getTypeWithConst (t : CType) : CType := Cxx.withConst t
/-- cppinterop.cpp:get_type_with_volatile:668. -/
def getTypeWithVolatile (t : CType) : CType := Cxx.withVolatile t

/-- What `Cpp::Get{Signed,Unsigned,Short,Long}Type` return (IA8: Clang's corresponding-type
functions, extended the way a `long`/`short` modifier reads; `null` where the library has no
answer). `long` of `long` is `long long`; `long` of `double` is `long double`; `short` of any
integer kind is the short of its signedness; `signed`/`unsigned` of a character or integer kind
its counterpart, `bool` unchanged. -/
def modifyType (p : Platform) (kw : String) (t : CType) : CType :=
  match Cxx.builtinKind? t with
  | none => .null
  | some k =>
    let signed := k.isSigned p
    match kw with
    | "signed" => match k with
      | .char | .uchar | .schar => .b .schar | .ushort | .short => .b .short | .uint | .int => .b .int
      | .ulong | .long => .b .long | .ullong | .llong => .b .llong | k => .b k
    | "unsigned" => match k with
      | .char | .uchar | .schar => .b .uchar | .ushort | .short => .b .ushort | .uint | .int => .b .uint
      | .ulong | .long => .b .ulong | .ullong | .llong => .b .ullong | k => .b k
    | "short" => if signed then .b .short else .b .ushort
    | "long" => match k with
      | .double => .b .ldouble
      | .long => .b .llong | .ulong => .b .ullong | .llong => .b .llong | .ullong => .b .ullong
      | _ => if signed then .b .long else .b .ulong
    | _ => .null

/-- cppinterop.cpp:get_signed_type:674. -/
def getSignedType (p : Platform) (t : CType) : CType := modifyType p "signed" t
/-- cppinterop.cpp:get_unsigned_type:680. -/
def getUnsignedType (p : Platform) (t : CType) : CType := modifyType p "unsigned" t
/-- cppinterop.cpp:get_short_type:686. -/
def getShortType (p : Platform) (t : CType) : CType := modifyType p "short" t
/-- cppinterop.cpp:get_long_type:692. -/
def getLongType (p : Platform) (t : CType) : CType := modifyType p "long" t
/-- cppinterop.cpp:is_short_type:698. -/
def isShortType (t : CType) : Bool :=
  match Cxx.builtinKind? t with | some .short | some .ushort => true | _ => false

/-- Clang's `QualType::getAsString` of a type (cppinterop.cpp:get_type_as_string:704). -/
partial def getTypeAsString : CType → String
  | .b k => k.spelling
  | .cv c v t => (if c then "const " else "") ++ (if v then "volatile " else "") ++ getTypeAsString t
  | .ptr t => getTypeAsString t ++ " *"
  | .lref t => getTypeAsString t ++ " &"
  | .rref t => getTypeAsString t ++ " &&"
  | .array e n => getTypeAsString e ++ s!"[{n.map toString |>.getD ""}]"
  | .fn r ps => getTypeAsString r ++ " (" ++ ", ".intercalate (ps.map getTypeAsString) ++ ")"
  | .enum n => n
  | .record n => n
  | .alias n _ => n
  | .memPtr c t => getTypeAsString t ++ s!" {c}::*"
  | .null => "<null>"
/-- cppinterop.cpp:get_type_as_truncated_string:710. -/
def getTypeAsTruncatedString (t : CType) : String := getTypeAsString t
/-- cppinterop.cpp:get_canonical_type:716. -/
def getCanonicalType (t : CType) : CType := t.canonical
/-- cppinterop.cpp:get_type:722 → `Cpp::GetType`: a builtin's spelling or a known type name. -/
def getType (w : World) (name : String) : CType :=
  let builtins : List (String × Builtin) :=
    [("void", .void), ("bool", .bool), ("char", .char), ("signed char", .schar),
     ("unsigned char", .uchar), ("wchar_t", .wchar), ("char8_t", .char8), ("char16_t", .char16),
     ("char32_t", .char32), ("short", .short), ("unsigned short", .ushort), ("int", .int),
     ("unsigned int", .uint), ("unsigned", .uint), ("long", .long), ("unsigned long", .ulong),
     ("long long", .llong), ("unsigned long long", .ullong), ("float", .float),
     ("double", .double), ("long double", .ldouble)]
  match builtins.lookup name with
  | some k => .b k
  | none =>
    if name == "size_t" then sizeT
    else if name == "int8_t" then .alias "int8_t" (.b .schar)
    else if name == "uint8_t" then .alias "uint8_t" (.b .uchar)
    else if name == "uint32_t" then .alias "uint32_t" (.b .uint)
    else if name == "int64_t" then .alias "int64_t" (.b .long)
    else if name == "uint64_t" then .alias "uint64_t" (.b .ulong)
    else match w.findClass name with
      | some c => .record c.name
      | none => .null
/-- cppinterop.cpp:get_type_from_scope:728. -/
def getTypeFromScope : Scope → CType
  | some (.class_ c) => .record c.name
  | some (.enum_ e) => .enum e.name
  | some (.enumConstant e _ _) => .enum e
  | some (.function f) => .fn f.ret f.params
  | some (.variable _ t _ _) => t
  | some (.typedef_ n t) => .alias n t
  | some (.field _ f) => f.type
  | _ => .null
/-- cppinterop.cpp:is_type_derived_from:734. -/
def isTypeDerivedFrom (w : World) (d b : CType) : Bool := Cxx.isDerivedFrom w d b
/-- cppinterop.cpp:is_const_method:740. -/
def isConstMethod (f : FnDecl) : Bool := f.isConst
/-- cppinterop.cpp:get_function_arg_name:746. -/
def getFunctionArgName (_ : FnDecl) (i : Nat) : String := s!"arg{i}"
/-- cppinterop.cpp:get_operator:752: operator functions declared for the argument types (the
model's classes declare none). -/
def getOperator (_ : Op) (_ : List CType) (_kind : Nat) : List FnDecl := []
/-- cppinterop.cpp:get_builtin_operator_type:763. -/
def getBuiltinOperatorType (p : Platform) (w : World) (op : Op) (args : List CType) : CType := Cxx.builtinOperatorType p w op args
/-- cppinterop.cpp:create_interpreter:770 (no effect on the model). -/
def createInterpreter : Unit := ()
/-- cppinterop.cpp:detect_resource_dir:782. -/
def detectResourceDir (_ : String) : String := ""
/-- cppinterop.cpp:instantiate_template:787 (with arguments): `std::vector<int>` only. -/
def instantiateTemplateWith (w : World) (tmpl : Scope) (args : List CType) : Scope :=
  match tmpl, args with
  | some (.class_ c), [t] =>
    if c.name == "std::vector" && t.canonical == .b .int then (w.findClass "std::vector<int>").map Decl.class_ else none
  | _, _ => none
/-- cppinterop.cpp:instantiate_template:796 (a specialization): true on failure, as
`Cpp::InstantiateTemplate` reports. -/
def instantiateTemplate (_ : Scope) : Bool := false

/-! ### Overload resolution (`Cpp::BestOverloadMatch`, `Cpp::GetOverloadCandidateInfo`) -/

def isPrimitiveNumber (t : CType) : Bool :=
  match (Cxx.nonRef t).canonical.unqual with
  | .b k => k.isArithmetic
  | _ => false

def isValidBoxedMath (t : CType) : Bool :=
  match (Cxx.nonRef t).canonical.unqual with
  | .record n => n == objectRefName ||
      ["integer", "small_integer", "real", "small_real", "big_integer", "big_decimal", "ratio"].any
        (fun v => n == orefName v)
  | _ => false

/-- The C++ type of `x->data` for a typed numeric `oref`. -/
def orefDataType (t : CType) : CType :=
  match (Cxx.nonRef t).canonical.unqual with
  | .record n =>
    if n == orefName "integer" then .b .long
    else if n == orefName "small_integer" then .b .int
    else if n == orefName "real" || n == orefName "small_real" then .b .double
    else .null
  | _ => .null

/-- Template argument deduction and the `requires` clauses of core/math.hpp for the math
templates: the instantiation (parameter types = the decayed argument types) and its return type
(`auto`, deduced from the `if constexpr` branch taken), or none. -/
def instantiateMath (p : Platform) (w : World) (k : TemplateKind) (args : List CType) : Option FnDecl :=
  let decayT (t : CType) : CType := (Cxx.decay (Cxx.nonRef t)).canonical.unqual
  match k, args with
  | .mathBinary op, [a, b] =>
    let l := decayT a
    let r := decayT b
    let cmp := op == "lt" || op == "lte"
    let arithOf (x y : CType) : CType :=
      match Cxx.promote p w x, Cxx.promote p w y with
      | some i, some j => .b (Cxx.usualArith p i j)
      | _, _ => .null
    let ret : CType :=
      if cmp then .b .bool
      else if isPrimitiveNumber l && isPrimitiveNumber r then arithOf l r
      else if isPrimitiveNumber l then
        (if !isValidBoxedMath r then objectRef
         else if (decayT r) == objectRef then objectRef else arithOf l (orefDataType r))
      else if isPrimitiveNumber r then
        (if !isValidBoxedMath l then objectRef
         else if l == objectRef then objectRef else arithOf (orefDataType l) r)
      else if !isValidBoxedMath l || !isValidBoxedMath r then objectRef
      else if l == objectRef || r == objectRef then objectRef
      else arithOf (orefDataType l) (orefDataType r)
    some { name := s!"jank::runtime::{op}", params := [l, r], required := 2, ret := ret,
           template := k }
  | .mathUnary op, [a] =>
    let l := decayT a
    let ret : CType :=
      if isPrimitiveNumber l then (if Cxx.isIntegral l then .b .long else l)
      else objectRef
    some { name := s!"jank::runtime::{op}", params := [l], required := 1, ret := ret, template := k }
  | _, _ => none

/-- The implicit object argument of a non-static member function (IA9): the class, a class
derived from it, or a pointer to one (jank emits `->` for pointers). -/
def implicitObjectOk (w : World) (owner : String) (a : CType) : Bool :=
  let t := (Cxx.nonRef a).canonical.unqual
  let t := match t with | .ptr u => u.canonical.unqual | u => u
  t == .record owner || Cxx.isDerivedFrom w t (.record owner)

/-- A candidate's conversion sequences for the arguments (`none`: not viable). For a non-static
member function the first argument is the invoking object. -/
def candidateRanks (p : Platform) (w : World) (f : FnDecl) (args0 : List CType) : Option (List Cxx.Rank) :=
  let member := f.isMethod && !f.isStatic && !f.isCtor
  let owner := f.owner
  if member && (args0.isEmpty || !implicitObjectOk w owner (args0.headD .null)) then none else
  let args := if member then args0.drop 1 else args0
  if args.length < f.required || (args.length > f.params.length && !f.isVariadic) then none
  else
    let ranks := (args.zip (f.params.take args.length)).map fun (a, prm) => Cxx.implicitConv p w a prm
    if ranks.all Option.isSome then some (ranks.filterMap id) else none

/-- `f` is better than `g` ([over.match.best]): no conversion worse, one better. -/
def better (rf rg : List Cxx.Rank) : Bool :=
  (rf.zip rg).all (fun (a, b) => a.ord ≤ b.ord) && (rf.zip rg).any (fun (a, b) => a.ord < b.ord)

/-- cppinterop.cpp:best_overload_match:802 → `Cpp::BestOverloadMatch` (IA9): templates are
instantiated by deduction; the unique best viable candidate, or every tied candidate when
ambiguous, or none. -/
def bestOverloadMatch (p : Platform) (w : World) (cands : List FnDecl) (args : List CType) : List FnDecl :=
  let inst := cands.filterMap fun f =>
    match f.template with
    | .none => some f
    | k => instantiateMath p w k args
  let viable := inst.filterMap fun f => (candidateRanks p w f args).map (f, ·)
  match viable with
  | [] => []
  | _ =>
    let best := viable.filter fun (_, r) => viable.all fun (_, r') => !(better r' r)
    match best with
    | [(f, _)] => [f]
    | _ => best.map (·.1)

/-- `Cpp::OverloadCandidateInfo`: viability and per-argument conversion kinds. -/
structure OverloadCandidateInfo where
  viable : Bool
  isTemplateInstantiationFailure : Bool := false
  conversions : List (Option Cxx.Rank)
  deriving Repr, Inhabited

/-- cppinterop.cpp:get_overload_candidate_info:811. -/
def getOverloadCandidateInfo (p : Platform) (w : World) (f : FnDecl) (args : List CType) : OverloadCandidateInfo :=
  { viable := (candidateRanks p w f args).isSome,
    conversions := (args.zip f.params).map fun (a, prm) => Cxx.implicitConv p w a prm }

end Jank.Interop.CppInterop
