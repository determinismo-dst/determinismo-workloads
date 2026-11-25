import Jank.R3.Interop.CppInterOp

/-!
# jank's interop paths that consume CppInterOp's answers (round 3)

Each definition replicates a function (or the part of one) of jank 7135b7708
(`upstream-main/compiler+runtime/src/cpp/jank/analyze/`), calling the round-3 CppInterOp replica
instead of round 2's standard-modeled answers. Round 2's object predicates
(`CppUtil.isAnyObject`, `isTypedObjectRef`, `isTraitConvertible`) are reused: on the class types
they see, round 2's `getScopeFromType` and CppInterOp's agree (`Census.lean`).

Programs are given as small ASTs (`TForm`) whose `text` is the jank source.
-/

namespace Jank.R3.Interop.Paths

open Jank.Interop
open Jank.R3.Interop.Clang
open Jank.R3.Interop.CppInterOp
open Jank.Interop.CppUtil (isAnyObject isTypedObjectRef isUntypedObject isTraitConvertible)

/-! ## cpp_util.cpp -/

/-- cpp_util.cpp:927 `is_implicitly_convertible`: same canonical non-reference types (or the
target's without cv), a class derived from the target (any access), else CppInterOp. -/
def isImplicitlyConvertible (p : Platform) (x : XWorld) (src dst : CType) : Bool :=
  let fromNoRef := getCanonicalType (getNonReferenceType src)
  let toNoRef := getCanonicalType (getNonReferenceType dst)
  if fromNoRef == toNoRef || fromNoRef == (getTypeWithoutCv toNoRef).canonical ||
     derivedFrom x fromNoRef toNoRef then true
  else CppInterOp.isImplicitlyConvertible p x src dst

/-- cpp_util.cpp:943 `is_implicitly_assignable`. -/
def isImplicitlyAssignable (p : Platform) (x : XWorld) (src dst : CType) : Bool :=
  if !isImplicitlyConvertible p x src dst then false
  else
    let toNoRef := getCanonicalType (getNonReferenceType dst)
    let toScope := getScopeFromType x toNoRef
    let isClassScope := match toScope with | some (.class_ _) => true | _ => false
    if isAnyObject x.w dst || !isClassScope then true
    else CppInterOp.isAssignable p x toNoRef src

/-- cpp_util.cpp:1025 `is_primitive`. -/
def isPrimitive (t : CType) : Bool :=
  CppInterOp.isBuiltin t || CppInterOp.isPointerType t || CppInterOp.isArrayType t || isEnumType t

/-- cpp_util.cpp:1033 `is_constructible`. -/
def isConstructible (p : Platform) (x : XWorld) (dst src : CType) : Bool :=
  if CppInterOp.isConstructible p x dst src then true
  else if CppInterOp.isReferenceType dst && !CppInterOp.isReferenceType src then
    getCanonicalType (getNonReferenceType dst) == getCanonicalType src
  else false

/-- cpp_util.cpp:984 `base_type`: references and every pointer level stripped. -/
def baseType (t : CType) : CType :=
  stripPtrs 16 (getNonReferenceType t)
where
  stripPtrs : Nat → CType → CType
    | 0, t => t
    | n + 1, t => if CppInterOp.isPointerType t then stripPtrs n (getPointeeType t) else t

/-- cpp_util.cpp:1099 `select_most_native_type`. -/
def selectMostNativeType (x : XWorld) (left right : CType) : CType × CType :=
  if !isAnyObject x.w left then (left, right)
  else if !isAnyObject x.w right then (right, left)
  else if isTypedObjectRef x.w left then (left, right)
  else if isTypedObjectRef x.w right then (right, left)
  else (left, right)

/-- cpp_util.cpp:1157 `non_void_type`. -/
def nonVoidType (t : CType) : CType := if CppInterOp.isVoid t then objectRef else t

/-- cpp_util.cpp:1909 `find_branch_common_type`: the `if`'s type (and whether a branch is boxed),
or the mismatch error. -/
def findBranchCommonType (p : Platform) (x : XWorld) (thenT elseT : CType) :
    Except String (CType × Bool × Bool) :=
  let w := x.w
  let isThenObject := isAnyObject w thenT
  let isElseObject := isAnyObject w elseT
  let isThenConvertible := isTraitConvertible w thenT
  let isElseConvertible := isTraitConvertible w elseT
  let common := getCommonType p x thenT elseT
  let isSame := getCanonicalType thenT == getCanonicalType elseT
  let isCompatible := isImplicitlyAssignable p x thenT elseT || isImplicitlyAssignable p x elseT thenT
    || !common.isNull
  if isSame || isCompatible || (isElseObject && isThenConvertible) || (isThenObject && isElseConvertible)
     || (isThenConvertible && isElseConvertible) then
    let thenConv := !isSame && (isElseObject || !isCompatible) && isThenConvertible && isElseConvertible
    let elseConv := !isSame && (isThenObject || !isCompatible) && isElseConvertible && isThenConvertible
    let finalThen := if thenConv then objectRef else thenT
    let finalElse := if !elseConv then elseT else objectRef
    let (chosen, other) := selectMostNativeType x (nonVoidType finalElse) (nonVoidType finalThen)
    let finalSame := getCanonicalType finalThen == getCanonicalType finalElse && !CppInterOp.isArrayType finalThen
    let finalCommon := getCommonType p x finalThen finalElse
    let chosen :=
      if isTypedObjectRef w chosen && isAnyObject w other && getCanonicalType chosen != getCanonicalType other then objectRef
      else if !finalSame && !finalCommon.isNull then finalCommon
      else if !isAnyObject w chosen && !isAnyObject w other && isCompatible && isImplicitlyConvertible p x chosen other then other
      else chosen
    .ok (chosen, thenConv, elseConv)
  else .error s!"Mismatched branch types `{CppInterOp.getCanonicalType thenT |> reprStr}` and `{reprStr elseT}`."

/-- cpp_util.hpp `implicit_conversion_action`. -/
inductive Action where
  | none | intoObject | fromObject | cast | unknown
  deriving Repr, BEq, DecidableEq, Inhabited

/-- cpp_util.cpp:2000 `determine_implicit_conversion` (pointer/array recursion bounded by `n`). -/
def determineImplicitConversion (p : Platform) (x : XWorld) : Nat → CType → CType → Action
  | 0, _, _ => .unknown
  | n + 1, exprType0, expected =>
    let w := x.w
    let exprType := getNonReferenceType exprType0
    let can := getCanonicalType
    if can exprType == can expected || can exprType == can (getTypeWithConst expected)
       || can (getTypeWithConst exprType) == can (getNonReferenceType expected)
       || derivedFrom x (can exprType) (can expected)
       || (isUntypedObject exprType && isUntypedObject expected) then .none
    else if isUntypedObject expected && isTypedObjectRef w exprType then .none
    else if isTypedObjectRef w expected && isUntypedObject exprType then .fromObject
    else if isAnyObject w expected && isTraitConvertible w exprType then .intoObject
    else if isAnyObject w exprType && isTraitConvertible w expected then .fromObject
    else if derivedFrom x (getUnderlyingType exprType) (getUnderlyingType expected)
      || (can exprType == can (getNonReferenceType expected) && !CppInterOp.isReferenceType exprType
          && CppInterOp.isReferenceType expected)
      || (can exprType == can .nullptrT && (CppInterOp.isPointerType expected || CppInterOp.isArrayType expected))
      || (CppInterOp.isArrayType exprType && CppInterOp.isArrayType expected
          && getArrayElementType exprType == getArrayElementType expected) then .none
    else if (CppInterOp.isPointerType exprType || CppInterOp.isArrayType exprType)
         && (CppInterOp.isPointerType expected || CppInterOp.isArrayType expected) then
      let ep := getPointeeType exprType
      let xp := getPointeeType expected
      if CppInterOp.isVoid ep || CppInterOp.isVoid xp then .none
      else match determineImplicitConversion p x n ep xp with
        | .none => .none
        | _ => .unknown
    else if isConstructible p x expected exprType then .cast
    else .unknown

/-! ## processor.cpp: the DSL (`analyze_cpp_dsl_impl`, 5003-5735) -/

/-- A DSL form: `cpp/name` (or a bare symbol), a keyword form `(:kw a b ...)`, a vector of
forms, an integer, a boolean. -/
inductive TForm where
  | sym (name : String)
  | kw (k : String) (args : List TForm)
  | vec (items : List TForm)
  | int (i : Int)
  | bool (b : Bool)
  | app (head : String) (args : List TForm)
  deriving Repr, Inhabited

partial def TForm.text : TForm → String
  | .sym n => n
  | .kw k as => "(:" ++ k ++ String.join (as.map (" " ++ ·.text)) ++ ")"
  | .vec as => "[" ++ " ".intercalate (as.map (·.text)) ++ "]"
  | .int i => toString i
  | .bool b => toString b
  | .app h as => "(" ++ h ++ String.join (as.map (" " ++ ·.text)) ++ ")"

/-- What `cpp/<name>` names in the analyzed program (`analyze_cpp_symbol` in type position:
`resolve_type`/`get_type` for builtins, else the scope's type). -/
def baseTypeOf (x : XWorld) (n : String) : Option CType :=
  let n := if n.startsWith "cpp/" then (n.drop 4).toString else n
  let builtins : List (String × Builtin) :=
    [("void", .void), ("bool", .bool), ("char", .char), ("wchar_t", .wchar), ("char8_t", .char8),
     ("char16_t", .char16), ("char32_t", .char32), ("short", .short), ("int", .int),
     ("long", .long), ("float", .float), ("double", .double)]
  match builtins.lookup n with
  | some k => some (.b k)
  | none =>
    if n == "size_t" then some sizeT
    else if n == "int8_t" then some (.alias "int8_t" (.b .schar))
    else match x.findClass n with
      | some c => some (.record c.name)
      | none => match x.findEnum n with
        | some e => some (.enum e.name)
        | none => none

/-- The four integer modifiers (processor.cpp:5130-5238): `is_integral` first; `:short` also
rejects plain `char` (`get_type_without_cv(type) == char_type`) and an already-short type;
`:long` accepts `double`, rejects plain `char` and short types. -/
def modify (p : Platform) (k : String) (t : CType) : Except String CType :=
  let noCv := (getTypeWithoutCv t).canonical
  match k with
  | "signed" => if !CppInterOp.isIntegral t then .error "Only integral types can be signed." else .ok (getSignedType p t)
  | "unsigned" => if !CppInterOp.isIntegral t then .error "Only integral types can be unsigned." else .ok (getUnsignedType p t)
  | "short" =>
    if !CppInterOp.isIntegral t || noCv == .b .char then .error "Only integer types can be short."
    else if isShortType t then .error "This type is already short."
    else .ok (getShortType p t)
  | "long" =>
    if (!CppInterOp.isIntegral t || noCv == .b .char) && noCv != .b .double then
      .error "Only integer types and double can be long."
    else if isShortType t then .error "This type is already short, so it cannot be made long."
    else .ok (getLongType p t)
  | "const" => if CppInterOp.isReferenceType t then .error "C++ does not allow const references." else .ok (getTypeWithConst t)
  | "*" => if CppInterOp.isReferenceType t then .error "C++ does not allow pointers to references." else .ok (getPointerType t)
  | "&" => if CppInterOp.isVoid t then .error "C++ does not allow references to void." else .ok (getLvalueReferenceType t)
  | _ => .error s!"Invalid C++ type modifier `:{k}`."

/-- A member-form result: a type, or a value of a type (with the declaration it names). -/
inductive DslOut where
  | type (t : CType)
  | value (t : CType) (d : Decl)
  deriving Repr, Inhabited

/-- `analyze_type` restricted to the forms the round-3 worlds draw. -/
partial def analyzeType (p : Platform) (x : XWorld) : TForm → Except String CType
  | .sym n => match baseTypeOf x n with
    | some t => .ok t
    | none => .error s!"Unable to find `{n}`."
  | .kw "fn" [r, .vec ps] => do
    let rt ← analyzeType p x r
    let pts ← ps.mapM (analyzeType p x)
    if pts.any CppInterOp.isVoid then .error "Function parameter types may not be void."
    else .ok (.fn rt pts)
  | .kw "fn" _ => .error "A sequence of parameter types was expected."
  | .kw k [a] => do modify p k (← analyzeType p x a)
  | .kw "member*" [t, m] => do
    match ← memberForm p x "member*" t m with
    | .type ty => .ok ty
    | .value .. => .error "A type was expected here."
  | .kw "member" [t, m] => do
    match ← memberForm p x "member" t m with
    | .type ty => .ok ty
    | .value .. => .error "A type was expected here."
  | f => .error s!"Invalid C++ type `{f.text}`."
where
  /-- processor.cpp:5372-5560: `(:member t name)`, `(:member* t name)`, `(:&member t name)`. -/
  memberForm (p : Platform) (x : XWorld) (kw : String) (t m : TForm) : Except String DslOut := do
    let .sym name := m | .error "Member names need to be symbols."
    let type ← analyzeType p x t
    let some (.class_ c) := getScopeFromType x type
      | .error s!"There is no `{name}` member within `{reprStr type}`."
    let some ms := getNamedInClass x c.name name
      | .error s!"There is no `{name}` member within `{c.name}`."
    if kw == "member" then
      let isTypeDecl := match ms with | .class_ _ | .enum_ _ | .typedef_ .. => true | _ => false
      if isPrivateVariable (some ms) || isProtectedVariable (some ms) then
        .error "This member is declared private or protected, so it cannot be accessed."
      else if isTypeDecl then .ok (.type (getTypeFromScope (some ms)))
      else
        let mt := getTypeFromScope (some ms)
        match ms with
        | .variable .. => .ok (.value (if CppInterOp.isPointerType mt then mt else getLvalueReferenceType mt) ms)
        | .enumConstant .. => .ok (.value (getNonReferenceType mt) ms)
        | .function _ => .ok (.value mt ms)
        | _ => .error "A C++ value was expected here."
    else
      let isMethod := match ms with | .function f => f.isMethod | _ => false
      let isStatic := match ms with | .function f => f.isMethod && f.isStatic | _ => false
      if !isNonStaticVariable (some ms) && !isMethod then
        .error s!"A member variable or function was expected here, but '{c.name}::{name}' was found."
      else if isStatic then .error s!"A non-static member was expected here, but '{c.name}::{name}' is static."
      else
        -- CppInterOp.cpp:3029 `GetPointerToMemberType`: the member's type, in its declaring class
        let (owner, mty) : String × CType := match ms with
          | .field o f => (o, f.type)
          | .function f => (f.owner, if f.isConst then .cv true false (.fn f.ret f.params) else .fn f.ret f.params)
          | _ => (c.name, .null)
        let pm := CType.memPtr owner mty
        if kw == "member*" then .ok (.type pm) else .ok (.value pm ms)

/-! ## processor.cpp:874 `build_indirect_cpp_call` (function pointers and pointers to members) -/

/-- The analysis of `(f a1 ... an)` where `f` has the non-reference type `sourceType0` (a function
pointer or a pointer to member) and the arguments have `argTypes`. `ok` with the call's return
type, or the error message. -/
def indirectCall (p : Platform) (x : XWorld) (sourceType0 : CType) (argTypes : List CType) :
    Except String CType := do
  let mut sourceType := getNonReferenceType sourceType0
  if isPointerToMemberType sourceType then
    let parent := match view sourceType with | .memPtr c _ => CType.record c | _ => .null
    let some argType := argTypes.head?
      | .error "Invalid pointer to member invocation. An argument is required."
    let objType := getCanonicalType (getTypeWithoutCv (baseType argType))
    if getCanonicalType parent != objType && !derivedFrom x objType parent then
      .error "Invalid pointer to member invocation. The pointer to member is for another type."
    else if isPointerToMemberFunctionType sourceType && CppInterOp.isConstType (baseType argType)
        && !(match view sourceType with | .memPtr _ f => isConstQualified f | _ => false) then
      .error "Invalid pointer to member invocation. The object is const, the member function is not."
    sourceType := getFunctionTypeFromPointerToMember sourceType argType
  else if !CppInterOp.isFunctionPointerType sourceType then
    .error "There is no call operator for this type (functors are not searched here)."
  let paramCount := getFunctionNumArgsFromType sourceType
  if paramCount != argTypes.length then
    .error s!"Unable to call function with {argTypes.length} arguments since it expects {paramCount} arguments instead."
  for (a, i) in argTypes.zipIdx do
    let prm := getFunctionArgTypeFromType sourceType i
    if !isImplicitlyConvertible p x a prm then
      .error s!"Unable to call function since argument {i} is not convertible from `{Jank.Interop.CppInterop.getTypeAsString a}` to `{Jank.Interop.CppInterop.getTypeAsString prm}`."
  match view sourceType with
  | .fn r _ => .ok r
  | .ptr u => match view u with | .fn r _ => .ok r | _ => .ok .null
  | _ => .ok .null

/-! ## processor.cpp:367-505: operator calls whose first operand is not primitive -/

/-- `(cpp/<op> a b)` on non-object class operands: `GetOperator` finds the declared operator
functions (the model's classes declare none, CXA10), then only `!`, `&&`, `||` fall back to
contextual conversion to `bool`; no built-in candidate is ever added. `ok` with the result type
(or the error). -/
def classOperatorCall (p : Platform) (x : XWorld) (op : Cxx.Op) (argTypes : List CType) :
    Except String CType :=
  let objType := getNonReferenceType (argTypes.headD .null)
  if isPrimitive objType then
    if argTypes.length == 1 || isPrimitive (getNonReferenceType (argTypes.getD 1 .null)) then
      let t := getBuiltinOperatorType p x op argTypes
      if t.isNull then .error "The operator is not supported for these types." else .ok t
    else .error "(not searched: primitive op object)"
  else
    let fns : List FnDecl := []
    let isLogical := op == .exclaim || op == .ampAmp || op == .pipePipe
    if fns.isEmpty && isLogical then
      let convertible := argTypes.all fun a =>
        isPrimitive (getNonReferenceType a) || CppInterOp.isConstructible p x (.b .bool) a
      if convertible then
        let t := getBuiltinOperatorType p x op (argTypes.map fun a => if isPrimitive (getNonReferenceType a) then a else .b .bool)
        if t.isNull then .error "The operator is not supported for these types." else .ok t
      else .error "The operator is not supported for the type."
    else .error "The operator is not supported for the type."

/-! ## processor.cpp:4730 `analyze_cpp_member_access` (`(cpp/.-name obj)`) -/

/-- `ok` with the member's type, or the error. -/
def memberAccess (x : XWorld) (name : String) (objType : CType) : Except String CType :=
  let parentType := getNonReferenceType objType
  let parentScope := getScopeFromType x parentType
  let member := lookupDatamember x name parentScope
  if parentScope.isNone then .error "Unable to find any members."
  else if member.isSome && isPrivateVariable member then .error s!"The `{name}` member is private."
  else if member.isSome && isProtectedVariable member then .error s!"The `{name}` member is protected."
  else match member with
    | some m => .ok (getLvalueReferenceType (getTypeFromScope m))
    | none =>
      match (getStaticDatamembers x parentScope).find? (fun d => match d with
          | .variable n _ _ _ => n.endsWith ("::" ++ name) | _ => false) with
      | some d => .ok (getLvalueReferenceType (getTypeFromScope (some d)))
      | none => .error s!"There is no `{name}` member within the class."

/-! ## processor.cpp:4395 `analyze_cpp_unsafe_cast` -/

/-- `ok` true for a constructor-style conversion, false for a C-style cast, or the error. -/
def unsafeCast (p : Platform) (x : XWorld) (type valueType : CType) : Except String Bool :=
  let isNullptr := getCanonicalType valueType == .b .nullptr
  let nullptrToArray := isNullptr && CppInterOp.isArrayType type
  let castType := if nullptrToArray then getPointerType (getArrayElementType type) else type
  if getCanonicalType castType == getCanonicalType valueType then .ok true
  else if isConstructible p x castType valueType then .ok true
  else if nullptrToArray || CppInterOp.isCStyleConvertible p x valueType castType then .ok false
  else .error "Invalid unsafe-cast."

/-! ## processor.cpp:3027-3120 `analyze_try`: catch types -/

/-- The handler type jank declares for `(catch T e ...)` (`catch({T'} e)` in the C++,
cpp_processor.cpp:1117): `void` rejected; anything but a pointer becomes an lvalue reference. -/
def catchType (t : CType) : Except String CType :=
  if CppInterOp.isVoid (getNonReferenceType t) then .error "Void is not a valid exception type to catch."
  else if !CppInterOp.isPointerType t then .ok (getLvalueReferenceType t)
  else .ok t

end Jank.R3.Interop.Paths
