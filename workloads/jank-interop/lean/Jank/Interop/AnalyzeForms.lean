import Jank.Interop.Analyze

/-!
# The interop special forms and the analysis that reaches them (processor.cpp)

`analyze_cpp_call`, `analyze_cpp_raw`, `analyze_cpp_type`, `analyze_cpp_cast`,
`analyze_cpp_unsafe_cast`, `analyze_cpp_box`, `analyze_cpp_unbox`, `analyze_cpp_new`,
`analyze_cpp_delete`, `analyze_cpp_member_access`, and the interop parts of `analyze`,
`analyze_symbol`, `analyze_call`, `analyze_if`, `analyze_let`, `analyze_loop`, `analyze_recur` and
`analyze_fn_arity`, mutually recursive as in the C++.
-/

namespace Jank.Interop.Analyze

open Jank.Analyzer (Obj ExprPosition ExprKind CppValueKind ConversionPolicy LoopKind)
open CppInterop (Scope)
open CppUtil

def listOf? : Obj → Option (List Obj)
  | .persistentList _ xs => some xs
  | _ => none

mutual

/-- processor.cpp:analyze:4850 (dispatch on the form's type). Vector, map and set literals are
taken as boxed literals (their `analyze_vector` etc. are the analyzer agent's). -/
partial def analyze (c : Ctx) (o : Obj) (pos : ExprPosition) (needsBox : Bool) : AR :=
  match o with
  | .persistentList _ xs => analyzeCall c o xs pos needsBox
  | .symbol _ ns n => analyzeSymbol c ns n pos needsBox
  | .persistentVector .. | .persistentHashMap .. | .persistentHashSet .. | .persistentArrayMap .. =>
    .ok (.mk pos needsBox o (.primitiveLiteral o))
  | _ => .ok (analyzePrimitiveLiteral o pos needsBox c.w)

/-- processor.cpp:analyze_symbol:1583: `cpp/` symbols (not `cpp/raw`) and `.member` symbols go to
`analyze_cpp_symbol`; then locals; then vars (`object_ref`). -/
partial def analyzeSymbol (c : Ctx) (ns name : String) (pos : ExprPosition) (needsBox : Bool) : AR := do
  if (ns == "cpp" && name != "raw") || (ns.isEmpty && name.startsWith ".") then
    return ← analyzeCppSymbol c name pos needsBox
  match c.locals.lookup name with
  | some (b, v) => return .mk pos (needsBox || b.needsBox) (Obj.s name) (.localReference b v)
  | none =>
    if jankFns.contains name || (inlines.map (·.1)).contains name then
      return .mk pos true (Obj.s name) (.varDeref name)
    aerr "analyze/unresolved-symbol" s!"The symbol `{name}` could not be resolved."

/-- processor.cpp:analyze_call:3421, the paths a C++ value or type in call position takes, the
`:inline` expansion of clojure.core's arithmetic (3543-3566), and the boxing of a jank call's
arguments (3628). -/
partial def analyzeCall (c : Ctx) (o : Obj) (xs : List Obj) (pos : ExprPosition) (needsBox : Bool) : AR := do
  match xs with
  | [] => return analyzePrimitiveLiteral o pos needsBox c.w
  | first :: args =>
  match first with
  | .symbol _ ns n =>
    let key := if ns.isEmpty then n else ns ++ "/" ++ n
    -- specials
    if key == "cpp/raw" then return ← analyzeCppRaw c o args pos needsBox
    if key == "cpp/cast" then return ← analyzeCppCast c o args pos needsBox
    if key == "cpp/unsafe-cast" then return ← analyzeCppUnsafeCast c o args pos needsBox
    if key == "cpp/box" then return ← analyzeCppBox c o args pos needsBox
    if key == "cpp/unbox" then return ← analyzeCppUnbox c o args pos needsBox
    if key == "cpp/new" then return ← analyzeCppNew c o args pos needsBox
    if key == "cpp/delete" then return ← analyzeCppDelete c o args pos needsBox
    if key == "cpp/dsl" then return ← analyzeCppDsl c o pos
    if key == "let*" || key == "let" then return ← analyzeLet c o args pos needsBox false
    if key == "loop*" || key == "loop" then return ← analyzeLoop c o args pos
    if key == "if" then return ← analyzeIf c o args pos
    if key == "recur" then return ← analyzeRecur c o args pos
    let source ← analyzeSymbol c ns n .call true
    if source.kind == .cppType then
      let .cppType _ t := source.data | .error (.unmodeled "")
      let value := mkCppValue pos needsBox o n t (CppInterop.getScopeFromType c.w t) .constructor
      return ← analyzeCppCall c o value pos needsBox
    if source.kind.isCpp || !isAnyObject c.w (expressionType source) then
      return ← analyzeCppCall c o source pos needsBox
    -- :inline metadata (clojure.core arithmetic)
    if source.kind == .varDeref then
      match inlines.find? (·.1 == n) with
      | some (_, target, swap, arity) =>
        if arity.isNone || arity == some args.length then
          let args' := if swap then args.reverse else args
          return ← analyze c (.persistentList none (Obj.sym "cpp" target :: args')) pos needsBox
      | none => pure ()
    let mut argExprs := []
    for a in args do
      let e ← analyze c a .value true
      argExprs := argExprs ++ [← applyImplicitConversion c e (expressionType e) untypedObjectRefType]
    return .mk pos true o (.call n argExprs)
  | _ =>
    let source ← analyze c first .call needsBox
    if source.kind == .cppType then
      let .cppType s t := source.data | .error (.unmodeled "")
      let value := mkCppValue pos needsBox o s t (CppInterop.getScopeFromType c.w t) .constructor
      return ← analyzeCppCall c o value pos needsBox
    if !isAnyObject c.w (expressionType source) then
      return ← analyzeCppCall c o source pos needsBox
    .error (.unmodeled "dynamic call of a non-symbol")

/-- processor.cpp:analyze_cpp_call:4054. `o` is the call's list; its rest are the arguments. -/
partial def analyzeCppCall (c : Ctx) (o : Obj) (source : IExpr) (pos : ExprPosition) (needsBox : Bool) : AR := do
  if let .cppValue _ _ _ .memberAccess := source.data then
    return ← analyzeCppMemberAccess c o source pos needsBox
  let args := (listOf? o |>.getD []).drop 1
  let mut argExprs := []
  let mut argTypes := []
  let mut argScopes := []
  for a in args do
    let e ← analyze c a .value true
    argExprs := argExprs ++ [e]
    argTypes := argTypes ++ [expressionType e]
    argScopes := argScopes ++ [expressionScope e]
  let directCall : Bool := match source.data with
    | .cppValue _ _ _ k => k != .variable
    | _ => false
  if directCall then
    let sourceType := expressionType source
    if !sourceType.isNull && CppInterop.isPointerToMemberType sourceType then
      return ← buildIndirectCppCall c o source argExprs argTypes argScopes pos needsBox
    return ← buildCppCall c source argExprs argTypes argScopes pos needsBox o
  else buildIndirectCppCall c o source argExprs argTypes argScopes pos needsBox

/-- processor.cpp:analyze_cpp_raw:4135: exactly one string literal; wrapped in a unique include
guard (by `std::hash` of the code) and a `#line`. -/
partial def analyzeCppRaw (c : Ctx) (l : Obj) (args : List Obj) (pos : ExprPosition) (needsBox : Bool) : AR := do
  match args with
  | [] => aerr "analyze/invalid-cpp-raw" "This call to 'cpp/raw' is missing the value string literal of C++ code."
  | [s] =>
    let e ← analyze c s .value false
    match e.data with
    | .cppLiteral (.persistentString code) =>
      let guardName := s!"JANK_CPP_RAW_{hash code}"
      return mkCppRaw pos needsBox l s!"#ifndef {guardName}\n#define {guardName}\n\n\n{code}\n#endif\n"
    | _ => aerr "analyze/invalid-cpp-raw" "The first and only argument to 'cpp/raw' must be a string of C++ code."
  | _ => aerr "analyze/invalid-cpp-raw" "A call to 'cpp/raw' must take a string literal of C++ code and nothing else."

/-- processor.cpp:analyze_cpp_type:4212. -/
partial def analyzeCppTypeForm (c : Ctx) (l : Obj) (args : List Obj) : AR := do
  if args.length != 1 then
    return ← aerr "analyze/invalid-cpp-type" s!"Exactly 1 argument is expected for 'cpp/type', but {args.length} were provided."
  let t ← analyzeType c l
  return mkCppType .type true "cpp/type" t

/-- processor.cpp:analyze_cpp_cast:4241. -/
partial def analyzeCppCast (c : Ctx) (l : Obj) (args : List Obj) (pos : ExprPosition) (needsBox : Bool) : AR := do
  match args with
  | [] => aerr "analyze/invalid-cpp-cast" "This call to 'cpp/cast' is missing a C++ type and a value as arguments."
  | [_] => aerr "analyze/invalid-cpp-cast" "This call to 'cpp/cast' is missing a value to cast as an argument."
  | [typeObj, valueObj] =>
    let type ← analyzeType c typeObj
    let valueExpr ← analyze c valueObj .value false
    let valueType := expressionType valueExpr
    let nullptrToArray := isNullptr valueType && CppInterop.isArrayType type
    let castType := if nullptrToArray then CppInterop.getPointerType (CppInterop.getArrayElementType type) else type
    if castType.canonical == valueType.canonical then return valueExpr
    else if nullptrToArray || isConstructible c.p c.w castType valueType ||
            CppInterop.isImplicitlyConvertible c.p c.w valueType castType ||
            isPointerToVoidConversion valueType castType then
      let v := mkCppValue pos needsBox l "cpp/cast" castType (CppInterop.getScopeFromType c.w castType) .constructor
      return ← analyzeCppCall c (.persistentList none [.nil, valueObj]) v pos needsBox
    if (isTypedObjectRef c.w type && isUntypedObject valueType) ||
       (isAnyObject c.w valueType && isTraitConvertible c.w type) then
      return mkCppConversion pos needsBox l type type .fromObject valueExpr
    if isAnyObject c.w type && isTraitConvertible c.w valueType then
      return mkCppConversion pos needsBox l type valueType .intoObject valueExpr
    aerr "analyze/invalid-cpp-cast"
      s!"Invalid cast from `{getQualifiedTypeName c.w valueType}` to `{getQualifiedTypeName c.w type}`. This is impossible considering both constructors and any specializations of 'jank::runtime::convert'."
  | _ => aerr "analyze/invalid-cpp-cast" "A call to 'cpp/cast' must only have a C++ type and a value as arguments and nothing else."

/-- processor.cpp:analyze_cpp_unsafe_cast:4363. -/
partial def analyzeCppUnsafeCast (c : Ctx) (l : Obj) (args : List Obj) (pos : ExprPosition) (needsBox : Bool) : AR := do
  match args with
  | [] => aerr "analyze/invalid-cpp-unsafe-cast" "This call to 'cpp/unsafe-cast' is missing its C++ type and value arguments."
  | [_] => aerr "analyze/invalid-cpp-unsafe-cast" "This call to 'cpp/unsafe-cast' is missing its value argument."
  | [typeObj, valueObj] =>
    let type ← analyzeType c typeObj
    let valueExpr ← analyze c valueObj .value false
    let valueType := expressionType valueExpr
    let nullptrToArray := isNullptr valueType && CppInterop.isArrayType type
    let castType := if nullptrToArray then CppInterop.getPointerType (CppInterop.getArrayElementType type) else type
    if castType.canonical == valueType.canonical then return valueExpr
    else if isConstructible c.p c.w castType valueType then
      let v := mkCppValue pos needsBox (Obj.s "cpp/unsafe-cast") "cpp/unsafe-cast" castType (CppInterop.getScopeFromType c.w castType) .constructor
      return ← analyzeCppCall c (.persistentList none [.nil, valueObj]) v pos needsBox
    else if nullptrToArray || CppInterop.isCStyleConvertible c.p c.w valueType castType then
      return mkCppUnsafeCast pos needsBox l castType valueExpr
    aerr "analyze/invalid-cpp-unsafe-cast"
      s!"Invalid unsafe-cast from `{getQualifiedTypeName c.w valueType}` to `{getQualifiedTypeName c.w type}`."
  | _ => aerr "analyze/invalid-cpp-unsafe-cast" "A call to 'cpp/unsafe-cast' must only have a C++ type and a value as arguments and nothing else."

/-- processor.cpp:analyze_cpp_box:4466: a raw pointer that is not a jank object. -/
partial def analyzeCppBox (c : Ctx) (l : Obj) (args : List Obj) (pos : ExprPosition) (needsBox : Bool) : AR := do
  match args with
  | [] => aerr "analyze/invalid-cpp-box" "This call to 'cpp/box' is missing a C++ pointer value."
  | [valueObj] =>
    let valueExpr ← analyze c valueObj .value false
    let valueType := CppInterop.getNonReferenceType (expressionType valueExpr)
    if !CppInterop.isPointerType valueType then
      return ← aerr "analyze/invalid-cpp-box"
        s!"Unable to create an opaque box from `{getQualifiedTypeName c.w valueType}`, since it's not a raw pointer type."
    else if isAnyObject c.w valueType then
      return ← aerr "analyze/invalid-cpp-box"
        s!"Unable to create an opaque box from `{getQualifiedTypeName c.w valueType}`, since it's already a boxed jank object."
    return mkCppBox pos needsBox l valueExpr
  | _ => aerr "analyze/invalid-cpp-box" "A call to 'cpp/box' must only have a C++ pointer value as argument and nothing else."

/-- processor.cpp:analyze_cpp_unbox:4535: a raw pointer type, and a jank object. -/
partial def analyzeCppUnbox (c : Ctx) (l : Obj) (args : List Obj) (pos : ExprPosition) (needsBox : Bool) : AR := do
  match args with
  | [] => aerr "analyze/invalid-cpp-unbox" "This call to 'cpp/unbox' is missing a C++ type and a value as arguments."
  | [_] => aerr "analyze/invalid-cpp-unbox" "This call to 'cpp/unbox' is missing a value to unbox as an argument."
  | [typeObj, valueObj] =>
    let type ← analyzeType c typeObj
    let valueExpr ← analyze c valueObj .value false
    if !CppInterop.isPointerType type then
      return ← aerr "analyze/invalid-cpp-unbox"
        s!"Unable to unbox to `{getQualifiedTypeName c.w type}`, since it's not a raw pointer type."
    let valueType := expressionType valueExpr
    if !isAnyObject c.w valueType then
      return ← aerr "analyze/invalid-cpp-unbox"
        s!"Unable to unbox value of type `{getQualifiedTypeName c.w valueType}`, since it's not a jank object type."
    return mkCppUnbox pos needsBox l type valueExpr
  | _ => aerr "analyze/invalid-cpp-unbox" "A call to 'cpp/unbox' must only have a C++ type and a value as arguments and nothing else."

/-- processor.cpp:analyze_cpp_new:4620: a constructor call of the type, wrapped. -/
partial def analyzeCppNew (c : Ctx) (l : Obj) (args : List Obj) (pos : ExprPosition) (needsBox : Bool) : AR := do
  match args with
  | [] => aerr "analyze/invalid-cpp-new" "The `cpp/new` form is missing the type to allocate."
  | typeObj :: ctorArgs =>
    let type ← analyzeType c typeObj
    let v := mkCppValue pos needsBox (Obj.s "cpp/new") "cpp/new" type (CppInterop.getScopeFromType c.w type) .constructor
    let valueExpr ← analyzeCppCall c (.persistentList none (typeObj :: ctorArgs)) v pos false
    return mkCppNew pos needsBox l type valueExpr

/-- processor.cpp:analyze_cpp_delete:4675: a raw pointer. -/
partial def analyzeCppDelete (c : Ctx) (l : Obj) (args : List Obj) (pos : ExprPosition) (needsBox : Bool) : AR := do
  match args with
  | [] => aerr "analyze/invalid-cpp-delete" "The `cpp/delete` form is missing the value to delete."
  | [valueObj] =>
    let valueExpr ← analyze c valueObj .value false
    let valueType := expressionType valueExpr
    if !CppInterop.isPointerType valueType then
      return ← aerr "analyze/invalid-cpp-delete"
        s!"The value `{getQualifiedTypeName c.w valueType}` cannot be deleted because it is not a raw pointer type."
    return mkCppDelete pos needsBox l valueExpr
  | _ => aerr "analyze/invalid-cpp-delete" "The `cpp/delete` form may only take one argument, which is the value to delete."

/-- processor.cpp:analyze_cpp_member_access:4724: `(.-name obj)`. -/
partial def analyzeCppMemberAccess (c : Ctx) (l : Obj) (val : IExpr) (pos : ExprPosition) (needsBox : Bool) : AR := do
  let name := ((valSym val).drop 2).toString
  let args := (listOf? l |>.getD []).drop 1
  match args with
  | [] => aerr "analyze/invalid-cpp-member-access" s!"Missing value from which to access `{name}` member."
  | [objForm] =>
    let objExpr ← analyze c objForm .value false
    let parentType := CppInterop.getNonReferenceType (expressionType objExpr)
    let parentScope := CppInterop.getScopeFromType c.w parentType
    let memberScope := CppInterop.lookupDatamember name parentScope
    if parentScope.isNone then
      return ← aerr "analyze/invalid-cpp-member-access" s!"Unable to find any members within `{getQualifiedTypeName c.w parentType}`."
    match memberScope with
    | some m =>
      if CppInterop.isPrivateVariable m then
        return ← aerr "analyze/invalid-cpp-member-access" s!"The `{name}` member within `{getQualifiedName parentScope}` is private. It can only be accessed if it's public."
      if CppInterop.isProtectedVariable m then
        return ← aerr "analyze/invalid-cpp-member-access" s!"The `{name}` member within `{getQualifiedName parentScope}` is protected. It can only be accessed if it's public."
      let memberType := CppInterop.getLvalueReferenceType m.type
      return mkCppMemberAccess pos needsBox l memberType m name objExpr
    | none =>
      match (CppInterop.getStaticDatamembers parentScope).find? (·.name == name) with
      | none => aerr "analyze/invalid-cpp-member-access" s!"There is no `{name}` member within `{getQualifiedName parentScope}`."
      | some m =>
        return val.withData (.cppValue (valSym val) (CppInterop.getLvalueReferenceType m.type)
          (some (.field (getQualifiedName parentScope) m)) .variable)
  | _ => aerr "analyze/invalid-cpp-member-access" s!"Excess arguments provided for `{name}` member access. Only one is expected."

/-- processor.cpp:analyze_if:2644, the native-type handling: a condition that is neither an object
nor `bool` is boxed when it is a builtin ("Clojure treats 0 and 0.0 as true"), else converted to
`bool`; the branches' types reconciled. -/
partial def analyzeIf (c : Ctx) (o : Obj) (args : List Obj) (pos : ExprPosition) : AR := do
  let needsBox := true
  if args.length < 2 then return ← aerr "analyze/invalid-if" "Each `if` form requires a condition and a `then` form."
  if args.length > 3 then return ← aerr "analyze/invalid-if" "An extra form specified in this 'if'."
  let condition ← analyze c (args.headD .nil) .value false
  let conditionType := getType condition
  let mut cond := condition
  if !isAnyObject c.w conditionType && !isBool conditionType then
    if CppInterop.isBuiltin conditionType then
      cond ← applyImplicitConversion c condition conditionType untypedObjectRefType
    else
      cond ← applyImplicitConversion c condition conditionType boolType
  let mut thenExpr ← analyze c (args.getD 1 .nil) pos needsBox
  let mut hasRecur := thenExpr.kind == .recur
  let mut elseOpt : Option IExpr := none
  if args.length == 3 then
    let e ← analyze c (args.getD 2 .nil) pos needsBox
    if e.kind == .recur then hasRecur := true
    elseOpt := some e
  -- 7135b7708 (processor.cpp:2740-2780): the branches' common type by
  -- `cpp_util::find_branch_common_type` (cpp_util.cpp:1907)
  match findBranchCommonType c.p c.w thenExpr elseOpt hasRecur with
  | .error msg => aerr "analyze/mismatched-if-types" msg
  | .ok bct =>
    if bct.thenNeedsConversion then
      thenExpr ← applyImplicitConversion c thenExpr (getType thenExpr) untypedObjectRefType
    if bct.elseNeedsConversion then
      if let some e := elseOpt then elseOpt := some (← applyImplicitConversion c e (getType e) untypedObjectRefType)
    return .mk pos needsBox o (.if_ bct.type cond thenExpr elseOpt)

/-- processor.cpp:analyze_let:2292, the binding types: a value keeps its native type; void becomes
nil; in a loop, `mutable_type` (typed objects and C strings erased, const dropped), boxed when it
became an object. -/
partial def analyzeLet (c : Ctx) (o : Obj) (args : List Obj) (pos : ExprPosition) (needsBox : Bool)
    (isLoop : Bool) : AR := do
  let some bindingForms := (match args.headD .nil with | .persistentVector _ xs => some xs | _ => none)
    | aerr "analyze/invalid-let" "The bindings for `let` must be in a vector."
  if bindingForms.length % 2 == 1 then
    return ← aerr "analyze/invalid-let" "The `let` bindings vector must contain an even number of entries."
  let mut ctx := c
  let mut pairs : List (Binding × IExpr) := []
  for i in List.range (bindingForms.length / 2) do
    let symObj := bindingForms.getD (2 * i) .nil
    let valObj := bindingForms.getD (2 * i + 1) .nil
    let .symbol _ "" name := symObj | return ← aerr "analyze/invalid-let" "The left-hand side of each `let` binding must be a symbol."
    -- 7135b7708 (processor.cpp:2364-2369): a `.member` symbol cannot be bound
    if name.startsWith "." then return ← aerr "analyze/invalid-cpp-position" name
    let mut valueExpr ← analyze ctx valObj .value false
    let mut exprType := getType valueExpr
    if CppInterop.isVoid exprType then
      valueExpr := mkCppConversion valueExpr.position valueExpr.needsBox valueExpr.form untypedObjectRefType exprType .intoObject valueExpr
      exprType := untypedObjectRefType
    if isLoop then
      let oldType := exprType
      exprType := mutableType c.w exprType
      if !isAnyObject c.w oldType && isAnyObject c.w exprType then
        valueExpr := mkCppConversion valueExpr.position valueExpr.needsBox valueExpr.form exprType oldType .intoObject valueExpr
    let b : Binding := { name, type := exprType, isLoopVariable := isLoop, needsBox := valueExpr.needsBox }
    ctx := { ctx with locals := (name, b, some valueExpr) :: ctx.locals }
    pairs := pairs ++ [(b, valueExpr)]
  if isLoop then ctx := { ctx with loop := some pairs }
  let body := args.drop 1
  let mut values := []
  for (form, i) in body.zipIdx do
    let isLast := i + 1 == body.length
    let e ← analyze ctx form (if isLast then pos else .statement) needsBox
    values := values ++ [e]
  if values.isEmpty then values := [analyzePrimitiveLiteral .nil pos needsBox c.w]
  return .mk pos needsBox o (.let_ pairs values (if isLoop then .loopWithRecur else .normal))

/-- processor.cpp:analyze_loop:2603: a let with `loop_details` set, analyzed in tail position. -/
partial def analyzeLoop (c : Ctx) (o : Obj) (args : List Obj) (pos : ExprPosition) : AR := do
  let e ← analyzeLet c o args .tail true true
  return e.propagatePosition pos

/-- processor.cpp:analyze_recur:2112, in a loop: each new value converted to `mutable_type` of the
binding's value type, after checking `(cpp/= binding value)` analyzes (or the type is trait
convertible). -/
partial def analyzeRecur (c : Ctx) (o : Obj) (args : List Obj) (pos : ExprPosition) : AR := do
  let some pairs := c.loop | .error (.unmodeled "recur outside a loop")
  if pos != .tail then return ← aerr "analyze/invalid-recur-position" "`recur` must be used in tail position."
  if pairs.length != args.length then
    return ← aerr "analyze/invalid-recur-args" s!"`recur` received {args.length} argument(s), but it requires exactly {pairs.length} here."
  let mut argExprs := []
  for (form, i) in args.zipIdx do
    let argExpr ← analyze c form .value true
    let (b, v) := pairs.getD i default
    let expected := mutableType c.w (getType v)
    let opEqual := analyzeCall c (.persistentList none [Obj.sym "cpp" "=", Obj.s b.name, form])
      [Obj.sym "cpp" "=", Obj.s b.name, form] .statement false
    if let .error e := opEqual then
      if !isTraitConvertible c.w expected then return ← .error e
    argExprs := argExprs ++ [← applyImplicitConversion c argExpr (getType argExpr) expected]
  return .mk pos true o (.recur argExprs)

end

/-- processor.cpp:analyze_fn_arity:1904: the body's last expression must be an object or trait
convertible, and is converted to `object_ref`. Parameters are `object_ref` locals. -/
def analyzeFnBody (c : Ctx) (params : List String) (body : Obj) : AR := do
  -- 7135b7708 (processor.cpp:1769-1774): a `.member` symbol cannot be a parameter
  if let some n := params.find? (·.startsWith ".") then return ← aerr "analyze/invalid-cpp-position" n
  let c := { c with locals := params.map (fun n => (n, { name := n, type := untypedObjectRefType }, none)) ++ c.locals }
  let e ← analyze c body .tail true
  let t := expressionType e
  if !isAnyObject c.w t && !isTraitConvertible c.w t then
    return ← aerr "analyze/invalid-cpp-conversion"
      s!"This function is returning a native object of type `{getQualifiedTypeName c.w t}`, which is not convertible to a jank runtime object."
  applyImplicitConversion c e t untypedObjectRefType

end Jank.Interop.Analyze
