import Jank.Interop.CppUtil

/-!
# The interop analysis of `src/cpp/jank/analyze/processor.cpp`, replicated

Every interop function of processor.cpp, one Lean definition each, with the C++ branching and
order (file:function:line cited): `build_builtin_operator_call`, `build_cpp_call`,
`build_indirect_cpp_call`, `resolved_expression`, both `apply_implicit_conversion` and both
`apply_implicit_conversions`, `analyze_primitive_literal`, `build_cpp_value`, `analyze_cpp_symbol`,
`analyze_cpp_call`, `analyze_cpp_raw`, `analyze_cpp_type`, `analyze_cpp_cast`,
`analyze_cpp_unsafe_cast`, `analyze_cpp_box`, `analyze_cpp_unbox`, `analyze_cpp_new`,
`analyze_cpp_delete`, `analyze_cpp_member_access`, `analyze_cpp_dsl`, `analyze_cpp_dsl_impl`,
`analyze_type`, `is_special` and the `specials` table's cpp entries.

The non-interop analyzer functions are the analyzer agent's. Their interop parts are replicated
here as far as the searched programs need them, and say so: `analyze` (dispatch, 4850),
`analyze_symbol` (cpp/ symbols and locals, 1583), `analyze_call` (cpp dispatch, `:inline`
expansion, argument boxing, 3421), `analyze_if` (native conditions and branch types, 2644),
`analyze_let` / `analyze_loop` (native bindings, loop typing, 2292 / 2603), `analyze_recur`
(conversion of the new values, 2112), `analyze_fn_arity`'s return conversion (1904).

Programs are `Obj` forms (Jank/Analyzer/Expr.lean). A jank diagnostic is
`Fault.analyzeError kind message`.
-/

namespace Jank.Interop.Analyze

open Jank.Analyzer (Obj ExprPosition ExprKind CppValueKind ConversionPolicy LoopKind)
open CppInterop (Scope)
open CppUtil

/-- The analyzer state the interop code reads. -/
structure Ctx where
  p : Platform := x86_64
  w : World := world0
  /-- Locals, latest first: the binding and (`resolved_expression`) its value expression. -/
  locals : List (String × Binding × Option IExpr) := []
  /-- `loop_details`: the enclosing `loop*`'s bindings and value expressions. -/
  loop : Option (List (Binding × IExpr)) := none
  deriving Inhabited

abbrev AR := Except Fault IExpr

def aerr {α : Type} (kind msg : String) : Except Fault α := .error (.analyzeError kind msg)

def symName : Obj → String
  | .symbol _ _ n => n
  | _ => ""

def symNs : Obj → String
  | .symbol _ ns _ => ns
  | _ => ""

/-- The `sym` of a `cpp_value` (its `form` member). -/
def valSym (e : IExpr) : String := match e.data with | .cppValue s .. => s | _ => ""

/-- clojure.core's `:inline` metadata for the arithmetic it inlines (core.jank 1371-1697):
symbol → the `cpp/` function and whether the arguments are swapped; `none` arity = any. -/
def inlines : List (String × String × Bool × Option Nat) :=
  [("+", "jank.runtime.add", false, some 2), ("-", "jank.runtime.sub", false, some 2),
   ("*", "jank.runtime.mul", false, some 2), ("/", "jank.runtime.div", false, some 2),
   ("<", "jank.runtime.lt", false, some 2), ("<=", "jank.runtime.lte", false, some 2),
   (">", "jank.runtime.lt", true, some 2), (">=", "jank.runtime.lte", true, some 2),
   ("inc", "jank.runtime.inc", false, none), ("dec", "jank.runtime.dec", false, none)]

/-- clojure.core functions the searched programs call without inlining (dynamic calls). -/
def jankFns : List String := ["identity", "str", "vector", "first", "println", "f"]

/-- processor.cpp:specials:1190, the `cpp/` entries (plus the special forms whose interop parts
are replicated). -/
def specials : List String :=
  ["def", "fn*", "recur", "do", "let*", "letfn*", "loop*", "if", "quote", "var", "throw", "try",
   "case*", "cpp/raw", "cpp/dsl", "cpp/cast", "cpp/unsafe-cast", "cpp/box", "cpp/unbox", "cpp/new",
   "cpp/delete"]

def symKey : Obj → String
  | .symbol _ ns n => if ns.isEmpty then n else ns ++ "/" ++ n
  | _ => ""

/-- processor.cpp:is_special:5778. -/
def isSpecial (form : Obj) : Bool :=
  match form with
  | .symbol _ ns n => (ns.isEmpty && (n == "finally" || n == "catch")) || specials.contains (symKey form)
  | _ => false

/-- processor.cpp:resolved_expression:1017: through local references to their value, stopping at
loop variables. -/
partial def resolvedExpression (e : IExpr) : IExpr :=
  match e.data with
  | .localReference b (some v) => if !b.isLoopVariable then resolvedExpression v else e
  | _ => e

/-- processor.cpp:analyze_primitive_literal:3233. -/
def analyzePrimitiveLiteral (o : Obj) (pos : ExprPosition) (needsBox : Bool) (w : World) : IExpr :=
  let type := literalType o false
  if isAnyObject w type then .mk pos needsBox o (.primitiveLiteral o)
  else mkCppLiteral pos needsBox o o

/-- processor.cpp:build_builtin_operator_call:196. -/
def buildBuiltinOperatorCall (c : Ctx) (val : IExpr) (op : Cxx.Op) (argExprs : List IExpr)
    (argTypes : List CType) (pos : ExprPosition) (needsBox : Bool) (form : Obj) : AR :=
  let opName := valSym val
  let queryArgTypes := argTypes.map fun t =>
    let nr := CppInterop.getNonReferenceType t
    if CppInterop.isArrayType nr then CppInterop.getPointerType (CppInterop.getArrayElementType nr) else t
  let type := CppInterop.getBuiltinOperatorType c.p c.w op queryArgTypes
  if type.isNull then
    if argTypes.length == 1 then
      aerr "analyze/invalid-cpp-operator-call"
        s!"The unary operator `{opName}` is not supported for the type `{getQualifiedTypeName c.w (argTypes.headD .null)}`."
    else
      aerr "analyze/invalid-cpp-operator-call"
        s!"The binary operator `{opName}` is not supported for the types `{getQualifiedTypeName c.w (argTypes.headD .null)}` and `{getQualifiedTypeName c.w (argTypes.getD 1 .null)}`."
  else .ok (mkCppBuiltinOperatorCall pos needsBox form op argExprs type)

def setAt {α : Type} (xs : List α) (i : Nat) (x : α) : List α := xs.set i x

mutual

/-- processor.cpp:apply_implicit_conversion:1031. -/
partial def applyImplicitConversion (c : Ctx) (expr : IExpr) (exprType expected : CType) : AR :=
  match determineImplicitConversion c.p c.w exprType expected with
  | .none => .ok expr
  | .intoObject =>
    let resolved := resolvedExpression expr
    match resolved.data with
    | .cppLiteral d =>
      applyImplicitConversion c (.mk expr.position expr.needsBox d (.primitiveLiteral d))
        (literalType d true) expected
    | _ =>
      let castPos := expr.position
      let e := expr.propagatePosition .value
      .ok (mkCppConversion castPos expr.needsBox expr.form expected exprType .intoObject e)
  | .fromObject =>
    let castPos := expr.position
    let e := expr.propagatePosition .value
    .ok (mkCppConversion castPos expr.needsBox expr.form (CppInterop.getNonReferenceType expected)
      expected .fromObject e)
  | .cast =>
    let castPos := expr.position
    let e := expr.propagatePosition .value
    let bare := CppInterop.getNonReferenceType (CppInterop.getTypeWithoutCv expected)
    let scope := CppInterop.getScopeFromType c.w bare
    let v := mkCppValue castPos false expr.form (CppInterop.getTypeAsString bare) bare scope .constructor
    buildCppCall c v [e] [exprType] [scope] castPos expr.needsBox expr.form false
  | .unknown =>
    aerr "analyze/invalid-cpp-conversion"
      s!"There is no implicit conversion from `{getQualifiedTypeName c.w exprType}` to `{getQualifiedTypeName c.w expected}`."

/-- processor.cpp:apply_implicit_conversions:1140 (parameter types). Variadic positions (a null
parameter type) keep the argument's type. -/
partial def applyImplicitConversionsTypes (c : Ctx) (paramTypes : List CType) (isNonStaticMember : Bool)
    (argExprs : List IExpr) (argTypes : List CType) : Except Fault (List IExpr) := do
  let off := if isNonStaticMember then 1 else 0
  let mut out := argExprs
  for i in List.range (argExprs.length - off) do
    let paramType := paramTypes.getD i .null
    let argType := argTypes.getD (i + off) .null
    let res ← applyImplicitConversion c (argExprs.getD (i + off) default) argType
      (if paramType.isNull then argType else paramType)
    out := setAt out (i + off) res
  return out

/-- processor.cpp:apply_implicit_conversions:1170 (a function's parameters). -/
partial def applyImplicitConversionsFn (c : Ctx) (fn : FnDecl) (argExprs : List IExpr)
    (argTypes : List CType) : Except Fault (List IExpr) :=
  let paramTypes := (List.range argExprs.length).map (CppInterop.getFunctionArgType fn)
  applyImplicitConversionsTypes c paramTypes (isNonStaticMemberFunction fn) argExprs argTypes

/-- The `cpp_call` / `cpp_member_call` / `cpp_constructor_call` a matched overload builds
(processor.cpp:655-695 and 710-750). -/
partial def buildMatched (c : Ctx) (val : IExpr) (isCtor isMemberCall : Bool) (m : FnDecl)
    (argExprs : List IExpr) (pos : ExprPosition) (needsBox : Bool) (form : Obj) : AR :=
  match val.data with
  | .cppValue sym valType _ _ =>
    if isCtor then .ok (mkCppConstructorCall pos needsBox form valType (some m) false argExprs)
    else if isMemberCall then
      .ok (mkCppMemberCall pos needsBox form (CppInterop.getFunctionReturnType m) m argExprs)
    else
      let returnType := CppInterop.getFunctionReturnType m
      let source := mkCppValue .value needsBox form sym (CppInterop.getTypeFromScope (some (.function m)))
        (some (.function m)) .function
      .ok (mkCppCall pos needsBox form returnType source argExprs)
  | _ => .error (.unmodeled "build_cpp_call on a non-cpp_value")

/-- processor.cpp:build_cpp_call:251. -/
partial def buildCppCall (c : Ctx) (val : IExpr) (argExprs0 : List IExpr) (argTypes0 : List CType)
    (argScopes : List Scope) (pos : ExprPosition) (needsBox : Bool) (form : Obj)
    (allowImplicitConversions : Bool := true) : AR := do
  let .cppValue sym valType valScope valKind := val.data | .error (.unmodeled "build_cpp_call")
  let mut argExprs := argExprs0
  let mut argTypes := argTypes0
  let mut fns : List FnDecl := []
  let isCtor := valKind == .constructor
  if isCtor && isPrimitive (CppInterop.getNonReferenceType valType) then
    if argTypes.length > 1 then
      return ← aerr "analyze/invalid-cpp-constructor-call"
        s!"The type `{getQualifiedTypeName c.w valType}` can only be constructed with one argument."
    if CppInterop.isVoid valType then
      return ← aerr "analyze/invalid-cpp-constructor-call" "A `void` instance cannot be constructed."
    if argTypes.length == 1 && !isConstructible c.p c.w valType (argTypes.headD .null) then
      let a0 := argTypes.headD .null
      if !(isTraitConvertible c.w valType && isAnyObject c.w a0) && !isPointerToVoidConversion a0 valType then
        return ← aerr "analyze/invalid-cpp-constructor-call"
          s!"The type `{getQualifiedTypeName c.w valType}` cannot be constructed from a value of type `{getQualifiedTypeName c.w a0}`."
      let conv ← applyImplicitConversion c (argExprs.headD default) a0 valType
      argExprs := setAt argExprs 0 conv
    return mkCppConstructorCall pos needsBox form valType none false argExprs
  let mut isMemberCall := valKind == .memberCall
  if isMemberCall then
    if argExprs.isEmpty then
      return ← aerr "analyze/invalid-cpp-member-call" "A member function call requires an invoking object."
    let objType := CppInterop.getNonReferenceType (argTypes.headD .null)
    let objScope := CppInterop.getScopeFromType c.w objType
    let memberName := (sym.drop 1).toString
    if objScope.isNone then
      return ← aerr "analyze/invalid-cpp-member-call"
        s!"There is no member function `{memberName}` on the type `{getQualifiedTypeName c.w objType}`."
    if !CppInterop.isReferenceType (argTypes.headD .null) then
      argTypes := setAt argTypes 0 (CppInterop.getLvalueReferenceType objType)
    fns := CppInterop.lookupMethods c.w memberName objScope
    if fns.isEmpty then
      return ← aerr "analyze/invalid-cpp-member-call"
        s!"There is no member function `{memberName}` on the type `{getQualifiedName objScope}`."
  let isOperatorCall := valKind == .operatorCall
  if isOperatorCall then
    let some op := matchOperator sym | .error (.unmodeled s!"operator {sym}")
    let argCount := argExprs.length
    if argCount == 0 then
      return ← aerr "analyze/invalid-cpp-operator-call" "An operator call requires an invoking object."
    -- 7135b7708 (processor.cpp:382): call operators take any number of arguments
    else if op != .call && argCount > 2 then
      return ← aerr "analyze/invalid-cpp-operator-call" "Operator calls may only take one or two arguments."
    let objType := CppInterop.getNonReferenceType (argTypes.headD .null)
    let isAddressof := op == .amp && argTypes.length == 1
    let alwaysUseBuiltin := isAddressof
    if alwaysUseBuiltin || isPrimitive objType then
      if alwaysUseBuiltin || (argTypes.length == 1 ||
          isPrimitive (CppInterop.getNonReferenceType (argTypes.getD 1 .null))) then
        return ← buildBuiltinOperatorCall c val op argExprs argTypes pos needsBox form
      else if !isAnyObject c.w objType && isTraitConvertible c.w objType &&
              isAnyObject c.w (CppInterop.getNonReferenceType (argTypes.getD 1 .null)) then
        let conv ← applyImplicitConversion c (argExprs.getD 1 default) (argTypes.getD 1 .null) objType
        argExprs := setAt argExprs 1 conv
        argTypes := setAt argTypes 1 objType
        return ← buildBuiltinOperatorCall c val op argExprs argTypes pos needsBox form
    else if argTypes.length == 2 && !isAnyObject c.w (argTypes.getD 1 .null) &&
            isTraitConvertible c.w (argTypes.getD 1 .null) &&
            isAnyObject c.w (CppInterop.getNonReferenceType objType) then
      let conv ← applyImplicitConversion c (argExprs.getD 1 default) (argTypes.getD 1 .null) objType
      argExprs := setAt argExprs 1 conv
      argTypes := setAt argTypes 1 objType
      return ← buildBuiltinOperatorCall c val op argExprs argTypes pos needsBox form
    fns := CppInterop.getOperator op argTypes (if argCount == 1 then 1 else 2)
    -- 7135b7708 (processor.cpp:464-511): `!`, `&&`, `||` with no overloaded operator contextually
    -- convert class operands constructible to `bool`, then use the builtin operator.
    let isLogicalOp := op == .exclaim || op == .ampAmp || op == .pipePipe
    if fns.isEmpty && isLogicalOp then
      let convertible := (List.range argExprs.length).all fun i =>
        let t := argTypes.getD i .null
        isPrimitive (CppInterop.getNonReferenceType t) || CppInterop.isConstructible c.p c.w boolType t
      if convertible then
        for i in List.range argExprs.length do
          if isPrimitive (CppInterop.getNonReferenceType (argTypes.getD i .null)) then continue
          let conv ← applyImplicitConversion c (argExprs.getD i default) (argTypes.getD i .null) boolType
          argExprs := setAt argExprs i conv
          argTypes := setAt argTypes i boolType
        return ← buildBuiltinOperatorCall c val op argExprs argTypes pos needsBox form
    if fns.isEmpty then
      return ← aerr "analyze/invalid-cpp-operator-call"
        s!"The operator `{sym}` is not supported for the type `{getQualifiedTypeName c.w objType}`."
  let mut scopeName := ""
  match valKind with
  | .null | .boolTrue | .boolFalse | .variable | .enumConstant | .memberAccess =>
    return ← aerr "analyze/invalid-cpp-call"
      s!"Values of type `{getQualifiedTypeName c.w (getType val)}` are not callable."
  | .constructor =>
    scopeName := CppInterop.getName valScope
    fns := CppInterop.lookupConstructors c.w "" valScope
  | .memberCall => scopeName := (sym.drop 1).toString
  | .operatorCall => scopeName := sym
  | .function =>
    scopeName := CppInterop.getName valScope
    fns := CppInterop.getFunctionsUsingName c.w (CppInterop.getParentScope valScope) scopeName
    if fns.isEmpty then
      return ← aerr "analyze/invalid-cpp-call" s!"There is no function named `{scopeName}`."
  argTypes := argTypes.map fun a =>
    if !CppInterop.isPointerType a && !CppInterop.isReferenceType a && !CppInterop.isBuiltin a then
      CppInterop.getLvalueReferenceType a else a
  match findBestOverload c.p c.w fns argTypes argScopes with
  | .error e => aerr "analyze/invalid-cpp-call" e
  | .ok (some m, argTypes') =>
    if isNonStaticMemberFunction m then isMemberCall := true
    if let .error e := instantiateIfNeeded c.w (some (.function m)) then
      return ← aerr "analyze/invalid-cpp-call" e
    -- The arg types could have changed during overload resolution: apply them to raw C++ values.
    argExprs := (argExprs.zip (List.range argExprs.length)).map fun (a, i) =>
      match a.data with
      | .cppValue s t sc k =>
        if t != CppInterop.getNonReferenceType (argTypes'.getD i .null) then
          a.withData (.cppValue s (argTypes'.getD i .null) sc k) else a
      | _ => a
    if allowImplicitConversions then
      argExprs ← applyImplicitConversionsFn c m argExprs argTypes'
    buildMatched c val isCtor isMemberCall m argExprs pos needsBox form
  | .ok (none, _) =>
    let mut newTypes ← match findBestArgTypesWithConversions c.p c.w fns argTypes isMemberCall with
      | .ok t => pure t
      | .error e => aerr "analyze/invalid-cpp-call" e
    -- 7135b7708 (processor.cpp:712-728): an operator call on a non-primitive also considers member
    -- operator functions (the invoking object first).
    if isOperatorCall && !isPrimitive (CppInterop.getNonReferenceType (argTypes.headD .null)) then
      newTypes ← match findBestArgTypesWithConversions c.p c.w fns argTypes true with
        | .ok t => pure t
        | .error e => aerr "analyze/invalid-cpp-call" e
    let emptyScopes := argScopes.map fun _ => (none : Scope)
    match findBestOverload c.p c.w fns newTypes emptyScopes with
    | .error e => aerr "analyze/invalid-cpp-call" e
    | .ok (some m, _) =>
      if isNonStaticMemberFunction m then isMemberCall := true
      -- 7135b7708 (processor.cpp:753): the conversion match is instantiated too
      if let .error e := instantiateIfNeeded c.w (some (.function m)) then
        return ← aerr "analyze/invalid-cpp-call" e
      argExprs ← applyImplicitConversionsFn c m argExprs argTypes
      buildMatched c val isCtor isMemberCall m argExprs pos needsBox form
    | .ok (none, _) =>
      if isCtor && !CppInterop.isComplete (CppInterop.getScopeFromType c.w valType) then
        return ← aerr "analyze/invalid-cpp-constructor-call"
          s!"Unable to construct incomplete type `{getQualifiedTypeName c.w valType}`. Are you missing an include?"
      if isCtor then
        let aggregateTypes := aggregateInitializationTypes c.w valScope
        let isAgg := match valScope with | some (.class_ k) => k.isAggregate | _ => false
        if isAgg || !aggregateTypes.isEmpty then
          if (findAggregateMatchWithConversions c.p c.w aggregateTypes argTypes).isSome then
            argExprs ← applyImplicitConversionsTypes c aggregateTypes false argExprs argTypes
            return mkCppConstructorCall pos needsBox form valType none true argExprs
      aerr "analyze/invalid-cpp-call"
        s!"No matching overload of the `{scopeName}` {if isCtor then "constructor" else "function"} was found for this call."

end

/-- processor.cpp:build_indirect_cpp_call:873: calls through member pointers, function pointers
and functors (`operator()`). -/
def buildIndirectCppCall (c : Ctx) (form : Obj) (source : IExpr) (argExprs : List IExpr)
    (argTypes : List CType) (argScopes : List Scope) (pos : ExprPosition) (needsBox : Bool) : AR := do
  let mut sourceType := CppInterop.getNonReferenceType (expressionType source)
  if CppInterop.isPointerToMemberType sourceType then
    let parentType := CppInterop.getParentTypeFromPointerToMember sourceType
    if argExprs.isEmpty then
      return ← aerr "analyze/invalid-cpp-call"
        s!"Invalid pointer to member invocation. An argument of type `{getQualifiedTypeName c.w parentType}` is required."
    let argType := expressionType (argExprs.headD default)
    let objType := CppInterop.getCanonicalType (CppInterop.getTypeWithoutCv (baseType argType))
    if CppInterop.getCanonicalType parentType != objType && !CppInterop.isTypeDerivedFrom c.w objType parentType then
      return ← aerr "analyze/invalid-cpp-call"
        s!"Invalid pointer to member invocation. The pointer to member is for type `{getQualifiedTypeName c.w parentType}`, but the object supplied is of type `{getQualifiedTypeName c.w argType}`."
    else if CppInterop.isPointerToMemberFunctionType sourceType && CppInterop.isConstType (baseType argType) &&
            !CppInterop.isFunctionTypeConst sourceType then
      return ← aerr "analyze/invalid-cpp-call"
        "Invalid pointer to member invocation. The object supplied is const, but the member function to call is non-const."
    sourceType := CppInterop.getFunctionTypeFromPointerToMember sourceType argType
  else if !CppInterop.isFunctionPointerType sourceType then
    let scope := CppInterop.getScopeFromType c.w sourceType
    if scope.isSome then
      let value := mkCppValue pos needsBox form "()" sourceType scope .operatorCall
      return ← buildCppCall c value (source :: argExprs) (sourceType :: argTypes) (scope :: argScopes) pos needsBox form
    return ← aerr "analyze/invalid-cpp-call"
      s!"There is no call operator for `{getQualifiedTypeName c.w sourceType}`."
  let paramCount := CppInterop.getFunctionNumArgsFromType sourceType
  if paramCount != argTypes.length then
    return ← aerr "analyze/invalid-cpp-call"
      s!"Unable to call function with {argTypes.length} arguments since it expects {paramCount} arguments instead."
  for i in List.range paramCount do
    let paramType := CppInterop.getFunctionArgTypeFromType sourceType i
    if !isImplicitlyConvertible c.p c.w (argTypes.getD i .null) paramType then
      return ← aerr "analyze/invalid-cpp-call"
        s!"Unable to call function since argument {i} is not convertible from `{getQualifiedTypeName c.w (argTypes.getD i .null)}` to `{getQualifiedTypeName c.w paramType}`."
  return mkCppCall pos needsBox form (CppInterop.getFunctionReturnTypeFromType sourceType) source argExprs

/-- processor.cpp:build_cpp_value:3700. -/
def buildCppValue (c : Ctx) (sym : String) (scope : Scope) (isCtor : Bool) (pos : ExprPosition)
    (needsBox : Bool) : AR := do
  if CppInterop.isNamespace scope then
    return ← aerr "analyze/invalid-cpp-symbol" "A C++ namespace cannot be taken by value."
  if CppInterop.isTemplatedFunction scope then
    match scope with
    | some (.function f) =>
      if isCtor then return mkCppValue pos needsBox (Obj.s sym) sym f.ret scope .constructor
      return mkCppValue pos needsBox (Obj.s sym) sym (CppInterop.getTypeFromScope scope) scope .function
    | _ => pure ()
  let mut resolvedScope := scope
  if CppInterop.isClassTemplate scope && (isCtor || pos == .call) then
    match instantiate c.w scope [] with
    | .error _ =>
      return ← aerr "analyze/invalid-cpp-constructor-call"
        s!"`{getQualifiedName scope}` cannot be constructed because it is missing the necessary template parameters."
    | .ok s => resolvedScope := s
  let mut type := CppInterop.getTypeFromScope resolvedScope
  if isPrimitive (CppInterop.getCanonicalType type) && isCtor then
    return mkCppValue pos needsBox (Obj.s sym) sym type scope .constructor
  if CppInterop.isClass resolvedScope || CppInterop.isTemplateSpecialization resolvedScope ||
     ((pos == .type || pos == .call) && CppInterop.isEnumType type && !CppInterop.isEnumConstant scope) then
    if isCtor then return mkCppValue pos needsBox (Obj.s sym) sym type resolvedScope .constructor
    return mkCppType pos needsBox sym type
  if CppInterop.isClassTemplate resolvedScope && isCtor then
    return ← aerr "analyze/invalid-cpp-constructor-call"
      s!"`{getQualifiedName scope}` cannot be constructed because it's missing the necessary type parameters."
  if isCtor then
    return ← aerr "analyze/invalid-cpp-symbol"
      s!"The '.' suffix for constructors may only be used on types. In this case, `{getQualifiedName scope}` is a value of type `{getQualifiedTypeName c.w type}`."
  let mut vk : Option CppValueKind := none
  if CppInterop.isVariable scope then
    vk := some .variable
    if !CppInterop.isPointerType type then type := CppInterop.getLvalueReferenceType type
  else if CppInterop.isEnumConstant scope then
    vk := some .enumConstant
    type := CppInterop.getNonReferenceType type
  else if CppInterop.isFunction scope then
    vk := some .function
  match vk with
  | some k => return mkCppValue pos needsBox (Obj.s sym) sym type scope k
  | none =>
    if pos == .type || pos == .call then return mkCppType pos needsBox sym type
    aerr "analyze/invalid-cpp-value" "This value could not be resolved to something jank can use."

/-- processor.cpp:analyze_cpp_symbol:3854 (`name` is the symbol's name, its `cpp` namespace
dropped). -/
def analyzeCppSymbol (c : Ctx) (name0 : String) (pos : ExprPosition) (needsBox : Bool) : AR := do
  let mut isCtor := false
  let mut name := name0
  if name.endsWith "." then
    isCtor := true
    name := (name.dropEnd 1).toString
  if name.endsWith "." || (name.splitOn "..").length > 1 then
    return ← aerr "analyze/invalid-cpp-symbol"
      "Name must not contain consecutive '.' dots. Each '.' corresponds with a '::' in C++."
  if name == "nullptr" then
    let scope := CppInterop.getUnderlyingScope c.w (some (.typedef_ "std::nullptr_t" (.b .nullptr)))
    return mkCppValue pos needsBox (Obj.s name0) name0 (.b .nullptr) scope .null
  else if name == "true" || name == "false" then
    return mkCppValue pos needsBox (Obj.s name0) name0 (.b .bool) none
      (if name == "true" then .boolTrue else .boolFalse)
  if (matchOperator name).isSome then
    if pos != .call then return ← aerr "analyze/invalid-cpp-position" s!"cpp/{name0}"
    return mkCppValue pos needsBox (Obj.s name0) name .null none .operatorCall
  if name.startsWith ".-" then
    if pos != .call then return ← aerr "analyze/invalid-cpp-position" name0
    return mkCppValue pos needsBox (Obj.s name0) name .null none .memberAccess
  else if name.startsWith "." then
    if pos != .call then return ← aerr "analyze/invalid-cpp-position" name0
    return mkCppValue pos needsBox (Obj.s name0) name .null none .memberCall
  if name == "void" then return mkCppType pos needsBox name0 CppInterop.getVoidType
  let globalType := resolveType c.w name
  if !globalType.isNull && isPrimitive globalType then
    if isCtor then return mkCppValue pos needsBox (Obj.s name0) name0 globalType none .constructor
    if pos != .type && pos != .call then
      return ← aerr "analyze/invalid-cpp-type-position" s!"cpp/{name0}"
    return mkCppType pos needsBox name0 globalType
  match resolveScope c.w name with
  | .error e =>
    match resolveLiteralValue name with
    | .ok r =>
      let source := mkCppValue .value needsBox (Obj.s name0) name0 (CppInterop.getTypeFromScope (some (.function r.fnScope)))
        (some (.function r.fnScope)) .function
      -- build_cpp_call with no arguments: the literal's function is its only overload.
      return mkCppCall pos needsBox (Obj.s name0) r.retType source [] r.functionCode
    | .error _ => aerr "analyze/unresolved-cpp-symbol" e
  | .ok scope =>
    let scope := CppInterop.getUnderlyingScope c.w scope
    buildCppValue c name scope isCtor pos needsBox

/-- The value of a DSL integral argument (`runtime::is_integral`, `runtime::to_i64`). -/
def objIntegral? : Obj → Option Int
  | .smallInteger v => some v.toInt
  | .integer v => some v.toInt
  | _ => none

def isKeyword (o : Obj) (k : String) : Bool := match o with | .keyword "" n => n == k | _ => false

def seqOf? : Obj → Option (List Obj)
  | .persistentList _ xs | .persistentVector _ xs => some xs
  | _ => none

mutual

/-- processor.cpp:analyze_cpp_dsl_impl:4915. -/
partial def analyzeCppDslImpl (c : Ctx) (o : Obj) (pos : ExprPosition) : AR := do
  if let .symbol _ _ n := o then
    return ← analyzeCppSymbol c n .type false
  let some xs := seqOf? o | aerr "analyze/invalid-cpp-dsl" "Invalid C++ type."
  let first := xs.headD .nil
  let args := xs.drop 1
  let requireArgs (expected : Nat) : Except Fault Unit :=
    if args.length != expected then
      aerr "analyze/invalid-cpp-dsl" s!"Invalid C++ type form. There were {expected} args expected, but {args.length} were provided."
    else .ok ()
  -- `transform_type`: validate the arity, analyze the type argument, validate it, transform it.
  let transformType (arity : Except Fault Unit) (validate : CType → Except Fault Unit)
      (transform : CType → Except Fault CType) : AR := do
    arity
    let t ← analyzeType c (args.headD .nil)
    validate t
    let r ← transform t
    return mkCppType .type false "cpp/dsl" r
  match first with
  | .keyword "" kw =>
    match kw with
    | "*" =>
      transformType (requireArgs 1)
        (fun t => if CppInterop.isReferenceType t then
          aerr "analyze/invalid-cpp-dsl" s!"C++ does not allow pointers to references. The full type here is `{getQualifiedTypeName c.w t}`." else .ok ())
        (fun t => .ok (CppInterop.getPointerType t))
    | "&" =>
      transformType (requireArgs 1)
        (fun t => if CppInterop.isVoid t then aerr "analyze/invalid-cpp-dsl" "C++ does not allow references to void." else .ok ())
        (fun t => .ok (CppInterop.getLvalueReferenceType t))
    | "&&" =>
      transformType (requireArgs 1)
        (fun t => if CppInterop.isVoid t then aerr "analyze/invalid-cpp-dsl" "C++ does not allow references to void." else .ok ())
        (fun t => .ok (CppInterop.getRvalueReferenceType t))
    | "const" =>
      transformType (requireArgs 1)
        (fun t => if CppInterop.isReferenceType t then aerr "analyze/invalid-cpp-dsl" "C++ does not allow const references." else .ok ())
        (fun t => .ok (CppInterop.getTypeWithConst t))
    | "volatile" =>
      transformType (requireArgs 1)
        (fun t => if CppInterop.isReferenceType t then aerr "analyze/invalid-cpp-dsl" "C++ does not allow volatile references." else .ok ())
        (fun t => .ok (CppInterop.getTypeWithVolatile t))
    | "signed" =>
      transformType (requireArgs 1)
        (fun t => if !CppInterop.isIntegral t then aerr "analyze/invalid-cpp-dsl" "Only integral types can be signed." else .ok ())
        (fun t => .ok (CppInterop.getSignedType c.p t))
    | "unsigned" =>
      transformType (requireArgs 1)
        (fun t => if !CppInterop.isIntegral t then aerr "analyze/invalid-cpp-dsl" "Only integral types can be unsigned." else .ok ())
        (fun t => .ok (CppInterop.getUnsignedType c.p t))
    | "short" =>
      transformType (requireArgs 1)
        (fun t =>
          if !CppInterop.isIntegral t || CppInterop.getTypeWithoutCv t == charType then
            aerr "analyze/invalid-cpp-dsl" "Only integer types can be short."
          else if CppInterop.isShortType t then aerr "analyze/invalid-cpp-dsl" "This type is already short."
          else .ok ())
        (fun t => .ok (CppInterop.getShortType c.p t))
    | "long" =>
      transformType (requireArgs 1)
        (fun t =>
          if (!CppInterop.isIntegral t || CppInterop.getTypeWithoutCv t == charType) &&
             CppInterop.getTypeWithoutCv t != .b .double then
            aerr "analyze/invalid-cpp-dsl" "Only integer types and double can be long."
          else if CppInterop.isShortType t then
            aerr "analyze/invalid-cpp-dsl" "This type is already short, so it cannot be made long."
          else .ok ())
        (fun t => .ok (CppInterop.getLongType c.p t))
    | "array" =>
      let argCount := args.length
      transformType
        (if argCount != 1 && argCount != 2 then
          aerr "analyze/invalid-cpp-dsl" s!"Invalid C++ array form. Either 1 or 2 args were expected, but {argCount} were provided."
         else .ok ())
        (fun t =>
          if CppInterop.isReferenceType t then aerr "analyze/invalid-cpp-dsl" "C++ does not allow arrays of references."
          else if CppInterop.isVoid t then aerr "analyze/invalid-cpp-dsl" "C++ does not allow arrays of void."
          else .ok ())
        (fun t =>
          if argCount == 1 then .ok (CppInterop.getArrayType t)
          else match objIntegral? (args.getD 1 .nil) with
            | some n => if n < 0 then aerr "analyze/invalid-cpp-dsl" "Array sizes must be either zero or positive integers."
                        else .ok (CppInterop.getArrayTypeSized t n.toNat)
            | none => aerr "analyze/invalid-cpp-dsl" "Invalid array size. An integer was expected.")
    | "fn" =>
      transformType (requireArgs 2) (fun _ => .ok ())
        (fun t => do
          let some ps := seqOf? (args.getD 1 .nil)
            | aerr "analyze/invalid-cpp-dsl" "A sequence of parameter types was expected."
          let mut types := []
          for prm in ps do
            let pt ← analyzeType c prm
            if CppInterop.isVoid pt then return ← aerr "analyze/invalid-cpp-dsl" "Function parameter types may not be void."
            types := types ++ [pt]
          return CppInterop.getFunctionType t types)
    | _ => aerr "analyze/invalid-cpp-dsl" s!"Invalid C++ type modifier `:{kw}`."
  | .symbol _ ns n =>
    if ns == "cpp" && n == "dsl" then analyzeCppDslImpl c (args.headD .nil) pos
    else
      let t := CppInterop.getType c.w n
      if !t.isNull then
        return ← aerr "analyze/invalid-cpp-dsl" s!"Unable to use `{getQualifiedTypeName c.w t}` as a template. If you just want the type, remove the surrounding parens."
      match resolveScope c.w n with
      | .error e => aerr "analyze/invalid-cpp-dsl" e
      | .ok scope =>
        if !CppInterop.isTemplate scope then
          return ← aerr "analyze/invalid-cpp-dsl" s!"Unable to use `{getQualifiedName scope}` as a template."
        let mut targs : List CType := []
        for a in args do
          match objIntegral? a with
          | some _ => targs := targs ++ [.b .llong]
          | none => targs := targs ++ [← analyzeType c a]
        match instantiate c.w scope targs with
        | .error _ => aerr "analyze/invalid-cpp-dsl" "Unable to instantiate this template with these arguments."
        | .ok inst =>
          if pos == .type then return mkCppType .type false n (CppInterop.getTypeFromScope inst)
          if pos == .call then return mkCppType .type false n (CppInterop.getTypeFromScope inst)
          aerr "analyze/invalid-cpp-dsl" "A C++ value was expected here, but a type was found."
  | _ => aerr "analyze/invalid-cpp-dsl" "Invalid form for the C++ DSL here."

/-- processor.cpp:analyze_type:5757. -/
partial def analyzeType (c : Ctx) (o : Obj) : Except Fault CType := do
  let e ← analyzeCppDslImpl c o .type
  match e.data with
  | .cppType _ t => return t
  | _ => aerr "analyze/invalid-cpp-type" "A type was expected here."

end

/-- processor.cpp:analyze_cpp_dsl:4905. -/
def analyzeCppDsl (c : Ctx) (o : Obj) (pos : ExprPosition) : AR := analyzeCppDslImpl c o pos

end Jank.Interop.Analyze

