import Jank.Analyzer.Arena
import Jank.Analyzer.Runtime

/-!
# `analyze::processor`, replicated

`src/cpp/jank/analyze/processor.cpp` at jank 7135b7708 (paths under `upstream-main/compiler+runtime/`;
line numbers are those of 7135b7708): every `analyze_*`
function and helper except the C++ interop ones (`analyze_cpp_*`, `build_cpp_*`,
`apply_implicit_conversions`), which are modeled by a small oracle (`Interop` section, assumptions
in the report). One Lean definition per C++ function, same branching and order of effects.

Monad. `AnR α` is `jtl::result<α, error_ref>` returned by value (`throw` = `return error`), over
`AnM`, whose own error is a C++ exception thrown through the analyzer (`Fault.thrown`: an
`expect_ok()` on an error result, a `std::runtime_error`) or the model's fuel running out.
-/

namespace Jank.Analyzer

inductive Fault where
  /-- A C++ exception escaping the analyzer. -/
  | thrown (e : AnalyzeError)
  /-- The model's fuel ran out (a bound, not a hang). -/
  | fuel
  /-- Undefined behaviour reached (e.g. `jtl::option::unwrap()` on an empty option, whose check
  is a debug assertion only). -/
  | ub (what : String)
  deriving Repr, BEq, Inhabited

/-- The modeled answers of Clang queries jank cannot answer by itself (assumption A4). -/
structure Oracle where
  /-- `Cpp::GetBuiltinOperatorType(=, [object_ref, object_ref])` is non-null. -/
  classBuiltinAssign : Bool := false
  deriving Repr, Inhabited

/-- `analyze::processor`'s fields plus what it reads of the runtime. -/
structure AnState where
  arena : Arena := {}
  rt : Runtime
  /-- `processor::vars`: each def's var and value expression. -/
  pvars : List (VarRef × ExprId) := []
  rootFrame : FrameId := 0
  /-- `processor::macro_expansions` (back = last element). -/
  macroExpansions : List Obj := []
  /-- `processor::loop_details`: `none`, `some none` (= `some(nullptr)`), `some (some let)`. -/
  loopDetails : Option (Option ExprId) := none
  /-- Thread bindings of `*no-recur*` (`context::no_recur_var`), innermost first. -/
  noRecur : List Bool := []
  oracle : Oracle := {}
  fuel : Nat := 20000
  /-- Model notes (dangling pointers created, UB reached). -/
  notes : List String := []

abbrev AnM := EStateM Fault AnState
abbrev AnR := ExceptT AnalyzeError AnM

def liftArena {α : Type} (k : ArenaM α) : AnR α := do
  let s ← get
  let (r, a) := k.run s.arena
  set { s with arena := a }
  pure r

def arena : AnR Arena := do pure (← get).arena

def mkExpr (position : ExprPosition) (frame : Option FrameId) (needsBox : Bool) (form : Obj)
    (data : ExprData) : AnR ExprId := do
  let s ← get
  let (a, i) := s.arena.addExpr { kind := data.kind, position, frame, needsBox, form, data }
  set { s with arena := a }
  pure i

def mkFrame (type : FrameType) (parent : Option FrameId) : AnR FrameId := do
  let s ← get
  let (a, i) := s.arena.addFrame { type, parent }
  set { s with arena := a }
  pure i

def mkBinding (b : LocalBinding) : AnR BindingId := do
  let s ← get
  let (a, i) := s.arena.addBinding b
  set { s with arena := a }
  pure i

def mkFnCtx (c : FunctionContext) : AnR FnCtxId := do
  let s ← get
  let (a, i) := s.arena.addFnCtx c
  set { s with arena := a }
  pure i

def getE (i : ExprId) : AnR Expr := do pure ((← arena).expr i)
def setE (i : ExprId) (f : Expr → Expr) : AnR Unit := liftArena (modifyExpr i f)
def typeOf (i : ExprId) : AnR CT := do pure (exprType (← arena) i 10000)

/-- Pushes a local onto `frame->locals[sym]` (`emplace_back`). -/
def pushLocal (frame : FrameId) (sym : Obj) (b : LocalBinding) : AnR BindingId := do
  let id ← mkBinding b
  liftArena <| modifyFrame frame fun f =>
    if f.locals.any (fun (k, _) => symKey k == symKey sym) then
      { f with locals := f.locals.map fun (k, bs) => if symKey k == symKey sym then (k, bs ++ [id]) else (k, bs) }
    else { f with locals := f.locals ++ [(sym, [id])] }
  pure id

def fail {α : Type} (kind message : String) (form : Obj := .nil) : AnR α := throw { kind, message, form }

/-- Records that a path of interest was taken (for classifying a search's findings; no effect on
the replica). -/
def tag (t : String) : AnR Unit :=
  modify fun s => if s.notes.contains s!"tag:{t}" then s else { s with notes := s.notes ++ [s!"tag:{t}"] }

/-- `expect_ok()` on a result: an error is thrown as a C++ exception (jtl/result.hpp:42). -/
def expectOk {α : Type} (r : Except AnalyzeError α) : AnR α :=
  match r with
  | .ok v => pure v
  | .error e => (throwThe Fault (Fault.thrown e) : AnM α)

/-- Runs `k`, keeping its result (ok or error) as a value. -/
def capture {α : Type} (k : AnR α) : AnR (Except AnalyzeError α) := (ExceptT.run k : AnM _)

def burn : AnR Unit := do
  let s ← get
  if s.fuel == 0 then (throwThe Fault Fault.fuel : AnM Unit)
  set { s with fuel := s.fuel - 1 }

def withRt {α : Type} (f : Runtime → Runtime × α) : AnR α := do
  let s ← get
  let (rt, r) := f s.rt
  set { s with rt := rt }
  pure r

/-! ## Helpers (processor.cpp:75-1217) -/

/-- `push_macro_expansions` (processor.cpp:80): when the form's meta has `:jank/macro-expansion`,
push `(second expansion)` (the original form) and report that a pop is due at scope exit. -/
def pushMacroExpansions (o : Obj) : AnR Bool := do
  let expansion := Obj.getOpt o.getMeta (kw "jank/macro-expansion")
  if expansion == .nil then return false
  let second := match expansion.elems with | some (_ :: x :: _) => x | _ => .nil
  modify fun s => { s with macroExpansions := s.macroExpansions ++ [second] }
  return true

def popMacroExpansion : AnR Unit :=
  modify fun s => { s with macroExpansions := s.macroExpansions.dropLast }

/-- Runs `k`, then pops the macro expansion pushed for this scope (the `scope_exit` returned by
`push_macro_expansions` runs on every return path). -/
def popAfter {α : Type} (pushed : Bool) (k : AnR α) : AnR α := do
  let r ← capture k
  if pushed then popMacroExpansion
  MonadExcept.ofExcept r

/-- `latest_expansion` (processor.cpp:97). -/
def latestExpansion (expansions : List Obj) : Obj :=
  match expansions.reverse.find? (fun e => Obj.getOpt e.getMeta (kw "jank/macro-expansion") != .nil) with
  | some e => match (Obj.getOpt e.getMeta (kw "jank/macro-expansion")).elems with
    | some (_ :: x :: _) => x
    | _ => .nil
  | none => expansions.getLast?.getD .nil

/-- `is_private_var` (processor.cpp:124). -/
def isPrivateVar (v : VarCell) : Bool := v.private_

/-- `can_access_var` (processor.cpp:130): inside any macro expansion, private vars are accessible. -/
def canAccessVar (rt : Runtime) (v : VarCell) (fromMacroExpansion : Bool) : Bool :=
  fromMacroExpansion || !isPrivateVar v || v.ns == rt.currentNs

/-- The binding scope of `*no-recur*` (`context::binding_scope`). -/
def withNoRecur {α : Type} (b : Bool) (k : AnR α) : AnR α := do
  modify fun s => { s with noRecur := b :: s.noRecur }
  let r ← capture k
  modify fun s => { s with noRecur := s.noRecur.drop 1 }
  MonadExcept.ofExcept r

/-- `resolved_expression` (processor.cpp:1017): through local references to non-loop locals with a
value. -/
partial def resolvedExpression (i : ExprId) : AnR ExprId := do
  let a ← arena
  match (a.expr i).data with
  | .localReference _ b =>
    let bd := a.binding b
    match bd.valueExpr with
    | some v => if !bd.isLoopVariable then resolvedExpression v else pure i
    | none => pure i
  | _ => pure i

/-- `build_cpp_call` for a cast to a primitive type (processor.cpp:252, the `is_ctor &&
is_primitive` branch at 267 with `allow_implicit_conversions = false`). -/
def buildPrimitiveCast (target : CT) (arg : ExprId) (argType : CT) (position : ExprPosition)
    (frame : Option FrameId) (needsBox : Bool) (form : Obj) : AnR ExprId := do
  if isVoid target then fail "analyze/invalid-cpp-constructor-call" "A `void` instance cannot be constructed." form
  if !cppIsConstructible target argType then
    if !(isTraitConvertible target && isAnyObject argType) then
      fail "analyze/invalid-cpp-constructor-call" s!"The type `{target.spelling}` cannot be constructed from a value of type `{argType.spelling}`." form
  mkExpr position frame needsBox form (.cppConstructorCall target.toCpp .null [arg] false)

/-- `apply_implicit_conversion` (processor.cpp:1031). -/
partial def applyImplicitConversion (e : ExprId) (exprType expected : CT) : AnR ExprId := do
  match determineImplicitConversion exprType expected with
  | .none => pure e
  | .intoObject =>
    let resolved ← resolvedExpression e
    let r ← getE resolved
    match r.data with
    | .cppLiteral d =>
      let x ← getE e
      let lit ← mkExpr x.position x.frame x.needsBox d (.primitiveLiteral d)
      applyImplicitConversion lit (literalType d true) expected
    | _ =>
      let x ← getE e
      let castPos := x.position
      liftArena (propagatePosition e .value)
      mkExpr castPos x.frame x.needsBox x.form (.cppConversion expected.toCpp exprType.toCpp e .intoObject)
  | .fromObject =>
    let x ← getE e
    let castPos := x.position
    liftArena (propagatePosition e .value)
    mkExpr castPos x.frame x.needsBox x.form (.cppConversion expected.toCpp expected.toCpp e .fromObject)
  | .cast =>
    let x ← getE e
    let castPos := x.position
    liftArena (propagatePosition e .value)
    -- The `cpp_value` constructor the call is built on is not kept by `build_cpp_call`'s
    -- primitive branch.
    let _ ← mkExpr castPos x.frame false x.form (.cppValue x.form (Obj.s expected.spelling) expected.toCpp .null .constructor)
    buildPrimitiveCast expected e exprType castPos x.frame x.needsBox x.form
  | .unknown =>
    let x ← getE e
    fail "analyze/invalid-cpp-conversion" s!"There is no implicit conversion from `{exprType.spelling}` to `{expected.spelling}`." x.form

/-- `apply_implicit_conversion(expr, expected)` (processor.cpp:1131). -/
def applyImplicitConversion2 (e : ExprId) (expected : CT) : AnR ExprId := do
  applyImplicitConversion e (← typeOf e) expected

/-- `processor::specials()` (processor.cpp:1190). -/
inductive Special where
  | def | fn | recur | do_ | let_ | letfn | loop | if_ | quote | var | throw | try_ | case_
  | cppRaw | cppDsl | cppCast | cppUnsafeCast | cppBox | cppUnbox | cppNew | cppDelete
  deriving Repr, BEq, DecidableEq

def specialOf (ns name : String) : Option Special :=
  if ns == "" then
    match name with
    | "def" => some .def | "fn*" => some .fn | "recur" => some .recur | "do" => some .do_
    | "let*" => some .let_ | "letfn*" => some .letfn | "loop*" => some .loop | "if" => some .if_
    | "quote" => some .quote | "var" => some .var | "throw" => some .throw | "try" => some .try_
    | "case*" => some .case_ | _ => none
  else if ns == "cpp" then
    match name with
    | "raw" => some .cppRaw | "dsl" => some .cppDsl | "cast" => some .cppCast
    | "unsafe-cast" => some .cppUnsafeCast | "box" => some .cppBox | "unbox" => some .cppUnbox
    | "new" => some .cppNew | "delete" => some .cppDelete | _ => none
  else none

/-- `processor::is_special` (processor.cpp:5778). -/
def isSpecial (form : Obj) : Bool :=
  match form with
  | .symbol _ ns name => (ns.isEmpty && (name == "finally" || name == "catch")) || (specialOf ns name).isSome
  | _ => false

/-! ## Interop oracle (owned by the interop agent; modeled for the forms jank code generates) -/

/-- `analyze_type` (processor.cpp:5758) for `cpp/<type>` symbols. -/
def analyzeTypeOracle (o : Obj) : AnR CT :=
  match o with
  | .symbol _ "cpp" n =>
    match n with
    | "jank.runtime.object_ref" => pure .objectRef
    | "int" => pure .int | "long" => pure .long | "double" => pure .double | "bool" => pure .bool
    | "void" => pure .void
    | _ => fail "analyze/invalid-cpp-type" "A type was expected here." o
  | _ => fail "analyze/invalid-cpp-type" "A type was expected here." o

/-- `analyze_cpp_symbol` (processor.cpp:3855), for operators (`cpp/=`), `cpp/true`/`cpp/false` and
`cpp/jank.runtime.<fn>`. -/
def analyzeCppSymbol (sym : Obj) (frame : FrameId) (position : ExprPosition) (needsBox : Bool) : AnR ExprId := do
  let (_, name) := symKey sym
  if name == "=" || name == "+" || name == "<" then
    if position != .call then fail "analyze/invalid-cpp-position" (symString sym) sym
    mkExpr position (some frame) needsBox sym (.cppValue sym sym .null .null .operatorCall)
  else if name == "true" || name == "false" then
    mkExpr position (some frame) needsBox sym
      (.cppValue sym sym CT.bool.toCpp .null (if name == "true" then .boolTrue else .boolFalse))
  else if name.startsWith "jank.runtime." then
    mkExpr position (some frame) needsBox sym (.cppValue sym sym .null (.named name) .function)
  else fail "analyze/unresolved-cpp-symbol" s!"Unable to find C++ symbol `{symString sym}`." sym

/-! ## The analyzer -/

mutual

/-- `processor::analyze(o, frame, position, fn_ctx, needs_box)` (processor.cpp:4850): dispatch on
the object's type. -/
partial def analyze (o : Obj) (frame : FrameId) (position : ExprPosition) (fnCtx : Option FnCtxId)
    (needsBox : Bool) : AnR ExprId := do
  burn
  match o with
  | .persistentList .. => analyzeCall o frame position fnCtx needsBox
  | .persistentVector .. => analyzeVector o frame position fnCtx needsBox
  | .persistentArrayMap .. | .persistentHashMap .. | .persistentSortedMap .. =>
    analyzeMap o frame position fnCtx needsBox
  | .persistentHashSet .. | .persistentSortedSet .. => analyzeSet o frame position fnCtx needsBox
  | .symbol .. => analyzeSymbol o frame position fnCtx needsBox
  | _ =>
    if o.sequential then
      analyzeCall (.persistentList o.getMeta (o.elems.getD [])) frame position fnCtx needsBox
    else match o with
      | .var ns name => analyzeVarVal ⟨ns, name⟩ frame position fnCtx needsBox
      | _ => analyzePrimitiveLiteral o frame position fnCtx needsBox

/-- `analyze_collection_meta` (processor.cpp:157). -/
partial def analyzeCollectionMeta (md : Option Obj) (frame : FrameId) (fnCtx : Option FnCtxId) :
    AnR (Option ExprId) := do
  match md with
  | none => pure none
  | some m =>
    if m == .nil then return none
    let runtimeMeta := stripSourceFromMeta m
    if runtimeMeta == .nil then return none
    if runtimeMeta.get (kw "jank/macro-expansion") != .nil then tag "macro-meta-on-literal"
    let metaForm := runtimeMeta.setMeta none
    let e ← analyze metaForm frame .value fnCtx true
    let e ← applyImplicitConversion e (← typeOf e) .objectRef
    pure (some e)

/-- `analyze_def` (processor.cpp:1254). -/
partial def analyzeDef (l : Obj) (frame : FrameId) (position : ExprPosition) (fnCtx : Option FnCtxId)
    (_needsBox : Bool) : AnR ExprId := do
  let pushed ← pushMacroExpansions l
  popAfter pushed do
    let xs := l.elems.getD []
    let length := xs.length
    if length < 2 then fail "analyze/invalid-def" "The `def` form is missing a var name." l
    else if length > 4 then fail "analyze/invalid-def" "The `def` form received too many arguments." l
    let symObj := xs[1]!
    match symObj with
    | .symbol md ns name =>
      if !ns.isEmpty then fail "analyze/invalid-def" "The var name in a `def` form must not be qualified." l
      -- 7135b7708 (processor.cpp:1296): C++ member syntax is only meaningful in call position.
      if name.startsWith "." then fail "analyze/invalid-cpp-position" (symString symObj) symObj
      let (qns, qname) := (← get).rt.qualifySymbol ns name
      let mut qualifiedSym : Obj := .symbol md qns qname
      let var ← withRt fun rt => rt.internOwnedVar qns qname
      let mut valueExpr : Option ExprId := none
      let hasValue := 3 ≤ length
      let hasDocstring := 4 ≤ length
      if hasValue then
        let valueOpt := if hasDocstring then xs[3]! else xs[2]!
        let v ← analyze valueOpt frame .value fnCtx true
        let v ← applyImplicitConversion v (← typeOf v) .objectRef
        valueExpr := some v
        modify fun s => { s with pvars := (var, v) :: s.pvars.filter (·.1 != var) }
      if hasDocstring then
        let docstringObj := xs[2]!
        match docstringObj with
        | .persistentString _ =>
          let metaWithDoc := (qualifiedSym.getMeta.getD .nil).assoc (kw "doc") docstringObj
          qualifiedSym := qualifiedSym.setMeta (some metaWithDoc)
        | _ => fail "analyze/invalid-def" "The docstring for a `def` form must be a string." docstringObj
      mkExpr position (some frame) true l (.def qualifiedSym valueExpr)
    | _ => fail "analyze/invalid-def" "The var name in a `def` form must be a symbol." symObj

/-- `analyze_case` (processor.cpp:1386). Since 7135b7708 each branch is typed against the default with
`find_branch_common_type`; the last branch's common type becomes the case's type (`case_::type`), and if any
pair needed a conversion, the default and every branch are converted to that type (1536-1569). -/
partial def analyzeCase (o : Obj) (frame : FrameId) (position : ExprPosition) (fnCtx : Option FnCtxId)
    (needsBox : Bool) : AnR ExprId := do
  let pushed ← pushMacroExpansions o
  popAfter pushed do
    let xs := o.elems.getD []
    if xs.length != 6 then fail "analyze/invalid-case" "The `case*` form requires exactly six parameters." o
    let valueExprR ← capture (analyze xs[1]! frame .value fnCtx needsBox)
    let valueExpr ← match valueExprR with
      | .ok v => pure v
      | .error e => fail "analyze/invalid-case" e.message o
    let valueExpr ← applyImplicitConversion valueExpr (← typeOf valueExpr) .objectRef
    let toI64 : Obj → Option (BitVec 64) := fun
      | .smallInteger v => some (v.signExtend 64)
      | .integer v => some v
      | .bigInteger v => some (BitVec.ofInt 64 v)
      | _ => none
    let shift ← match toI64 xs[2]! with
      | some v => pure v
      | none => fail "analyze/invalid-case" "The shift value for `case*` must be an integer." o
    let mask ← match toI64 xs[3]! with
      | some v => pure v
      | none => fail "analyze/invalid-case" "The mask value for `case*` must be an integer." o
    let defaultR ← capture (analyze xs[4]! frame position fnCtx needsBox)
    let imap := xs[5]!
    -- `default_expr.expect_ok()` (processor.cpp:1483): an error in the default is thrown.
    let mut dflt ← expectOk defaultR
    let mut needsConversion := false
    let mut chosenType ← typeOf dflt
    let mut hasRecur := (← getE (← resolveTailExpression dflt)).kind == .recur
    if !imap.mapLike then fail "analyze/invalid-case" "The keys and expressions for `case*` must be in a map-like structure." o
    let mut keys : List (BitVec 64) := []
    let mut exprs : List ExprId := []
    for e in imap.elems.getD [] do
      let kv := e.elems.getD []
      let k := kv.headD .nil
      let v := (kv.drop 1).headD .nil
      match toI64 k with
      | none => fail "analyze/invalid-case" "Each key in a `case*` map must be an integer." o
      | some key =>
        let r ← capture (analyze v frame position fnCtx needsBox)
        match r with
        | .error err => fail "analyze/invalid-case" err.message o
        | .ok x =>
          hasRecur := hasRecur || (← getE (← resolveTailExpression x)).kind == .recur
          -- Each branch against the default; the last branch's common type wins (processor.cpp:1521).
          match findBranchCommonType (← typeOf x) (some (← typeOf dflt)) hasRecur with
          | .error msg => fail "analyze/invalid-case" msg o
          | .ok bct =>
            needsConversion := needsConversion || bct.thenNeedsConversion || bct.elseNeedsConversion
            if chosenType != bct.type && keys.length > 0 then tag "case-branch-type"
            chosenType := bct.type
            keys := keys ++ [key]
            exprs := exprs ++ [x]
    let mut convertedExprs : List ExprId := []
    if needsConversion then
      dflt ← applyImplicitConversion dflt (← typeOf dflt) chosenType
      for x in exprs do
        convertedExprs := convertedExprs ++ [← applyImplicitConversion x (← typeOf x) chosenType]
    let finalExprs := if needsConversion then convertedExprs else exprs
    -- A branch whose type is not the case's type is converted by the IR's `set_local`.
    for x in finalExprs ++ [dflt] do
      let t ← typeOf x
      if t != chosenType && !(isAnyObject t && isUntypedObject chosenType) then tag "case-branch-type"
    let ci ← mkExpr position (some frame) needsBox o (.case_ valueExpr shift mask dflt keys finalExprs)
    setE ci fun e => { e with caseType := chosenType.toCpp }
    pure ci

/-- `analyze_symbol` (processor.cpp:1583). -/
partial def analyzeSymbol (sym : Obj) (frame : FrameId) (position : ExprPosition) (_fc : Option FnCtxId)
    (needsBox0 : Bool) : AnR ExprId := do
  let (ns, name) := symKey sym
  if (ns == "cpp" && name != "raw") || (ns.isEmpty && name.startsWith ".") then
    return ← analyzeCppSymbol sym frame position needsBox0
  let pushed ← pushMacroExpansions sym
  popAfter pushed do
    let mut needsBox := needsBox0
    let a ← arena
    match findLocalOrCapture a frame sym with
    | some found =>
      if let some nr := findNamedRecursion a frame sym then
        if !found.crossedFns.contains nr.fnFrame then pure () else tag "fn-name-shadowed"
      -- Captured locals must be copyable: every type of the universe is.
      liftArena (registerCaptures found)
      let bd := (← arena).binding found.binding
      needsBox := needsBox || bd.needsBox
      let mut found := found
      if !found.crossedFns.isEmpty then
        needsBox := true
        liftArena (modifyBinding found.binding fun b => { b with hasBoxedUsage := true })
        match findLocalOrCapture (← arena) frame sym with
        | some f => found := f
        | none => pure ()
      if needsBox then liftArena (modifyBinding found.binding fun b => { b with hasBoxedUsage := true })
      else liftArena (modifyBinding found.binding fun b => { b with hasUnboxedUsage := true })
      mkExpr position (some frame) needsBox sym (.localReference sym found.binding)
    | none =>
      match findNamedRecursion (← arena) frame sym with
      | some nr =>
        liftArena (registerNamedCaptures frame nr)
        modify fun s => { s with notes := s.notes ++ ["register_captures(frame, named_recursion): originating_binding points to a dead stack local"] }
        let ctx := ((← arena).frame nr.fnFrame).fnCtx.getD 0
        liftArena (modifyFnCtx ctx fun c => { c with isNamedRecursive := true })
        mkExpr position (some frame) needsBox sym (.recursionReference ctx)
      | none =>
        let rt := (← get).rt
        let (qns, qname) := rt.qualifySymbol ns name
        match rt.findVar qns qname with
        | none =>
          match rt.findReferredGlobal name with
          | some g => analyzeCppSymbol g frame position needsBox
          | none => fail "analyze/unresolved-symbol" s!"The symbol `{symString sym}` could not be resolved." sym
        | some vr =>
          let v := (rt.var? vr).getD { ns := vr.ns, name := vr.name }
          if v.private_ && v.ns != rt.currentNs && !(← get).macroExpansions.isEmpty then tag "private-under-expansion"
          if !canAccessVar rt v !(← get).macroExpansions.isEmpty then
            fail "analyze/private-var" s!"The var `{qns}/{qname}` is private and can only be accessed from namespace `{v.ns}`." sym
          mkExpr position (some frame) true (.symbol none qns qname) (.varDeref (.symbol none qns qname) vr)

/-- `analyze_fn_arity` (processor.cpp:1713). `list` is `([params] body...)`. -/
partial def analyzeFnArity (list : Obj) (name : String) (currentFrame : FrameId) : AnR FunctionArity := do
  let xs := list.elems.getD []
  let paramsObj ← match xs.head? with
    | none => fail "analyze/invalid-fn-parameters" "This function is missing its parameter vector." list
    | some p => pure p
  let params ← match paramsObj with
    | .persistentVector _ ps => pure ps
    | _ => fail "analyze/invalid-fn-parameters" "The parameter vector for this function must be a vector." paramsObj
  withNoRecur false do
    let frame ← mkFrame .fn (some currentFrame)
    let mut paramSymbols : List Parameter := []
    let mut unique : List (String × String) := []
    let mut isVariadic := false
    let mut idx := 0
    for p in params do
      match p with
      | .symbol md pns pname =>
        if !pns.isEmpty then
          fail "analyze/invalid-fn-parameters" "Each function parameter must be an unqualified symbol." p
        else if pname.startsWith "." then
          -- 7135b7708 (processor.cpp:1769).
          fail "analyze/invalid-cpp-position" (symString p) p
        else if pname == "&" then
          if idx + 1 == params.length then
            fail "analyze/invalid-fn-parameters" "A symbol must follow `&` to name the variadic parameter." p
          else if idx + 2 != params.length then
            fail "analyze/invalid-fn-parameters" "There may be no additional parameters after the variadic parameter." p
          isVariadic := true
        else
          if Obj.getOpt md (kw "tag") != .nil then
            (throwThe Fault (Fault.thrown { kind := "model/unmodeled", message := ":tag on a parameter" }) : AnM Unit)
          let paramType := CT.objectRef
          if unique.contains (pns, pname) then
            -- Rename the first parameter with this name (C++ has no duplicate parameter names).
            let mut renamed := false
            let mut ps' : List Parameter := []
            for q in paramSymbols do
              if !renamed && symKey q.name == (pns, pname) then
                let fresh ← withRt fun rt => rt.uniqueString "shadowed"
                ps' := ps' ++ [{ q with name := Obj.s fresh }]
                renamed := true
              else ps' := ps' ++ [q]
            paramSymbols := ps'
          else unique := unique ++ [(pns, pname)]
          let _ ← pushLocal frame p { name := p, nativeName := pname, valueExpr := none,
                                      originatingFrame := some currentFrame, type := paramType.toCpp }
          paramSymbols := paramSymbols ++ [{ name := p, type := paramType.toCpp }]
      | _ => fail "analyze/invalid-fn-parameters" "Each function parameter must be a symbol." p
      idx := idx + 1
    if paramSymbols.length > 10 then
      fail "analyze/invalid-fn-parameters" "This function has too many parameters. The max is 10." paramsObj
    let fnCtx ← mkFnCtx { name, isVariadic, paramCount := paramSymbols.length.toUInt64 }
    liftArena (modifyFrame frame fun f => { f with fnCtx := some fnCtx })
    let bodyDo ← mkExpr .tail (some frame) true list (.do_ [])
    let formCount := xs.length - 1
    let mut i := 0
    for item in xs.drop 1 do
      i := i + 1
      let lastItem := i == formCount
      let pos := if lastItem then ExprPosition.tail else .statement
      let nb := pos != .statement
      let form ← analyze item frame pos (some fnCtx) nb
      setE bodyDo fun e => match e.data with
        | .do_ vs => { e with data := .do_ (vs ++ [form]) }
        | _ => e
    if ((← arena).fnCtx fnCtx).isRecurRecursive then liftArena (forceBoxed bodyDo)
    match (← getE bodyDo).data with
    | .do_ vs =>
      if let some last := vs.getLast? then
        let t ← typeOf last
        if !isAnyObject t && !isTraitConvertible t then
          fail "analyze/invalid-cpp-conversion" s!"This function is returning a native object of type `{t.spelling}`, which is not convertible to a jank runtime object." list
        let newLast ← applyImplicitConversion last t .objectRef
        setE bodyDo fun e => { e with data := .do_ (vs.dropLast ++ [newLast]) }
    | _ => pure ()
    pure { params := paramSymbols, body := bodyDo, frame := some frame, fnCtx }

/-- `analyze_fn` (processor.cpp:1941). -/
partial def analyzeFn (fullList : Obj) (frame : FrameId) (position : ExprPosition) (_fnCtx : Option FnCtxId)
    (_needsBox : Bool) : AnR ExprId := do
  let pushed ← pushMacroExpansions fullList
  popAfter pushed do
    let xs := fullList.elems.getD []
    let length := xs.length
    if length < 2 then fail "analyze/invalid-fn" "This function is missing its parameter vector." fullList
    let mut list := xs
    let mut name := ""
    let mut uniqueName := ""
    let mut firstElem := xs[1]!
    match firstElem with
    | .symbol _ _ sname =>
      -- 7135b7708 (processor.cpp:1963).
      if sname.startsWith "." then fail "analyze/invalid-cpp-position" (symString firstElem) firstElem
      name := sname
      uniqueName ← withRt fun rt => rt.uniqueNamespacedString name
      if length < 3 then fail "analyze/invalid-fn" "This function is missing its parameter vector." fullList
      firstElem := xs[2]!
      list := xs.drop 1
    | _ =>
      name ← withRt fun rt => rt.uniqueNamespacedString "fn"
      uniqueName := name
    let mut arities : List FunctionArity := []
    match firstElem with
    | .persistentVector .. =>
      let ar ← analyzeFnArity (.persistentList none (list.drop 1)) name frame
      arities := arities ++ [ar]
    | _ =>
      for arityListObj in list.drop 1 do
        if arityListObj.sequenceLike then
          let ar ← analyzeFnArity (.persistentList none (arityListObj.elems.getD [])) name frame
          arities := arities ++ [ar]
        else
          fail "analyze/invalid-fn" "Invalid 'fn' syntax. Please provide either a list of arities or a parameter vector." fullList
    let a ← arena
    let mut foundVariadic := 0
    let mut variadicArity := 0
    for ar in arities do
      if (a.fnCtx ar.fnCtx).isVariadic then
        foundVariadic := foundVariadic + 1
        variadicArity := ar.params.length
    if foundVariadic > 1 then fail "analyze/invalid-fn" "A function may only have one variadic arity." fullList
    if foundVariadic > 0 then
      for ar in arities do
        if !(a.fnCtx ar.fnCtx).isVariadic && ar.params.length ≥ variadicArity then
          fail "analyze/invalid-fn" "The variadic arity of this function has fewer parameters than one of its fixed arities, which would lead to ambiguities when it's called." fullList
    let rt := (← get).rt
    let fnMeta : Obj := .persistentHashMap none [(kw "name", str s!"{rt.currentNs}/{name}")]
    let ret ← mkExpr position (some frame) true fullList (.function name uniqueName [] fnMeta false)
    let mut rest := arities
    while !rest.isEmpty do
      let base := rest.head!
      rest := rest.tail!
      liftArena (modifyFnCtx base.fnCtx fun c => { c with fn := some ret, name, uniqueName })
      let a ← arena
      for other in rest do
        if base.params.length == other.params.length
           && (a.fnCtx base.fnCtx).isVariadic == (a.fnCtx other.fnCtx).isVariadic then
          fail "analyze/invalid-fn" "There are multiple arities with the same number of parameters. Each one must be unique." fullList
    setE ret fun e => { e with data := .function name uniqueName arities fnMeta (foundVariadic != 0) }
    pure ret

/-- `analyze_recur` (processor.cpp:2112). -/
partial def analyzeRecur (list : Obj) (frame : FrameId) (position : ExprPosition) (fnCtx : Option FnCtxId)
    (_needsBox : Bool) : AnR ExprId := do
  let pushed ← pushMacroExpansions list
  popAfter pushed do
    let s ← get
    if fnCtx.isNone && s.loopDetails.isNone then
      fail "analyze/invalid-recur-position" "`recur` may only be used inside a function or a `loop`." list
    else if s.noRecur.head? == some true then
      fail "analyze/invalid-recur-from-try" "`recur` may not be used through a `try` form." list
    else if position != .tail then
      fail "analyze/invalid-recur-position" "`recur` must be used in tail position." list
    let xs := list.elems.getD []
    let argCount := xs.length - 1
    let isLoop := s.loopDetails.isSome
    let loopLet : Option ExprId := s.loopDetails.getD none
    if let some l := loopLet then
      let lf := ((← arena).expr l).frame.getD 0
      if !withinSameFn (← arena) frame lf then tag "recur-crosses-fn"
    let pairsOf : AnR (List (BindingId × ExprId)) := do
      match loopLet with
      | some l => match (← getE l).data with
        | .let pairs _ _ => pure pairs
        | _ => pure []
      | none => pure []
    if isLoop then
      let pairs ← pairsOf
      if pairs.length != argCount then
        fail "analyze/invalid-recur-args" s!"`recur` received {argCount} argument(s), but it requires exactly {pairs.length} here." list
    else
      let pc := ((← arena).fnCtx fnCtx.get!).paramCount
      if pc.toNat != argCount then
        fail "analyze/invalid-recur-args" s!"`recur` received {argCount} argument(s), but it requires exactly {pc} here." list
    let mut argIndex : UInt8 := 0
    let mut argExprs : List ExprId := []
    let mut opEqualExprs : List ExprId := []
    for form in xs.drop 1 do
      let argExpr ← analyze form frame .value fnCtx true
      let mut expectedType := CT.objectRef
      if isLoop then
        let pairs ← pairsOf
        let pair := pairs[argIndex.toNat]!
        expectedType := mutableType (← typeOf pair.2)
        if !isAnyObject expectedType && (← typeOf argExpr) != expectedType then tag "loop-native-recur"
        let bindingName := ((← arena).binding pair.1).name
        let opEqualCall ← capture (analyzeCall (.persistentList none [Obj.sym "cpp" "=", bindingName, form])
          frame .statement fnCtx false)
        match opEqualCall with
        | .error e =>
          if !isTraitConvertible expectedType then throw e
          let x ← expectOk (.error e : Except AnalyzeError ExprId)
          opEqualExprs := opEqualExprs ++ [x]
        | .ok x => opEqualExprs := opEqualExprs ++ [x]
      let argType ← typeOf argExpr
      let argExpr ← applyImplicitConversion argExpr argType expectedType
      argExprs := argExprs ++ [argExpr]
      argIndex := argIndex + 1
    if isLoop then
      if let some l := loopLet then
        setE l fun e => match e.data with
          | .let p b _ => { e with data := .let p b .loopWithRecur }
          | _ => e
    else
      liftArena (modifyFnCtx fnCtx.get! fun c => { c with isRecurRecursive := true })
    mkExpr position (some frame) true list
      (.recur (.persistentList none (xs.drop 1)) argExprs opEqualExprs (if isLoop then loopLet else none))

/-- `analyze_do` (processor.cpp:2245). The do's own form is `{}` (nil). -/
partial def analyzeDo (list : Obj) (frame : FrameId) (position : ExprPosition) (fnCtx : Option FnCtxId)
    (needsBox : Bool) : AnR ExprId := do
  let pushed ← pushMacroExpansions list
  popAfter pushed do
    let xs := list.elems.getD []
    let formCount := xs.length - 1
    let mut i := 0
    let mut values : List ExprId := []
    let mut retNeedsBox := true
    for item in xs.drop 1 do
      i := i + 1
      let isLast := i == formCount
      let formType := if isLast then position else .statement
      let form ← analyze item frame formType fnCtx (if formType == .statement then false else needsBox)
      if isLast then retNeedsBox := (← getE form).needsBox
      values := values ++ [form]
    if values.isEmpty then
      let nil ← analyzePrimitiveLiteral .nil frame position fnCtx needsBox
      values := [nil]
    mkExpr position (some frame) retNeedsBox .nil (.do_ values)

/-- `analyze_let` (processor.cpp:2292), also the body of `analyze_loop`. -/
partial def analyzeLet (o : Obj) (currentFrame : FrameId) (position : ExprPosition) (fnCtx : Option FnCtxId)
    (needsBox : Bool) : AnR ExprId := do
  let pushed ← pushMacroExpansions o
  popAfter pushed do
    let xs := o.elems.getD []
    if xs.length < 2 then fail "analyze/invalid-let" "The `let` form requires a bindings vector." o
    let bindings ← match xs[1]! with
      | .persistentVector _ bs => pure bs
      | b => fail "analyze/invalid-let" "The bindings for `let` must be in a vector." b
    if bindings.length % 2 == 1 then
      fail "analyze/invalid-let" "The `let` bindings vector must contain an even number of entries." o
    let frame ← mkFrame .let (some currentFrame)
    let body ← mkExpr position (some frame) needsBox o (.do_ [])
    let ret ← mkExpr position (some frame) needsBox o (.let [] body .normal)
    let mut isLoop := false
    if (← get).loopDetails.isSome && (xs.headD .nil).equiv (Obj.s "loop*") then
      isLoop := true
      modify fun s => { s with loopDetails := some (some ret) }
    let mut i := 0
    while i < bindings.length do
      let symObj := bindings[i]!
      let val := bindings[i + 1]!
      match symObj with
      | .symbol _ sns sname =>
        if !sns.isEmpty then fail "analyze/invalid-let" "The binding symbols in `let` must be unqualified." symObj
        -- 7135b7708 (processor.cpp:2364).
        if sname.startsWith "." then fail "analyze/invalid-cpp-position" (symString symObj) symObj
        let mut valueExpr ← analyze val frame .value fnCtx false
        let mut exprType ← typeOf valueExpr
        if isVoid exprType then
          let v ← getE valueExpr
          valueExpr ← mkExpr v.position v.frame v.needsBox v.form
            (.cppConversion CT.objectRef.toCpp exprType.toCpp valueExpr .intoObject)
          exprType := .objectRef
        if isLoop then
          let oldType := exprType
          exprType := mutableType exprType
          if !isAnyObject oldType && isAnyObject exprType then
            let v ← getE valueExpr
            valueExpr ← mkExpr v.position v.frame v.needsBox v.form
              (.cppConversion exprType.toCpp oldType.toCpp valueExpr .intoObject)
        let nativeName ← withRt fun rt => rt.uniqueString sname
        let vNeedsBox := (← getE valueExpr).needsBox
        let nb : LocalBinding :=
          { name := symObj, nativeName, valueExpr := some valueExpr, originatingFrame := some frame, needsBox := vNeedsBox, isLoopVariable := isLoop, type := exprType.toCpp }
        let b ← pushLocal frame symObj nb
        setE ret fun e => match e.data with
          | .let p bd k => { e with data := .let (p ++ [(b, valueExpr)]) bd k }
          | _ => e
      | _ => fail "analyze/invalid-let" "The left-hand side of each `let` binding must be a symbol." symObj
      i := i + 2
    let formCount := xs.length - 2
    let mut j := 0
    for item in xs.drop 2 do
      j := j + 1
      let isLast := j == formCount
      let formType := if isLast then position else .statement
      let res ← analyze item frame formType fnCtx needsBox
      if isLast then
        let nb := (← getE res).needsBox
        setE ret fun e => { e with needsBox := nb }
      setE body fun e => match e.data with
        | .do_ vs => { e with data := .do_ (vs ++ [res]) }
        | _ => e
    match (← getE body).data with
    | .do_ [] =>
      let retPos := (← getE ret).position
      let nil ← analyzePrimitiveLiteral .nil frame retPos fnCtx needsBox
      setE body fun e => { e with data := .do_ [nil] }
    | _ => pure ()
    pure ret

/-- `analyze_letfn` (processor.cpp:2460). No macro-expansion push. -/
partial def analyzeLetfn (o : Obj) (currentFrame : FrameId) (position : ExprPosition) (fnCtx : Option FnCtxId)
    (needsBox : Bool) : AnR ExprId := do
  let xs := o.elems.getD []
  if xs.length < 2 then fail "analyze/invalid-letfn" "The `letfn*` form requires a bindings vector." o
  let bindings ← match xs[1]! with
    | .persistentVector _ bs => pure bs
    | b => fail "analyze/invalid-letfn" "The bindings for `letfn*` must be in a vector." b
  if bindings.length % 2 == 1 then
    fail "analyze/invalid-letfn" "The `letfn*` bindings vector must contain an even number of entries." o
  let frame ← mkFrame .letfn (some currentFrame)
  let body ← mkExpr position (some frame) needsBox o (.do_ [])
  let ret ← mkExpr position (some frame) needsBox o (.letfn [] body)
  let mut i := 0
  while i < bindings.length do
    let symObj := bindings[i]!
    match symObj with
    | .symbol _ sns sname =>
      if !sns.isEmpty then fail "analyze/invalid-letfn" "The binding symbols in `letfn*` must be unqualified." symObj
      -- 7135b7708 (processor.cpp:2528).
      if sname.startsWith "." then fail "analyze/invalid-cpp-position" (symString symObj) symObj
      let _ ← pushLocal frame symObj { name := symObj, nativeName := sname, valueExpr := none,
                                       originatingFrame := some currentFrame }
    | _ => fail "analyze/invalid-letfn" "The left-hand side of each `letfn*` binding must be a symbol." symObj
    i := i + 2
  i := 0
  while i < bindings.length do
    let symObj := bindings[i]!
    let val := bindings[i + 1]!
    let fexpr ← analyze val frame .value fnCtx false
    if (← getE fexpr).kind != .function then
      fail "analyze/invalid-letfn" "The right-hand side of each `letfn*` binding must be a function." val
    let exprType := nonVoidExpressionType (← arena) fexpr
    -- `locals.find(sym)->second.back()`: the latest binding of that name.
    let a ← arena
    let bid := match (a.frame frame).locals.find? (fun (k, _) => symKey k == symKey symObj) with
      | some (_, bs) => bs.getLast?.getD 0
      | none => 0
    let fnb := (← getE fexpr).needsBox
    liftArena (modifyBinding bid fun b => { b with valueExpr := some fexpr, needsBox := fnb, type := exprType.toCpp })
    setE ret fun e => match e.data with
      | .letfn p bd => { e with data := .letfn (p ++ [(bid, fexpr)]) bd }
      | _ => e
    i := i + 2
  let formCount := xs.length - 2
  let mut j := 0
  for item in xs.drop 2 do
    j := j + 1
    let isLast := j == formCount
    let formType := if isLast then position else .statement
    let res ← analyze item frame formType fnCtx needsBox
    if isLast then
      let nb := (← getE res).needsBox
      setE ret fun e => { e with needsBox := nb }
    setE body fun e => match e.data with
      | .do_ vs => { e with data := .do_ (vs ++ [res]) }
      | _ => e
  match (← getE body).data with
  | .do_ [] =>
    let retPos := (← getE ret).position
    let nil ← analyzePrimitiveLiteral .nil frame retPos fnCtx needsBox
    setE body fun e => { e with data := .do_ [nil] }
  | _ => pure ()
  pure ret

/-- `analyze_loop` (processor.cpp:2603). -/
partial def analyzeLoop (list : Obj) (frame : FrameId) (position : ExprPosition) (fnCtx : Option FnCtxId)
    (_needsBox : Bool) : AnR ExprId := do
  let old := (← get).loopDetails
  modify fun s => { s with loopDetails := some none }
  let r ← capture <| withNoRecur false do
    let l ← analyzeLet list frame .tail fnCtx true
    liftArena (propagatePosition l position)
    setE l fun e => match e.data with
      | .let p b .normal => { e with data := .let p b .loopWithoutRecur }
      | _ => e
    pure l
  modify fun s => { s with loopDetails := old }
  MonadExcept.ofExcept r

/-- `resolve_tail_expression` (processor.cpp:1362). -/
partial def resolveTailExpression (i : ExprId) : AnR ExprId := do
  match (← getE i).data with
  | .do_ vs => match vs.getLast? with
    | some l => resolveTailExpression l
    | none => pure i
  | .let _ body _ =>
    match (← getE body).data with
    | .do_ vs => match vs.getLast? with
      | some l => resolveTailExpression l
      | none => pure i
    | _ => pure i
  | _ => pure i

/-- `analyze_if` (processor.cpp:2644). -/
partial def analyzeIf (o : Obj) (frame : FrameId) (position : ExprPosition) (fnCtx : Option FnCtxId)
    (_needsBox : Bool) : AnR ExprId := do
  let pushed ← pushMacroExpansions o
  popAfter pushed do
    let needsBox := true
    let xs := o.elems.getD []
    let formCount := xs.length
    if formCount < 3 then fail "analyze/invalid-if" "Each `if` form requires a condition and a `then` form." o
    else if formCount > 4 then fail "analyze/invalid-if" "An extra form specified in this 'if'." o
    let mut conditionExpr ← analyze xs[1]! frame .value fnCtx false
    let conditionType ← typeOf conditionExpr
    if !isAnyObject conditionType && !isBool conditionType then
      if isBuiltin conditionType then
        conditionExpr ← applyImplicitConversion conditionExpr conditionType .objectRef
      else
        conditionExpr ← applyImplicitConversion conditionExpr conditionType .bool
    let mut hasRecur := false
    let mut thenExpr ← analyze xs[2]! frame position fnCtx needsBox
    if (← getE (← resolveTailExpression thenExpr)).kind == .recur then hasRecur := true
    let mut elseExprOpt : Option ExprId := none
    if formCount == 4 then
      let elseExpr ← analyze xs[3]! frame position fnCtx needsBox
      if (← getE (← resolveTailExpression elseExpr)).kind == .recur then hasRecur := true
      elseExprOpt := some elseExpr
    let thenType ← typeOf thenExpr
    let elseType? ← match elseExprOpt with
      | some e => pure (some (← typeOf e))
      | none => pure none
    -- `cpp_util::find_branch_common_type` (cpp_util.cpp:1908), processor.cpp:2740.
    match findBranchCommonType thenType elseType? hasRecur with
    | .error msg => fail "analyze/mismatched-if-types" msg o
    | .ok bct =>
      if bct.thenNeedsConversion then
        -- The result is not checked: `then_expr.expect_ok()` below throws an error.
        let r ← capture (applyImplicitConversion thenExpr (← typeOf thenExpr) .objectRef)
        thenExpr ← expectOk r
      if bct.elseNeedsConversion then
        if let some e := elseExprOpt then
          elseExprOpt := some (← applyImplicitConversion e (← typeOf e) .objectRef)
      let chosenType := bct.type
      let finalThenType ← typeOf thenExpr
      let finalElseType ← match elseExprOpt with
        | some e => typeOf e
        | none => pure CT.objectRef
      if !isAnyObject chosenType && (finalThenType != chosenType || finalElseType != chosenType) then tag "if-native-merge"
      mkExpr position (some frame) needsBox o (.if_ chosenType.toCpp conditionExpr thenExpr elseExprOpt)

/-- `analyze_quote` (processor.cpp:2784). -/
partial def analyzeQuote (o : Obj) (frame : FrameId) (position : ExprPosition) (fnCtx : Option FnCtxId)
    (needsBox : Bool) : AnR ExprId := do
  let pushed ← pushMacroExpansions o
  popAfter pushed do
    let xs := o.elems.getD []
    if xs.length != 2 then fail "analyze/invalid-quote" "The `quote` form requires exactly one form to quote." o
    analyzePrimitiveLiteral xs[1]! frame position fnCtx needsBox

/-- `analyze_var_call` (processor.cpp:2807). -/
partial def analyzeVarCall (o : Obj) (frame : FrameId) (position : ExprPosition) (_fnCtx : Option FnCtxId)
    (_needsBox : Bool) : AnR ExprId := do
  let pushed ← pushMacroExpansions o
  popAfter pushed do
    let xs := o.elems.getD []
    if xs.length != 2 then fail "analyze/invalid-var-reference" "The `var` form requires exactly one form to resolve." o
    match xs[1]! with
    | .symbol _ ns name =>
      let rt := (← get).rt
      let (qns, qname) := rt.qualifySymbol ns name
      match rt.findVar qns qname with
      | none => fail "analyze/unresolved-var" s!"This `{qns}/{qname}` cannot be resolved as a var." o
      | some vr => mkExpr position (some frame) true (.symbol none vr.ns vr.name) (.varRef (.symbol none vr.ns vr.name) vr)
    | arg => fail "analyze/invalid-var-reference" "The argument to `var` must be a symbol." arg

/-- `analyze_var_val` (processor.cpp:2852). -/
partial def analyzeVarVal (v : VarRef) (frame : FrameId) (position : ExprPosition) (_fnCtx : Option FnCtxId)
    (_needsBox : Bool) : AnR ExprId := do
  let (qns, qname) := (← get).rt.qualifySymbol v.ns v.name
  mkExpr position (some frame) true (.symbol none qns qname) (.varRef (.symbol none qns qname) v)

/-- `analyze_throw` (processor.cpp:2865). Every type of the universe is copy or move
constructible, so the throwability checks pass. -/
partial def analyzeThrow (o : Obj) (frame : FrameId) (position : ExprPosition) (fnCtx : Option FnCtxId)
    (_needsBox : Bool) : AnR ExprId := do
  let pushed ← pushMacroExpansions o
  popAfter pushed do
    let xs := o.elems.getD []
    if 3 ≤ xs.length then fail "analyze/invalid-throw" "The `throw` form requires at most one argument." o
    if xs.length == 1 then return ← mkExpr position (some frame) true o (.throw_ none)
    let arg ← analyze xs[1]! frame .value fnCtx true
    mkExpr position (some frame) true o (.throw_ (some arg))

/-- `analyze_try` (processor.cpp:2925). -/
partial def analyzeTry (list : Obj) (currentFrame : FrameId) (position : ExprPosition) (fnCtx : Option FnCtxId)
    (_needsBox : Bool) : AnR ExprId := do
  let pushed ← pushMacroExpansions list
  popAfter pushed do
    let tryFrame ← mkFrame .try_ (some currentFrame)
    let finallyFrame ← mkFrame .finally (some currentFrame)
    -- `jtl::make_ref<expr::do_>()`: kind do_, default position (value), no frame, form nil.
    let body ← mkExpr .value none true .nil (.do_ [])
    let ret ← mkExpr position (some tryFrame) true list (.try_ body [] none)
    withNoRecur true do
      let mut hasCatch := false
      let mut hasCatchAll := false
      let mut hasFinally := false
      let items := (list.elems.getD []).drop 1
      let mut idx := 0
      for item in items do
        idx := idx + 1
        let isLast := idx == items.length
        let kind : Nat :=
          if item == .nil || !item.seqable then 0
          else
            let first := item.first
            if first.equiv (Obj.s "catch") then 1 else if first.equiv (Obj.s "finally") then 2 else 0
        if kind == 0 then
          if hasCatch || hasFinally then
            fail "analyze/invalid-try" "No extra forms may appear after `catch` or `finally`." item
          let formType := if isLast then position else .statement
          let form ← analyze item tryFrame formType fnCtx isLast
          setE body fun e => match e.data with
            | .do_ vs => { e with data := .do_ (vs ++ [form]) }
            | _ => e
        else if kind == 1 then
          if hasFinally then fail "analyze/invalid-try" "No 'catch' forms are permitted after a 'finally' form has been been provided." item
          if hasCatchAll then fail "analyze/invalid-try" "No 'catch' forms are permitted after a catch-all (:default) form has been been provided." item
          hasCatch := true
          let catchList := item.elems.getD []
          if catchList.length < 2 then
            fail "analyze/invalid-try" "Each 'catch' form requires the type of exception to catch and a symbol for the name of the exception value." item
          let catchTypeForm := catchList[1]!
          -- `catch_it.first().unwrap()` on an empty rest: the check is a debug assertion only.
          if catchList.length < 3 then
            (throwThe Fault (Fault.ub "(catch T) without a binding symbol: jtl::option::unwrap() on none (processor.cpp:3048)") : AnM Unit)
          let catchSymForm := catchList.getD 2 .nil
          let mut catchType := CT.void
          if catchTypeForm.equiv (kw "default") then hasCatchAll := true
          else
            let r ← capture (analyzeTypeOracle catchTypeForm)
            match r with
            | .error e => fail "analyze/invalid-try" e.message catchTypeForm
            | .ok t =>
              if isVoid t then fail "analyze/invalid-try" "Void is not a valid exception type to catch." catchTypeForm
              catchType := t  -- `get_lvalue_reference_type` (no references in the universe)
          match catchSymForm with
          | .symbol _ cns cname =>
            if !cns.isEmpty then fail "analyze/invalid-try" "The binding symbol in `catch` must be unqualified." item
            -- 7135b7708 (processor.cpp:3105).
            if cname.startsWith "." then fail "analyze/invalid-cpp-position" (symString catchSymForm) catchSymForm
            match (← getE ret).data with
            | .try_ _ cs _ =>
              if cs.any (·.type == catchType.toCpp) then
                fail "analyze/invalid-try" "Each `catch` form must specify a unique exception type." item
            | _ => pure ()
            let isObject := isAnyObject catchType
            let catchFrame ← mkFrame .catch_ (some currentFrame)
            let cb : LocalBinding :=
              { name := catchSymForm, nativeName := cname, valueExpr := none, originatingFrame := some catchFrame, needsBox := isObject, type := catchType.toCpp }
            let _ ← pushLocal catchFrame catchSymForm cb
            let doList : Obj := .persistentList none (Obj.s "do" :: catchList.drop 3)
            let doRes ← analyze doList catchFrame position fnCtx true
            setE doRes fun e => { e with frame := some catchFrame }
            setE ret fun e => match e.data with
              | .try_ b cs f => { e with data := .try_ b (cs ++ [⟨catchSymForm, catchType.toCpp, doRes⟩]) f }
              | _ => e
          | _ => fail "analyze/invalid-try" "A symbol is required after 'catch', which is used as the binding to hold the exception value." item
        else
          if hasFinally then fail "analyze/invalid-try" "Only one `finally` form may be supplied." item
          hasFinally := true
          let finallyList := item.elems.getD []
          let doList : Obj := .persistentList none (Obj.s "do" :: finallyList.drop 1)
          let doRes ← analyze doList finallyFrame .statement fnCtx false
          setE ret fun e => match e.data with
            | .try_ b cs _ => { e with data := .try_ b cs (some doRes) }
            | _ => e
      if !hasCatch && !hasFinally then return body
      setE body fun e => { e with frame := some tryFrame }
      liftArena (propagatePosition body position)
      match (← getE ret).data with
      | .try_ _ _ (some f) => setE f fun e => { e with frame := some finallyFrame }
      | _ => pure ()
      let ensureBoxedReturn : ExprId → AnR Unit := fun doId => do
        match (← getE doId).data with
        | .do_ vs =>
          if let some last := vs.getLast? then
            let t ← typeOf last
            let n ← applyImplicitConversion last t .objectRef
            setE doId fun e => { e with data := .do_ (vs.dropLast ++ [n]) }
        | _ => pure ()
      ensureBoxedReturn body
      match (← getE ret).data with
      | .try_ _ cs _ => for c in cs do ensureBoxedReturn c.body
      | _ => pure ()
      pure ret

/-- `analyze_primitive_literal` (processor.cpp:3234). -/
partial def analyzePrimitiveLiteral (o : Obj) (frame : FrameId) (position : ExprPosition) (_fnCtx : Option FnCtxId)
    (needsBox : Bool) : AnR ExprId := do
  let pushed ← pushMacroExpansions o
  popAfter pushed do
    let t := literalType o false
    if isAnyObject t then mkExpr position (some frame) needsBox o (.primitiveLiteral o)
    else mkExpr position (some frame) needsBox o (.cppLiteral o)

/-- `analyze_vector` (processor.cpp:3251). A vector of literals with no meta is evaluated at
analysis (`evaluate::eval`) into one literal. -/
partial def analyzeVector (o : Obj) (frame : FrameId) (position : ExprPosition) (fnCtx : Option FnCtxId)
    (_needsBox : Bool) : AnR ExprId := do
  let pushed ← pushMacroExpansions o
  popAfter pushed do
    let md ← analyzeCollectionMeta o.getMeta frame fnCtx
    let mut exprs : List ExprId := []
    let mut literal := md.isNone
    for d in o.elems.getD [] do
      let r ← analyze d frame .value fnCtx true
      let r ← applyImplicitConversion r (← typeOf r) .objectRef
      exprs := exprs ++ [r]
      if (← getE r).kind != .primitiveLiteral then literal := false
    if literal then
      let pre ← mkExpr position (some frame) true o (.vector exprs md)
      let v ← evalConst pre
      mkExpr position (some frame) true o (.primitiveLiteral v)
    else mkExpr position (some frame) true o (.vector exprs md)

/-- `analyze_map` (processor.cpp:3302). No literal detection. -/
partial def analyzeMap (o : Obj) (frame : FrameId) (position : ExprPosition) (fnCtx : Option FnCtxId)
    (_needsBox : Bool) : AnR ExprId := do
  let pushed ← pushMacroExpansions o
  popAfter pushed do
    let md ← analyzeCollectionMeta o.getMeta frame fnCtx
    let kvs := match o with
      | .persistentArrayMap _ kvs | .persistentHashMap _ kvs | .persistentSortedMap _ kvs => kvs
      | _ => []
    let mut exprs : List (ExprId × ExprId) := []
    for (k, v) in kvs do
      let ke ← analyze k frame .value fnCtx true
      let ke ← applyImplicitConversion ke (← typeOf ke) .objectRef
      let ve ← analyze v frame .value fnCtx true
      let ve ← applyImplicitConversion ve (← typeOf ve) .objectRef
      exprs := exprs ++ [(ke, ve)]
    mkExpr position (some frame) true o (.map exprs md)

/-- `analyze_set` (processor.cpp:3363). The literal check ignores the meta (unlike vectors). -/
partial def analyzeSet (o : Obj) (frame : FrameId) (position : ExprPosition) (fnCtx : Option FnCtxId)
    (_needsBox : Bool) : AnR ExprId := do
  let pushed ← pushMacroExpansions o
  popAfter pushed do
    let md ← analyzeCollectionMeta o.getMeta frame fnCtx
    let mut exprs : List ExprId := []
    let mut literal := true
    for d in o.elems.getD [] do
      let r ← analyze d frame .value fnCtx true
      let r ← applyImplicitConversion r (← typeOf r) .objectRef
      exprs := exprs ++ [r]
      if (← getE r).kind != .primitiveLiteral then literal := false
    if literal then
      let pre ← mkExpr position (some frame) true o (.set exprs md)
      let c ← evalConst pre
      mkExpr position (some frame) true o (.primitiveLiteral c)
    else mkExpr position (some frame) true o (.set exprs md)

/-- `evaluate::eval` of the constant collections `analyze_vector`/`analyze_set` evaluate
(evaluate.cpp:411-509): literals and collections of them, with their meta. -/
partial def evalConst (i : ExprId) : AnR Obj := do
  let e ← getE i
  match e.data with
  | .primitiveLiteral d => pure d
  | .cppLiteral d => pure d
  | .vector xs md => do
    let vs ← xs.mapM evalConst
    let m ← md.mapM evalConst
    pure (.persistentVector m vs)
  | .set xs md => do
    let vs ← xs.mapM evalConst
    let m ← md.mapM evalConst
    pure (.persistentHashSet m (vs.foldl (fun acc v => if acc.any (·.equiv v) then acc else acc ++ [v]) []))
  | .map kvs md => do
    let vs ← kvs.mapM fun (k, v) => do pure (← evalConst k, ← evalConst v)
    let m ← md.mapM evalConst
    pure (.persistentArrayMap m vs)
  | .list xs md => do
    let vs ← xs.mapM evalConst
    let m ← md.mapM evalConst
    pure (.persistentList m vs)
  | .cppConversion _ _ v _ => evalConst v
  | _ => (throwThe Fault (Fault.thrown { kind := "model/unmodeled", message := "eval of a non-constant" }) : AnM Obj)

/-- `analyze_call` (processor.cpp:3421). -/
partial def analyzeCall (o : Obj) (frame : FrameId) (position : ExprPosition) (fnCtx : Option FnCtxId)
    (needsBox : Bool) : AnR ExprId := do
  let xs := o.elems.getD []
  let count := xs.length
  if count == 0 then
    let md ← analyzeCollectionMeta o.getMeta frame fnCtx
    match md with
    | some m => return ← mkExpr position (some frame) needsBox o (.list [] (some m))
    | none => return ← analyzePrimitiveLiteral o frame position fnCtx needsBox
  let argCount := count - 1
  let first := xs.head!
  let needsRetBox := true
  let needsArgBox := true
  let mut pushed := false
  match first with
  | .symbol _ ns name =>
    if let some sp := specialOf ns name then
      return ← analyzeSpecial sp o frame position fnCtx needsBox
    pushed ← pushMacroExpansions o
  | .keyword .. =>
    if count ≤ 3 then
      -- `(:k m d)` → `(cpp/jank.runtime.get m :k d)`
      let rest := xs.drop 1
      let callForm : Obj := consObj (Obj.sym "cpp" "jank.runtime.get")
        (consObj (rest.headD .nil) (consObj first (.persistentList none (rest.drop 1))))
      return ← analyze callForm frame position fnCtx needsBox
    pushed ← pushMacroExpansions o
  | _ => pushed ← pushMacroExpansions o
  popAfter pushed do
    let sourceR : Sum ExprId ExprId ← match first with
    | .symbol .. => do
      let source ← analyzeSymbol first frame .call fnCtx true
      let se ← getE source
      if se.kind == .cppType then
        fail "model/unmodeled" "constructor call through a C++ type" o
      if se.kind.isCpp || !isAnyObject (← typeOf source) then
        return ← analyzeCppCall o source frame position fnCtx needsBox
      if se.kind != .localReference then
        let rt := (← get).rt
        if se.kind == .recursionReference && macroexpand1Changes rt o then tag "macro-over-fn-name"
        match macroexpand rt 1000 o with
        | .error msg => fail "analyze/macro-expansion-exception" msg o
        | .ok expanded =>
          if macroexpand1Changes rt o then
            return ← analyze expanded frame position fnCtx needsBox
      match se.data with
      | .varDeref _ vr =>
        let v := ((← get).rt.var? vr).getD { ns := vr.ns, name := vr.name }
        let arityOk := match v.inlineArities with
          | none => true
          | some ars => ars.contains argCount
        if arityOk then
          if let some inl := v.inline then
            match inl (xs.drop 1) with
            | .error msg => (throwThe Fault (Fault.thrown { kind := "inline", message := msg }) : AnM Unit)
            | .ok expanded =>
              -- 7135b7708 (processor.cpp:3561-3563): the inline result's own meta merged with the call's.
              let merged := match expanded.getMeta, o.getMeta with
                | none, m => m.getD .nil
                | some em, none => em
                | some em, some m => (match m with
                    | .persistentArrayMap _ kvs | .persistentHashMap _ kvs => kvs.foldl (fun acc (k, v) => acc.assoc k v) em
                    | _ => em)
              let expanded := withMetaGraceful expanded merged
              return ← analyze expanded frame position fnCtx needsBox
      | _ => pure ()
      pure (Sum.inr source)
    | _ => do
      let callable ← analyze first frame .call fnCtx needsBox
      if (← getE callable).kind == .cppType then fail "model/unmodeled" "constructor call through a C++ type" o
      if !isAnyObject (← typeOf callable) then
        return ← analyzeCppCall o callable frame position fnCtx needsBox
      pure (Sum.inr callable)
    let source ← match sourceR with
      | .inl done => return done
      | .inr s => pure s
    let mut argExprs : List ExprId := []
    let args := xs.drop 1
    for a in args.take 10 do
      let ae ← analyze a frame .value fnCtx needsArgBox
      let ae ← applyImplicitConversion ae (← typeOf ae) .objectRef
      argExprs := argExprs ++ [ae]
    if 10 < argCount then
      let mut packed : List ExprId := []
      for a in args.drop 10 do
        let ae ← analyze a frame .value fnCtx needsArgBox
        let ae ← applyImplicitConversion ae (← typeOf ae) .objectRef
        packed := packed ++ [ae]
      let l ← mkExpr .value (some frame) needsArgBox o (.list packed none)
      argExprs := argExprs ++ [l]
    match (← getE source).data with
    | .recursionReference _ =>
      mkExpr position (some frame) needsRetBox o (.namedRecursion source (.persistentList none args) argExprs)
    | _ => mkExpr position (some frame) needsRetBox o (.call source argExprs o)

/-- Whether `macroexpand` changed the form (`expanded != o`). -/
partial def macroexpand1Changes (rt : Runtime) (o : Obj) : Bool :=
  match macroexpand1Step rt o with
  | .ok (some _) => true
  | _ => false

/-- The `specials()` dispatch (processor.cpp:3466). -/
partial def analyzeSpecial (sp : Special) (o : Obj) (frame : FrameId) (position : ExprPosition)
    (fnCtx : Option FnCtxId) (needsBox : Bool) : AnR ExprId :=
  match sp with
  | .def => analyzeDef o frame position fnCtx needsBox
  | .fn => analyzeFn o frame position fnCtx needsBox
  | .recur => analyzeRecur o frame position fnCtx needsBox
  | .do_ => analyzeDo o frame position fnCtx needsBox
  | .let_ => analyzeLet o frame position fnCtx needsBox
  | .letfn => analyzeLetfn o frame position fnCtx needsBox
  | .loop => analyzeLoop o frame position fnCtx needsBox
  | .if_ => analyzeIf o frame position fnCtx needsBox
  | .quote => analyzeQuote o frame position fnCtx needsBox
  | .var => analyzeVarCall o frame position fnCtx needsBox
  | .throw => analyzeThrow o frame position fnCtx needsBox
  | .try_ => analyzeTry o frame position fnCtx needsBox
  | .case_ => analyzeCase o frame position fnCtx needsBox
  | _ => fail "model/unmodeled" "cpp special form (interop agent)" o

/-- `analyze_cpp_call` (processor.cpp:4055) and `build_cpp_call`'s operator branch
(processor.cpp:368), for `cpp/=` and `cpp/jank.runtime.<fn>` (oracle; assumption A4). -/
partial def analyzeCppCall (o : Obj) (source : ExprId) (frame : FrameId) (position : ExprPosition)
    (fnCtx : Option FnCtxId) (needsBox : Bool) : AnR ExprId := do
  let args := (o.elems.getD []).drop 1
  let mut argExprs : List ExprId := []
  let mut argTypes : List CT := []
  for a in args do
    let ae ← analyze a frame .value fnCtx true
    argExprs := argExprs ++ [ae]
    argTypes := argTypes ++ [← typeOf ae]
  let se ← getE source
  match se.data with
  | .cppValue _ sym _ scope .operatorCall =>
    let opName := (symKey sym).2
    if argExprs.isEmpty then fail "analyze/invalid-cpp-operator-call" "An operator call requires an invoking object." o
    if argExprs.length > 2 then fail "analyze/invalid-cpp-operator-call" "Operator calls may only take one or two arguments." o
    let objType := argTypes[0]!
    let builtin (ts : List CT) (es : List ExprId) : AnR ExprId := do
      let classAssign := (← get).oracle.classBuiltinAssign
      let l := ts.headD .void
      let r := ts.getLast?.getD .void
      let resultType : Option CT :=
        if opName == "=" then
          (if ts.length == 2 && builtinAssignOk l r then some l
           else if ts.length == 2 && classAssign && isAnyObject l && isAnyObject r then some l else none)
        else if ts.all isArithmetic then
          (if opName == "<" then some .bool else getCommonType l r)
        else none
      let msg := s!"The binary operator `{opName}` is not supported for the types `{l.spelling}` and `{r.spelling}`."
      if opName == "=" && isAnyObject l then tag "op-equal-object-builtin"
      match resultType with
      | some t => mkExpr position (some frame) needsBox o (.cppBuiltinOperatorCall 0 es t.toCpp)
      | none => fail "analyze/invalid-cpp-operator-call" msg o
    if isPrimitive objType then
      if argTypes.length == 1 || isPrimitive argTypes[1]! then
        return ← builtin argTypes argExprs
      else if !isAnyObject objType && isTraitConvertible objType && isAnyObject argTypes[1]! then
        let c ← applyImplicitConversion argExprs[1]! argTypes[1]! objType
        return ← builtin [objType, objType] [argExprs[0]!, c]
    else if argTypes.length == 2 && !isAnyObject argTypes[1]! && isTraitConvertible argTypes[1]!
            && isAnyObject objType then
      let c ← applyImplicitConversion argExprs[1]! argTypes[1]! objType
      return ← builtin [objType, objType] [argExprs[0]!, c]
    -- `get_operator`: an object's member `operator=` (both objects).
    if opName == "=" && isAnyObject objType && argTypes.length == 2 && isAnyObject argTypes[1]! then
      return ← mkExpr position (some frame) needsBox o (.cppMemberCall objType.toCpp .null argExprs)
    let _ := scope
    fail "analyze/invalid-cpp-operator-call" s!"The operator `{opName}` is not supported for the type `{objType.spelling}`." o
  | .cppValue _ _ _ (.named fname) .function =>
    -- Overloads of jank's C++ runtime functions (core/math.hpp templates on native numbers,
    -- `object_ref` otherwise).
    let ret : CT :=
      if fname == "jank.runtime.inc" || fname == "jank.runtime.dec" then
        match argTypes with
        | [t] => if t == .int || t == .long || t == .bool then .long else if t == .double then .double else .objectRef
        | _ => .objectRef
      else if fname == "jank.runtime.add" || fname == "jank.runtime.sub" || fname == "jank.runtime.mul" then
        match argTypes with
        | [a, b] => if isArithmetic a && isArithmetic b then (getCommonType a b).getD .objectRef else .objectRef
        | _ => .objectRef
      else if fname == "jank.runtime.lt" || fname == "jank.runtime.is_equiv" || fname == "jank.runtime.is_pos"
              || fname == "jank.runtime.is_nil" || fname == "jank.runtime.is_some" then .bool
      else .objectRef
    if (fname == "jank.runtime.inc" || fname == "jank.runtime.add" || fname == "jank.runtime.mul") && argTypes.contains .bool then tag "bool-arith"
    if (fname == "jank.runtime.add" || fname == "jank.runtime.mul") && argTypes == [.int, .int] then tag "int-arith"
    let templated := fname == "jank.runtime.inc" || fname == "jank.runtime.dec" || fname == "jank.runtime.add"
      || fname == "jank.runtime.sub" || fname == "jank.runtime.mul" || fname == "jank.runtime.lt"
    let mut finalArgs : List ExprId := []
    for (ae, t) in argExprs.zip argTypes do
      if templated && (isArithmetic t || isAnyObject t) then finalArgs := finalArgs ++ [ae]
      else finalArgs := finalArgs ++ [← applyImplicitConversion ae t .objectRef]
    mkExpr position (some frame) needsBox o (.cppCall ret.toCpp source finalArgs "")
  | _ =>
    let st ← typeOf source
    if !isAnyObject st && isArithmetic st then
      -- A native number in call position (`build_indirect_cpp_call`, processor.cpp:873; modeled).
      tag "native-callee"
      fail "analyze/invalid-cpp-call" s!"Values of type `{st.spelling}` are not callable." o
    fail "model/unmodeled" "C++ call (interop agent)" o

end

/-! ## Entry points -/

/-- `processor::processor()` (processor.cpp:1219): a root frame. -/
def initialState (rt : Runtime) (oracle : Oracle := {}) : AnState :=
  let (a, root) := ({} : Arena).addFrame { type := .root }
  { arena := a, rt, rootFrame := root, oracle }

/-- `processor::analyze(o, position)` (processor.cpp:4844). -/
def analyzeTop (o : Obj) (position : ExprPosition) : AnR ExprId := do
  analyze o (← get).rootFrame position none true

/-- `processor::analyze(parse_current, parse_end)` (processor.cpp:1224): every form of the stream
in one anonymous `(fn* [] forms...)`. -/
def analyzeForms (forms : List Obj) : AnR ExprId :=
  analyzeTop (.persistentList none (Obj.s "fn*" :: .persistentVector none [] :: forms)) .value

/-- `pass::strip_source_meta` (pass/strip_source_meta.cpp): every `primitive_literal`'s data keeps
its meta without `:jank/source`. -/
def stripSourceMeta (root : ExprId) : AnR ExprId := do
  let a ← arena
  let ids := postwalk a (fun i acc => acc ++ [i]) 100000 root []
  for i in ids do
    match ((← arena).expr i).data with
    | .primitiveLiteral d =>
      if d.metadatable then
        let m := match d.getMeta with | some m => stripSourceFromMeta m | none => .nil
        let d' := d.setMeta (some m)
        setE i fun e => { e with data := .primitiveLiteral d' }
    | _ => pure ()
  pure root

/-- `pass::optimize` (pass/optimize.cpp:11). -/
def optimize (root : ExprId) : AnR ExprId := stripSourceMeta root

/-- Runs an analysis: the result and the final state. -/
def runAnalysis {α : Type} (k : AnR α) (s : AnState) : Except Fault (Except AnalyzeError α) × AnState :=
  match (ExceptT.run k).run s with
  | .ok r s' => (.ok r, s')
  | .error f s' => (.error f, s')

end Jank.Analyzer
