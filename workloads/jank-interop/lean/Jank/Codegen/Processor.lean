import Jank.Codegen.Ir

/-!
# Expressions to IR: `src/cpp/jank/ir/processor.cpp` (jank 7135b7708)

One Lean definition per C++ `gen` overload, in the C++ order of effects. Recursion carries
`fuel` (the expression tree's depth bounds it). `jtl::option::unwrap` of `none` and `.at` on a
missing key are `jank_panic`s: here `throw` (the compiler crashes, no code is produced).

The analyzer's tree is `Jank.Analyzer.Arena` (the analyzer agent's replica); IR generation
mutates it (`propagate_position`), as in C++.
-/

namespace Jank.Codegen

open Jank.Analyzer

def exprAt (id : ExprId) : GenM Expr := do
  match (← get).g.arena.exprs[id]? with
  | some e => pure e
  | none => throw s!"no expression {id}"

def setExpr (id : ExprId) (e : Expr) : GenM Unit :=
  modify fun s => { s with g := { s.g with arena := { s.g.arena with
    exprs := s.g.arena.exprs.set! id e } } }

def bindingAt (id : BindingId) : GenM LocalBinding := do
  match (← get).g.arena.bindings[id]? with
  | some b => pure b
  | none => throw s!"no binding {id}"

def frameAt (id : FrameId) : GenM LocalFrame := do
  match (← get).g.arena.frames[id]? with
  | some f => pure f
  | none => throw s!"no frame {id}"

def fnCtxAt (id : FnCtxId) : GenM FunctionContext := do
  match (← get).g.arena.fnCtxs[id]? with
  | some f => pure f
  | none => throw s!"no fn context {id}"

/-- A symbol's name (`symbol::get_name`). -/
def symName : Obj → String
  | .symbol _ _ n => n
  | _ => ""

def symMeta : Obj → Obj
  | .symbol (some m) _ _ => m
  | _ => .nil

/-- `symbol::to_code_string` for an unqualified or qualified symbol: `ns/name` or `name`. -/
def symCode : Obj → String
  | .symbol _ ns n => if ns.isEmpty then n else ns ++ "/" ++ n
  | _ => ""

/-- `expression::propagate_position` and its overrides (expression.cpp:41, do.cpp:33,
if.cpp:24, let.cpp:19, letfn.cpp:19, try.cpp:34, case.cpp:29). -/
def propagatePosition : Nat → ExprId → ExprPosition → GenM Unit
  | 0, _, _ => throw "fuel"
  | fuel + 1, id, pos => do
    let e ← exprAt id
    setExpr id { e with position := pos }
    match e.data with
    | .do_ values => if let some l := values.getLast? then propagatePosition fuel l pos
    | .if_ _ _ t el => do
      propagatePosition fuel t pos
      if let some x := el then propagatePosition fuel x pos
    | .let _ body _ => propagatePosition fuel body pos
    | .letfn _ body => propagatePosition fuel body pos
    | .try_ body catches _ => do
      propagatePosition fuel body pos
      for c in catches do propagatePosition fuel c.body pos
    | .case_ _ _ _ d _ exprs => do
      propagatePosition fuel d pos
      for x in exprs do propagatePosition fuel x pos
    | _ => pure ()

/-- `expression::get_type` and its overrides for the non-interop kinds (expression.cpp:59,
do.cpp:64, if.cpp:56, let.cpp:53, letfn.cpp:53, local_reference.cpp:29,
primitive_literal.cpp:27, and, new in 7135b7708, case.cpp:71 `case_::get_type`).
`cpp_util::expression_type(e)` is `e->get_type()` (cpp_util.cpp:1051).

The analyzer agent's `ExprData.case_` has no `type` field; the type `analyze_case` stores
(analyze/processor.cpp:1483-1579: the `find_branch_common_type` of the last key's expression and
the default) is recomputed here from the children, which gives the same type: after the
conversions it applies, the children have that type. -/
def exprType : Nat → ExprId → GenM CppType
  | 0, _ => throw "fuel"
  | fuel + 1, id => do
    let e ← exprAt id
    match e.data with
    | .do_ values => match values.getLast? with
      | some l => exprType fuel l
      | none => pure Ty.objectRef
    | .if_ t _ _ _ => pure t
    | .let _ body _ => exprType fuel body
    | .letfn _ body => exprType fuel body
    | .localReference _ b => pure (← bindingAt b).type
    | .case_ _ _ _ d _ exprs => do
      let dt ← exprType fuel d
      let mut chosen := dt
      for x in exprs do
        chosen := (findBranchCommonType (← exprType fuel x) (some dt)).1
      pure chosen
    | .primitiveLiteral d => pure (literalTypeBoxed d)
    | .cppLiteral d => pure (literalTypeBoxed d)
    | .cppConversion t _ _ _ | .cppUnsafeCast t _ | .cppCall t _ _ _
    | .cppConstructorCall t _ _ _ | .cppMemberAccess t _ _ _ | .cppBuiltinOperatorCall _ _ t
    | .cppUnbox t _ _ | .cppNew t _ | .cppValue _ _ t _ _ | .cppType _ t => pure t
    | _ => pure Ty.objectRef

/-- `arity_flags(arities)` (processor.cpp:339-369) with `runtime::build_arity_flags`
(call.hpp: `(is_variadic << 7) | (is_variadic_ambiguous << 6) | highest_fixed_arity`, a `u8`). -/
def arityFlags (arities : List FunctionArity) : GenM Nat := do
  let mut variadic : Option FunctionContext := none
  let mut highest : Option FunctionContext := none
  for a in arities do
    let c ← fnCtxAt a.fnCtx
    if c.isVariadic then variadic := some c
    else if highest.isNone || (highest.map (·.paramCount) |>.getD 0) < c.paramCount then
      highest := some c
  match variadic with
  | some v =>
    let ambiguous := match highest with
      | some h => h.paramCount == v.paramCount - 1
      | none => false
    pure (((1 <<< 7) ||| ((if ambiguous then 1 else 0) <<< 6) ||| (v.paramCount.toNat - 1)) % 256)
  | none =>
    match highest with
    | some h => pure (h.paramCount.toNat % 256)
    | none => throw "jank_assert: highest_fixed_arity != nullptr"

/-- The locals map's `operator[]`: the value, or a default-inserted empty identifier. -/
def localsIndex (k : String) : GenM Ident := do
  let s ← get
  match assocGet? s.b.locals k with
  | some v => pure v
  | none =>
    set { s with b := { s.b with locals := s.b.locals ++ [(k, "")] } }
    pure ""

def setLocalName (k : String) (v : Ident) : GenM Unit :=
  modify fun s => { s with b := { s.b with locals := assocSet s.b.locals k v } }

/-- `local_to_loop_shadow[name]` (`operator[]`: default-inserted empty when missing). -/
def shadowIndex (k : String) : GenM Ident := do
  let s ← get
  match assocGet? s.b.localToLoopShadow k with
  | some v => pure v
  | none =>
    set { s with b := { s.b with localToLoopShadow := s.b.localToLoopShadow ++ [(k, "")] } }
    pure ""

def setShadow (k : String) (v : Ident) : GenM Unit :=
  modify fun s => { s with b := { s.b with localToLoopShadow := assocSet s.b.localToLoopShadow k v } }

def unwrapI (o : Option Ident) (what : String) : GenM Ident :=
  match o with
  | some v => pure v
  | none => throw s!"panic: unwrap of none ({what})"

def hasTerminator : GenM Bool := do pure (← curBlock).hasTerminator

/-- `function::captures()` (function.cpp:53-64): every arity's `frame->captures`, first
occurrence of each symbol kept (`emplace`). -/
def fnCaptures (arities : List FunctionArity) : GenM (List (Obj × BindingId)) := do
  let mut ret : List (Obj × BindingId) := []
  for a in arities do
    if let some fr := a.frame then
      for (sym, cap) in (← frameAt fr).captures do
        if !(ret.any fun p => p.1 == sym) then ret := ret ++ [(sym, cap.binding)]
  pure ret

mutual

/-- `gen(expression_ref)` (processor.cpp:976-985): dispatch on the kind. -/
partial def gen (fuel : Nat) (id : ExprId) : GenM (Option Ident) := do
  if fuel == 0 then throw "fuel"
  let fuel := fuel - 1
  let e ← exprAt id
  match e.data with
  | .def name value => genDef fuel e name value
  | .varDeref _ v => some <$> bVarDeref e.position s!"{v.ns}/{v.name}"
  | .varRef _ v => some <$> bVarRef e.position s!"{v.ns}/{v.name}"
  | .call src args _ => genCall fuel e src args
  | .primitiveLiteral d => some <$> bLiteral e.position d
  | .list xs m => genColl fuel e xs m fun n vs mm => .persistentList n vs mm
  | .vector xs m => genColl fuel e xs m fun n vs mm => .persistentVector n vs mm
  | .set xs m => genColl fuel e xs m fun n vs mm => .persistentHashSet n vs mm
  | .map kvs m => genMap fuel e kvs m
  | .localReference name b => genLocalReference fuel id e name b
  | .function .. => genFunction fuel e
  | .recur _ args _ loopTarget => genRecur fuel args loopTarget
  | .recursionReference ctx => genRecursionReference fuel id e ctx
  | .namedRecursion rr _ args => genNamedRecursion fuel e rr args
  | .let pairs body kind => genLet fuel id e pairs body kind
  | .letfn pairs body => genLetfn fuel pairs body
  | .do_ values => genDo fuel e values
  | .if_ _ c t el => genIf fuel id e c t el
  | .throw_ v => genThrow fuel e v
  | .try_ body catches fin => genTry fuel id e body catches fin
  | .case_ v shift mask d keys exprs => genCase fuel id e v shift mask d keys exprs
  | .cppType .. =>
    throw "codegen_internal_failure: A cpp_type expression was found during codegen"
  | .uninitialized => throw "uninitialized expression"
  | d => genCppOpaque fuel id e d

/-- `gen(expr::def_ref)` (processor.cpp:82-96). -/
partial def genDef (fuel : Nat) (e : Expr) (name : Obj) (value : Option ExprId) :
    GenM (Option Ident) := do
  let mut vi : Option Ident := none
  if let some v := value then vi ← gen fuel v
  let mta := symMeta name
  let dyn := match mta with
    | .persistentArrayMap _ kvs | .persistentHashMap _ kvs =>
      match kvs.find? (fun p => p.1 == .keyword "" "dynamic") with
      | some (_, v) => match v with | .nil => false | .boolean false => false | _ => true
      | none => false
    | _ => false
  some <$> bDef e.position (symCode name) vi mta dyn

/-- `gen(expr::call_ref)` (processor.cpp:110-121): the arguments first, then the function. -/
partial def genCall (fuel : Nat) (e : Expr) (src : ExprId) (args : List ExprId) :
    GenM (Option Ident) := do
  let mut argIdents : List Ident := []
  for a in args do argIdents := argIdents ++ [← unwrapI (← gen fuel a) "call arg"]
  let fnIdent ← unwrapI (← gen fuel src) "call source"
  some <$> bDynamicCall e.position fnIdent argIdents

/-- `gen(expr::list_ref)`, `vector_ref`, `set_ref` (processor.cpp:128-162, 186-202). -/
partial def genColl (fuel : Nat) (e : Expr) (xs : List ExprId) (m : Option ExprId)
    (mk : Ident → List Ident → Option Ident → Inst) : GenM (Option Ident) := do
  let mut values : List Ident := []
  for x in xs do values := values ++ [← unwrapI (← gen fuel x) "collection value"]
  let mut mta : Option Ident := none
  if let some mm := m then mta := some (← unwrapI (← gen fuel mm) "meta")
  some <$> bColl e.position fun n => mk n values mta

/-- `gen(expr::map_ref)` (processor.cpp:164-184): an array map up to 8 pairs, else a hash map. -/
partial def genMap (fuel : Nat) (e : Expr) (kvs : List (ExprId × ExprId)) (m : Option ExprId) :
    GenM (Option Ident) := do
  let mut values : List (Ident × Ident) := []
  for (k, v) in kvs do
    let ki ← unwrapI (← gen fuel k) "map key"
    let vi ← unwrapI (← gen fuel v) "map value"
    values := values ++ [(ki, vi)]
  let mut mta : Option Ident := none
  if let some mm := m then mta := some (← unwrapI (← gen fuel mm) "meta")
  if kvs.length ≤ arrayMapMaxSize then
    some <$> bColl e.position fun n => .persistentArrayMap n values mta
  else some <$> bColl e.position fun n => .persistentHashMap n values mta

/-- `gen(expr::local_reference_ref)` (processor.cpp:204-223): looked up by the munged name. -/
partial def genLocalReference (fuel : Nat) (id : ExprId) (e : Expr) (name : Obj) (_b : BindingId) :
    GenM (Option Ident) := do
  let localName := munge (symName name)
  let s ← get
  match assocGet? s.b.locals localName with
  | some l =>
    if e.position == .tail then some <$> bRet l (← exprType fuel id)
    else pure (some l)
  | none =>
    if s.b.allowedDefers.contains localName then pure (some ":defer")
    else pure none

/-- `gen_arity` (processor.cpp:225-337). Returns the C function name. -/
partial def genArity (fuel : Nat) (fnExpr : Expr) (arity : FunctionArity) : GenM String := do
  let (fnName, uniqueName) := match fnExpr.data with
    | .function n u .. => (n, u)
    | _ => ("", "")
  let name := munge (formatTo "{}_{}" [uniqueName, toString arity.params.length])
  let ctx ← fnCtxAt arity.fnCtx
  let caps ← match arity.frame with
    | some fr => do
      let f ← frameAt fr
      let mut cs : List (String × CppType) := []
      for (sym, cap) in f.captures do cs := cs ++ [(symName sym, (← bindingAt cap.binding).type)]
      pure cs
    | none => pure []
  let bodyVals ← match (← exprAt arity.body).data with
    | .do_ vs => pure vs
    | _ => pure [arity.body]
  let info : ArityInfo :=
    { params := arity.params.map fun p => (symName p.name, p.type), captures := caps,
      fnName := fnName, fnUniqueName := uniqueName, paramCount := ctx.paramCount.toNat,
      bodyEmpty := bodyVals.isEmpty, fnCtx := arity.fnCtx }
  -- `mod.functions.emplace_back(mod.functions.size(), &arity)`, then a new builder.
  let s0 ← get
  let idx := s0.g.mod.functions.size
  let f : IrFn := { index := idx, arity := info, name := name, blocks := #[{ index := 0, name := "entry" }] }
  let fs := s0.g.mod.functions.push f
  let g1 := { s0.g with mod := { s0.g.mod with functions := fs } }
  set ({ g := g1, b := { fnIndex := idx } } : GenState)
  let fnScope ← bScopeOpen
  setLocalName (munge fnName) (← bParameter .value Ty.objectRef (munge fnName))
  for p in arity.params do
    let pn := munge (symName p.name)
    setLocalName pn (← bParameter .value p.type (munge pn))
  for (capName, capType) in caps do
    let cn := munge capName
    setLocalName cn (← bCapture .value capType cn)
  if ctx.isRecurRecursive then
    let recurShadow ← nextShadow
    let mut shadows : List LoopShadow := []
    for p in arity.params do
      let shadow ← nextShadow
      let pn := munge (symName p.name)
      setShadow pn shadow
      shadows := shadows ++ [{ name := shadow, value := ← localsIndex pn, type := Ty.objectRef }]
    let recurBlk ← newBlock (← nextIdentP "recur")
    modify fun s => { s with b := { s.b with fnRecurTarget := some recurBlk } }
    let mergeBlk ← newBlock (← nextIdentP "recur-merge")
    let _ ← bLoop (← blockName recurBlk) (some (← blockName mergeBlk))
      (some (recurShadow, Ty.objectRef)) shadows
    enterBlock recurBlk
    for p in arity.params do
      let pn := munge (symName p.name)
      setLocalName pn (← bBranchGet (← shadowIndex pn) Ty.objectRef)
    let mut bodyRes : Option Ident := none
    for x in bodyVals do bodyRes ← gen fuel x
    if !(← hasTerminator) then
      let _ ← bBranchSet recurShadow (← unwrapI bodyRes "recur body")
      let _ ← bJump mergeBlk
      enterBlock mergeBlk
      for p in arity.params do
        let pn := munge (symName p.name)
        setLocalName pn (← bBranchGet (← shadowIndex pn) Ty.objectRef)
    else
      let fn ← curFn
      let fn := fn.removeBlock mergeBlk
      setCurFn fn
      modify fun s => { s with b := { s.b with
        blockIndex := if s.b.blockIndex ≥ mergeBlk then s.b.blockIndex - 1 else s.b.blockIndex } }
      -- `static_cast<inst::loop &>(*fn->blocks[0].instructions.back()).merge_block = none;`
      let fn ← curFn
      match fn.blocks[0]? with
      | some b0 =>
        match b0.insts.back? with
        | some (.loop n lb _ sh bs) =>
          setCurFn { fn with blocks := fn.blocks.set! 0 { b0 with insts := b0.insts.pop.push (.loop n lb none sh bs) } }
        | _ => throw "static_cast to loop of a non-loop instruction (UB)"
      | none => throw "no entry block"
  else
    for x in bodyVals do let _ ← gen fuel x
  if bodyVals.isEmpty then let _ ← bLiteral .tail .nil
  let _ ← bScopeClose fnScope
  -- The outer builder resumes.
  modify fun s => { s with b := s0.b }
  pure name

/-- `gen(expr::function_ref)` (processor.cpp:371-405). In 7135b7708 a capture keeps its binding's
type (`capture.second->type`, line 394; before: `mutable_type` of it). -/
partial def genFunction (fuel : Nat) (e : Expr) : GenM (Option Ident) := do
  let .function _ uniqueName arities _ isVariadic := e.data | throw "not a function"
  let flags ← arityFlags arities
  let mut ar : List (Nat × String) := []
  for a in arities do
    let n ← genArity fuel e a
    -- `arities[arity.params.size()] = ...`
    ar := if ar.any (·.1 == a.params.length) then
      ar.map fun p => if p.1 == a.params.length then (p.1, n) else p
      else ar ++ [(a.params.length, n)]
  let captures ← fnCaptures arities
  if !captures.isEmpty then
    let mut capIdents : List (String × (Ident × CppType)) := []
    for (sym, bId) in captures do
      let nm := munge (symName sym)
      -- a temporary `local_reference` in value position, looked up like any other
      let s ← get
      let v ← match assocGet? s.b.locals nm with
        | some l => pure l
        | none => if s.b.allowedDefers.contains nm then pure ":defer"
                  else throw s!"panic: unwrap of none (capture {nm})"
      let ty := (← bindingAt bId).type
      capIdents := assocSet capIdents nm (v, ty)
    some <$> bClosure e.position (munge (uniqueName ++ "_ctx")) ar capIdents flags isVariadic
  else
    some <$> bFunction e.position ar flags isVariadic

/-- `gen(expr::recur_ref)` (processor.cpp:407-443). -/
partial def genRecur (fuel : Nat) (args : List ExprId) (loopTarget : Option ExprId) :
    GenM (Option Ident) := do
  let mut argIdents : List Ident := []
  for a in args do argIdents := argIdents ++ [← unwrapI (← gen fuel a) "recur arg"]
  match loopTarget with
  | some lt =>
    let le ← exprAt lt
    let .let pairs _ _ := le.data | throw "loop target is not a let"
    let mut i := 0
    for (bId, _) in pairs do
      let nm := munge (symName (← bindingAt bId).name)
      let shadow ← shadowIndex nm
      let newVal := argIdents.getD i ""
      if shadow != newVal then let _ ← bBranchSet shadow newVal
      i := i + 1
    let tgt := (← get).b.loopRecurTarget
    let some t := tgt | throw "panic: unwrap of none (loop_recur_target)"
    some <$> bJump t true
  | none =>
    let f ← curFn
    let mut i := 0
    for (pname, _) in f.arity.params do
      let _ ← nextShadow
      let nm := munge pname
      let _ ← bBranchSet (← shadowIndex nm) (argIdents.getD i "")
      i := i + 1
    let some t := (← get).b.fnRecurTarget | throw "panic: unwrap of none (fn_recur_target)"
    some <$> bJump t true

/-- `gen(expr::recursion_reference_ref)` (processor.cpp:445-457): across functions the local is
looked up by the function's **unmunged** name (`b.locals[expr->fn_ctx->name]`). -/
partial def genRecursionReference (fuel : Nat) (id : ExprId) (e : Expr) (ctx : FnCtxId) :
    GenM (Option Ident) := do
  let f ← curFn
  if ctx != f.arity.fnCtx then
    let c ← fnCtxAt ctx
    let name ← localsIndex c.name
    if e.position == .tail then some <$> bRet name (← exprType fuel id)
    else pure (some name)
  else some <$> bRecursionReference e.position

/-- `gen(expr::named_recursion_ref)` (processor.cpp:459-508). -/
partial def genNamedRecursion (fuel : Nat) (e : Expr) (rr : ExprId) (args : List ExprId) :
    GenM (Option Ident) := do
  let mut argIdents : List Ident := []
  for a in args do argIdents := argIdents ++ [← unwrapI (← gen fuel a) "named recursion arg"]
  let .recursionReference ctxId := (← exprAt rr).data | throw "not a recursion reference"
  let ctx ← fnCtxAt ctxId
  let some fnId := ctx.fn | throw "null fn"
  let fe ← exprAt fnId
  let .function _ uniqueName arities _ isVariadic := fe.data | throw "not a function"
  let mut needsDyn := true
  if !isVariadic then
    for a in arities do
      if (← fnCtxAt a.fnCtx).paramCount.toNat == args.length then
        needsDyn := false
        break
  let f ← curFn
  let fn ← if ctxId != f.arity.fnCtx then do pure (munge (← localsIndex (munge ctx.name)))
           else pure (munge ctx.name)
  some <$> bNamedRecursion e.position fn (munge uniqueName) argIdents needsDyn

/-- `gen(expr::let_ref)` (processor.cpp:510-590; the type erase tests `is_typed_object_ref`,
523-524). -/
partial def genLet (fuel : Nat) (id : ExprId) (e : Expr) (pairs : List (BindingId × ExprId))
    (body : ExprId) (kind : LoopKind) : GenM (Option Ident) := do
  let oldLocals := (← get).b.locals
  let scope ← bScopeOpen
  for (bId, v) in pairs do
    let nm := munge (symName (← bindingAt bId).name)
    setLocalName nm (← unwrapI (← gen fuel v) "let value")
    let lt ← exprType fuel v
    if kind != .normal && isTypedObject lt then
      setLocalName nm (← bTypeErase .value (← localsIndex nm))
  let res ← if kind == .loopWithRecur then do
      let loopLocal ← bLocal (← exprType fuel id)
      let mut shadows : List LoopShadow := []
      for (bId, v) in pairs do
        let shadow ← nextShadow
        let nm := munge (symName (← bindingAt bId).name)
        let ty := mutableType (← exprType fuel v)
        setShadow nm shadow
        shadows := shadows ++ [{ name := shadow, value := ← localsIndex nm, type := ty }]
      let loopBlk ← newBlock (← nextIdentP "loop")
      let mergeBlk ← newBlock (← nextIdentP "loop-merge")
      let oldLoop := (← get).b.loopRecurTarget
      modify fun s => { s with b := { s.b with loopRecurTarget := some loopBlk } }
      let e' ← exprAt id
      let mbName ← blockName mergeBlk
      let lbName ← blockName loopBlk
      let _ ← bLoop lbName (if e'.position != .tail then some mbName else none) none shadows
      enterBlock loopBlk
      for (bId, v) in pairs do
        let nm := munge (symName (← bindingAt bId).name)
        setLocalName nm (← bBranchGet (← shadowIndex nm) (← exprType fuel v))
      let bodyRes ← gen fuel body
      let e' ← exprAt id
      if e'.position != .tail && !(← hasTerminator) then
        let _ ← bSetLocal loopLocal (← unwrapI bodyRes "loop body")
        let _ ← bJump mergeBlk
      let r ← if e'.position != .tail then do
          enterBlock mergeBlk
          let _ ← bScopeClose scope
          pure (some loopLocal)
        else do
          removeBlockB mergeBlk
          let _ ← bScopeClose scope
          pure (some loopLocal)
      modify fun s => { s with b := { s.b with loopRecurTarget := oldLoop } }
      pure r
    else do
      let r ← gen fuel body
      let _ ← bScopeClose scope
      pure r
  modify fun s => { s with b := { s.b with locals := oldLocals } }
  pure res

/-- `gen(expr::letfn_ref)` (processor.cpp:592-620). -/
partial def genLetfn (fuel : Nat) (pairs : List (BindingId × ExprId)) (body : ExprId) :
    GenM (Option Ident) := do
  let s0 ← get
  let oldDefers := s0.b.allowedDefers
  let oldLocals := s0.b.locals
  modify fun s => { s with b := { s.b with allowedDefers := [] } }
  let mut bindings : List String := []
  for (bId, _) in pairs do
    let nm := munge (symName (← bindingAt bId).name)
    bindings := bindings ++ [nm]
    let ad := (← get).b.allowedDefers
    let ad := if ad.contains nm then ad else ad ++ [nm]
    modify fun s => { s with b := { s.b with allowedDefers := ad } }
  let _ ← bLetfn bindings
  for (bId, v) in pairs do
    let nm := munge (symName (← bindingAt bId).name)
    setLocalName nm (← unwrapI (← gen fuel v) "letfn value")
  let r ← gen fuel body
  modify fun s => { s with b := { s.b with allowedDefers := oldDefers, locals := oldLocals } }
  pure r

/-- `gen(expr::do_ref)` (processor.cpp:622-645). -/
partial def genDo (fuel : Nat) (e : Expr) (values : List ExprId) : GenM (Option Ident) := do
  let mut name : Option Ident := none
  for x in values do
    name ← gen fuel x
    if ← hasTerminator then return name
  if name.isSome then return name
  if ← hasTerminator then return none
  some <$> bLiteral e.position .nil

/-- `gen(expr::if_ref)` (processor.cpp:647-705). -/
partial def genIf (fuel : Nat) (id : ExprId) (e : Expr) (c t : ExprId) (el : Option ExprId) :
    GenM (Option Ident) := do
  let condName ← unwrapI (← gen fuel c) "if condition"
  if ← hasTerminator then return none
  let thenBlk ← newBlock (← nextIdentP "if")
  let elseBlk ← newBlock (← nextIdentP "else")
  let mergeBlk ← newBlock (← nextIdentP "if-merge")
  let ifType ← exprType fuel id
  let loc ← bLocal ifType
  let originalPos := e.position
  propagatePosition fuel id .value
  let mut boolCond := condName
  if isAnyObject (← exprType fuel c) then boolCond ← bTruthy boolCond
  let _ ← bBranch boolCond (← blockName thenBlk) (← blockName elseBlk) (← blockName mergeBlk)
  enterBlock thenBlk
  let thenName ← gen fuel t
  if !(← hasTerminator) then
    let _ ← bSetLocal loc (← unwrapI thenName "then")
    let _ ← bJump mergeBlk
  enterBlock elseBlk
  let elseName ← match el with
    | some x => gen fuel x
    | none => do some <$> bLiteral (← exprAt id).position .nil
  if !(← hasTerminator) then
    let _ ← bSetLocal loc (← unwrapI elseName "else")
    let _ ← bJump mergeBlk
  enterBlock mergeBlk
  if originalPos == .tail then some <$> bRet loc Ty.objectRef
  else pure (some loc)

/-- `gen(expr::throw_ref)` (processor.cpp:707-725). -/
partial def genThrow (fuel : Nat) (e : Expr) (v : Option ExprId) : GenM (Option Ident) := do
  let r ← match v with
    | some x => do
      let vi ← unwrapI (← gen fuel x) "throw value"
      bThrow (some (vi, ← exprType fuel x))
    | none => bThrow none
  if e.position == .tail then some <$> bRet r Ty.objectRef
  else pure (some r)

/-- `gen(expr::try_ref)` (processor.cpp:727-796). -/
partial def genTry (fuel : Nat) (id : ExprId) (e : Expr) (body : ExprId) (catches : List Catch)
    (fin : Option ExprId) : GenM (Option Ident) := do
  let loc ← bLocal (← exprType fuel id)
  let tryBlk ← newBlock (← nextIdentP "try")
  let _ ← bJump tryBlk
  let mergeBlk ← newBlock (← nextIdentP "try-merge")
  let originalPos := e.position
  let mut jumpBlk := mergeBlk
  let mut finallyBlk : Option Ident := none
  if let some fb := fin then
    let blk ← newBlock (← nextIdentP "finally")
    jumpBlk := blk
    finallyBlk := some (← blockName blk)
    enterBlock blk
    let _ ← bFinally (← blockName mergeBlk)
    let _ ← gen fuel fb
    if !(← hasTerminator) then let _ ← bJump mergeBlk
  propagatePosition fuel id .value
  let mut catchBlocks : List (CppType × Ident) := []
  for c in catches do
    let catchBlk ← newBlock (← nextIdentP "catch")
    enterBlock catchBlk
    let oldLocals := (← get).b.locals
    setLocalName (munge (symName c.sym))
      (← bCatch c.type (some (← blockName mergeBlk)) (some loc) finallyBlk)
    let res ← gen fuel c.body
    catchBlocks := catchBlocks ++ [(c.type, ← blockName catchBlk)]
    if !(← hasTerminator) then
      let _ ← bSetLocal loc (← unwrapI res "catch body")
      let _ ← bJump jumpBlk
    modify fun s => { s with b := { s.b with locals := oldLocals } }
  enterBlock tryBlk
  let _ ← bTry catchBlocks (← blockName mergeBlk) loc finallyBlk
  let tryRes ← gen fuel body
  if !(← hasTerminator) then
    let _ ← bSetLocal loc (← unwrapI tryRes "try body")
    let _ ← bJump jumpBlk
  enterBlock mergeBlk
  if originalPos == .tail then some <$> bRet loc Ty.objectRef
  else pure (some loc)

/-- `gen(expr::case_ref)` (processor.cpp:798-855); its local is declared with the case's type,
typed since 7135b7708. -/
partial def genCase (fuel : Nat) (id : ExprId) (e : Expr) (v : ExprId) (shift mask : BitVec 64)
    (d : ExprId) (keys : List (BitVec 64)) (exprs : List ExprId) : GenM (Option Ident) := do
  let valueIdent ← unwrapI (← gen fuel v) "case value"
  if ← hasTerminator then return none
  let startingBlock := (← curBlock).index
  let loc ← bLocal (← exprType fuel id)
  let mergeBlk ← newBlock (← nextIdentP "case-merge")
  let originalPos := e.position
  propagatePosition fuel id .value
  let mut cases : List (Int × Ident) := []
  let mut i := 0
  for k in keys do
    let blk ← newBlock (← nextIdentP "case")
    let bn ← blockName blk
    cases := if cases.any (·.1 == k.toInt) then cases.map fun p => if p.1 == k.toInt then (p.1, bn) else p
             else cases ++ [(k.toInt, bn)]
    enterBlock blk
    let res ← gen fuel (exprs.getD i 0)
    if (← exprAt id).position != .tail && !(← hasTerminator) then
      let _ ← bSetLocal loc (← unwrapI res "case body")
      let _ ← bJump mergeBlk
    i := i + 1
  let defaultBlock ← newBlock (← nextIdentP "default")
  enterBlock defaultBlock
  let dres ← gen fuel d
  if !(← hasTerminator) then
    let _ ← bSetLocal loc (← unwrapI dres "case default")
    let _ ← bJump mergeBlk
  enterBlock startingBlock
  let _ ← bCase shift.toInt mask.toInt valueIdent cases (← blockName defaultBlock) (← blockName mergeBlk)
  enterBlock mergeBlk
  if originalPos == .tail then some <$> bRet loc Ty.objectRef
  else pure (some loc)

/-- The `cpp_*` overloads (processor.cpp:857-974), opaque: their operands generated in the C++
order, then one instruction of the expression's type. A `cpp_conversion` (which `analyze_case`
now inserts, G16) carries its policy and conversion type in the kind string, for the code
generator's `gen(cpp_into_object)`. -/
partial def genCppOpaque (fuel : Nat) (id : ExprId) (e : Expr) (d : ExprData) :
    GenM (Option Ident) := do
  let ops : List ExprId := match d with
    | .cppConversion _ _ v _ | .cppUnsafeCast _ v | .cppMemberAccess _ _ _ v | .cppBox v _
    | .cppUnbox _ v _ | .cppDelete v => [v]
    | .cppCall _ _ args _ | .cppConstructorCall _ _ args _ | .cppMemberCall _ _ args
    | .cppBuiltinOperatorCall _ args _ => args
    | _ => []
  let mut refs : List Ident := []
  for o in ops do refs := refs ++ [← unwrapI (← gen fuel o) "cpp operand"]
  let kind := match d with
    | .cppConversion _ ct _ pol =>
      s!"cppConversion|{if pol == .intoObject then "into_object" else "from_object"}|{ct.spelling}"
    | _ => toString (repr d.kind)
  -- `builder::cpp_conversion` (builder.cpp:596-622): into an object from `void` is a nil literal
  match d with
  | .cppConversion t _ _ .intoObject =>
    if t == Ty.void then return some (← bLiteral e.position .nil)
  | _ => pure ()
  some <$> bCppOpaque kind e.position (← exprType fuel id) refs

end

/-- Which IR passes run (`util::cli::opts`; `-O0` default: none of the optional three; `-O1`:
`hoist_literals`, `remove_nops`; `-O3`: also `hoist_var_derefs`; cli.cpp:204-226, unchanged). -/
structure Passes where
  hoistLiterals : Bool := false
  hoistVarDerefs : Bool := false
  removeNops : Bool := false
  deriving Repr, Inhabited

def Passes.ofLevel : Nat → Passes
  | 0 => {}
  | 1 | 2 => { hoistLiterals := true, removeNops := true }
  | _ => { hoistLiterals := true, removeNops := true, hoistVarDerefs := true }

/-- `ir::create` up to the passes (processor.cpp:987-1007): entry points, the module, one IR
function per arity. -/
def createModule (fnId : ExprId) (moduleName : String) (target : Target) (fuel : Nat := 400) :
    GenM Unit := do
  let fe ← exprAt fnId
  let .function _ uniqueName arities _ _ := fe.data | throw "not a function"
  let entry := arities.map fun a => munge (formatTo "{}_{}" [uniqueName, toString a.params.length])
  let flags ← arityFlags arities
  let m : Module := { name := moduleName, target := target, arityFlags := flags, rootFn := fnId,
                      entryPoints := entry }
  modify fun s => { s with g := { s.g with mod := m } }
  for a in arities do let _ ← genArity fuel fe a

end Jank.Codegen
