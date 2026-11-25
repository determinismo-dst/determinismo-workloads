import Jank.Analyzer.Types

/-!
# Expression methods and local frames over the arena

- Each expression struct's virtual methods (`src/cpp/jank/analyze/expression.cpp`,
  `expr/*.cpp`): `propagate_position`, `walk`, `get_type`.
- `src/cpp/jank/analyze/local_frame.cpp`: `find_local_impl`, `find_local_or_capture`,
  `register_captures` (both overloads), `find_named_recursion`, `find_closest_fn_frame`,
  `within_same_fn`.
- `src/cpp/jank/analyze/pass/walk.cpp` (`postwalk`, `prewalk`) and `step/force_boxed.cpp`.

All mutate the arena in place, as the C++ mutates the heap.
-/

namespace Jank.Analyzer

abbrev ArenaM := StateM Arena

namespace Arena

def expr (a : Arena) (i : ExprId) : Expr := a.exprs.getD i default
def frame (a : Arena) (i : FrameId) : LocalFrame := a.frames.getD i { type := .root }
def binding (a : Arena) (i : BindingId) : LocalBinding := a.bindings.getD i { name := .nil }
def fnCtx (a : Arena) (i : FnCtxId) : FunctionContext := a.fnCtxs.getD i {}

def addExpr (a : Arena) (e : Expr) : Arena × ExprId := ({ a with exprs := a.exprs.push e }, a.exprs.size)
def addFrame (a : Arena) (f : LocalFrame) : Arena × FrameId := ({ a with frames := a.frames.push f }, a.frames.size)
def addBinding (a : Arena) (b : LocalBinding) : Arena × BindingId := ({ a with bindings := a.bindings.push b }, a.bindings.size)
def addFnCtx (a : Arena) (c : FunctionContext) : Arena × FnCtxId := ({ a with fnCtxs := a.fnCtxs.push c }, a.fnCtxs.size)

def setExpr (a : Arena) (i : ExprId) (e : Expr) : Arena := { a with exprs := a.exprs.set! i e }
def setFrame (a : Arena) (i : FrameId) (f : LocalFrame) : Arena := { a with frames := a.frames.set! i f }
def setBinding (a : Arena) (i : BindingId) (b : LocalBinding) : Arena := { a with bindings := a.bindings.set! i b }
def setFnCtx (a : Arena) (i : FnCtxId) (c : FunctionContext) : Arena := { a with fnCtxs := a.fnCtxs.set! i c }

end Arena

def getExpr (i : ExprId) : ArenaM Expr := do pure ((← get).expr i)
def modifyExpr (i : ExprId) (f : Expr → Expr) : ArenaM Unit := modify fun a => a.setExpr i (f (a.expr i))
def modifyBinding (i : BindingId) (f : LocalBinding → LocalBinding) : ArenaM Unit :=
  modify fun a => a.setBinding i (f (a.binding i))
def modifyFrame (i : FrameId) (f : LocalFrame → LocalFrame) : ArenaM Unit :=
  modify fun a => a.setFrame i (f (a.frame i))
def modifyFnCtx (i : FnCtxId) (f : FunctionContext → FunctionContext) : ArenaM Unit :=
  modify fun a => a.setFnCtx i (f (a.fnCtx i))

/-- Symbol keys compare by ns and name (`std::equal_to<symbol_ref>`, symbol.cpp `equal`). -/
def symKey : Obj → String × String
  | .symbol _ ns n => (ns, n)
  | _ => ("", "")

/-- `symbol::to_string` (symbol.cpp:121). -/
def symString (o : Obj) : String :=
  let (ns, n) := symKey o
  if ns.isEmpty then n else s!"{ns}/{n}"

/-! ## Expression methods -/

/-- `propagate_position(pos)` of every expression struct (unchanged in 7135b7708). The base (`expression.cpp:39`) sets the
position; `do_` (do.cpp) sets it and propagates to its last value; `if_` (if.cpp) to then/else;
`let`, `letfn` to the body; `try_` (try.cpp) to the body and each catch body (not finally);
`case_` (case.cpp) to the default and each branch, then sets it; the `cpp_*` set it. -/
partial def propagatePosition (i : ExprId) (pos : ExprPosition) : ArenaM Unit := do
  let e ← getExpr i
  match e.data with
  | .do_ values =>
    modifyExpr i fun e => { e with position := pos }
    if let some last := values.getLast? then propagatePosition last pos
  | .if_ _ _ then_ else_ =>
    modifyExpr i fun e => { e with position := pos }
    propagatePosition then_ pos
    if let some el := else_ then propagatePosition el pos
  | .let _ body _ | .letfn _ body =>
    modifyExpr i fun e => { e with position := pos }
    propagatePosition body pos
  | .try_ body catches _ =>
    modifyExpr i fun e => { e with position := pos }
    propagatePosition body pos
    for c in catches do propagatePosition c.body pos
  | .case_ _ _ _ dflt _ exprs =>
    propagatePosition dflt pos
    for x in exprs do propagatePosition x pos
    modifyExpr i fun e => { e with position := pos }
  | _ => modifyExpr i fun e => { e with position := pos }

/-- `walk(f)`: the children each struct visits, in order (call.cpp, case.cpp, def.cpp, do.cpp,
function.cpp (arity bodies), if.cpp, let.cpp, letfn.cpp, list/vector/set/map.cpp (data then meta),
named_recursion.cpp, recur.cpp (arg exprs only), throw.cpp, try.cpp). -/
def children (a : Arena) (i : ExprId) : List ExprId :=
  match (a.expr i).data with
  | .call src args _ => src :: args
  | .case_ v _ _ d _ xs => v :: d :: xs
  | .def _ (some v) => [v]
  | .do_ vs => vs
  | .function _ _ arities _ _ => arities.map (·.body)
  | .if_ _ c t (some e) => [c, t, e]
  | .if_ _ c t none => [c, t]
  | .let pairs body _ => pairs.map (·.2) ++ [body]
  | .letfn pairs body => pairs.map (·.2) ++ [body]
  | .list xs m | .vector xs m | .set xs m => xs ++ m.toList
  | .map kvs m => kvs.flatMap (fun (k, v) => [k, v]) ++ m.toList
  | .namedRecursion _ _ args => args
  | .recur _ args _ _ => args
  | .throw_ (some v) => [v]
  | .try_ b cs f => b :: cs.map (·.body) ++ f.toList
  | .cppConversion _ _ v _ | .cppUnsafeCast _ v | .cppBox v _ | .cppUnbox _ v _ | .cppNew _ v
  | .cppDelete v => [v]
  | .cppCall _ s args _ => s :: args
  | .cppConstructorCall _ _ args _ | .cppMemberCall _ _ args | .cppBuiltinOperatorCall _ args _ => args
  | .cppMemberAccess _ _ _ o => [o]
  | _ => []

/-- `pass::postwalk` (pass/walk.cpp:5), with fuel against cycles. -/
def postwalk (a : Arena) (f : ExprId → List ExprId → List ExprId) : Nat → ExprId → List ExprId → List ExprId
  | 0, _, acc => acc
  | n + 1, i, acc => f i ((children a i).foldl (fun acc c => postwalk a f n c acc) acc)

/-- `pass::prewalk` (pass/walk.cpp:11), with fuel against cycles. -/
def prewalk (a : Arena) (f : ExprId → List ExprId → List ExprId) : Nat → ExprId → List ExprId → List ExprId
  | 0, _, acc => acc
  | n + 1, i, acc => (children a i).foldl (fun acc c => prewalk a f n c acc) (f i acc)

/-- `get_type()` of every expression struct. -/
def exprType (a : Arena) (i : ExprId) : Nat → CT
  | 0 => .objectRef
  | n + 1 =>
    let e := a.expr i
    match e.data with
    | .primitiveLiteral d => literalType d true
    | .cppLiteral d => literalType d false
    | .localReference _ b => (a.binding b).type.toCT
    | .do_ [] => .objectRef
    | .do_ vs => exprType a (vs.getLast?.getD 0) n
    | .if_ t .. => t.toCT
    | .let _ body _ | .letfn _ body => exprType a body n
    | .cppType _ t | .cppValue _ _ t _ _ | .cppConversion t _ _ _ | .cppUnsafeCast t _
    | .cppCall t .. | .cppConstructorCall t .. | .cppMemberAccess t .. | .cppBuiltinOperatorCall _ _ t
    | .cppUnbox t .. | .cppNew t _ => t.toCT
    | .cppMemberCall t _ _ => t.toCT
    | .cppRaw _ | .cppDelete _ => .void
    -- `case_::get_type()` (case.cpp:71, 7135b7708): the branches' common type.
    | .case_ .. => e.caseType.toCT
    | _ => .objectRef

/-- `cpp_util::non_void_expression_type` (cpp_util.cpp:1146). -/
def nonVoidExpressionType (a : Arena) (i : ExprId) : CT :=
  let t := exprType a i 10000
  if isVoid t then .objectRef else t

/-! ## Local frames -/

/-- `local_frame::binding_find_result`. -/
structure BindingFind where
  binding : BindingId
  crossedFns : List FrameId
  deriving Repr, BEq, DecidableEq

/-- `find_local_impl` (local_frame.cpp:48): walk from `start` to the root; in each frame the
latest local of that name, then (when allowed) a capture of that name; record every `fn` frame
left behind. -/
def findLocalImpl (a : Arena) (start : FrameId) (sym : Obj) (allowCaptures : Bool) : Nat → Option BindingFind :=
  go start []
where
  go (it : FrameId) (crossed : List FrameId) : Nat → Option BindingFind
    | 0 => none
    | n + 1 =>
      let f := a.frame it
      match f.locals.find? (fun (k, _) => symKey k == symKey sym) with
      | some (_, bs) =>
        match bs.getLast? with
        | some b => some ⟨b, crossed⟩
        | none => none
      | none =>
        match (if allowCaptures then f.captures.find? (fun (k, _) => symKey k == symKey sym) else none) with
        | some (_, c) => some ⟨c.binding, crossed⟩
        | none =>
          match f.parent with
          | some p => go p (if f.type == .fn then crossed ++ [it] else crossed) n
          | none => none

/-- `local_frame::find_local_or_capture` (local_frame.cpp:90). -/
def findLocalOrCapture (a : Arena) (frame : FrameId) (sym : Obj) : Option BindingFind :=
  findLocalImpl a frame sym true 10000

/-- `local_frame::register_captures(binding_find_result)` (local_frame.cpp:95): every crossed fn
gets a copy of the binding as a capture (`emplace`: an existing capture of that name is kept),
marked captured and boxed, with its type made non-reference. -/
def registerCaptures (r : BindingFind) : ArenaM Unit := do
  for crossed in r.crossedFns do
    let a ← get
    let orig := a.binding r.binding
    let f := a.frame crossed
    -- `emplace` keeps an existing capture; the flags below are then written to that one.
    let target ← match f.captures.find? (fun (k, _) => symKey k == symKey orig.name) with
      | some (_, c) => pure c.binding
      | none => do
        let (a', copy) := a.addBinding orig
        set a'
        modifyFrame crossed fun f => { f with captures := f.captures ++ [(orig.name, ⟨copy, r.binding⟩)] }
        pure copy
    modifyBinding target fun b =>
      { b with isCapture := true, needsBox := true, hasBoxedUsage := true, hasUnboxedUsage := false }

/-- `local_frame::named_recursion_find_result`. -/
structure NamedRecursionFind where
  fnFrame : FrameId
  crossedFns : List FrameId
  deriving Repr, BEq, DecidableEq

/-- `local_frame::find_named_recursion` (local_frame.cpp:133): the nearest `fn` frame whose
function context's name equals the symbol's `to_string()`. -/
def findNamedRecursion (a : Arena) (start : FrameId) (sym : Obj) : Option NamedRecursionFind :=
  go start [] 10000
where
  go (it : FrameId) (crossed : List FrameId) : Nat → Option NamedRecursionFind
    | 0 => none
    | n + 1 =>
      let f := a.frame it
      let nameMatches := f.type == .fn && (match f.fnCtx with
        | some c => (a.fnCtx c).name == symString sym
        | none => false)
      if nameMatches then some ⟨it, crossed⟩
      else match f.parent with
        | some p => go p (if f.type == .fn then crossed ++ [it] else crossed) n
        | none => none

/-- `local_frame::register_captures(frame, named_recursion_find_result)` (local_frame.cpp:118):
a binding named after the fn is built on the stack (`b`), `register_captures` stores `&b` as each
capture's `originating_binding`; `b` dies at return, so those pointers dangle (`alive := false`). -/
def registerNamedCaptures (frame : FrameId) (r : NamedRecursionFind) : ArenaM Unit := do
  let a ← get
  let ctxId := (a.frame r.fnFrame).fnCtx.getD 0
  let ctx := a.fnCtx ctxId
  let nb : LocalBinding :=
    { name := .symbol none "" ctx.name, nativeName := ctx.name, valueExpr := ctx.fn, originatingFrame := some frame }
  let (a', b) := a.addBinding nb
  set a'
  registerCaptures ⟨b, r.crossedFns⟩
  modifyBinding b fun b => { b with alive := false }

/-- `local_frame::find_closest_fn_frame` (local_frame.cpp:161): the nearest `fn` frame, else the
root. -/
def findClosestFnFrame (a : Arena) : Nat → FrameId → FrameId
  | 0, f => f
  | n + 1, f =>
    let fr := a.frame f
    if fr.type == .fn then f
    else match fr.parent with
      | some p => findClosestFnFrame a n p
      | none => f

/-- `local_frame::within_same_fn` (local_frame.cpp:183). -/
def withinSameFn (a : Arena) (l r : FrameId) : Bool :=
  findClosestFnFrame a 10000 l == findClosestFnFrame a 10000 r

/-! ## step::force_boxed -/

/-- `step::force_boxed` (step/force_boxed.cpp:58). Its `walk` compares `std::decay_t` of the
visited `jtl::ref<expr::T>` with `expr::if_`, `expr::do_`, ...: never equal, so it applies `f` to
the last expression only. And every caller's `do_` already has `needs_box` true
(processor.cpp:1881), so the call returns at once. -/
def forceBoxed (doId : ExprId) : ArenaM Unit := do
  let d ← getExpr doId
  if d.needsBox then return
  modifyExpr doId fun e => { e with needsBox := true }
  match d.data with
  | .do_ values =>
    if let some last := values.getLast? then modifyExpr last fun e => { e with needsBox := true }
  | _ => pure ()

end Jank.Analyzer
