import Jank.Codegen.Processor
import Jank.Codegen.Value
import Jank.Codegen.Prims

/-!
# Programs: their forms, how jank's analyzer turns them into its tree, and Clojure's meaning

Mirrors jank 7135b7708's analyzer (`analyze/processor.cpp`): `analyze_if` and `analyze_case`
take their type from `cpp_util::find_branch_common_type`; `analyze_case` (1206-1580) converts its
branches to the type of the last key's branch when some branch needed a conversion; names starting
with `.` are rejected as `def` names, parameters, fn names, `let`/`letfn` bindings and catch symbols
(`analyze_invalid_cpp_position`, 1296, 1769, 1963, 2364, 2528, 3105).

`Form` is a program after macro expansion (special forms only, as `let`, `loop`, `fn`, `defn`,
`case` expand to `let*`, `loop*`, `fn*`, `def`, `case*`). `analyze` builds the analyzer's tree
(`Jank.Analyzer.Arena`, the analyzer agent's types) the way `analyze/processor.cpp` does for these
forms: frames and captures (`local_frame.cpp` `find_local_impl`, `register_captures`), named
recursion, positions (`analyze_do`, `analyze_let`, `analyze_loop`, `analyze_if`, `analyze_fn_arity`),
loop kinds, literal folding of vectors (`analyze_vector`), `case*` keys. It is this agent's own
replica of that subset (assumption C5 of the report); the analyzer agent owns the full analyzer.

`cljEval` is the spec: Clojure 1.12's evaluation of the same forms (left-to-right evaluation of
the operator then the operands, lexical scope, `recur` rebinding, vars read at each use,
metadata maps of `def` evaluated, `try`/`catch`/`finally`, `case` by `=`).

The calls programs make are to user-level functions (`user/log`, `user/add`, ...), which have no
`:inline` metadata, so the analyzer keeps them as calls.
-/

namespace Jank.Codegen

open Jank.Analyzer

inductive Form where
  | lit (o : Obj)
  | sym (n : String)
  | vec (xs : List Form)
  | call (f : Form) (args : List Form)
  | let_ (bs : List (String × Form)) (body : List Form)
  | loop (bs : List (String × Form)) (body : List Form)
  | recur (args : List Form)
  | if_ (c t : Form) (e : Option Form)
  | do_ (xs : List Form)
  | fn_ (name : Option String) (params : List String) (body : List Form)
  /-- `(def ^{k v ...} name value)`: metadata values as the reader's forms. -/
  | def_ (name : String) (mta : List (String × JV)) (v : Option Form)
  | throw_ (x : Form)
  | try_ (body : List Form) (catch_ : Option (String × List Form)) (fin : Option (List Form))
  | letfn (fns : List (String × List String × List Form)) (body : List Form)
  /-- `(case e test then ... default)` with integer tests (the macro's `:ints` mode). -/
  | case_ (e : Form) (clauses : List (Int × Form)) (dflt : Form)
  | varq (n : String)
  deriving Repr, Inhabited

/-- The program as text. -/
partial def Form.code : Form → String
  | .lit o => match o with
    | .smallInteger v => toString v.toInt
    | .integer v => toString v.toInt
    | .keyword ns n => ":" ++ (if ns.isEmpty then n else ns ++ "/" ++ n)
    | .nil => "nil"
    | .boolean b => toString b
    | o => (JV.ofObj o).show
  | .sym n => n
  | .vec xs => "[" ++ " ".intercalate (xs.map Form.code) ++ "]"
  | .call f args => "(" ++ " ".intercalate (f.code :: args.map Form.code) ++ ")"
  | .let_ bs body => "(let [" ++ " ".intercalate (bs.map fun (n, v) => n ++ " " ++ v.code) ++ "] " ++ " ".intercalate (body.map Form.code) ++ ")"
  | .loop bs body => "(loop [" ++ " ".intercalate (bs.map fun (n, v) => n ++ " " ++ v.code) ++ "] " ++ " ".intercalate (body.map Form.code) ++ ")"
  | .recur args => "(recur " ++ " ".intercalate (args.map Form.code) ++ ")"
  | .if_ c t e => "(if " ++ c.code ++ " " ++ t.code ++ (match e with | some x => " " ++ x.code | none => "") ++ ")"
  | .do_ xs => "(do " ++ " ".intercalate (xs.map Form.code) ++ ")"
  | .fn_ n ps body => "(fn " ++ (match n with | some x => x ++ " " | none => "") ++ "[" ++ " ".intercalate ps ++ "] " ++ " ".intercalate (body.map Form.code) ++ ")"
  | .def_ n m v => "(def " ++ (if m.isEmpty then "" else "^{" ++ ", ".intercalate (m.map fun (k, x) => ":" ++ k ++ " " ++ x.show) ++ "} ") ++ n ++ (match v with | some x => " " ++ x.code | none => "") ++ ")"
  | .throw_ x => "(throw " ++ x.code ++ ")"
  | .try_ b c f => "(try " ++ " ".intercalate (b.map Form.code) ++ (match c with | some (e, h) => " (catch Object " ++ e ++ " " ++ " ".intercalate (h.map Form.code) ++ ")" | none => "") ++ (match f with | some fs => " (finally " ++ " ".intercalate (fs.map Form.code) ++ ")" | none => "") ++ ")"
  | .letfn fns body => "(letfn [" ++ " ".intercalate (fns.map fun (n, ps, b) => "(" ++ n ++ " [" ++ " ".intercalate ps ++ "] " ++ " ".intercalate (b.map Form.code) ++ ")") ++ "] " ++ " ".intercalate (body.map Form.code) ++ ")"
  | .case_ e cs d => "(case " ++ e.code ++ " " ++ " ".intercalate (cs.map fun (k, x) => toString k ++ " " ++ x.code) ++ " " ++ d.code ++ ")"
  | .varq n => "(var " ++ n ++ ")"

/-- User-level functions programs call: name → primitive. -/
def userPrims : List (String × String) :=
  [("log", "user/log"), ("add", "clojure.core/+"), ("lt", "clojure.core/<"), ("eq", "clojure.core/="),
   ("inc", "clojure.core/inc"), ("dec", "clojure.core/dec"), ("vector", "clojure.core/vector"),
   ("first", "clojure.core/first"), ("list?", "clojure.core/list?"), ("vector?", "clojure.core/vector?"),
   ("zero?", "clojure.core/zero?"), ("pos?", "clojure.core/pos?"), ("identity", "clojure.core/identity"),
   ("count", "clojure.core/count"), ("meta-of", "user/meta-of")]

/-! ## The analyzer, for these forms -/

structure AState where
  arena : Arena := {}
  counter : Nat := 0
  /-- Interned vars (qualified). -/
  vars : List String := userPrims.map fun (n, _) => "user/" ++ n
  /-- `loop_details`: `none` outside a loop, `some none` before the loop's let exists. -/
  loopDetails : Option (Option ExprId) := none
  deriving Inhabited

abbrev AM := StateT AState (Except String)

def aUnique (pfx : String) : AM String := do
  let s ← get
  set { s with counter := s.counter + 1 }
  pure (uniqueString pfx (s.counter + 1))

/-- `unique_namespaced_string(prefix)` (context.cpp:361-373): `ns$prefix_N`. -/
def aUniqueNs (pfx : String) : AM String := do
  let s ← get
  set { s with counter := s.counter + 1 }
  pure s!"user${pfx}_{s.counter + 1}"

def mkExpr (e : Expr) : AM ExprId := do
  let s ← get
  set { s with arena := { s.arena with exprs := s.arena.exprs.push e } }
  pure s.arena.exprs.size

def getExpr (i : ExprId) : AM Expr := do pure ((← get).arena.exprs[i]?.getD default)
def putExpr (i : ExprId) (e : Expr) : AM Unit :=
  modify fun s => { s with arena := { s.arena with exprs := s.arena.exprs.set! i e } }

def mkFrame (f : LocalFrame) : AM FrameId := do
  let s ← get
  set { s with arena := { s.arena with frames := s.arena.frames.push f } }
  pure s.arena.frames.size

def getFrame (i : FrameId) : AM LocalFrame := do pure ((← get).arena.frames[i]?.getD default)
def putFrame (i : FrameId) (f : LocalFrame) : AM Unit :=
  modify fun s => { s with arena := { s.arena with frames := s.arena.frames.set! i f } }

def mkBinding (b : LocalBinding) : AM BindingId := do
  let s ← get
  set { s with arena := { s.arena with bindings := s.arena.bindings.push b } }
  pure s.arena.bindings.size

def getBinding (i : BindingId) : AM LocalBinding := do pure ((← get).arena.bindings[i]?.getD default)

def mkFnCtx (c : FunctionContext) : AM FnCtxId := do
  let s ← get
  set { s with arena := { s.arena with fnCtxs := s.arena.fnCtxs.push c } }
  pure s.arena.fnCtxs.size

def getFnCtx (i : FnCtxId) : AM FunctionContext := do pure ((← get).arena.fnCtxs[i]?.getD default)
def putFnCtx (i : FnCtxId) (c : FunctionContext) : AM Unit :=
  modify fun s => { s with arena := { s.arena with fnCtxs := s.arena.fnCtxs.set! i c } }

def addLocal (fr : FrameId) (sym : Obj) (b : BindingId) : AM Unit := do
  let f ← getFrame fr
  let locals := if f.locals.any (·.1 == sym) then f.locals.map fun p => if p.1 == sym then (p.1, p.2 ++ [b]) else p
                else f.locals ++ [(sym, [b])]
  putFrame fr { f with locals }

/-- `find_local_impl` (local_frame.cpp:43-80): the latest binding of the name, the fn frames
crossed on the way. -/
def findLocal (start : FrameId) (sym : Obj) : AM (Option (BindingId × List FrameId)) := do
  let mut it := start
  let mut crossed : List FrameId := []
  let mut fuel := 1000
  while fuel > 0 do
    fuel := fuel - 1
    let f ← getFrame it
    if let some (_, bs) := f.locals.find? (·.1 == sym) then
      if let some b := bs.getLast? then return some (b, crossed)
    if let some (_, c) := f.captures.find? (·.1 == sym) then return some (c.binding, crossed)
    match f.parent with
    | some p =>
      if f.type == .fn then crossed := crossed ++ [it]
      it := p
    | none => return none
  return none

/-- `register_captures(result)` (local_frame.cpp:95-116): a copy of the binding in each crossed
fn frame's captures (first registration kept). -/
def registerCaptures (sym : Obj) (b : BindingId) (crossed : List FrameId) : AM Unit := do
  for fr in crossed do
    let f ← getFrame fr
    if f.captures.any (·.1 == sym) then continue
    let orig ← getBinding b
    let copy ← mkBinding { orig with isCapture := true, needsBox := true, hasBoxedUsage := true,
                                     hasUnboxedUsage := false }
    putFrame fr { f with captures := f.captures ++ [(sym, { binding := copy, originatingBinding := b })] }

/-- `find_named_recursion` (local_frame.cpp:132-159). -/
def findNamedRecursion (start : FrameId) (name : String) : AM (Option (FrameId × List FrameId)) := do
  let mut it := start
  let mut crossed : List FrameId := []
  let mut fuel := 1000
  while fuel > 0 do
    fuel := fuel - 1
    let f ← getFrame it
    if f.type == .fn then
      if let some c := f.fnCtx then
        if (← getFnCtx c).name == name then return some (it, crossed)
    match f.parent with
    | some p =>
      if f.type == .fn then crossed := crossed ++ [it]
      it := p
    | none => return none
  return none

partial def exprTypeA (i : ExprId) : AM CppType := do
  match (← get).arena.exprs[i]? with
  | some e => match e.data with
    | .primitiveLiteral d => pure (literalTypeBoxed d)
    | .localReference _ b => pure (← getBinding b).type
    | .if_ t .. => pure t
    | .let _ body _ | .letfn _ body => exprTypeA body
    | .do_ vs => match vs.getLast? with | some l => exprTypeA l | none => pure Ty.objectRef
    | .cppConversion t .. => pure t
    | .case_ _ _ _ d _ xs => do
      let dt ← exprTypeA d
      let mut chosen := dt
      for x in xs do chosen := (findBranchCommonType (← exprTypeA x) (some dt)).1
      pure chosen
    | _ => pure Ty.objectRef
  | none => pure Ty.objectRef

/-- `analyze_invalid_cpp_position` for a name starting with `.` (C++ member syntax). -/
def checkName (n : String) : AM Unit := do
  if n.startsWith "." then throw s!"analyze_invalid_cpp_position: {n}"

def mkE (pos : ExprPosition) (fr : FrameId) (d : ExprData) : AM ExprId :=
  mkExpr { kind := d.kind, position := pos, frame := some fr, data := d }

/-- `propagate_position` on the analyzer side (the overrides of expression.cpp/do.cpp/...). -/
partial def aPropagate (i : ExprId) (pos : ExprPosition) : AM Unit := do
  let e ← getExpr i
  putExpr i { e with position := pos }
  match e.data with
  | .do_ vs => if let some l := vs.getLast? then aPropagate l pos
  | .if_ _ _ t el => aPropagate t pos; if let some x := el then aPropagate x pos
  | .let _ b _ | .letfn _ b => aPropagate b pos
  | .try_ b cs _ => aPropagate b pos; for c in cs do aPropagate c.body pos
  | .case_ _ _ _ d _ xs => aPropagate d pos; for x in xs do aPropagate x pos
  | _ => pure ()

/-- The value of a literal form (for folding a vector of literals, `analyze_vector`). -/
def litObj (i : ExprId) : AM (Option Obj) := do
  match (← getExpr i).data with
  | .primitiveLiteral o => pure (some o)
  | _ => pure none

/-- `apply_implicit_conversion(expr, expected)` (analyze/processor.cpp:1032-1130) with
`determine_implicit_conversion` (cpp_util.cpp:2004-2070) for object types: none between equal
types, between two `object_ref`s, or from a typed ref to `object_ref`; `from_object` from
`object_ref` to a typed ref (a `cpp_conversion` of type and conversion type `expected`); a typed
ref to another typed ref is trait convertible: `into_object` (type `expected`, conversion type
the expression's). The expression goes to value position; the conversion takes its position. -/
def implicitConversion (e : ExprId) (expected : CppType) (fr : FrameId) : AM ExprId := do
  let et ← exprTypeA e
  if et == expected || (isUntypedObject et && isUntypedObject expected)
     || (isUntypedObject expected && isTypedObject et) then return e
  let x ← getExpr e
  let castPos := x.position
  aPropagate e .value
  if isTypedObject expected && isUntypedObject et then
    mkE castPos fr (.cppConversion expected expected e .fromObject)
  else
    mkE castPos fr (.cppConversion expected et e .intoObject)

/-- Prep-ints of the `case` macro (core.jank 4376-4391) for integer tests: no shift/mask when they
fit an 8192-wide table (or no shift/mask separates them), else the first shift/mask that does. -/
def caseKeys (tests : List Int) : Int × Int × List Int :=
  let mx := tests.foldl max (tests.headD 0)
  let mn := tests.foldl min (tests.headD 0)
  if mx - mn < 8192 then (0, 0, tests)
  else
    let cands := (List.range 13).flatMap fun b => (List.range 31).map fun sh => (sh, 2 ^ (b + 1) - 1)
    match cands.find? (fun (sh, m) => (tests.map fun t => shiftMask t sh m).eraseDups.length == tests.length) with
    | some (sh, m) => (sh, m, tests.map fun t => shiftMask t sh m)
    | none => (0, 0, tests)

mutual

partial def analyze (f : Form) (fr : FrameId) (pos : ExprPosition) (fnCtx : Option FnCtxId) : AM ExprId := do
  match f with
  | .lit o => mkE pos fr (.primitiveLiteral o)
  | .sym n => analyzeSym n fr pos
  | .vec xs =>
    let ids ← xs.mapM fun x => analyze x fr .value fnCtx
    let lits ← ids.mapM litObj
    if lits.all Option.isSome then mkE pos fr (.primitiveLiteral (.persistentVector none (lits.filterMap id)))
    else mkE pos fr (.vector ids none)
  | .call fn args =>
    let src ← match fn with
      | .sym n => analyzeSym n fr .call
      | other => analyze other fr .call fnCtx
    let argIds ← args.mapM fun a => analyze a fr .value fnCtx
    match (← getExpr src).data with
    | .recursionReference _ => mkE pos fr (.namedRecursion src .nil argIds)
    | _ => mkE pos fr (.call src argIds .nil)
  | .let_ bs body => analyzeLet false bs body fr pos fnCtx
  | .loop bs body =>
    let old := (← get).loopDetails
    modify fun s => { s with loopDetails := some none }
    let l ← analyzeLet true bs body fr .tail fnCtx
    modify fun s => { s with loopDetails := old }
    aPropagate l pos
    let e ← getExpr l
    if let .let ps b .normal := e.data then putExpr l { e with data := .let ps b .loopWithoutRecur }
    pure l
  | .recur args =>
    let argIds ← args.mapM fun a => analyze a fr .value fnCtx
    match (← get).loopDetails with
    | some (some l) =>
      let e ← getExpr l
      if let .let ps b _ := e.data then
        if ps.length != args.length then throw "recur arity"
        putExpr l { e with data := .let ps b .loopWithRecur }
      mkE pos fr (.recur .nil argIds [] (some l))
    | some none => throw "recur before the loop's let"
    | none =>
      let some c := fnCtx | throw "recur outside fn"
      let ctx ← getFnCtx c
      putFnCtx c { ctx with isRecurRecursive := true }
      mkE pos fr (.recur .nil argIds [] none)
  | .if_ c t el =>
    let ci ← analyze c fr .value fnCtx
    let ti ← analyze t fr pos fnCtx
    let ei ← match el with
      | some x => some <$> analyze x fr pos fnCtx
      | none => pure none
    let tt ← exprTypeA ti
    let et ← match ei with | some x => some <$> exprTypeA x | none => pure none
    -- `find_branch_common_type` (its conversions are no-ops between object types)
    mkE pos fr (.if_ (findBranchCommonType tt et).1 ci ti ei)
  | .do_ xs => analyzeDo xs fr pos fnCtx
  | .fn_ name params body => analyzeFn name params body fr pos
  | .def_ name mta v =>
    checkName name
    let q := "user/" ++ name
    modify fun s => { s with vars := if s.vars.contains q then s.vars else s.vars ++ [q] }
    let vi ← match v with
      | some x => some <$> analyze x fr .value fnCtx
      | none => pure none
    let metaObj : Option Obj := if mta.isEmpty then none
      else some (.persistentArrayMap none (mta.map fun (k, x) => (.keyword "" k, jvToObj x)))
    mkE pos fr (.def (.symbol metaObj "user" name) vi)
  | .throw_ x =>
    let xi ← analyze x fr .value fnCtx
    mkE pos fr (.throw_ (some xi))
  | .try_ body c fin =>
    let tryFr ← mkFrame { type := .try_, parent := some fr, fnCtx := fnCtx }
    let bi ← analyzeDo body tryFr pos fnCtx
    let catches ← match c with
      | some (sym, h) => do
        checkName sym
        let cfr ← mkFrame { type := .catch_, parent := some fr, fnCtx := fnCtx }
        let b ← mkBinding { name := .symbol none "" sym, originatingFrame := some cfr }
        addLocal cfr (.symbol none "" sym) b
        let hi ← analyzeDo h cfr pos fnCtx
        pure [{ sym := .symbol none "" sym, type := Ty.objectRef, body := hi : Catch }]
      | none => pure []
    let fi ← match fin with
      | some fs => do
        let ffr ← mkFrame { type := .finally, parent := some fr, fnCtx := fnCtx }
        some <$> analyzeDo fs ffr .statement fnCtx
      | none => pure none
    mkE pos fr (.try_ bi catches fi)
  | .letfn fns body =>
    let lfr ← mkFrame { type := .letfn, parent := some fr, fnCtx := fnCtx }
    let mut bids : List BindingId := []
    for (n, _, _) in fns do
      checkName n
      let b ← mkBinding { name := .symbol none "" n, originatingFrame := some lfr }
      addLocal lfr (.symbol none "" n) b
      bids := bids ++ [b]
    let mut pairs : List (BindingId × ExprId) := []
    for ((n, ps, b), bid) in fns.zip bids do
      let fi ← analyzeFn (some n) ps b lfr .value
      pairs := pairs ++ [(bid, fi)]
    let bi ← analyzeDo body lfr pos fnCtx
    mkE pos fr (.letfn pairs bi)
  | .case_ e clauses dflt =>
    -- `(let* [G e] (case* G shift mask default imap))`, imap a sorted map of key → condp
    let g ← aUnique "G_"
    let (shift, mask, keys) := caseKeys (clauses.map (·.1))
    let sorted := ((keys.zip clauses).toArray.qsort (fun a b => a.1 < b.1)).toList
    let lfr ← mkFrame { type := .let, parent := some fr, fnCtx := fnCtx }
    let ei ← analyze e lfr .value fnCtx
    let b ← mkBinding { name := .symbol none "" g, valueExpr := some ei, originatingFrame := some lfr,
                        type := ← exprTypeA ei }
    addLocal lfr (.symbol none "" g) b
    let vi ← analyze (.sym g) lfr .value fnCtx
    let mut di ← analyze dflt lfr pos fnCtx
    -- analyze_case (1483-1579): the type of the last key's branch against the default
    let dt ← exprTypeA di
    let mut needsConversion := false
    let mut chosen := dt
    let mut ks : List (BitVec 64) := []
    let mut xs : List ExprId := []
    for (k, (t, th)) in sorted do
      ks := ks ++ [BitVec.ofInt 64 k]
      let xi ← analyze (.if_ (.call (.sym "eq") [.lit (Obj.ofInt t), .sym g]) th (some dflt)) lfr pos fnCtx
      let (ct, nc) := findBranchCommonType (← exprTypeA xi) (some dt)
      needsConversion := needsConversion || nc
      chosen := ct
      xs := xs ++ [xi]
    if needsConversion then
      di ← implicitConversion di chosen lfr
      let mut cxs : List ExprId := []
      for x in xs do cxs := cxs ++ [← implicitConversion x chosen lfr]
      xs := cxs
    let ci ← mkE pos lfr (.case_ vi (BitVec.ofInt 64 shift) (BitVec.ofInt 64 mask) di ks xs)
    let bodyDo ← mkE pos lfr (.do_ [ci])
    mkE pos fr (.let [(b, ei)] bodyDo .normal)
  | .varq n => mkE pos fr (.varRef .nil { ns := "user", name := n })

partial def analyzeSym (n : String) (fr : FrameId) (pos : ExprPosition) : AM ExprId := do
  let sym : Obj := .symbol none "" n
  if let some (b, crossed) ← findLocal fr sym then
    if !crossed.isEmpty then
      registerCaptures sym b crossed
      match ← findLocal fr sym with
      | some (b2, _) => return ← mkE pos fr (.localReference sym b2)
      | none => throw "capture lost"
    return ← mkE pos fr (.localReference sym b)
  if let some (fnFr, crossed) ← findNamedRecursion fr n then
    let f ← getFrame fnFr
    let some c := f.fnCtx | throw "fn frame without context"
    let ctx ← getFnCtx c
    let b ← mkBinding { name := .symbol none "" ctx.name, nativeName := ctx.name, valueExpr := ctx.fn,
                        originatingFrame := some fr }
    registerCaptures (.symbol none "" ctx.name) b crossed
    putFnCtx c { ctx with isNamedRecursive := true }
    return ← mkE pos fr (.recursionReference c)
  let q := "user/" ++ n
  if (← get).vars.contains q then return ← mkE pos fr (.varDeref .nil { ns := "user", name := n })
  throw s!"Unable to resolve symbol: {n}"

partial def analyzeDo (xs : List Form) (fr : FrameId) (pos : ExprPosition) (fnCtx : Option FnCtxId) :
    AM ExprId := do
  let n := xs.length
  let mut ids : List ExprId := []
  let mut i := 0
  for x in xs do
    i := i + 1
    ids := ids ++ [← analyze x fr (if i == n then pos else .statement) fnCtx]
  if ids.isEmpty then ids := [← mkE pos fr (.primitiveLiteral .nil)]
  mkE pos fr (.do_ ids)

partial def analyzeLet (isLoop : Bool) (bs : List (String × Form)) (body : List Form) (fr : FrameId)
    (pos : ExprPosition) (fnCtx : Option FnCtxId) : AM ExprId := do
  let lfr ← mkFrame { type := .let, parent := some fr, fnCtx := fnCtx }
  let bodyPlaceholder ← mkE pos lfr (.do_ [])
  let li ← mkE pos lfr (.let [] bodyPlaceholder .normal)
  if isLoop then modify fun s => { s with loopDetails := some (some li) }
  let mut pairs : List (BindingId × ExprId) := []
  for (n, v) in bs do
    checkName n
    let vi ← analyze v lfr .value fnCtx
    let t ← exprTypeA vi
    let b ← mkBinding { name := .symbol none "" n, valueExpr := some vi, originatingFrame := some lfr,
                        isLoopVariable := isLoop, type := if isLoop then mutableType t else t }
    addLocal lfr (.symbol none "" n) b
    pairs := pairs ++ [(b, vi)]
    let e ← getExpr li
    if let .let _ bd k := e.data then putExpr li { e with data := .let pairs bd k }
  let bi ← analyzeDo body lfr pos fnCtx
  let e ← getExpr li
  if let .let ps _ k := e.data then putExpr li { e with data := .let ps bi k }
  pure li

partial def analyzeFn (name : Option String) (params : List String) (body : List Form) (fr : FrameId)
    (pos : ExprPosition) : AM ExprId := do
  let (nm, unique) ← match name with
    | some n => do pure (n, ← aUniqueNs n)
    | none => do let u ← aUniqueNs "fn"; pure (u, u)
  -- analyze_fn_arity: a fn frame, parameters (an earlier duplicate renamed `shadowed_N`)
  let ffr ← mkFrame { type := .fn, parent := some fr }
  let c ← mkFnCtx { name := nm, uniqueName := unique, paramCount := params.length.toUInt64 }
  putFrame ffr { (← getFrame ffr) with fnCtx := some c }
  let mut ps : List Parameter := []
  if let some n := name then checkName n
  for p in params do
    checkName p
    if ps.any (fun q => q.name == .symbol none "" p) then
      let u ← aUnique "shadowed"
      ps := ps.map fun q => if q.name == .symbol none "" p then { q with name := .symbol none "" u } else q
    let b ← mkBinding { name := .symbol none "" p, nativeName := p, originatingFrame := some fr }
    addLocal ffr (.symbol none "" p) b
    ps := ps ++ [{ name := .symbol none "" p, type := Ty.objectRef }]
  let oldLoop := (← get).loopDetails
  let bi ← analyzeDo body ffr .tail (some c)
  modify fun s => { s with loopDetails := oldLoop }
  let fe ← mkE pos fr (.function nm unique [{ params := ps, body := bi, frame := some ffr, fnCtx := c }] .nil false)
  let ctx ← getFnCtx c
  putFnCtx c { ctx with fn := some fe, name := nm, uniqueName := unique }
  pure fe

partial def jvToObj : JV → Obj
  | .nil => .nil
  | .bool b => .boolean b
  | .int v => Obj.ofInt v
  | .str s => .persistentString s
  | .kw ns n => .keyword ns n
  | .sym ns n _ => .symbol none ns n
  | .vec xs _ => .persistentVector none (xs.map jvToObj)
  | .list xs _ => .persistentList none (xs.map jvToObj)
  | .map kvs => .persistentArrayMap none (kvs.map fun (k, v) => (jvToObj k, jvToObj v))
  | _ => .nil

end

/-- The analyzed program: a root `(fn* [] forms...)` (`analyze(parse_current, parse_end)`,
processor.cpp: the forms wrapped in an anonymous fn). -/
def analyzeProgram (body : List Form) (rootName : Option String := none) : Except String (ExprId × AState) := do
  let st : AState := {}
  let go : AM ExprId := do
    let root ← mkFrame { type := .root }
    analyzeFn rootName [] body root .value
  match go.run st with
  | .ok (e, s) => pure (e, s)
  | .error e => throw e

end Jank.Codegen
