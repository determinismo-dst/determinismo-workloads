import Jank.Analyzer.Eval

/-!
# The spec: Clojure 1.12's meaning of the same forms

Clojure's reference (clojure.org/reference/special_forms, evaluation, macros) and the reference
implementation's precise rules (`clojure-ref/src/jvm/clojure/lang/Compiler.java`):

- `analyzeSeq` (Compiler.java:7140-): `macroexpand1` first (not for special forms, not when the
  operator is a local: `isMacro`, 7429), then `isInline` (also not for locals, 7446), then special
  forms, then an invocation;
- `macroexpand1` (7509) calls the macro with `(form, &env, args...)`: `&form` is the whole form,
  `&env` the map of locals in scope;
- `FnMethod.parse` (5902): the fn's name is a local registered before the parameters, so it shadows
  every outer binding; `LOOP_LOCALS` is bound to the method's parameters (5869): a `recur` targets
  the innermost `fn` or `loop`;
- `LetExpr.Parser` (6875): loop inits see no recur target; a recur argument of the wrong primitive
  type re-analyzes the loop with that local boxed (6911): values pass through `recur` unchanged;
- `RecurExpr.Parser` (7180): only in tail position, never across `try`, exactly as many
  arguments as the target has locals;
- resolving a private var of another namespace is an error (`resolveIn`, `isMacro`, `isInline`),
  inside macro expansions too.

The analysis produces a small tree (`CE`) that is then evaluated with the shared `builtin`s.
-/

namespace Jank.Analyzer

/-- Clojure's analyzed expression (the parts the programs use). -/
inductive CE where
  | const (o : Obj)
  | local (id : Nat)
  | var (vr : VarRef)
  | theVar (vr : VarRef)
  | if_ (c t e : CE)
  | do_ (xs : List CE)
  | let_ (binds : List (Nat × CE)) (body : CE) (isLoop : Bool)
  | recur (args : List CE)
  | fn (self : Option Nat) (arities : List (List Nat × Option Nat × CE))
  | call (f : CE) (args : List CE)
  | def (vr : VarRef) (value : Option CE)
  | throw (x : CE)
  | vector (xs : List CE) (md : Option CE)
  | map (kvs : List (CE × CE)) (md : Option CE)
  | set (xs : List CE) (md : Option CE)
  | letfn (binds : List (Nat × CE)) (body : CE)
  deriving Inhabited

/-- Compiler context (`C.RETURN`, `C.EXPRESSION`, `C.STATEMENT`). -/
inductive Ctx where
  | ret | expr | stmt
  deriving BEq, Inhabited

structure CEnv where
  /-- name → local id, innermost first. -/
  locals : List (String × Nat) := []
  /-- `LOOP_LOCALS`: how many locals the recur target has (none: no target). -/
  loopLocals : Option Nat := none
  /-- `NO_RECUR`. -/
  noRecur : Bool := false

structure CState where
  rt : Runtime
  next : Nat := 0
  fuel : Nat := 20000

abbrev CA := StateT CState (Except Outcome)

def cerr {α : Type} (msg : String) : CA α := throw (.compileError msg)

def freshLocal : CA Nat := do
  let s ← get
  set { s with next := s.next + 1 }
  pure s.next

def cburn : CA Unit := do
  let s ← get
  if s.fuel == 0 then throw .fuel
  set { s with fuel := s.fuel - 1 }

/-- Clojure's special forms that the programs use (`Compiler.specials`). -/
def cljSpecial (o : Obj) : Bool :=
  match o with
  | .symbol _ "" n => ["def", "loop*", "recur", "if", "case*", "let*", "letfn*", "do", "fn*", "quote",
      "var", "import*", ".", "set!", "deftype*", "reify*", "try", "throw", "monitor-enter",
      "monitor-exit", "catch", "finally", "new", "&"].contains n
  | _ => false

/-- `lookupVar` / `resolveIn` for a symbol: the var, or a compile error for a private var of
another namespace. -/
def cljResolveVar (rt : Runtime) (ns name : String) : CA (Option VarCell) := do
  let (qns, qname) := rt.qualifySymbol ns name
  match rt.findVar qns qname with
  | none => pure none
  | some vr =>
    let v := (rt.var? vr).getD { ns := vr.ns, name := vr.name }
    if v.private_ && v.ns != rt.currentNs then cerr s!"var: #'{v.ns}/{v.name} is not public"
    pure (some v)

mutual

/-- `Compiler.analyze`. -/
partial def cljAnalyze (form : Obj) (env : CEnv) (ctx : Ctx) : CA CE := do
  cburn
  match form with
  | .symbol _ ns name =>
    if ns.isEmpty then
      if let some id := env.locals.lookup name then return .local id
    match ← cljResolveVar (← get).rt ns name with
    | some v =>
      if v.isMacro then cerr s!"Can't take value of a macro: #'{v.ns}/{v.name}"
      pure (.var v.ref)
    | none => cerr s!"Unable to resolve symbol: {symString form} in this context"
  | .persistentList _ [] => pure (.const form)
  | .persistentVector md xs =>
    let es ← xs.mapM (cljAnalyze · env .expr)
    let m ← match md with
      | some m => pure (some (← cljAnalyze m env .expr))
      | none => pure none
    pure (.vector es m)
  | .persistentArrayMap md kvs | .persistentHashMap md kvs =>
    let es ← kvs.mapM fun (k, v) => do pure (← cljAnalyze k env .expr, ← cljAnalyze v env .expr)
    let m ← match md with
      | some m => pure (some (← cljAnalyze m env .expr))
      | none => pure none
    pure (.map es m)
  | .persistentHashSet md xs =>
    let es ← xs.mapM (cljAnalyze · env .expr)
    let m ← match md with
      | some m => pure (some (← cljAnalyze m env .expr))
      | none => pure none
    pure (.set es m)
  | _ =>
    if form.sequential then cljAnalyzeSeq form env ctx
    else pure (.const form)

/-- `Compiler.analyzeSeq`. -/
partial def cljAnalyzeSeq (form : Obj) (env : CEnv) (ctx : Ctx) : CA CE := do
  let xs := form.elems.getD []
  let op := xs.headD .nil
  let isLocalOp := match op with
    | .symbol _ "" n => (env.locals.lookup n).isSome
    | _ => false
  -- macroexpand1: not for special forms, not when the operator is a local.
  if !cljSpecial op && !isLocalOp then
    match op with
    | .symbol _ ns name =>
      match ← cljResolveVar (← get).rt ns name with
      | some v =>
        if v.isMacro then
          let envMap : Obj := .persistentArrayMap none (env.locals.map fun (n, _) => (Obj.s n, .nil))
          match v.cljMacroFn <|> v.macroFn with
          | some f =>
            match f (form :: envMap :: xs.drop 1) with
            | .ok expanded => return ← cljAnalyze expanded env ctx
            | .error m => cerr s!"macroexpansion: {m}"
          | none => cerr "unbound macro"
        -- isInline
        if let some inl := v.inline then
          let ok := match v.inlineArities with | none => true | some ars => ars.contains (xs.length - 1)
          if ok then
            -- The programs' inline expansions are the same function's semantics: analyze as a call.
            let _ := inl
            pure ()
      | none => pure ()
    | _ => pure ()
  match op with
  | .symbol _ "" "if" =>
    if xs.length > 4 then cerr "Too many arguments to if"
    if xs.length < 3 then cerr "Too few arguments to if"
    let c ← cljAnalyze xs[1]! env .expr
    let t ← cljAnalyze xs[2]! env ctx
    let e ← if xs.length == 4 then cljAnalyze xs[3]! env ctx else pure (.const .nil)
    pure (.if_ c t e)
  | .symbol _ "" "do" =>
    let body := xs.drop 1
    if body.isEmpty then return .const .nil
    let n := body.length
    let mut es := []
    let mut i := 0
    for b in body do
      i := i + 1
      es := es ++ [← cljAnalyze b env (if i == n then ctx else .stmt)]
    pure (.do_ es)
  | .symbol _ "" "quote" =>
    if xs.length != 2 then cerr "Wrong number of args to quote"
    pure (.const xs[1]!)
  | .symbol _ "" "var" =>
    match xs.getD 1 .nil with
    | .symbol _ ns name =>
      match ← cljResolveVar (← get).rt ns name with
      | some v => pure (.theVar v.ref)
      | none => cerr s!"Unable to resolve var: {name} in this context"
    | _ => cerr "var requires a symbol"
  | .symbol _ "" "throw" =>
    pure (.throw (← cljAnalyze (xs.getD 1 .nil) env .expr))
  | .symbol _ "" "def" =>
    match xs.getD 1 .nil with
    | .symbol _ "" name =>
      let xs := if xs.length == 4 && (match xs[2]! with | .persistentString _ => true | _ => false)
        then [xs[0]!, xs[1]!, xs[3]!] else xs
      if xs.length > 3 then cerr "Too many arguments to def"
      let rt := (← get).rt
      let (rt', vr) := rt.internOwnedVar rt.currentNs name
      modify fun s => { s with rt := rt' }
      let v ← if xs.length == 3 then pure (some (← cljAnalyze xs[2]! env .expr)) else pure none
      pure (.def vr v)
    | _ => cerr "First argument to def must be a Symbol"
  | .symbol _ "" "let*" => cljAnalyzeLet xs env ctx false
  | .symbol _ "" "loop*" => cljAnalyzeLet xs env ctx true
  | .symbol _ "" "recur" =>
    if ctx != .ret || env.loopLocals.isNone then cerr "Can only recur from tail position"
    if env.noRecur then cerr "Cannot recur across try"
    let args := xs.drop 1
    let n := env.loopLocals.get!
    let es ← args.mapM (cljAnalyze · env .expr)
    if es.length != n then cerr s!"Mismatched argument count to recur, expected: {n} args, got: {es.length}"
    pure (.recur es)
  | .symbol _ "" "fn*" => cljAnalyzeFn xs env
  | .symbol _ "" "letfn*" =>
    match xs.getD 1 .nil with
    | .persistentVector _ bs =>
      let mut env' := env
      let mut ids := []
      let mut i := 0
      while i + 1 < bs.length do
        match bs[i]! with
        | .symbol _ "" n =>
          let id ← freshLocal
          env' := { env' with locals := (n, id) :: env'.locals }
          ids := ids ++ [id]
        | _ => cerr "Bad binding form, expected symbol"
        i := i + 2
      let mut binds := []
      i := 0
      for id in ids do
        binds := binds ++ [(id, ← cljAnalyze bs[i + 1]! env' .expr)]
        i := i + 2
      let body ← cljAnalyzeBody (xs.drop 2) env' ctx
      pure (.letfn binds body)
    | _ => cerr "Bad binding form, expected vector"
  | .symbol _ "" "try" =>
    -- The programs use try without catch: its body, recur not allowed through it.
    cljAnalyzeBody (xs.drop 1) { env with noRecur := true } ctx
  | _ =>
    let f ← cljAnalyze op env .expr
    let args ← (xs.drop 1).mapM (cljAnalyze · env .expr)
    pure (.call f args)

partial def cljAnalyzeBody (body : List Obj) (env : CEnv) (ctx : Ctx) : CA CE := do
  if body.isEmpty then return .const .nil
  let n := body.length
  let mut es := []
  let mut i := 0
  for b in body do
    i := i + 1
    es := es ++ [← cljAnalyze b env (if i == n then ctx else .stmt)]
  pure (.do_ es)

/-- `LetExpr.Parser` (Compiler.java:6860). -/
partial def cljAnalyzeLet (xs : List Obj) (env : CEnv) (ctx : Ctx) (isLoop : Bool) : CA CE := do
  let bs ← match xs.getD 1 .nil with
    | .persistentVector _ bs => pure bs
    | _ => cerr "Bad binding form, expected vector"
  if bs.length % 2 != 0 then cerr "Bad binding form, expected matched symbol expression pairs"
  -- A loop outside of return context is wrapped in a fn (FNONCE): its inits see no recur target,
  -- as inside a return-context loop.
  let initEnv := if isLoop then { env with loopLocals := none } else env
  let mut env' := initEnv
  let mut binds := []
  let mut i := 0
  while i + 1 < bs.length do
    match bs[i]! with
    | .symbol _ "" n =>
      let init ← cljAnalyze bs[i + 1]! env' .expr
      let id ← freshLocal
      env' := { env' with locals := (n, id) :: env'.locals }
      binds := binds ++ [(id, init)]
    | _ => cerr "Bad binding form, expected symbol"
    i := i + 2
  let bodyEnv := if isLoop then { env' with loopLocals := some binds.length, noRecur := false } else
    { env' with loopLocals := env.loopLocals }
  let body ← cljAnalyzeBody (xs.drop 2) bodyEnv (if isLoop then .ret else ctx)
  pure (.let_ binds body isLoop)

/-- `FnExpr.parse` / `FnMethod.parse` (Compiler.java:5860). -/
partial def cljAnalyzeFn (xs : List Obj) (env : CEnv) : CA CE := do
  let (selfName, rest) := match xs.getD 1 .nil with
    | .symbol _ _ n => (some n, xs.drop 2)
    | _ => (none, xs.drop 1)
  let selfId ← match selfName with
    | some _ => pure (some (← freshLocal))
    | none => pure none
  let methods : List Obj := match rest.headD .nil with
    | .persistentVector .. => [.persistentList none rest]
    | _ => rest
  let mut arities := []
  for m in methods do
    let ms := m.elems.getD []
    let ps ← match ms.headD .nil with
      | .persistentVector _ ps => pure ps
      | _ => cerr "fn params must be a vector"
    let mut menv : CEnv := { env with loopLocals := none, noRecur := false }
    if let (some n, some id) := (selfName, selfId) then
      menv := { menv with locals := (n, id) :: menv.locals }
    let mut pids := []
    let mut restId := none
    let mut seenAmp := false
    for p in ps do
      match p with
      | .symbol _ "" "&" => seenAmp := true
      | .symbol _ "" n =>
        let id ← freshLocal
        menv := { menv with locals := (n, id) :: menv.locals }
        if seenAmp then restId := some id else pids := pids ++ [id]
      | _ => cerr "fn params must be Symbols"
    menv := { menv with loopLocals := some (pids.length + (if restId.isSome then 1 else 0)) }
    let body ← cljAnalyzeBody (ms.drop 1) menv .ret
    arities := arities ++ [(pids, restId, body)]
  pure (.fn selfId arities)

end

/-! ## Evaluation -/

structure CClosure where
  self : Option Nat
  arities : List (List Nat × Option Nat × CE)
  env : List (Nat × Obj)
  deriving Inhabited

structure CEvState where
  closures : Array CClosure := #[]
  roots : List (VarRef × VarRoot) := []
  fuel : Nat := 200000

abbrev CEvM := StateT CEvState (Except Outcome)

def ctick : CEvM Unit := do
  let s ← get
  if s.fuel == 0 then throw .fuel
  set { s with fuel := s.fuel - 1 }

def cClosureObj (k : Nat) : Obj := .opaque .jitFunction k

mutual

partial def cEval (e : CE) (env : List (Nat × Obj)) : CEvM Flow := do
  ctick
  match e with
  | .const o => pure (.val (.obj o))
  | .local id => match env.lookup id with
    | some v => pure (.val (.obj v))
    | none => throw (.unsupported "unbound local")
  | .var vr => match (← get).roots.lookup vr with
    | some (.obj o) => pure (.val (.obj o))
    | some (.builtin n) => pure (.val (.obj (builtinObj (builtinNames.idxOf n))))
    | _ => throw (.thrown s!"Unbound var {vr.ns}/{vr.name}")
  | .theVar vr => pure (.val (.obj (.var vr.ns vr.name)))
  | .if_ c t el =>
    let cv ← cEvalV c env
    if cv.truthy then cEval t env else cEval el env
  | .do_ xs =>
    let mut last : Flow := .val (.obj .nil)
    for x in xs do
      last ← cEval x env
      if let .recur _ := last then return last
    pure last
  | .let_ binds body isLoop =>
    let mut env := env
    for (id, init) in binds do
      env := (id, ← cEvalV init env) :: env
    if !isLoop then return ← cEval body env
    let mut cur := env
    for _ in [0:100000] do
      match ← cEval body cur with
      | .val v => return .val v
      | .recur args =>
        cur := (binds.map (·.1)).zip (args.map Val.toObj) ++ cur
    throw .fuel
  | .recur args =>
    let vs ← args.mapM (cEvalV · env)
    pure (.recur (vs.map Val.obj))
  | .fn self arities =>
    let s ← get
    let k := s.closures.size
    set { s with closures := s.closures.push { self, arities, env } }
    pure (.val (.obj (cClosureObj k)))
  | .letfn binds body =>
    let s ← get
    let base := s.closures.size
    let mut env' := env
    let mut idx := 0
    for (id, _) in binds do
      env' := (id, cClosureObj (base + idx)) :: env'
      idx := idx + 1
    for (_, f) in binds do
      match f with
      | .fn self ars => modify fun s => { s with closures := s.closures.push { self, arities := ars, env := env' } }
      | _ => throw (.unsupported "letfn value")
    cEval body env'
  | .call f args =>
    let fv ← cEvalV f env
    let vs ← args.mapM (cEvalV · env)
    pure (.val (.obj (← cInvoke fv vs)))
  | .def vr value =>
    match value with
    | some v =>
      let x ← cEvalV v env
      modify fun s => { s with roots := (vr, .obj x) :: s.roots.filter (·.1 != vr) }
    | none => modify fun s => if (s.roots.lookup vr).isSome then s else { s with roots := (vr, .unbound) :: s.roots }
    pure (.val (.obj (.var vr.ns vr.name)))
  | .throw x =>
    let v ← cEvalV x env
    throw (.thrown v.pr)
  | .vector xs md =>
    let vs ← xs.mapM (cEvalV · env)
    let m ← md.mapM (cEvalV · env)
    pure (.val (.obj (.persistentVector m vs)))
  | .map kvs md =>
    let vs ← kvs.mapM fun (k, v) => do pure (← cEvalV k env, ← cEvalV v env)
    let m ← md.mapM (cEvalV · env)
    pure (.val (.obj (.persistentArrayMap m vs)))
  | .set xs md =>
    let vs ← xs.mapM (cEvalV · env)
    let m ← md.mapM (cEvalV · env)
    pure (.val (.obj (.persistentHashSet m vs)))

partial def cEvalV (e : CE) (env : List (Nat × Obj)) : CEvM Obj := do
  match ← cEval e env with
  | .val v => pure v.toObj
  | .recur _ => throw (.compileError "recur escaped")

partial def cInvoke (f : Obj) (args : List Obj) : CEvM Obj := do
  ctick
  match f with
  | .opaque .nativeFunctionWrapper k =>
    match builtin (builtinNames.getD k "") args with
    | some (.ok r) => pure r
    | some (.error m) => throw (.thrown m)
    | none => throw (.thrown "ArityException")
  | .opaque .jitFunction k =>
    let c := (← get).closures[k]!
    let n := args.length
    let fixed := c.arities.find? fun (ps, r, _) => r.isNone && ps.length == n
    let variadic := c.arities.find? fun (ps, r, _) => r.isSome && ps.length ≤ n
    let some (ps, r, body) := fixed <|> variadic | throw (.thrown s!"ArityException: Wrong number of args ({n})")
    let selfEnv := match c.self with | some id => [(id, f)] | none => []
    let bind (xs : List Obj) : List (Nat × Obj) :=
      match r with
      | some rid =>
        let restV : Obj := if xs.length > ps.length then .persistentList none (xs.drop ps.length) else .nil
        ps.zip (xs.take ps.length) ++ [(rid, restV)] ++ selfEnv ++ c.env
      | none => ps.zip xs ++ selfEnv ++ c.env
    let mut cur := args
    for _ in [0:100000] do
      match ← cEval body (bind cur) with
      | .val v => return v.toObj
      | .recur vs =>
        let vs := vs.map Val.toObj
        cur := match r with
          | some _ => vs.take ps.length ++ ((vs.drop ps.length).headD .nil |>.elems |>.getD [])
          | none => vs
    throw .fuel
  | .keyword .. =>
    match args with
    | [m] => pure (builtinGet m f)
    | [m, d] => pure (builtinGet m f d)
    | _ => throw (.thrown "ArityException: keyword")
  | _ => throw (.thrown s!"{f.pr} cannot be cast to clojure.lang.IFn")

end

end Jank.Analyzer
