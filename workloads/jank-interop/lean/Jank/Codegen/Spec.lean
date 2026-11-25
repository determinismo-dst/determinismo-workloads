import Jank.Codegen.Surface

/-!
# The spec: Clojure 1.12's meaning of a program

Per clojure.org/reference/evaluation and special_forms: a call evaluates the operator, then the
operands, left to right; `let`/`loop` bind sequentially, `recur` rebinds the nearest `loop` or
`fn` (tail position only); a symbol names the innermost local, else the enclosing named `fn`,
else a var, whose current root is read at each use; `def` evaluates the metadata map on its name
(Compiler.DefExpr: `analyze(C.EXPRESSION, mm)`) in the lexical scope and sets the var's root;
`try`/`catch`/`finally` as the JVM (finally on every exit; its exception replaces the one in
flight); `case` dispatches by `=` on the test constants.
-/

namespace Jank.Codegen.Spec

open Jank.Codegen Jank.Analyzer

structure Closure where
  name : Option String
  params : List String
  body : List Form
  env : List (String × JV)
  deriving Inhabited

structure CS where
  fns : Array Closure := #[]
  vars : List (String × (Option JV × JV)) := userPrims.map fun (n, p) => ("user/" ++ n, (some (JV.prim p), JV.nil))
  out : List String := []
  fuel : Nat := 100000
  deriving Inhabited

inductive CExc where
  | thrown (v : JV)
  | recur (args : List JV)
  | fuel
  | err (m : String)
  deriving Inhabited

abbrev CM := EStateM CExc CS

def tickC : CM Unit := do
  let s ← get
  if s.fuel == 0 then throw .fuel
  set { s with fuel := s.fuel - 1 }

def varRootC (q : String) : CM JV := do
  match assocGet? (← get).vars q with
  | some (some v, _) => pure v
  | _ => throw (.thrown (.other s!"unbound var {q}"))

mutual

partial def eval (env : List (String × JV)) (f : Form) : CM JV := do
  tickC
  match f with
  | .lit o => pure (JV.ofObj o)
  | .sym n =>
    match assocGet? env n with
    | some v => pure v
    | none => varRootC ("user/" ++ n)
  | .vec xs => pure (.vec (← xs.mapM (eval env)) none)
  | .call fn args =>
    let fv ← eval env fn
    let avs ← args.mapM (eval env)
    apply fv avs
  | .let_ bs body =>
    let mut e := env
    for (n, v) in bs do e := (n, ← eval e v) :: e
    evalBody e body
  | .loop bs body =>
    let mut e := env
    for (n, v) in bs do e := (n, ← eval e v) :: e
    let names := bs.map (·.1)
    let mut g := 100000
    while g > 0 do
      g := g - 1
      let r ← tryCatch (do let v ← evalBody e body; pure (Sum.inl v)) fun ex =>
        match ex with
        | .recur args => pure (Sum.inr args)
        | other => throw other
      match r with
      | .inl v => return v
      | .inr args =>
        -- every binding rebound (later duplicates shadow earlier ones)
        e := (names.zip args).foldl (fun acc (n, v) => (n, v) :: acc) env
    throw .fuel
  | .recur args => throw (.recur (← args.mapM (eval env)))
  | .if_ c t el =>
    if (← eval env c).truthy then eval env t
    else match el with
      | some x => eval env x
      | none => pure .nil
  | .do_ xs => evalBody env xs
  | .fn_ name params body =>
    let s ← get
    set { s with fns := s.fns.push { name, params, body, env } }
    pure (.fn s.fns.size)
  | .def_ name mta v =>
    let q := "user/" ++ name
    -- the metadata map is evaluated in the lexical scope (locals visible)
    let mut m : List (JV × JV) := []
    for (k, x) in mta do
      let vars := (← get).vars
      let lookup := fun (q : String) =>
        match assocGet? env (strDrop q 5) with
        | some v => if q.startsWith "user/" then some v else none
        | none => (assocGet? vars q).bind (·.1)
      match evalForm lookup (← get).out x with
      | .ok (val, o) => modify (fun s => { s with out := o }); m := m ++ [(.kw "" k, val)]
      | .error e => throw (.thrown (.other e))
    let metaV : JV := if mta.isEmpty then .nil else .map m
    match v with
    | some x =>
      let val ← eval env x
      modify fun s => { s with vars := assocSet s.vars q (some val, metaV) }
    | none =>
      modify fun s => { s with vars := assocSet s.vars q ((assocGet? s.vars q).bind (·.1), metaV) }
    pure (.var q)
  | .throw_ x => throw (.thrown (← eval env x))
  | .try_ body c fin =>
    let r ← tryCatch (do let v ← evalBody env body; pure (Sum.inl v)) fun ex =>
      match ex with
      | .thrown v => pure (Sum.inr v)
      | other => throw other
    let res ← match r, c with
      | .inl v, _ => pure (Sum.inl v)
      | .inr v, some (sym, h) =>
        tryCatch (do let x ← evalBody ((sym, v) :: env) h; pure (Sum.inl x)) fun ex =>
          match ex with
          | .thrown v2 => pure (Sum.inr v2)
          | other => throw other
      | .inr v, none => pure (Sum.inr v)
    if let some fs := fin then let _ ← evalBody env fs
    match res with
    | .inl v => pure v
    | .inr v => throw (.thrown v)
  | .letfn fns body =>
    -- each fn sees all the letfn names (closures over the extended environment)
    let s ← get
    let base := s.fns.size
    let names := fns.map (·.1)
    let env' := (names.zipIdx.map fun (n, i) => (n, JV.fn (base + i))) ++ env
    set { s with fns := s.fns ++ (fns.map fun (n, ps, b) => { name := some n, params := ps, body := b, env := env' : Closure }).toArray }
    evalBody env' body
  | .case_ e clauses dflt =>
    let v ← eval env e
    match clauses.find? (fun (t, _) => v.equiv (.int t)) with
    | some (_, th) => eval env th
    | none => eval env dflt
  | .varq n => pure (.var ("user/" ++ n))

partial def evalBody (env : List (String × JV)) (xs : List Form) : CM JV := do
  let mut r := JV.nil
  for x in xs do r ← eval env x
  pure r

partial def apply (f : JV) (args : List JV) : CM JV := do
  tickC
  match f with
  | .fn i =>
    let some c := (← get).fns[i]? | throw (.err "no closure")
    if c.params.length != args.length then throw (.thrown (.other "wrong number of args"))
    let self : List (String × JV) := match c.name with | some n => [(n, .fn i)] | none => []
    let mut argv := args
    let mut g := 100000
    while g > 0 do
      g := g - 1
      let e := (c.params.zip argv).reverse ++ self ++ c.env
      let r ← tryCatch (do let v ← evalBody e c.body; pure (Sum.inl v)) fun ex =>
        match ex with
        | .recur a => pure (Sum.inr a)
        | other => throw other
      match r with
      | .inl v => return v
      | .inr a => argv := a
    throw .fuel
  | .var q => apply (← varRootC q) args
  | .prim "user/meta-of" =>
    match args with
    | [.var q] => pure ((assocGet? (← get).vars q).map (·.2) |>.getD .nil)
    | _ => throw (.thrown (.other "meta-of"))
  | .prim n =>
    match prim n args (← get).out with
    | .ok (v, o) => modify (fun s => { s with out := o }); pure v
    | .error e => throw (.thrown (.other e))
  | other => throw (.thrown (.other s!"{other.show} is not callable"))

end

/-- How a program ended. -/
inductive Outcome where
  | value (v : JV) (out : List String)
  | threw (out : List String)
  /-- jank only: the generated C++ does not compile, or the compiler itself fails. -/
  | compileError (msg : String)
  /-- jank only: undefined behaviour, `std::terminate`. -/
  | crash (msg : String)
  /-- Outside what the models cover (not a result). -/
  | unsupported (msg : String)
  deriving Inhabited

def Outcome.show : Outcome → String
  | .value v o => s!"{v.show}{if o.isEmpty then "" else " printing " ++ toString o}"
  | .threw o => s!"throws{if o.isEmpty then "" else " after printing " ++ toString o}"
  | .compileError m => s!"compile error ({m})"
  | .crash m => s!"crash ({m})"
  | .unsupported m => s!"unsupported ({m})"

/-- Clojure's outcome: the forms evaluated in order; `result` read from `user/result` when set. -/
def run (body : List Form) : Outcome :=
  match (evalBody [] body).run {} with
  | .ok v s => .value v s.out
  | .error (.thrown _) s => .threw s.out
  | .error .fuel _ => .unsupported "fuel"
  | .error (.recur _) _ => .unsupported "recur outside a loop"
  | .error (.err m) _ => .unsupported m

end Jank.Codegen.Spec
