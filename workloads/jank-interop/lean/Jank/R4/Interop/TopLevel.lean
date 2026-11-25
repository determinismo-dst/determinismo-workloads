import Jank.R3.Interop.Worlds

/-!
# Round 4: top-level evaluation around interop forms (the S49/S57 feedback)

Round 3 judged each interop case on one analysis, against a world where every `cpp/raw`
declaration already existed, and took every `if` as compiled. On the real jank the round-3 tests
for S49 and S57 (and S50 and S53, which share their shape) failed with an analysis error, not with
the predicted value. This file replicates the two mechanisms the round-3 replica left out:

- **What a top-level form sees.** `context::eval` (runtime/context_dynamic.cpp 220-226) and
  `eval_string` (59-79) analyze a read form whole, then evaluate it. `analyze_do`
  (analyze/processor.cpp 2245) analyzes every sub-form before anything runs; `analyze_cpp_raw`
  (4136-4209) only wraps the code in a guard, and `evaluate.cpp` `eval(cpp_raw)` (633-637) is what
  hands it to the interpreter. So inside one top-level `(do (cpp/raw "…") use)` the use is
  analyzed before its declaration exists: `analyze_cpp_symbol` (3855-4053) fails in
  `cpp_util::resolve_scope`, tries the preprocessor (`resolve_literal_value`) and returns
  `analyze_unresolved_cpp_symbol`; the DSL head of `(#cpp (f T) …)` fails in the same lookup
  (5617-5624, `analyze_invalid_cpp_dsl`).
- **Which `if` is compiled.** `evaluate.cpp` interprets a top-level `if` (594-606): it evaluates
  the condition, then the chosen branch alone, each through its own wrapper (a `cpp_value` is
  wrapped, compiled and boxed by its own type, 644-649). Inside a fn (or a `let`, `loop`, `try`,
  which evaluate.cpp wraps and compiles) codegen declares one local of the `if`'s type
  (ir/processor.cpp `gen(if)` 647-700, cpp_processor.cpp `gen(local)` 913 and `gen(set_local)`
  `local = std::move(branch)`), so the chosen branch is converted to that type by C++ assignment,
  then boxed by it (`convert<T>::into_object`, cpp_processor.cpp 1287-1331).

The values are Clojure-visible: an integer (boxed from any integral C++ type through `i64`), a
double, a boolean.
-/

namespace Jank.R4.Interop.TopLevel

open Jank.Interop
open Jank.R3.Interop
open Jank.R3.Interop.Clang
open Jank.R3.Interop.CppInterOp

/-- A Clojure-visible value. -/
inductive Val where
  | int (n : Int)
  | dbl (x : Float)
  | bool (b : Bool)
  deriving Repr, Inhabited

def Val.show : Val → String
  | .int n => toString n
  | .dbl x => toString x
  | .bool b => toString b

/-- Clojure's `=` between the values these programs produce (`(= 2 2.0)` is false). -/
def Val.same : Val → Val → Bool
  | .int a, .int b => a == b
  | .dbl a, .dbl b => a == b
  | .bool a, .bool b => a == b
  | _, _ => false

/-- Truncation toward zero of a finite double (C++ [conv.fpint]); the values here are small. -/
def truncF (x : Float) : Int :=
  let t := if x < 0 then -((-x).floor) else x.floor
  if t < 0 then -(((-t).toUInt64).toNat : Int) else (t.toUInt64.toNat : Int)

/-- C++'s conversion of a value of the source kind to the builtin `k` by assignment
([conv.integral] modulo 2^w since C++20, [conv.fpint] truncation, [conv.bool]). `none` for UB
(a double out of the target's range). -/
def convertTo (p : Platform) (k : Builtin) : Val → Option Val
  | .bool b => if k == .bool then some (.bool b)
      else if k.isFloating then some (.dbl (if b then 1.0 else 0.0))
      else some (.int (if b then 1 else 0))
  | .int n =>
    if k == .bool then some (.bool (n != 0))
    else if k.isFloating then some (.dbl (Float.ofInt n))
    else
      let w := k.width
      let m : Int := (2 : Int) ^ w
      let r := n % m
      let r := if k.isSigned p && r ≥ m / 2 then r - m else r
      some (.int r)
  | .dbl x =>
    if k == .bool then some (.bool (x != 0.0))
    else if k.isFloating then some (.dbl x)
    else
      let t := truncF x
      if k.fits p t then some (.int t) else none

/-- The value an expression of C++ type `t` boxes to (`convert<T>::into_object`, builtin.hpp:
integral types and enums through `i64`, `bool` to a boolean, floating to a real). -/
def boxAs (p : Platform) (x : XWorld) (t : CType) (v : Val) : Option Val :=
  match (nonRef t).canonical.unqual with
  | .b k => convertTo p k v
  | .enum n => match (x.findEnum n) with
    | some e => convertTo p e.underlying v
    | none => convertTo p .int v
  | _ => none

/-! ## The world of the feedback programs -/

/-- A `cpp/raw` declaration, as far as the feedback programs use one. -/
inductive Decl where
  /-- `double gd = 2.5;` (a global variable: `cpp/gd` is an lvalue of its type). -/
  | global (name : String) (type : CType) (init : Val)
  /-- `template <typename T> T add(T a, T b)` and friends. -/
  | fnTemplate (t : FnTemplate)
  /-- `long (*twice_ptr)(long const &) = twice;` -/
  | fnPtr (name : String) (type : CType)
  /-- A class (with conversion functions) and a function returning it by value. -/
  | classMaker (cls : ClassDecl) (maker : String)
  /-- An enumerator (`cpp/red` is a prvalue of the enum type, processor.cpp 3818-3822). -/
  | enumConst (name : String) (type : CType) (v : Val)
  deriving Inhabited

def Decl.name : Decl → String
  | .global n .. | .fnPtr n _ | .classMaker _ n | .enumConst n .. => n
  | .fnTemplate t => t.name

/-- What the program refers to. -/
inductive Form where
  | raw (decls : List Decl)
  | do_ (forms : List Form)
  | if_ (c : Form) (t e : Form)
  | lit (t : CType) (v : Val)
  /-- `cpp/name`. -/
  | cppSym (name : String)
  /-- `(#cpp (f T…) args…)`. -/
  | tmplCall (name : String) (explicit : List CType) (args : List Form)
  /-- `(cpp/name args…)` through a function pointer. -/
  | ptrCall (name : String) (args : List Form)
  /-- `(cpp/<op> a b)` where `a` is `(cpp/maker)`. -/
  | classOp (op : Cxx.Op) (maker : String) (other : Form)
  /-- `((fn [c] body) arg)`: the body is compiled. -/
  | callFn (param : String) (body : Form) (arg : Form)
  /-- the fn's parameter (an object). -/
  | param (name : String)
  deriving Inhabited

/-- The analyzed form: its C++ type, and how to run it in either context. -/
inductive AExpr where
  | raw (decls : List Decl)
  | do_ (es : List AExpr)
  | if_ (c t e : AExpr) (type : CType)
  | lit (t : CType) (v : Val)
  | global (t : CType) (v : Val)
  | call (ret : CType) (v : Option Val)
  | fnCall (body : AExpr) (arg : AExpr)
  | param (v : Val)
  deriving Inhabited

partial def AExpr.type : AExpr → CType
  | .raw _ => objectRef
  | .do_ es => match es.getLast? with | some e => e.type | none => objectRef
  | .if_ _ _ _ t => t
  | .lit t _ => t
  | .global t _ => t
  | .call r _ => r
  | .fnCall .. => objectRef
  | .param _ => objectRef

structure Env where
  decls : List Decl := []
  /-- The fn parameter's value while analyzing a fn body. -/
  params : List (String × Val) := []
  deriving Inhabited

def Env.find (env : Env) (n : String) : Option Decl := env.decls.find? (·.name == n)

/-- The XWorld the analysis queries: round 3's `x3` plus the declared templates and classes. -/
def Env.xworld (env : Env) : XWorld :=
  let x := Jank.R3.Interop.Worlds.x3
  { x with
    templates := x.templates ++ env.decls.filterMap (fun | .fnTemplate t => some t | _ => none),
    w := { x.w with classes := x.w.classes ++ env.decls.filterMap (fun | .classMaker c _ => some c | _ => none) } }

def unresolved (n : String) : String :=
  s!"analyze/unresolved-cpp-symbol: unable to find C++ symbol `{n}` (cpp_util::resolve_scope failed, and it is no preprocessor value)"

def addArgs : List Val → Option Val
  | [.int a, .int b] => some (.int (a + b))
  | [.dbl a, .dbl b] => some (.dbl (a + b))
  | [.int a, .dbl b] => some (.dbl (Float.ofInt a + b))
  | [.dbl a, .int b] => some (.dbl (a + Float.ofInt b))
  | _ => none

/-- Analysis of one form (`processor::analyze`), in the environment declared so far. A `do`
analyzes all of its forms first (processor.cpp 2245-2290); `cpp/raw` declares nothing at
analysis. -/
partial def analyze (p : Platform) (env : Env) : Form → Except String AExpr
  | .raw ds => .ok (.raw ds)
  | .do_ fs => do
    let es ← fs.mapM (analyze p env)
    .ok (.do_ es)
  | .lit t v => .ok (.lit t v)
  | .param n => match env.params.lookup n with
    | some v => .ok (.param v)
    | none => .error s!"unable to resolve symbol `{n}`"
  | .cppSym n => match env.find n with
    | some (.global _ t v) => .ok (.global (.lref t) v)
    | some (.enumConst _ t v) => .ok (.global t v)
    | some _ => .error s!"`{n}` is not a value here"
    | none => .error (unresolved n)
  | .tmplCall n explicitArgs args => do
    let some (.fnTemplate t) := env.find n
      | .error s!"analyze/invalid-cpp-dsl: {unresolved n}"
    let as ← args.mapM (analyze p env)
    let c : Jank.R3.Interop.Worlds.TmplCase := { tmpl := t, explicitArgs, callArgs := as.map AExpr.type }
    match Jank.R3.Interop.Worlds.tmplJank p c with
    | .error e => .error e
    | .ok r =>
      -- the call deduces from the arguments (tmplJank): `add<int>(1, 2)` and friends
      let vals := as.filterMap fun | .lit _ v => some v | _ => none
      .ok (.call r (if t.name.endsWith "add" then addArgs vals else none))
  | .ptrCall n args => do
    let some (.fnPtr _ ty) := env.find n | .error (unresolved n)
    let as ← args.mapM (analyze p env)
    match Paths.indirectCall p env.xworld ty (as.map AExpr.type) with
    | .error e => .error e
    | .ok r => .ok (.call r none)
  | .classOp op maker other => do
    let some (.classMaker c _) := env.find maker | .error (unresolved maker)
    let o ← analyze p env other
    match Paths.classOperatorCall p env.xworld op [.record c.name, o.type] with
    | .error e => .error e
    | .ok r => .ok (.call r none)
  | .if_ c t e => do
    let ce ← analyze p env c
    let te ← analyze p env t
    let ee ← analyze p env e
    match Paths.findBranchCommonType p env.xworld te.type ee.type with
    | .error err => .error err
    | .ok (ty, _, _) => .ok (.if_ ce te ee ty)
  | .callFn prm body arg => do
    let a ← analyze p env arg
    let argV := match a with | .lit _ v | .global _ v | .param v => v | _ => .bool false
    let b ← analyze p { env with params := (prm, argV) :: env.params } body
    .ok (.fnCall b a)

def truthy : Val → Bool
  | .bool b => b
  | _ => true

/-- Compiled meaning of an analyzed expression: the C++ value of its type (`none`: no value, or
UB). -/
partial def runCompiled (p : Platform) (x : XWorld) : AExpr → Option Val
  | .lit _ v | .global _ v | .param v => some v
  | .call _ v => v
  | .do_ es => es.foldl (fun _ e => runCompiled p x e) none
  | .raw _ => none
  | .fnCall b _ => runCompiled p x b >>= boxAs' (b.type)
  | .if_ c t e ty => do
    let cv ← runCompiled p x c
    let branch := if truthy cv then t else e
    let v ← runCompiled p x branch
    -- `ty local{}; local = std::move(branch);`
    if Jank.Interop.CppUtil.isAnyObject x.w ty then some v
    else match (nonRef ty).canonical.unqual with
      | .b k => convertTo p k v
      | .enum _ => boxAs p x ty v
      | _ => some v
where
  boxAs' (t : CType) (v : Val) : Option Val :=
    if Jank.Interop.CppUtil.isAnyObject x.w t then some v else boxAs p x t v

/-- Top-level evaluation (`evaluate::eval`): `if` and `do` interpreted, everything else wrapped,
compiled and boxed by its type; `cpp/raw` declares. Returns the value and the environment. -/
partial def evalTop (p : Platform) (env : Env) (e : AExpr) : Except String (Option Val × Env) :=
  match e with
  | .raw ds => .ok (none, { env with decls := env.decls ++ ds })
  | .do_ es => es.foldlM (fun (_, en) x => evalTop p en x) (none, env)
  | .if_ c t el _ => do
    let (cv, env) ← evalTop p env c
    let branch := if truthy (cv.getD (.bool false)) then t else el
    evalTop p env branch
  | other =>
    let x := env.xworld
    match runCompiled p x other with
    | none => .ok (none, env)
    | some v =>
      let t := other.type
      .ok ((if Jank.Interop.CppUtil.isAnyObject x.w t then some v else boxAs p x t v), env)

/-- A program: top-level forms, each read, analyzed whole and evaluated in turn
(`eval_string`); the value of the last, or the first error. -/
def runProgram (p : Platform) (forms : List Form) : Except String (Option Val) := do
  let mut env : Env := {}
  let mut last : Option Val := none
  for f in forms do
    let a ← analyze p env f
    let (v, env') ← evalTop p env a
    env := env'
    last := v
  return last

/-! ## The round-3 tests and their corrected shapes -/

def tmplAdd (n : String) : FnTemplate := { name := n, tparams := 1, params := [.param 0, .param 0], ret := .param 0 }
def litI (n : Int) : Form := .lit (.b .int) (.int n)
def litD (x : Float) : Form := .lit (.b .double) (.dbl x)
def litB (b : Bool) : Form := .lit (.b .bool) (.bool b)

def twicePtrType : CType := .ptr (.fn (.b .long) [.lref (.const (.b .long))])
def metersClass (n : String) : ClassDecl := { name := n, convertsTo := [.b .double] }

/-- One program as round 3's test wrote it: `(ev "(do (cpp/raw …) use)")`. -/
def r3Shape (decl : Decl) (use : Form) : List Form := [.do_ [.raw [decl], use]]

/-- The corrected shape: the declaration in its own top-level eval first. -/
def r4Shape (decl : Decl) (use : Form) : List Form := [.raw [decl], use]

structure Item where
  name : String
  text : String
  decl : Decl
  use : Form
  /-- The use with the `if` inside a compiled fn (S57 only). -/
  useInFn : Option Form := none
  /-- C++/Clojure's value. -/
  spec : Val

def items : List Item :=
  [{ name := "S49", text := "(#cpp (s49_add double) 1 2)",
     decl := .fnTemplate (tmplAdd "s49_add"),
     use := .tmplCall "s49_add" [.b .double] [litI 1, litI 2], spec := .dbl 3.0 },
   { name := "S50", text := "(cpp/s50_ptr 21)",
     decl := .fnPtr "s50_ptr" twicePtrType,
     use := .ptrCall "s50_ptr" [litI 21], spec := .int 42 },
   { name := "S53", text := "(cpp/+ (cpp/s53_mk) 1.0)",
     decl := .classMaker (metersClass "s53_meters") "s53_mk",
     use := .classOp .plus "s53_mk" (litD 1.0), spec := .dbl 2.5 },
   { name := "S57", text := "(if false 1 cpp/s57_gd)",
     decl := .global "s57_gd" (.b .double) (.dbl 2.5),
     use := .if_ (litB false) (litI 1) (.cppSym "s57_gd"),
     useInFn := some (.callFn "c" (.if_ (.param "c") (litI 1) (.cppSym "s57_gd")) (litB false)),
     spec := .dbl 2.5 }]

def showRes : Except String (Option Val) → String
  | .ok (some v) => v.show
  | .ok none => "nil"
  | .error e => s!"error: {e}"

def outcomeLine (p : Platform) (it : Item) : List String :=
  let r3 := runProgram p (r3Shape it.decl it.use)
  let r4 := runProgram p (r4Shape it.decl it.use)
  let fnLine := match it.useInFn with
    | some u => [s!"    corrected, inside a fn ((fn [c] (if c 1 cpp/…)) false): {showRes (runProgram p (r4Shape it.decl u))}"]
    | none => []
  [s!"  {it.name} {it.text}: C++/Clojure {it.spec.show}",
   s!"    round-3 test shape (one top-level do): {showRes r3}",
   s!"    corrected (cpp/raw in its own top-level eval): {showRes r4}"] ++ fnLine

/-! ## World XVI in both contexts -/

/-- The value each round-3 branch form holds (the globals the world declares). -/
def branchVal : String → Val
  | "1" => .int 1
  | "3000000000" => .int 3000000000
  | "2.5" => .dbl 2.5
  | "true" => .bool true
  | "cpp/gint" => .int 7
  | "cpp/glong" => .int 5000000000
  | "cpp/gdouble" => .dbl 2.5
  | "cpp/guint" => .int 4000000000
  | "cpp/red" => .int 0
  | _ => .int 0

def branchForm (s : String) (t : CType) : Form :=
  if s.startsWith "cpp/" then .cppSym (s.drop 4).toString else .lit t (branchVal s)

def branchDecls : List Decl :=
  Jank.R3.Interop.Worlds.brTypes.filterMap fun (s, t) =>
    if s.startsWith "cpp/" && s != "cpp/red" then some (.global (s.drop 4).toString (nonRef t) (branchVal s)) else
    if s == "cpp/red" then some (.enumConst "red" (.enum "color") (.int 0)) else none

/-- One case: then/else forms, the chosen branch, and the context. -/
structure CtxCase where
  a : String × CType
  b : String × CType
  cond : Bool
  inFn : Bool
  deriving Inhabited

def CtxCase.text (c : CtxCase) : String :=
  let body := s!"(if c {c.a.1} {c.b.1})"
  if c.inFn then s!"((fn [c] {body}) {c.cond})" else s!"top level, c = {c.cond}: {body}"

def ctxProgram (c : CtxCase) : List Form :=
  let ifF (cf : Form) := Form.if_ cf (branchForm c.a.1 c.a.2) (branchForm c.b.1 c.b.2)
  [.raw branchDecls] ++
    if c.inFn then [.callFn "c" (ifF (.param "c")) (litB c.cond)] else [ifF (litB c.cond)]

/-- Clojure's `(if c a b)`: the chosen branch's own value. -/
def ctxSpec (c : CtxCase) : Val := branchVal (if c.cond then c.a.1 else c.b.1)

def ctxJudge (p : Platform) (c : CtxCase) : Option (String × String) :=
  match runProgram p (ctxProgram c) with
  | .error e => some ("rejects", s!"{c.text}: Clojure {(ctxSpec c).show}; jank {e}")
  | .ok none => some ("no-value", s!"{c.text}: Clojure {(ctxSpec c).show}; jank no value (UB)")
  | .ok (some v) =>
    if v.same (ctxSpec c) then none
    else some (if c.inFn then "compiled-if-converts" else "top-level-if-converts",
      s!"{c.text}: Clojure {(ctxSpec c).show}; jank {v.show}")

def allCtx : List CtxCase :=
  let ts := Jank.R3.Interop.Worlds.brTypes
  ts.flatMap fun a => ts.flatMap fun b => [true, false].flatMap fun cond =>
    [false, true].map fun inFn => { a, b, cond, inFn }

end Jank.R4.Interop.TopLevel
