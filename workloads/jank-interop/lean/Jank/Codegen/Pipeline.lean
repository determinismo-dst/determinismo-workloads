import Jank.Codegen.Spec
import Jank.Codegen.Opt
import Jank.Codegen.Cpp
import Jank.Codegen.Exec
import Jank.Equality

/-!
# jank's pipeline for a program: analyze → IR → passes → C++ → compile check → run

`jankRun` follows `evaluate::eval(expr::function_ref)` (evaluate.cpp:522-554 in 7135b7708, eval target) and
`context::eval_string` with `*compile-files*` (context_dynamic.cpp:83-125, module target):
`ir::create` (the IR and its passes), `codegen::gen_cpp`, then the C++ compiler (here: the parse
and scope check of `CppAst`) and the program run (`Exec`).
-/

namespace Jank.Codegen

open Jank.Analyzer Jank.Codegen.Exec
open Jank.Codegen.Spec (Outcome)

/-- An analyzer object as the first round's equality values (for jank's `=` and `to_hash`). -/
partial def objToV : Obj → Jank.Equality.V
  | .nil => .nil
  | .boolean b => .str (if b then "\u0001true" else "\u0001false")
  | .smallInteger v => .int v.toInt
  | .integer v => .int v.toInt
  | .bigInteger v => .big v
  | .real b | .smallReal b => .real b
  | .persistentString s => .str s
  | .keyword ns n => .kw (if ns.isEmpty then n else ns ++ "/" ++ n)
  | .symbol _ ns n => .str ("\u0001sym " ++ ns ++ "/" ++ n)
  | .character d => .str ("\u0001char " ++ d)
  | .persistentVector _ xs => .vec (xs.map objToV)
  | .persistentList _ xs => .list (xs.map objToV)
  | .lazySequence _ xs | .seqOf _ xs => .lazy (xs.map objToV)
  | .persistentHashSet _ xs | .persistentSortedSet _ xs => .set (xs.map objToV)
  | .persistentArrayMap _ kvs | .persistentHashMap _ kvs | .persistentSortedMap _ kvs =>
      .map (kvs.map fun (k, v) => (objToV k, objToV v))
  | o => .str s!"\u0001other {repr o.type}"

def objMeta : Obj → Option Obj
  | .symbol m _ _ | .persistentList m _ | .persistentVector m _ | .persistentArrayMap m _
  | .persistentHashMap m _ | .persistentHashSet m _ => m
  | _ => none

/-- Two constants land on one key of `lifted_constants` / `global_constants`
(`std::hash<object_ref>` then `very_equal_to_with_meta`, object.cpp:346-354): the same type,
jank's `=`, equal metadata, and (the map compares the cached hashes first) the same hash. -/
def constKey (a b : Obj) : Bool :=
  let eq := fun x y => Jank.Equality.jankEq .signed 24 (objToV x) (objToV y)
  let h := fun x => Jank.Equality.jankHash .signed 24 (objToV x)
  a.type == b.type && eq a b && h a == h b &&
    (match objMeta a, objMeta b with
     | none, none => true
     | some x, some y => eq x y
     | _, _ => false)

structure Config where
  target : Target := .eval
  passes : Passes := {}
  runtime : Runtime := {}
  deriving Repr, Inhabited

/-- What the pipeline produced, for a report. -/
structure Trace where
  ir : String := ""
  cpp : String := ""
  expr : String := ""
  deriving Inhabited

def irText (m : Module) : String :=
  String.join (m.functions.toList.map fun f =>
    s!"fn {f.name}\n" ++ String.join (f.blocks.toList.map fun b =>
      s!"  {b.name}:\n" ++ String.join (b.insts.toList.map fun i => s!"    {i.kindName} {i.name} {repr i |>.pretty 200 |>.replace "\n" " "}\n")))

/-- Run a program through jank's code generator. -/
def jankRun (body : List Form) (cfg : Config) (withTrace : Bool := false) : Outcome × Trace := Id.run do
  let rootName := if cfg.target == .module then some "jank_load_user" else none
  let (root, ast) ← match analyzeProgram body rootName with
    | .ok r => pure r
    | .error e => return (.unsupported s!"analysis: {e}", {})
  -- IR
  let g0 : Global := { mod := default, arena := ast.arena, counter := ast.counter, constKey := constKey }
  let st0 : GenState := { g := g0, b := {} }
  let modName := if cfg.target == .module then "user" else "user_prog"
  let st ← match (createModule root modName cfg.target).run st0 with
    | .ok (_, s) => pure s
    | .error e => return (.compileError s!"IR generation: {e}", {})
  let isDyn := fun (_ : String) => false
  let mut mod := st.g.mod
  let mut counter := st.g.counter
  let mut fns : Array IrFn := #[]
  for f in mod.functions do
    match (runPasses f cfg.passes.hoistLiterals cfg.passes.hoistVarDerefs cfg.passes.removeNops constKey isDyn).run counter with
    | .ok (f', c) => fns := fns.push f'; counter := c
    | .error e => return (.compileError s!"IR pass: {e}", {})
  mod := { mod with functions := fns }
  let trIr := if withTrace then irText mod else ""
  -- C++
  let env : CgEnv := { mod := mod, heap := {}, counter := counter, constKey := constKey }
  let ((decl, expr), env') ← match (genCpp "user_ns" "jank_load_user" counter).run env with
    | .ok r => pure r
    | .error e => return (.compileError s!"codegen: {e}", { ir := trIr })
  let tr : Trace := if withTrace then { ir := trIr, cpp := decl, expr := expr } else {}
  -- the C++ compiler
  let prog ← match CppAst.parseProgram decl with
    | .ok p => pure p
    | .error e => return (.compileError e, tr)
  if let .error e := CppAst.checkProgram prog then return (.compileError e, tr)
  -- run
  let vars : List (String × VarCell) := userPrims.map fun (n, p) => ("user/" ++ n, { root := some (JV.prim p) })
  let m0 : M := { prog := prog, heap := env'.heap, vars := vars }
  let rt := cfg.runtime
  let runIt : XM JV := do
    if cfg.target == .eval then
      let (ss, final) ← match CppAst.parseStmtsText expr with
        | .ok r => pure r
        | .error e => throw (.err e)
      let env0 : Env := [[]]
      let mut env := env0
      for s in ss do
        let (_, e') ← execStmt rt env s
        env := e'
      let some fe := final | throw (.err "no expression")
      let fv ← evalE rt env fe
      dynCall rt (← objOf fv) []
    else
      -- namespace variables, then the load function; the root fn's `call()` result kept
      let mut sc : List (String × Nat) := []
      for gname in prog.globals do
        let slot ← alloc (.obj .nil)
        sc := (gname, slot) :: sc
      modify fun m => { m with globalScope := sc }
      let mut env : Env := [sc]
      let mut result : JV := .nil
      for s in prog.load do
        match s with
        | .expr (.call (.arrow (.id f) "call") []) =>
          let fv ← evalE rt env (.id f)
          result ← dynCall rt (← objOf fv) []
        | _ =>
          let (_, e') ← execStmt rt env s
          env := e'
      pure result
  match runIt.run m0 with
  | .ok v m => (.value v m.out, tr)
  | .error (.thrown _) m => (.threw m.out, tr)
  | .error (.terminate why) _ => (.crash s!"std::terminate: {why}", tr)
  | .error (.ub what) _ => (.crash s!"undefined behaviour: {what}", tr)
  | .error .fuel _ => (.unsupported "fuel", tr)
  | .error (.err e) _ => (.unsupported s!"interpreter: {e}", tr)

/-- Do two outcomes agree (Clojure's, jank's)? A model gap on either side is not a result. -/
def agree : Outcome → Outcome → Option Bool
  | .unsupported _, _ | _, .unsupported _ => none
  | .value a o, .value b p => some (a.same b && o == p || (match a, b with
      | .fn _, .fn _ => o == p
      | _, _ => false))
  | .threw o, .threw p => some (o == p)
  | _, _ => some false

end Jank.Codegen
