import Determinismo
import Jank.R4.Modules.Load
import Jank.R4.Modules.Munge

/-!
# Round 4, AOT: a compiled program's start-up against `run-main` and `clojure -M -m`

jank 7135b7708:

- `jank compile <m>` (main.cpp 174–195): `compile_module("clojure.core")` or its load (phase 2),
  `compile_module(m)` (context_dynamic.cpp 212–218: `*compile-files*` bound true, then
  `load_module`): every module loaded meanwhile is evaluated and written (eval_string 88–127:
  all of the file's forms re-analyzed into one fn `jank_load_<module>`), then
  `aot::processor::build_executable` (aot/processor.cpp 411–524): **every namespace** that exists
  (`context::all_ns`, which skips only `cpp`) other than `user` and the core modules must have a
  compiled module in the build directory or on the module path, else "Compiled module '…' not
  found." (473).
- The generated entry point (aot/processor.cpp 34–165): `jank_load_clojure_core()`, then
  `jank_module_register(ns, &jank_load_<ns>)` for every namespace but `user`, then
  `jank_load_<m>()` **called directly** (no `load_module`, so no `*ns*` binding), then
  `(apply -main args)`; `jank_init_static` (c_api.cpp 1133–1169) returns **0** whatever `fn`
  returned or threw; `jank_init_dynamic` (c_api_dynamic.cpp 84–130) returns 1 after an exception.
- A module's load fn (cpp_processor.cpp 2042–2186): `jank_ns_intern_c(module)`, then every lifted
  var `_jank_var("ns/name")` (owned is never set: ir/builder.cpp 287, 309), then the module's
  forms. `_jank_var` → `context::intern_var` (context.cpp 491–515) → `ns::intern_var` (ns.cpp
  26–47) maps a **new var** when the name has no mapping yet. Every var the module's code
  references is therefore interned before `(ns …)` refers `clojure.core`; `ns::refer`
  (ns.cpp 174–192) then throws for a core name the module shadows (the R109 mechanism, on the
  first load).
- `run-main` (main.cpp 83–115): `load_module(m)`, then `-main` with `*ns*` as the context left it
  (`clojure.core`); its status is `jank_init_dynamic`'s.

Clojure (the spec): `clojure -M -m m` (clojure.main 511–517): `(in-ns 'user)`, `(require 'm)`,
`(apply -main args)`, status 1 after an uncaught exception; an AOT-compiled Clojure program
behaves as its source does.
-/

namespace Jank.R4.Modules.Aot

open Determinismo Jank.R4.Modules.Load

/-- A program: library `b`, the main module `app.core`, and `-main`'s body. -/
structure Prog where
  b : List Form
  app : List Form
  main : List Form
  deriving Repr, BEq, Inhabited

def Prog.files (p : Prog) : Files := [("b", p.b), ("app.core", p.app)]

/-- `-main`'s body is compiled in `app.core`: its references resolve there (when the module is
analyzed), whatever `*ns*` is when it runs. -/
def Prog.mainCode (p : Prog) : List Form := p.main.map fun f => match f with
  | .ref sym => Form.refIn "app.core" sym
  | f => f

/-- How a run ends: what it printed, its exit status, and where it stopped. -/
structure Run where
  out : List String
  status : Nat
  /-- The kind of what was thrown, if anything. -/
  kind : String := ""
  /-- `compile` (the build failed), `startup` (loading threw), `main` (-main threw), or `ok`. -/
  phase : String
  deriving Repr, BEq, Inhabited

def refsOf (fs : List Form) : List String :=
  fs.filterMap fun f => match f with | .ref s => some s | _ => none

/-- Clojure: `clojure -M -m app.core`. -/
def clojureRun (p : Prog) : Run :=
  let act : M Unit := loadLibs .clj p.files [.sym "app.core"] [] false
  match act.run initialSt with
  | .error e s => { out := s.out, status := 1, phase := "startup", kind := e.kind }
  | .ok _ s =>
    match (p.mainCode.forM (evalForm .clj p.files)).run s with
    | .ok _ s' => { out := s'.out, status := 0, phase := "ok" }
    | .error e s' => { out := s'.out, status := 1, phase := "main", kind := e.kind }

/-- jank `run-main app.core`: `load_module` (binds `*ns*`), then `-main` with `*ns*` =
clojure.core. -/
def runMainRun (p : Prog) : Run :=
  let act : M Unit := do
    modify fun s => { s with cur := "clojure.core" }
    match p.files.lookup "app.core" with
    | none => throwK "module-not-found"
    | some forms =>
      withState (·.cur) (fun s v => { s with cur := v }) "clojure.core" do
        evalFile .jank p.files "app.core" forms
      modify fun s => { s with libs := s.libs ++ ["app.core"] }
  match act.run initialSt with
  | .error e s => { out := s.out, status := 1, phase := "startup", kind := e.kind }
  | .ok _ s =>
    match (p.mainCode.forM (evalForm .jank p.files)).run s with
    | .ok _ s' => { out := s'.out, status := 0, phase := "ok" }
    | .error e s' => { out := s'.out, status := 1, phase := "main", kind := e.kind }

/-- The compile phase: the JIT load with `*compile-files*`; the lifted vars of each module
(resolved in its namespace once loaded); the namespaces `build_executable` needs. -/
def compileProg (p : Prog) : Except String (List (String × List (String × String))) :=
  let act : M Unit := do
    match p.files.lookup "app.core" with
    | none => throwK "module-not-found"
    | some forms =>
      withState (·.cur) (fun s v => { s with cur := v }) "clojure.core" do
        evalFile .jank p.files "app.core" forms
  match act.run initialSt with
  | .error e _ => .error s!"compile: {e.kind}"
  | .ok _ s =>
    let modules := s.evals.eraseDups
    -- build_executable: every namespace but user and the core modules needs a module.
    match s.nss.find? (fun n => n.name != "user" && n.name != "clojure.core" && !modules.contains n.name) with
    | some n => .error s!"Compiled module '{n.name}' not found."
    | none =>
      -- Each module's lifted vars: its references (and -main's, for app.core), resolved in the
      -- namespace the module defines.
      let lifted (m : String) : Except String (List (String × String)) :=
        let fs := (p.files.lookup m).getD []
        let refs := refsOf fs ++ (if m == "app.core" then refsOf p.main else [])
        let resolveAll : M (List (String × String)) := do
          modify fun s => { s with cur := m }
          refs.mapM fun r => do let v ← resolveSym r; pure (v.ns, v.name)
        match resolveAll.run s with
        | .ok xs _ => .ok xs
        | .error e _ => .error s!"compile: {e.kind}"
      modules.mapM fun m => do pure (m, ← lifted m)

/-- The compiled program's run: each module's load fn interns its lifted vars before its forms;
the main module's load fn is called directly; `static` returns 0 whatever happened. -/
def aotRun (p : Prog) (static : Bool) : Run :=
  match compileProg p with
  | .error e => { out := [e], status := 1, phase := "compile" }
  | .ok lifted =>
    let prologue (m : String) : List Form :=
      .createNs m :: ((lifted.lookup m).getD []).map fun (n, v) => Form.internLifted n v
    let files' : Files := p.files.map fun (m, fs) => (m, prologue m ++ fs)
    let fail (s : St) (ph : String) (k : String) : Run := { out := s.out, status := if static then 0 else 1, phase := ph, kind := k }
    -- jank_load_app_core() directly: no binding of *ns*.
    let act : M Unit := do
      for f in (files'.lookup "app.core").getD [] do evalForm .jank files' f
    match act.run initialSt with
    | .error e s => fail s "startup" e.kind
    | .ok _ s =>
      match (p.mainCode.forM (evalForm .jank files')).run s with
      | .ok _ s' => { out := s'.out, status := 0, phase := "ok" }
      | .error e s' => fail s' "main" e.kind

/-! ## The search world -/

def bPool : List (List Form) :=
  [[.ns "b" [], .defv "x", .print "b"],
   [.ns "b" [], .defv "inc", .defv "x", .print "b"],
   [.ns "b" [.referClojure ["inc"]], .defv "inc", .defv "x", .print "b"]]

def appHead : List (List Form) :=
  [[.ns "app.core" []], [.ns "app.core" [.require [.sym "b"]]],
   [.ns "app.core" [.require [.vec "b" [.as "bb"]]]], [.ns "app.core" [.require [.vec "c" [.asAlias "cc"]]]]]

def appTail : List (List Form) :=
  [[], [.defv "inc"], [.createNs "scratch"], [.defv "y", .ref "y"]]

def mainPool : List (List Form) :=
  [[], [.printNs], [.ref "inc"], [.ref "b/x"], [.ref "bb/x"], [.ref "b/inc"], [.boom], [.ref "y"]]

structure W where
  decisions : Decisions

instance : Chaotic W where
  decisions w := w.decisions
  setDecisions w d := { w with decisions := d }

def classify (c j a : Run) : String :=
  if a.phase == "compile" && j.phase != "compile" && (a.out.any (·.startsWith "Compiled module")) then
    "F14 jank compile: a namespace with no module (create-ns, :as-alias) stops the build"
  else if a.phase == "startup" && j.phase != "startup" then
    "F2 AOT: a module's referenced vars are interned before its (ns …): refer of clojure.core throws"
  else if a.status == 0 && c.status == 1 then
    "F3 AOT (static runtime): exit status 0 after an uncaught exception"
  else if (a.out.any (·.startsWith "*ns*")) || (j.out.any (·.startsWith "*ns*")) then
    "F1 *ns* during -main: run-main clojure.core, AOT the main module's ns, clojure -m user"
  else "unexplained"

def body : EStateM Stop W Unit := do
  let b ← decide "b" bPool.length
  let h ← decide "app.head" appHead.length
  let t ← decide "app.tail" appTail.length
  let m ← decide "main" mainPool.length
  let p : Prog := { b := bPool[b]!, app := appHead[h]! ++ appTail[t]!, main := mainPool[m]! }
  let c := clojureRun p
  let j := runMainRun p
  let a := aotRun p true
  -- A program whose -main refers to what its module cannot resolve does not compile anywhere.
  let invalid := c.kind == "unresolved"
  let same (x y : Run) : Bool := x.out == y.out && x.status == y.status && x.phase == y.phase
  if !invalid && !(same c j && same j a) then
    let cls := classify c j a
    -- a JIT run-main that already disagrees with Clojure for a known reason, with AOT agreeing
    -- with run-main, is that reason's class
    violate cls s!"program {repr p}; clojure -m {repr c}; jank run-main {repr j}; jank AOT(static) {repr a}"

def run (source : Source) : Ended :=
  match body.run { decisions := { source } } with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }
  | .error (.nodeDown _) w => { taken := w.decisions.taken, violation := none }

end Jank.R4.Modules.Aot
