import Jank.Analyzer.World

/-!
# Round 5 (coordinator): why `jank.math` cannot load

`compiler+runtime/src/jank/jank/math.jank` (94d32623, unchanged since ae555143, 2024-07-20) is
installed with every jank (cmake/install.cmake 48–51 installs `src/jank/*`), so `(require
'jank.math)` finds it on the module path. Its body is four `defn`s whose bodies are
`(native/raw "…")`. `native/raw` was a special form until 529718a6 ("Remove native/raw",
2024-11-27), which deleted its analyzer case; nothing replaced it.

At 94d32623 the module's forms are evaluated one by one (the `ns` form first, which creates and
enters `jank.math`). The first `defn` expands to `(def tan (fn* tan ([o] (native/raw "…"))))`;
`context::eval` analyzes the whole form (S71), so `analyze_fn` analyzes the body at load time,
even though the fn's code generation is deferred (U8–U14). The body is a call whose head is the
symbol `native/raw`:
- analyze_call (analyze/processor.cpp 3459–3465): `native/raw` is not in `specials()`;
- analyze_symbol (1583–1695): its namespace is `native`, not `cpp`, so it is not a C++ symbol
  (1589); it is no local and no named recursion; `qualify_symbol` (context.cpp 116–134) finds no
  namespace or alias `native` and keeps the symbol; `find_var` (136–159) finds no namespace
  `native` and returns nil; `find_referred_global` finds nothing; so analysis fails with
  `analyze_unresolved_symbol` "The symbol `native/raw` could not be resolved." (1693–1696).

The replica below runs the module's first form through round 2's analyzer replica (`runJank`),
with `defn` written as its expansion (the replica has no `defn` macro), and a control where the
body is a call of a resolvable var: the first gives exactly that error, the control analyzes.
-/

namespace Jank.R5.Coord.JankMath

open Jank.Analyzer

/-- `(def name (fn* name ([o] body)))`: what `(defn name [o] body)` expands to. -/
def defnForm (name : String) (body : Obj) : Obj :=
  L [Obj.sym "" "def", Obj.sym "" name,
     L [Obj.sym "" "fn*", Obj.sym "" name, L [V [Obj.sym "" "o"], body]]]

/-- `(native/raw "__value = make_box(std::tan(to_real(~{ o })));")`, math.jank line 4. -/
def nativeRaw : Obj := L [Obj.sym "native" "raw", S "__value = make_box(std::tan(to_real(~{ o })));"]

/-- The module's first defn, `tan` (math.jank 3–4). -/
def tanForm : Obj := defnForm "tan" nativeRaw

/-- Control: the same defn with a resolvable call in its body. -/
def controlForm : Obj := defnForm "tan" (L [Obj.sym "" "str", Obj.sym "" "o"])

def showOutcome : Outcome → String
  | .value _ => "value"
  | .thrown m => s!"thrown: {m}"
  | .compileError m => s!"analysis error: {m}"
  | .ub m => s!"undefined behavior: {m}"
  | .fuel => "fuel"
  | .unsupported m => s!"unsupported: {m}"

def report : List String :=
  [ s!"(defn tan [o] (native/raw …)): {showOutcome (runJank [tanForm]).outcome}",
    s!"control (defn tan [o] (str o)): {showOutcome (runJank [controlForm]).outcome}" ]

end Jank.R5.Coord.JankMath
