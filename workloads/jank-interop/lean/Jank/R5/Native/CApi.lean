import Jank.R4.Modules.Aot
import Determinismo

/-!
# Round 5, the C API beyond the AOT entry points

jank 94d32623, `upstream-r5/compiler+runtime/`:
- `include/cpp/jank/c_api.h` 1–373 (the declarations, inside `extern "C"` for C callers);
- `src/cpp/jank/c_api.cpp` 51–1183, `c_api_dynamic.cpp` 19–136, `c_api_dynamic_phase_2.cpp`
  12–66, `c_api_static.cpp` 4–23;
- the AOT entry point jank writes, `src/cpp/jank/aot/processor.cpp` 40–140: `-main` is called as
  `jank_call2(jank_deref(apply), jank_deref(fn), command_line_args)` and the lambda returns 0.

What each function does at the boundary (read, and replicated below where a search or proof
needs it):

- **Exceptions.** `jank_call2` (c_api.cpp 168–181) and `jank_eval_file_c` (65–75) catch every
  exception (`std::exception`, a jank object, a jank error, anything else), print it, and return
  nil. `jank_call0`, `jank_call1`, `jank_call3`–`jank_call11`, `jank_eval`, `jank_read_string`,
  `jank_require_c` (`.expect_ok()`), `jank_var_intern` (`try_object`) and the rest let it
  propagate out of the `extern "C"` function. `jank_init_static` (1133–1169) catches all and
  returns 0; `jank_init_dynamic` (c_api_dynamic.cpp 84–130) catches the three jank kinds and
  returns 1, and lets anything else escape (std::terminate); `jank_init_dynamic_embedded`
  (37–76) the same, without a fn.
- **Names.** `jank_symbol_create(ns, name)` (433–438) builds `symbol(object_ref ns, object_ref n)`
  (obj/symbol.cpp 60–65), which stores `ns.to_string()`: a nil ns is the namespace `"nil"`.
  `jank_keyword_intern(ns, name)` (139–147) interns `ns.to_string() + "/" + name` (context.cpp
  561–586, `resolved` defaults to true): nil gives `:nil/name`. jank's own `keyword`
  (core.cpp 521–542) treats nil as no namespace, as Clojure's `Keyword.intern(null, name)` and
  `Symbol.intern(null, name)` do.
- **A debug print.** `jank_eval_file_c` prints `jank_eval_file_c <path>` on stdout first (67).
- **C.** `c_api.h` uses `bool` (358, 367) without `<stdbool.h>`: a C11/C17 translation unit that
  includes it does not compile (results/r5-native-capi-header.txt, Apple clang 16, gnu17/c17/c11).
-/

namespace Jank.R5.Native.CApi

open Jank.R4.Modules Jank.R4.Modules.Aot Jank.R4.Modules.Load

/-! ## The exception boundary -/

/-- What a call into jank throws (if anything). -/
inductive Thrown where
  | nothing
  /-- A thrown jank object (`throw`, `ex-info`). -/
  | jankObject
  /-- A `jank::error_ref` (analysis, read, runtime errors of jank's own). -/
  | jankError
  /-- A `std::exception` (most runtime type errors: `try_object`, `std::runtime_error`). -/
  | stdException
  /-- Anything else (a C++ `throw 5;` from `cpp/raw` code). -/
  | other
  deriving Repr, DecidableEq, Inhabited

/-- The C functions that call into jank. -/
inductive CFn where
  | call (arity : Nat)    -- jank_call0 … jank_call11
  | eval | evalFile | evalFileC | readString | requireC | varIntern
  deriving Repr, DecidableEq

/-- Does the function catch what its call throws (c_api.cpp as above)? -/
def catches : CFn → Bool
  | .call 2 => true
  | .evalFileC => true
  | _ => false

/-- What escapes the `extern "C"` function to its caller. -/
def escapes (f : CFn) (t : Thrown) : Thrown := if catches f then .nothing else t

/-- Clojure's Java API (`IFn.invoke`, `Compiler.load`, `RT.var(...).invoke`): what the call
throws reaches the caller. -/
def cljEscapes (_f : CFn) (t : Thrown) : Thrown := t

/-! ## The AOT program's exit status -/

/-- jank's generated `main` (aot/processor.cpp 98–140): `fn` loads clojure.core, registers
modules, calls the main module's load fn (`startup`), then `jank_call2(apply, -main, args)`
(which catches whatever `-main` throws) and returns 0; `jank_init_static`/`jank_init_dynamic`
wrap `fn`. `none` = std::terminate (an exception escaped `main`). -/
def aotStatus (static : Bool) (startup main : Thrown) : Option Nat :=
  let fnThrows : Thrown := if startup != .nothing then startup else escapes (.call 2) main
  if static then some 0     -- jank_init_static: `return 0;` (c_api.cpp 1168)
  else match fnThrows with
    | .nothing => some 0
    | .other => none        -- jank_init_dynamic has no catch-all
    | _ => some 1

/-- Clojure: `clojure -M -m app.core` (clojure.main) exits 1 when loading or `-main` throws, 0
otherwise; an AOT-compiled Clojure program behaves as its source does. -/
def cljStatus (startup main : Thrown) : Nat :=
  if startup != .nothing || main != .nothing then 1 else 0

/-- ★ For every runtime and every throw from `-main`, jank's AOT program exits 0. -/
theorem aot_main_throw_status_zero (static : Bool) (t : Thrown) :
    aotStatus static .nothing t = some 0 := by
  cases static <;> cases t <;> rfl

/-- ★ Where the dynamic runtime's status differs from Clojure's: exactly when `-main` throws
(and start-up did not), or start-up threw something that is not a jank or std exception. -/
theorem aot_dynamic_differs_iff (s m : Thrown) :
    aotStatus false s m ≠ some (cljStatus s m) ↔
      (s = .nothing ∧ m ≠ .nothing) ∨ s = .other := by
  cases s <;> cases m <;> decide

/-- Round 4's model (`Jank.R4.Modules.Aot.aotRun p false`) gave status 1 for the dynamic runtime
after `-main` throws; the corrected run: `-main` goes through `jank_call2`, which catches and
prints, so `fn` returns 0 under either runtime. Start-up throws keep round 4's statuses. -/
def aotRunR5 (p : Prog) (static : Bool) : Run :=
  match compileProg p with
  | .error e => { out := [e], status := 1, phase := "compile" }
  | .ok lifted =>
    let prologue (m : String) : List Form :=
      .createNs m :: ((lifted.lookup m).getD []).map fun (n, v) => Form.internLifted n v
    let files' : Files := p.files.map fun (m, fs) => (m, prologue m ++ fs)
    let act : M Unit := do
      for f in (files'.lookup "app.core").getD [] do evalForm .jank files' f
    match act.run initialSt with
    | .error e s => { out := s.out, status := if static then 0 else 1, phase := "startup", kind := e.kind }
    | .ok _ s =>
      match (p.mainCode.forM (evalForm .jank files')).run s with
      | .ok _ s' => { out := s'.out, status := 0, phase := "ok" }
      -- jank_call2 (c_api.cpp 175–179) prints the exception and returns nil; main returns 0.
      | .error e s' => { out := s'.out, status := 0, phase := "main", kind := e.kind }

/-- ★ In round 4's whole AOT world (every program), a `-main` that throws ends the dynamic-runtime
program with status 0. -/
theorem aotRunR5_main_zero (p : Prog) (static : Bool) (h : (aotRunR5 p static).phase = "main") :
    (aotRunR5 p static).status = 0 := by
  unfold aotRunR5 at *
  cases hc : compileProg p with
  | error e => simp [hc] at h
  | ok lifted =>
    simp only [hc] at *
    split at h
    · simp_all
    · split at h
      · simp_all
      · simp

/-! ## Names with a nil namespace -/

/-- The few objects this needs: nil, a string. -/
inductive Obj where
  | nil
  | str (s : String)
  deriving Repr, DecidableEq

/-- `object_ref::to_string` (nil prints as "nil"). -/
def Obj.toStr : Obj → String
  | .nil => "nil"
  | .str s => s

/-- A symbol or keyword's namespace and name. -/
structure QName where
  ns : Option String
  name : String
  deriving Repr, DecidableEq

/-- `jank_symbol_create` → `symbol(object_ref, object_ref)` (obj/symbol.cpp 60–65). An empty ns
string means no namespace in jank's symbols. -/
def jankSymbolCreate (ns name : Obj) : QName :=
  let n := ns.toStr
  { ns := if n.isEmpty then none else some n, name := name.toStr }

/-- `jank_keyword_intern` → `intern_keyword(ns.to_string(), name.to_string())` (context.cpp
561–586 with `resolved = true`). -/
def jankKeywordIntern (ns name : Obj) : QName :=
  let n := ns.toStr
  { ns := if n.isEmpty then none else some n, name := name.toStr }

/-- Clojure: `Symbol.intern(String ns, String name)`, `Keyword.intern(ns, name)`; null ns = none. -/
def cljIntern (ns name : Obj) : QName :=
  { ns := match ns with | .nil => none | .str s => if s.isEmpty then none else some s,
    name := name.toStr }

theorem symbol_nil_ns : jankSymbolCreate .nil (.str "a") = { ns := some "nil", name := "a" } := rfl
theorem keyword_nil_ns : jankKeywordIntern .nil (.str "a") = { ns := some "nil", name := "a" } := rfl
theorem clj_nil_ns : cljIntern .nil (.str "a") = { ns := none, name := "a" } := rfl

/-- ★ The C API agrees with Clojure exactly when the namespace is not nil. -/
theorem symbol_create_agrees_iff (ns name : Obj) :
    jankSymbolCreate ns name = cljIntern ns name ↔ ns ≠ .nil := by
  cases ns with
  | nil => simp [jankSymbolCreate, cljIntern, Obj.toStr]
  | str s => simp [jankSymbolCreate, cljIntern, Obj.toStr]

end Jank.R5.Native.CApi
