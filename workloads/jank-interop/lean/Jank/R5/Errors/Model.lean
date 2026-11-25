/-!
# Round 5, errors: what a program sees of an error, jank 94d32623 beside Clojure 1.12

Every jank path is under `upstream-r5/compiler+runtime/` at 94d32623 (byte-identical to
7135b7708's `compiler+runtime`). Clojure paths are under `clojure-ref/src/` (1.12.0).

**What jank throws.** A C++ `throw` carries one of four kinds of value:
- an `object_ref` (`throw` of any jank value, `ex-info` among them; codegen `gen(throw)`
  cpp_processor.cpp 1024–1050);
- a `std::exception` (the runtime's own errors: `try_object`, `persistent_vector::nth` 327–338,
  `read_string`'s option checks context.cpp 176–244, …);
- a `jank::error_ref` (`jtl::ref<error::base>`, error.hpp 293): every lex, parse and analysis
  error, every module-loading error. A `jtl::result<_, error_ref>`'s `expect_ok` throws it
  (jtl/result.hpp `panic` 41–68, line 56), which is how `context::eval` (context_dynamic.cpp
  220–226), `context::read_string` (context.cpp 271, 281) and core.jank `load` (4801–4812,
  `.expect_ok`) raise it;
- any other native value (`foreign` here).

**What a jank `catch` catches** (analyze_try processor.cpp 3046–3100, codegen `gen(catch)`
cpp_processor.cpp 1105–1123): `(catch cpp/jank.runtime.object_ref e …)` is `catch(object_ref e)`
and sees only objects; `cpp/std.exception` sees `std::exception`s; `cpp/jank.error_ref` sees
error_refs; `:default` is `catch(...)` with `e` a default (nil) `object_ref`. Clojure's
`(catch Throwable e …)` sees every exception.

The replica below gives each path one function per side.
-/

namespace Jank.R5.Errors

/-! ## Values -/

/-- Exception data: nil, or a map, by its keys (each key's value is 1 in the programs here;
Clojure's compiler errors carry `:clojure.error/*` keys). -/
inductive Data where
  | nil
  | keys (ks : List String)
  deriving Repr, BEq, Inhabited, DecidableEq

def Data.has (d : Data) (k : String) : Bool :=
  match d with
  | .nil => false
  | .keys ks => ks.contains k

/-- jank's error kinds that the paths below raise (error.hpp 21–133). -/
inductive ErrKind where
  | parseUnterminatedList
  | parseUnexpectedClosing
  | analyzeUnresolvedSymbol
  | analyzeMacroExpansionException
  | runtimeModuleNotFound
  | runtimeUnableToLoadModule
  deriving Repr, BEq, Inhabited, DecidableEq

/-- A `jank::error::base` (error.hpp 213–290): its kind, message and `cause` chain. -/
structure JErr where
  kind : ErrKind
  message : String
  /-- The error_ref causes, outermost first (`base::cause`). -/
  causes : List (ErrKind × String) := []
  deriving Repr, BEq, Inhabited

/-- An `obj::exception_info` (exception_info.hpp/.cpp): `message`, `data`, the `cause` chain
(each an exception_info: message and data), and the `error` it wraps when built from an
error_ref (exception_info.cpp 23–27, which sets nothing else). -/
structure JEx where
  message : String
  data : Data
  causes : List (String × Data) := []
  error : Option JErr := none
  deriving Repr, BEq, Inhabited

/-- jank objects the programs handle. -/
inductive JVal where
  | nil
  | int (n : Int)
  | str (s : String)
  | kw (s : String)
  | map (d : Data)
  | ex (e : JEx)
  deriving Repr, BEq, Inhabited

/-- What a C++ `throw` carries. -/
inductive JThrown where
  | obj (o : JVal)
  | std (what : String)
  | err (e : JErr)
  | foreign
  deriving Repr, BEq, Inhabited

/-- A jank evaluation: a value, an exception, or the process ended by `std::terminate`. -/
inductive JRes where
  | ok (v : JVal)
  | thrown (t : JThrown)
  | terminated (why : String)
  deriving Repr, BEq, Inhabited

/-- Clojure's exception classes met here. -/
inductive CCls where
  | exceptionInfo
  | compilerException
  | runtimeException
  | indexOutOfBounds
  | fileNotFound
  | executionException
  | illegalArgument
  | classCast
  deriving Repr, BEq, Inhabited, DecidableEq

/-- One link of a Clojure exception chain: its class, message, and `ex-data` (`some` only for an
IExceptionInfo: ExceptionInfo, CompilerException). -/
structure CLink where
  cls : CCls
  message : Option String
  data : Option Data := none
  deriving Repr, BEq, Inhabited

/-- A Clojure Throwable: its chain, outermost first (`getCause` walks it). -/
abbrev CEx := List CLink

inductive CVal where
  | nil
  | int (n : Int)
  | str (s : String)
  | kw (s : String)
  | map (d : Data)
  | ex (e : CEx)
  deriving Repr, BEq, Inhabited

inductive CRes where
  | ok (v : CVal)
  | thrown (e : CEx)
  deriving Repr, BEq, Inhabited

/-! ## Catching -/

/-- A jank catch clause's type (analyze_try 3046–3100; gen(catch) 1105–1123). -/
inductive JCatch where
  | object
  | stdException
  | errorRef
  | default_
  deriving Repr, BEq, Inhabited, DecidableEq

/-- Whether `catch(T e)` matches what was thrown. An `object_ref` handler matches only a thrown
`object_ref`; `std::exception&` only a class derived from it; `error_ref` only an error_ref;
`catch(...)` everything ([except.handle]/3). -/
def jMatches : JCatch → JThrown → Bool
  | .object, .obj _ => true
  | .stdException, .std _ => true
  | .errorRef, .err _ => true
  | .default_, _ => true
  | _, _ => false

/-- What `(catch :default e …)` binds: a default-constructed `object_ref`, which is nil
(gen(catch) 1111–1113). -/
def jDefaultBinding (_ : JThrown) : JVal := .nil

/-- The tests' observer, `outcome`: `(try (f) [:returned] (catch object_ref e [:object e])
(catch std.exception _ [:native]) (catch jank.error_ref _ [:error]))`. -/
inductive Kind where
  | returned
  | object
  | native
  | error
  | uncaught
  | terminated
  deriving Repr, BEq, Inhabited, DecidableEq

def jOutcome : JRes → Kind
  | .ok _ => .returned
  | .thrown t =>
    if jMatches .object t then .object
    else if jMatches .stdException t then .native
    else if jMatches .errorRef t then .error
    else .uncaught
  | .terminated _ => .terminated

/-- Clojure's `outcome` (object_ref → Throwable): every exception here is a Throwable. -/
def cOutcome : CRes → Kind
  | .ok _ => .returned
  | .thrown _ => .object

/-! ## ex-info, ex-message, ex-data, ex-cause

jank: core.jank 113–150 → core.cpp `ex_info` 1322–1336 (the message goes through
`convert<immutable_string>::from_object`, builtin.hpp 323–341, which is
`try_object<persistent_string>`; the cause through `try_object<exception_info>`; the data
unchecked), `ex_message` 1338, `ex_data` 1343, `ex_cause` 1348 (`try_object<exception_info>`).
Clojure: core.clj 4832–4864, ExceptionInfo.java (1.12: a nil data map is stored as `{}`). -/

def tryObjectFail (expected : String) (got : String) : JThrown :=
  .std s!"An object of type `{expected}` was expected here, but a `{got}` was provided instead."

def JVal.typeName : JVal → String
  | .nil => "nil"
  | .int _ => "integer"
  | .str _ => "persistent_string"
  | .kw _ => "keyword"
  | .map _ => "persistent_array_map"
  | .ex _ => "exception_info"

/-- `(ex-info msg data)` in jank. -/
def jExInfo (msg : JVal) (data : Data) : JRes :=
  match msg with
  | .str s => .ok (.ex { message := s, data })
  | o => .thrown (tryObjectFail "persistent_string" o.typeName)

/-- `(ex-info msg data)` in Clojure 1.12: `(ExceptionInfo. msg map)`; a nil message stays nil,
a nil map becomes `{}` (ExceptionInfo.java 1.12, the constructor's `data == null` branch). A
non-String message fails the constructor's String cast (one 2-argument constructor, so a direct
call with casts: ClassCastException). -/
def cExInfo (msg : CVal) (data : Data) : CRes :=
  let d := match data with | .nil => Data.keys [] | k => k
  match msg with
  | .str s => .ok (.ex [{ cls := .exceptionInfo, message := some s, data := some d }])
  | .nil => .ok (.ex [{ cls := .exceptionInfo, message := none, data := some d }])
  | _ => .thrown [{ cls := .classCast, message := some "cannot be cast to class java.lang.String" }]

def jExMessage : JVal → JRes
  | .ex e => .ok (.str e.message)
  | o => .thrown (tryObjectFail "exception_info" o.typeName)

def jExData : JVal → JRes
  | .ex e => .ok (match e.data with | .nil => .nil | d => .map d)
  | o => .thrown (tryObjectFail "exception_info" o.typeName)

def cExMessage : CVal → Option String
  | .ex (l :: _) => l.message
  | _ => none

def cExData : CVal → Option Data
  | .ex (l :: _) => l.data
  | _ => none

/-- The data of the first link, walking `ex-cause` from the outside, whose data has key `k`
(the tests' `data-with`). jank: the exception_info chain. -/
def jDataWith (e : JEx) (k : String) : Option Data :=
  if e.data.has k then some e.data
  else (e.causes.find? (fun (_, d) => d.has k)).map (·.2)

def cDataWith (e : CEx) (k : String) : Option Data :=
  match e.find? (fun l => match l.data with | some d => d.has k | none => false) with
  | some l => l.data
  | none => none

/-! ## read-string

jank: core.jank `read-string` 5974–5984: the 1-arity calls `(read-string {} s)`, so
`context::read_string(code, {})` (context.cpp 300–305 → 166–298) runs with no `:eof` option:
`eof_value` is nil, `throw_on_eof` is `equal(nil, :eofthrow)`, false, and a text without a form
returns nil (285–296). Only the C++-side default `read_string(code)` (307–314, used by no
clojure.core function) passes `{:eof :eofthrow}`. A form that fails to parse: `expect_ok` at
271/281 throws the parser's error_ref.

Clojure: core.clj 3831–3842 → RT.readString (RT.java 1890–1897) → LispReader.read(r, opts)
(196–208): a missing `:eof` key means `:eofthrow`, so a text without a form throws
RuntimeException "EOF while reading". Over a plain PushbackReader a reader error is thrown as
is (no ReaderException wrapper, which needs a LineNumberingPushbackReader). -/

/-- What the text holds, as far as these paths care. -/
inductive Text where
  /-- One readable form, then anything. -/
  | form (v : Int)
  /-- Nothing but whitespace and comments. -/
  | empty
  /-- An unterminated list, `(`. -/
  | unterminated
  /-- A stray closer, `)`. -/
  | strayCloser
  deriving Repr, BEq, Inhabited, DecidableEq

/-- `:eof` in the options map: absent, `:eofthrow`, or a value. -/
inductive EofOpt where
  | absent
  | eofthrow
  | value (v : Int)
  deriving Repr, BEq, Inhabited, DecidableEq

def jReadString (opt : EofOpt) (t : Text) : JRes :=
  match t with
  | .form v => .ok (.int v)
  | .unterminated => .thrown (.err { kind := .parseUnterminatedList, message := "Unterminated list." })
  | .strayCloser => .thrown (.err { kind := .parseUnexpectedClosing, message := "Unexpected closing character." })
  | .empty =>
    match opt with
    | .eofthrow => .thrown (.std "EOF was reached while reading. To override this behavior, provide a value for the EOF case via the `:eof` reader option.")
    | .absent => .ok .nil
    | .value v => .ok (.int v)

/-- core.jank's 1-arity `read-string`: `(read-string {} s)`. -/
def jReadString1 (t : Text) : JRes := jReadString .absent t

def cReadString (opt : EofOpt) (t : Text) : CRes :=
  match t with
  | .form v => .ok (.int v)
  | .unterminated => .thrown [{ cls := .runtimeException, message := some "EOF while reading" }]
  | .strayCloser => .thrown [{ cls := .runtimeException, message := some "Unmatched delimiter: )" }]
  | .empty =>
    match opt with
    | .absent | .eofthrow => .thrown [{ cls := .runtimeException, message := some "EOF while reading" }]
    | .value v => .ok (.int v)

def cReadString1 (t : Text) : CRes := cReadString .absent t

/-! ## What raises: the error sources of the programs -/

/-- A form that raises when evaluated (inside a fn, a module or a macro body). -/
inductive Inner where
  /-- `(throw (ex-info "x" {:k 1}))` -/
  | exInfo
  /-- `(nth [1 2] 5)` -/
  | native
  /-- `(read-string "(")` -/
  | readBad
  /-- `(eval 'nope)`: an unresolved symbol, analyzed at run time -/
  | evalUnresolved
  deriving Repr, BEq, Inhabited, DecidableEq

def Inner.all : List Inner := [.exInfo, .native, .readBad, .evalUnresolved]

/-- The key of the ex-info's data in `Inner.exInfo`. -/
def dataKey : String := "k"

/-- jank: what evaluating the inner form throws. `nth` out of range is a `std::runtime_error`
(persistent_vector.cpp 321–338); `eval` of an unresolved symbol is analyze_symbol's error_ref
raised by `context::eval`'s `expect_ok` (context_dynamic.cpp 220–226). -/
def jInner : Inner → JThrown
  | .exInfo => .obj (.ex { message := "x", data := .keys [dataKey] })
  | .native => .std "The index `5` is out of bounds for this `persistent_vector`."
  | .readBad => .err { kind := .parseUnterminatedList, message := "Unterminated list." }
  | .evalUnresolved => .err { kind := .analyzeUnresolvedSymbol, message := "Unable to resolve symbol 'nope'." }

def cLink (c : CCls) (m : String) : CLink := { cls := c, message := some m }

/-- Clojure's compiler error data (CompilerException 7381–7389): phase, line, column (and source,
symbol when known). -/
def compilerData : Data := .keys ["clojure.error/phase", "clojure.error/line", "clojure.error/column"]

def cCompiler (phase : String) : CLink :=
  { cls := .compilerException, message := some s!"Syntax error ({phase})", data := some compilerData }

/-- Clojure: what evaluating the inner form throws, inside a fn (no wrapper: the fn's own body;
`eval` of an unresolved symbol throws the CompilerException that analyze raised). -/
def cInner : Inner → CEx
  | .exInfo => [{ cls := .exceptionInfo, message := some "x", data := some (.keys [dataKey]) }]
  | .native => [{ cls := .indexOutOfBounds, message := none }]
  | .readBad => [cLink .runtimeException "EOF while reading"]
  | .evalUnresolved => [cCompiler "compile-syntax-check",
                        cLink .runtimeException "Unable to resolve symbol: nope in this context"]

/-! ## Loading a module and `load-lib`

jank:
- core.jank `load` 4801–4812: `(.expect_ok (.load_module __rt_ctx (.to_string path) …))`.
- `context::load_module` (context.cpp 324–354): binds `*ns*` and `*current-module*` (RAII), runs
  `module_loader.load`, and turns **every** exception into an error result: a `std::exception`
  into `runtime_unable_to_load_module(e.what())` (342–345), an object into
  `runtime_unable_to_load_module(e.to_code_string())`, an error_ref into itself. So `load`'s
  `expect_ok` throws an error_ref for every failure of the module's code.
- `loader::load` (loader_dynamic.cpp 721–777): `set_is_loaded` only after the file's forms all
  evaluated.
- core.jank `load-lib` 4836–4873: `(try (load lib need-ns? require) (catch
  cpp/jank.runtime.object_ref e (when undefined-on-entry? (remove-ns lib)) (throw e)))`. The
  handler is an object handler: the error_ref from `load` passes it, `remove-ns` never runs.

Clojure: core.clj `load-lib` 5981–6026 catches `Exception` and removes a namespace that was
undefined on entry; Compiler.load (8130–8180) wraps every Throwable from the file in a
CompilerException (phase `:read-source` for a reader error, `:execution` otherwise; an analysis
CompilerException is rethrown as is). -/

/-- A module's top level: `(ns lib)` first (which creates the namespace), then forms; `raises`
is the first form that raises, if any. -/
structure Module where
  lib : String
  raises : Option Inner
  deriving Repr, BEq, Inhabited

/-- The state these paths touch: the namespaces, `*loaded-libs*`, and `*ns*`. -/
structure NsState where
  nss : List String := ["clojure.core", "user"]
  loaded : List String := []
  cur : String := "user"
  deriving Repr, BEq, Inhabited

/-- `context::load_module`'s conversion of what the module threw (context.cpp 342–353). -/
def jLoadModuleConvert : JThrown → JThrown
  | .std w => .err { kind := .runtimeUnableToLoadModule, message := w }
  | .obj o => .err { kind := .runtimeUnableToLoadModule,
                     message := match o with | .ex e => s!"#error {e.message}" | _ => "object" }
  | .err e => .err e
  | .foreign => .foreign

/-- jank `load` of a module present on the module path: the namespace is created by its `ns`
form (in-ns, so `*ns*` changes inside the binding only), which also records the lib in
`*loaded-libs*` (core.jank ns 5645; Clojure's ns does the same, core.clj 5873), then the forms
run; `*ns*` is restored by `binding_scope`. So after a failed load the lib is in `*loaded-libs*`
on both sides, and a second `require` loads nothing. -/
def jLoad (m : Module) (s : NsState) : JRes × NsState :=
  let s1 := { s with nss := if s.nss.contains m.lib then s.nss else s.nss ++ [m.lib],
                     loaded := if s.loaded.contains m.lib then s.loaded else s.loaded ++ [m.lib] }
  match m.raises with
  | none => (.ok .nil, s1)
  | some i => (.thrown (jLoadModuleConvert (jInner i)), s1)

/-- jank `load-lib` (4836–4873) for `(require lib)` with the lib not loaded yet. -/
def jLoadLib (m : Module) (s : NsState) : JRes × NsState :=
  let undefinedOnEntry := !s.nss.contains m.lib
  let (r, s') := jLoad m s
  match r with
  | .thrown t =>
    if jMatches .object t then
      (.thrown t, if undefinedOnEntry then { s' with nss := s'.nss.filter (· != m.lib) } else s')
    else (.thrown t, s')
  | r => (r, s')

/-- Compiler.load's wrapper around what a file's form threw. -/
def cLoadWrap : Inner → CEx
  | .evalUnresolved => cInner .evalUnresolved
  | i => cCompiler "execution" :: cInner i

def cLoad (m : Module) (s : NsState) : CRes × NsState :=
  let s1 := { s with nss := if s.nss.contains m.lib then s.nss else s.nss ++ [m.lib],
                     loaded := if s.loaded.contains m.lib then s.loaded else s.loaded ++ [m.lib] }
  match m.raises with
  | none => (.ok .nil, s1)
  | some i => (.thrown (cLoadWrap i), s1)

/-- Clojure `load-lib`: `(catch Exception e (when undefined-on-entry (remove-ns lib)) (throw e))`;
every CEx here is an Exception. -/
def cLoadLib (m : Module) (s : NsState) : CRes × NsState :=
  let undefinedOnEntry := !s.nss.contains m.lib
  let (r, s') := cLoad m s
  match r with
  | .thrown e => (.thrown e, if undefinedOnEntry then { s' with nss := s'.nss.filter (· != m.lib) } else s')
  | r => (r, s')

/-- `(require lib)` of a lib absent from the module path. jank: `loader::find` fails with
`runtime_module_not_found` (loader_dynamic.cpp 745–749), an error_ref through `expect_ok`.
Clojure: RT.load throws FileNotFoundException "Could not locate …", which load-lib rethrows. -/
def jRequireMissing : JRes :=
  .thrown (.err { kind := .runtimeModuleNotFound, message := "Unable to find module." })

def cRequireMissing : CRes :=
  .thrown [cLink .fileNotFound "Could not locate jank_lean/vb_no_such_namespace__init.class, …"]

/-! ## Macro expansion

jank: analyze_call (processor.cpp 3502–3530) runs `macroexpand` under `cpptrace::try_catch`
and turns what the macro threw into `analyze_macro_expansion_exception` (error/analyze.cpp
172–209): from a `std::exception` its `what()`; from an object its printed form (`to_string` of a
string, else `to_code_string`), with **no cause**; from an error_ref the fixed message
"Uncaught exception while expanding macro." with the error as cause. `context::eval`'s
`expect_ok` throws that error_ref.

Clojure: Compiler.macroexpand1 (7509–7550): a CompilerException is rethrown; an
ExceptionInfo, IllegalArgumentException or IllegalStateException becomes a CompilerException
`:macro-syntax-check` with it as cause; any other Throwable a CompilerException
(`:macroexpansion`) with it as cause. -/

def jMacroConvert : JThrown → JThrown
  | .std w => .err { kind := .analyzeMacroExpansionException, message := w }
  | .obj o => .err { kind := .analyzeMacroExpansionException,
                     message := match o with
                       | .str s => s
                       | .ex e => s!"#error {e.message}"
                       | _ => "object" }
  | .err e => .err { kind := .analyzeMacroExpansionException,
                     message := "Uncaught exception while expanding macro.",
                     causes := (e.kind, e.message) :: e.causes }
  | .foreign => .foreign

def cMacroWrap (i : Inner) : CEx :=
  match i with
  | .evalUnresolved => cInner .evalUnresolved
  | .exInfo => cCompiler "macro-syntax-check" :: cInner i
  | _ => cCompiler "macroexpansion" :: cInner i

/-! ## A top-level `def` whose value raises

jank: evaluate.cpp eval(def) 333–362: `intern_var`, then `var->set_meta(eval(name's meta))`
(336–337) and `set_dynamic` (339–340), **then** the value (351, 357). A value that throws leaves
the var interned, unbound, with the def's metadata. The exception propagates as thrown
(evaluate::eval 303–322 only adds a usage note to an error_ref).

Clojure: a top-level `def` is DefExpr.eval (Compiler.eval 7690–7700 → 449–471): `bindRoot(init)`
first, `setMeta` after it; a throw is wrapped in a CompilerException (`:execution`). The parser
(568–604) interns the var and sets `:dynamic` and `:arglists` before; any other key of the def's
metadata is set only once the value returned. -/

structure VarState where
  interned : Bool := false
  bound : Bool := false
  /-- The keys of the def's own metadata that the var carries. -/
  metaKeys : List String := []
  dynamic : Bool := false
  deriving Repr, BEq, Inhabited

/-- `(def ^{metaKeys, :dynamic dyn} x value)` at the top level; `value` none = it returns. -/
def jTopDef (metaKeys : List String) (dyn : Bool) (value : Option Inner) : JRes × VarState :=
  let v : VarState := { interned := true, metaKeys := metaKeys ++ (if dyn then ["dynamic"] else []), dynamic := dyn }
  match value with
  | none => (.ok .nil, { v with bound := true })
  | some i => (.thrown (jInner i), v)

def cTopDef (metaKeys : List String) (dyn : Bool) (value : Option Inner) : CRes × VarState :=
  match value with
  | none => (.ok .nil, { interned := true, bound := true,
                         metaKeys := metaKeys ++ (if dyn then ["dynamic"] else []), dynamic := dyn })
  | some i =>
    let e := match i with
      | .evalUnresolved => cInner i
      | _ => cCompiler "execution" :: cInner i
    (.thrown e, { interned := true, bound := false, metaKeys := [], dynamic := dyn })

/-! ## delay

jank: delay.cpp `deref` 19–45: under the mutex, a set `val` is returned; a set `error` (an
object) is thrown; else `val = fn.call()`, and a `std::exception` sets
`error = make_box(e.what())` (a string object) and rethrows the native exception, an object
sets `error = e` and rethrows (36–45); an error_ref or another native value passes both handlers, so
neither `val` nor `error` is set and the next deref calls the body again. A nil result leaves
`val` unset too (round 1's D19). `is_realized` is `val.is_some()` (49–53).

Clojure: Delay.java `realize`/`deref` 28–58: the body runs once; a Throwable is kept in
`exception` and every deref throws that same object; `isRealized` is `lock == null`. -/

structure JDelay where
  val : Option JVal := none
  error : Option JVal := none
  runs : Nat := 0
  deriving Repr, BEq, Inhabited

/-- One `deref` of a jank delay whose body gives `body` each time it runs. -/
def jDelayDeref (body : JRes) (d : JDelay) : JRes × JDelay :=
  match d.val with
  | some v => (.ok v, d)
  | none =>
    match d.error with
    | some e => (.thrown (.obj e), d)
    | none =>
      let d := { d with runs := d.runs + 1 }
      match body with
      | .ok .nil => (.ok .nil, d)
      | .ok v => (.ok v, { d with val := some v })
      | .thrown (.std w) => (.thrown (.std w), { d with error := some (.str w) })
      | .thrown (.obj o) => (.thrown (.obj o), { d with error := some o })
      | .thrown t => (.thrown t, d)
      | .terminated w => (.terminated w, d)

structure CDelay where
  done : Bool := false
  result : Option CRes := none
  runs : Nat := 0
  deriving Repr, BEq, Inhabited

def cDelayDeref (body : CRes) (d : CDelay) : CRes × CDelay :=
  if d.done then (d.result.getD (.ok .nil), d)
  else (body, { done := true, result := some body, runs := d.runs + 1 })

/-- `n` derefs, each result kept. -/
def jDelayDerefs (body : JRes) : Nat → JDelay → List JRes × JDelay
  | 0, d => ([], d)
  | n + 1, d =>
    let (r, d1) := jDelayDeref body d
    match r with
    | .terminated _ => ([r], d1)
    | _ =>
      let (rs, d2) := jDelayDerefs body n d1
      (r :: rs, d2)

def cDelayDerefs (body : CRes) : Nat → CDelay → List CRes × CDelay
  | 0, d => ([], d)
  | n + 1, d =>
    let (r, d1) := cDelayDeref body d
    let (rs, d2) := cDelayDerefs body n d1
    (r :: rs, d2)

/-! ## future

jank: core.cpp `future` 1091–1166: the thread runs the body inside `try`; an object is kept as
the future's `error`; a `std::exception` as `make_box(e.what())`, a string; `catch(...)` (any
other type: an error_ref, a foreign native value) records "Unknown exception." and **rethrows**
(1163–1169), so the exception leaves the thread's function and `std::terminate` ends the process
([thread.thread.constr]: an exception escaping the thread's function calls terminate).
future.cpp `deref` 12–33 throws the recorded `error` object.

Clojure: core.clj `future-call` 7110–7135 → `deref-future` 2315–2322 → Future.get: an
ExecutionException whose cause is what the body threw (java.util.concurrent.FutureTask). -/

def jFuture (body : JRes) : JRes :=
  match body with
  | .ok v => .ok v
  | .thrown (.obj o) => .thrown (.obj o)
  | .thrown (.std w) => .thrown (.obj (.str w))
  | .thrown _ => .terminated "std::terminate: an exception left the future's thread (core.cpp 1163–1169)"
  | .terminated w => .terminated w

def cFuture (body : CRes) : CRes :=
  match body with
  | .ok v => .ok v
  | .thrown e => .thrown ({ cls := .executionException, message := some "java.util.concurrent.ExecutionException" } :: e)

/-! ## The nREPL's `*e`

jank: evaluate.cpp `safe_eval` 733–778: an error_ref becomes `make_box<exception_info>(e)`, which
has an empty message, nil data and no cause (exception_info.cpp 23–27; round 4's U44); an
exception_info object is kept; another object becomes `ex_info(e.to_string(), {})`; a
`std::exception` `ex_info(e.what(), {})`. Clojure: `*e` is what was thrown. -/

def jStarE : JThrown → JEx
  | .err e => { message := "", data := .nil, error := some e }
  | .obj (.ex e) => e
  | .obj (.str s) => { message := s, data := .nil }
  | .obj _ => { message := "object", data := .nil }
  | .std w => { message := w, data := .nil }
  | .foreign => { message := "uncaught exception", data := .nil }

/-! ## Printing -/

def Inner.show : Inner → String
  | .exInfo => "(throw (ex-info \"x\" {:k 1}))"
  | .native => "(nth [1 2] 5)"
  | .readBad => "(read-string \"(\")"
  | .evalUnresolved => "(eval 'nope)"

def Text.show : Text → String
  | .form v => s!"\"{v}\""
  | .empty => "\"\""
  | .unterminated => "\"(\""
  | .strayCloser => "\")\""

def EofOpt.show : EofOpt → String
  | .absent => ""
  | .eofthrow => "{:eof :eofthrow} "
  | .value v => s!"{"{"}:eof {v}} "

def Kind.show : Kind → String
  | .returned => ":returned"
  | .object => ":object"
  | .native => ":native"
  | .error => ":error"
  | .uncaught => ":uncaught"
  | .terminated => ":terminated"

end Jank.R5.Errors
