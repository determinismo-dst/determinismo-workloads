import Jank.Nrepl.Bencode

/-!
# What the handlers read: namespaces, vars' metadata, the abstract evaluator, `safe_eval`

(jank 7135b7708. ns.cpp, context.cpp, var.cpp, meta.cpp, loader.cpp, option.hpp, storage.hpp,
oref.hpp and context_dynamic.cpp are unchanged from f3d82d654; `safe_eval` moved to
evaluate.cpp:733, its `unwrap` to line 743.)

## The `:jank/source` metadata (core/meta.cpp)

`source_to_meta(start, end)` (meta.cpp:216) records the module only when
`is_core_module(current ns)` (loader.cpp:284, the list at 256–280: cpp, user, clojure.core,
clojure.string, clojure.walk, the nREPL server's namespaces, ...), and `source_to_meta(source)`
(meta.cpp:170) writes `:module` only then (lines 177–181). A var's metadata is its name symbol's
(evaluate.cpp:336 `var->set_meta(eval(name->get_meta()))`, the reader's source meta included,
analyze/processor.cpp `analyze_def`). So a var defined in a project namespace has a
`:jank/source` with no `:module`.

## Namespaces (ns.cpp, context.cpp)

`ns-resolve` (core.jank:4675) → `runtime::ns_resolve` (core.cpp:865) → `ns::find_var(sym)`
(ns.cpp:117):

    if(!sym->ns.empty()) {
      auto const qualified_sym(__rt_ctx->qualify_symbol(sym));
      return __rt_ctx->find_var(qualified_sym);
    }
    ... the ns's own mappings (`vars`) ...

`context::qualify_symbol` (context.cpp:116) resolves the symbol's namespace part with
`resolve_ns` (context.cpp:444), which looks the alias up in `current_ns()` — the value of `*ns*`
on the calling thread — not in the namespace `ns-resolve` was given. `context::find_var`
(context.cpp:136) then finds the namespace by its full name and looks the var up there.

Clojure (Compiler.java `maybeResolveIn` → `namespaceFor(n, sym)`, clojure-ref
src/jvm/clojure/lang/Compiler.java): the alias is looked up in `n`, the namespace given to
`ns-resolve`, then by full name.

The namespaces here are a fixed registry: clojure.core (with the metadata its `defn`s give:
`:arglists '(...)` is the literal parameter vectors, core.jank `defn` line 727 via `sigs`),
clojure.string, user (referring clojure.core, handler/eval.jank:15) and `my.app`, a user namespace
with an alias, loaded before the session (assumption).

## Evaluation (abstract)

Code is looked up in a table of programs (`program`): a list of forms, each a step of the
connection thread. `context::eval_string` (context_dynamic.cpp:50) evaluates the forms in order
and returns the last value, or `jtl::none` when the code holds no form (only whitespace, comments,
`#_` discards: the parser yields `none`, parse.cpp:204–330).

`safe_eval` (evaluate.cpp:733) calls `eval_string(code, p).unwrap()` (line 743) without checking for none.
`jtl::option::unwrap` (option.hpp:161) is `jank_debug_assert(set); return *data;`: a debug build
(no NDEBUG, primitive.hpp:3) aborts the process (assert.cpp `do_assertion_panic` → `::abort()`);
a release build returns the storage, which `jtl::storage` zero-initializes
(storage.hpp:132 `u8 value[sizeof(T)]{}`): an `object_ref` whose bits are 0, which oref.hpp decodes
as the double +0.0 (`is_tagged_small_real`: bits < 0xFFF8000000000000, line 113).
-/

namespace Jank.NreplServer

/-- A var's metadata as `lookup` and `completions` read it. -/
structure VarInfo where
  ns : String
  name : String
  doc : Option String := none
  arglists : Option JVal := none
  isMacro : Bool := false
  /-- `(get-in (meta v) [:jank/source :module])`. -/
  module : Option String := none
  deriving Repr, Inhabited

structure NsInfo where
  name : String
  /-- `ns-map`: symbol name → var (interned or referred). -/
  mappings : List (String × VarInfo)
  aliases : List (String × String) := []
  deriving Repr, Inhabited

/-- loader.cpp `core_modules` (line 256). -/
def coreModules : List String :=
  ["cpp", "user", "clojure.core", "clojure.core-native", "clojure.string", "clojure.string-native",
   "clojure.walk", "jank.perf-native", "jank.compiler-native", "jank.nrepl.server.inspect",
   "jank.nrepl.server.core", "jank.nrepl.server.handler", "jank.nrepl.server.bencode",
   "jank.nrepl.server.capture", "jank.nrepl.server.util", "jank.nrepl.server.eval",
   "jank.nrepl.server.handler.close", "jank.nrepl.server.handler.clone",
   "jank.nrepl.server.handler.describe", "jank.nrepl.server.handler.completions",
   "jank.nrepl.server.handler.eval", "jank.nrepl.server.handler.lookup"]

/-- meta.cpp `source_to_meta`: `:module` only for a core module. -/
def moduleOf (ns : String) : Option String := if coreModules.contains ns then some ns else none

/-- Each var's `:module`, as its namespace gives it. -/
def withModule (vs : List VarInfo) : List VarInfo := vs.map fun v => { v with module := moduleOf v.ns }

/-- `(iteration ...)`'s arglists (core.jank:7602): `([step & {:keys [somef vf kf initk] :or {vf
identity kf identity somef some? initk nil}}])`. -/
def iterationArglists : JVal :=
  .list [.vec [JVal.y "step", JVal.y "&",
    .map [(JVal.k "keys", .vec [JVal.y "somef", JVal.y "vf", JVal.y "kf", JVal.y "initk"]),
          (JVal.k "or", .map [(JVal.y "vf", JVal.y "identity"), (JVal.y "kf", JVal.y "identity"),
                              (JVal.y "somef", JVal.y "some?"), (JVal.y "initk", .nil)])]]]

def coreVars : List VarInfo := withModule [
  { ns := "clojure.core", name := "map", doc := some "Returns a lazy sequence ...",
    arglists := some (.list [.vec [JVal.y "f"], .vec [JVal.y "f", JVal.y "coll"]]) },
  { ns := "clojure.core", name := "iteration", doc := some "Creates a seqable/reducible ...",
    arglists := some iterationArglists },
  { ns := "clojure.core", name := "when", doc := some "Evaluates test.", isMacro := true,
    arglists := some (.list [.vec [JVal.y "test", JVal.y "&", JVal.y "body"]]) },
  { ns := "clojure.core", name := "*ns*" } ]

def stringVars : List VarInfo := withModule [
  { ns := "clojure.string", name := "join", doc := some "Returns a string of all elements in coll ...",
    arglists := some (.list [.vec [JVal.y "coll"], .vec [JVal.y "separator", JVal.y "coll"]]) } ]

/-- `user` (a core module): `(defn f [& {:keys [verbose] :or {verbose false}}] ...)` and
`(defn g [& {:keys [x] :or {x 1.5}}] ...)` evaluated there. -/
def userVars : List VarInfo := withModule [
  { ns := "user", name := "f",
    arglists := some (.list [.vec [JVal.y "&", .map [(JVal.k "keys", .vec [JVal.y "verbose"]),
      (JVal.k "or", .map [(JVal.y "verbose", .bool false)])]]]) },
  { ns := "user", name := "g",
    arglists := some (.list [.vec [JVal.y "&", .map [(JVal.k "keys", .vec [JVal.y "x"]),
      (JVal.k "or", .map [(JVal.y "x", .real "1.5")])]]]) } ]

/-- `my.app`, a project namespace: `(ns my.app (:require [clojure.string :as str]))`,
`(defn h "Adds one." [x] (inc x))`. -/
def appVars : List VarInfo := withModule [
  { ns := "my.app", name := "h", doc := some "Adds one.",
    arglists := some (.list [.vec [JVal.y "x"]]) } ]

def registry : List NsInfo := [
  { name := "clojure.core", mappings := coreVars.map fun v => (v.name, v) },
  { name := "clojure.string", mappings := stringVars.map fun v => (v.name, v) },
  { name := "user", mappings := (coreVars ++ userVars).map fun v => (v.name, v) },
  { name := "my.app", mappings := (coreVars ++ appVars).map (fun v => (v.name, v)),
    aliases := [("str", "clojure.string")] } ]

def findNs (name : String) : Option NsInfo := registry.find? (·.name == name)

/-- A symbol read from a string (`(symbol "a/b")`): its namespace part and name. -/
def splitSym (s : String) : Option String × String :=
  match s.splitOn "/" with
  | [n] => (none, n)
  | q :: rest => if q.isEmpty || rest == [""] then (none, s) else (some q, "/".intercalate rest)
  | [] => (none, s)

/-- context.cpp `resolve_ns` (line 444): an alias of `current` (the thread's `*ns*`), else the
namespace of that full name. -/
def resolveNs (current : String) (target : String) : Option String :=
  match (findNs current).bind (fun n => n.aliases.lookup target) with
  | some a => some a
  | none => (findNs target).map (·.name)

/-- jank `ns-resolve`: ns.cpp `ns::find_var` (line 117) with `qualify_symbol` (context.cpp:116)
resolving the alias against `current` (the calling thread's `*ns*`), then `context::find_var`
(context.cpp:136). -/
def jankNsResolve (current : String) (n : NsInfo) (sym : Option String × String) : Option VarInfo :=
  match sym with
  | (some q, name) =>
    let qualifiedNs := (resolveNs current q).getD q
    (findNs qualifiedNs).bind fun target => target.mappings.lookup name
  | (none, name) => n.mappings.lookup name

/-- Clojure `ns-resolve` (Compiler.maybeResolveIn → namespaceFor(n, sym)): the alias is looked up
in `n`, the namespace given, then the full name. -/
def cljNsResolve (n : NsInfo) (sym : Option String × String) : Option VarInfo :=
  match sym with
  | (some q, name) =>
    let target := (n.aliases.lookup q).getD q
    (findNs target).bind fun t => t.mappings.lookup name
  | (none, name) => n.mappings.lookup name

/-! ## The abstract evaluator -/

/-- A runtime value of user code. -/
inductive RVal where
  | nil
  /-- the double +0.0: what a zero `object_ref` decodes to -/
  | real0
  | long (i : Int)
  | str (s : String)
  | exInfo (msg : String)
  deriving Repr, BEq, Inhabited

/-- `to_code_string` (what `pr-str` gives). -/
def RVal.pr : RVal → String
  | .nil => "nil"
  | .real0 => "0.0"
  | .long i => toString i
  | .str s => "\"" ++ s ++ "\""
  | .exInfo m => s!"#error \{:cause \"{m}\"}"

/-- `to_string` (what `str` gives). -/
def RVal.text : RVal → String
  | .str s => s
  | v => v.pr

/-- A form of the abstract language: one step of the evaluating thread each (`println` two:
its `fwrite` and its `putc`, core.cpp:171). -/
inductive Form where
  | lit (v : RVal)
  /-- `(println s)`: `fwrite` of `s`, then `putc('\n')`, to `*out*`'s `FILE*` -/
  | println (s : String)
  /-- `(print s)`: `fwrite` of `s` -/
  | print (s : String)
  /-- `(throw (ex-info msg {}))` -/
  | throw (msg : String)
  deriving Repr, BEq, Inhabited

/-- The program each code text reads as (assumption: jank's reader reads these texts to these
forms; the reader itself is another component). -/
def program (code : String) : List Form :=
  match code with
  | "" => []
  | ";; nothing here" => []
  | "#_(foo)" => []
  | "1" => [.lit (.long 1)]
  | "2" => [.lit (.long 2)]
  | "(println)" => [.println ""]
  | "(print \"  \")" => [.print "  "]
  | "(println \"hi\")" => [.println "hi"]
  | "(do (print \"a\") 3)" => [.print "a", .lit (.long 3)]
  | "(throw (ex-info \"boom\" {}))" => [.throw "boom"]
  | "(do (println \"x\") (str (range 300)))" => [.println "x", .lit (.str (String.ofList (List.replicate 300 'z')))]
  | _ => [.lit .nil]

/-- What `eval_string` gives: `none` for no form, else the last value or the exception thrown. -/
inductive EvalOut where
  | none
  | value (v : RVal)
  | thrown (e : RVal)
  deriving Repr, BEq, Inhabited

end Jank.NreplServer
