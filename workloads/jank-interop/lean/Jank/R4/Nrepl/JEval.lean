import Jank.R3.Nrepl.Rt

/-!
# Round 3, nREPL: jank's evaluation of a code string, wired to the reader and analyzer replicas

The path an nREPL `eval` takes in jank 7135b7708 (paths under `upstream-main/compiler+runtime/`):

- handler/eval.jank `do-eval` (22) → `(binding [*ns* target-ns *file* file-path] [(safe-eval code
  line col) *ns*])` (33–36) → eval.jank `safe-eval` (4) → evaluate.cpp `safe_eval` (733);
- `safe_eval` → `context::eval_string(code, p)` (context_dynamic.cpp:50) `.unwrap()` (743); on
  success `*3`, `*2`, `*1` shift once (746–748); an `error_ref`, a jank object, a `std::exception`
  or anything else sets `*e` (750–775) and returns false;
- `eval_string`: a lexer and a parser over the whole string; `for(auto const &form : p_prc)` reads
  ONE form (`processor::iterator::operator++` → `processor::next`, parse.cpp:159/204), analyzes it
  with a fresh `analyze::processor` in statement position (69), `pass::optimize`s it, evaluates it
  (`evaluate::eval`, 71), then reads the next. A read error is thrown by `form.expect_ok()` (61/69)
  after the earlier forms ran; an analysis error by `.expect_ok()` (70). The value is the last
  form's; no form at all gives `jtl::none` (76–79), which `safe_eval`'s `unwrap` turns into a zeroed
  `object_ref` (release) or an abort (debug) (REPORT-2 R132).

Replicas used: the reader `Jank.Read.nextForm` (parse.cpp `next`, one call per form, the parser
state kept across forms), `jankForm` (the objects `parse_*` build, with `source_to_meta` read
under the thread's current `*ns*` and `*file*`), the analyzer `Jank.Analyzer.analyzeTop` +
`optimize` (processor.cpp, one fresh processor per form: `initialState`), its runtime view
(`Runtime`: namespaces, `qualify_symbol`, `find_var`, `intern_owned_var`, `macroexpand`) rebuilt
from this process's state before each analysis, and the evaluation of the analyzed tree: the meaning
`Jank.Analyzer.Eval` gives it (if/case/let typing and conversions, closures, `recur`), copied here
with the runtime it needs (effects, vars with roots and metadata, thread bindings, exceptions as
objects, `cpp/jank.runtime.*` calls) — Eval.lean's own `evalE`/`invoke` have no effects and a fixed
builtin table, so they cannot be called as they are.

The core library (`clojure.core` as core.jank defines the vars the grammar uses): macros as
core.jank expands them (`defn` 712, `defmacro` 808, `ns` 5581, `when` 855, `let` 642, `fn` 650,
`comment` 932), functions as the C++ runtime functions they call (core.cpp `print1` 161,
`println` 169, `pr` 192, `prn` 213, `in_ns` 819 (returns nil), `refer` 4717 → `ns::refer`
ns.cpp:174, `pr-str` 627 (one argument), ...).
-/

namespace Jank.R4.Nrepl
open Jank.R3.Nrepl

open Jank.Analyzer

/-! ## The process's shared state (jank) -/

/-- Everything the threads share: namespaces (the analyzer's `NsCell`s), var cells, the heap, the
analyzer's arena (closures point into it), closures. -/
structure JW where
  nss : List NsCell
  slots : Slots
  heap : Heap := {}
  arena : Arena := {}
  closures : Array Closure := #[]
  gensym : Nat := 0
  deriving Inhabited

/-- How an evaluation step can fail. -/
inductive Fail where
  /-- A jank object thrown (`throw`): caught by `safe_eval` as `object_ref`. -/
  | thrown (o : Obj)
  /-- A `jank::error_ref` (read, analysis, `expect_ok` on a failed result). -/
  | error (kind msg : String)
  /-- A `std::exception` (`std::runtime_error` from the runtime). -/
  | stdex (msg : String)
  | ub (what : String)
  /-- Outside the model's grammar. -/
  | unsupported (what : String)
  | fuel
  deriving Inhabited

/-- The failures `safe_eval` catches (as opposed to the model's own bounds). -/
def Fail.isUser : Fail → Bool
  | .thrown _ | .error .. | .stdex _ => true
  | _ => false

def Fail.show (h : Heap) : Fail → String
  | .thrown o => s!"throws {prObj .jank h o}"
  | .error k m => s!"error_ref {k}: {m}"
  | .stdex m => s!"std::exception {m}"
  | .ub w => s!"UB {w}"
  | .unsupported w => s!"unsupported {w}"
  | .fuel => "fuel"

/-- One evaluation's state: the shared state, the evaluating thread's bindings, what it printed. -/
structure ES where
  w : JW
  tb : TB
  out : Array OutEv := #[]
  fuel : Nat := 4000
  deriving Inhabited

abbrev EM := EStateM Fail ES

def etick : EM Unit := do
  let s ← get
  if s.fuel == 0 then throw .fuel
  set { s with fuel := s.fuel - 1 }

def eliftE {α : Type} (e : Except Outcome α) : EM α :=
  match e with
  | .ok v => pure v
  | .error (.thrown m) => throw (.stdex m)
  | .error (.compileError m) => throw (.error "codegen" m)
  | .error (.ub m) => throw (.ub m)
  | .error .fuel => throw .fuel
  | .error (.unsupported m) => throw (.unsupported m)
  | .error (.value _) => throw (.unsupported "value as an error")

def heapM : EM Heap := do pure (← get).w.heap
def setHeap (h : Heap) : EM Unit := modify fun s => { s with w := { s.w with heap := h } }
def emit (e : OutEv) : EM Unit := modify fun s => { s with out := s.out.push e }

/-- `ex_info(msg, data)` as a jank object. -/
def newEx (msg : String) (data : Obj := .nil) (origin : String := "throw") : EM Obj := do
  let (h, o) := (← heapM).newEx { msg, data, origin }
  setHeap h
  pure o

def curNsName (s : ES) : String :=
  match s.tb.deref s.w.slots vNs with
  | some o => (s.w.heap.nsName? o).getD "clojure.core"
  | none => "clojure.core"

/-! ## The core library -/

/-- The runtime functions the grammar calls, by name (`.opaque .nativeFunctionWrapper k`). -/
def jBuiltins : List String :=
  ["=", "nil?", "meta", "vector", "list", "count", "first", "rest", "str", "inc", "+", "<", "pos?",
   "*", "println", "print", "prn", "pr", "pr-str", "ex-info", "ex-message", "ex-data", "in-ns",
   "refer", "require", "alias", "find-ns", "the-ns", "ns-name", "create-ns", "reset-meta!", "assoc",
   "conj", "deref", "swap!", "map", "symbol", "keyword", "identity", "hash-map", "iteration",
   "clojure.string/join", "clojure.string/blank?", "var-get", "list*", "seq", "set-macro!", "vec", "doall",
   -- round 4: binding, dotimes, the spec's try
   "push-thread-bindings", "pop-thread-bindings", "int", "long", "unchecked-inc", "spec-try"]

def bObj (n : String) : Obj := .opaque .nativeFunctionWrapper (jBuiltins.idxOf n)

def sym (n : String) : Obj := .symbol none "" n
def qsym (ns n : String) : Obj := .symbol none ns n
def lst (xs : List Obj) : Obj := .persistentList none xs
def vec (xs : List Obj) : Obj := .persistentVector none xs
def quoteO (o : Obj) : Obj := lst [sym "quote", o]
def amap (kvs : List (Obj × Obj)) : Obj := .persistentArrayMap none kvs

/-- `(fn* [args] ...)`'s `:arglists` the core vars carry, as data. -/
def arglistsOf (ps : List (List String)) : Obj := lst (ps.map fun p => vec (p.map sym))

/-- core.jank's metadata for a var it defines: `:arglists`, `:doc`, the reader's `:jank/source`
(`:module "clojure.core"`, a core module). -/
def coreMeta (ns : String) (arglists : Option Obj) (doc : String) (isMacro : Bool := false) : Obj :=
  amap ([(kw "jank/source", amap [(kw "module", str ns)])]
    ++ (match arglists with | some a => [(kw "arglists", a)] | none => [])
    ++ [(kw "doc", str doc)] ++ (if isMacro then [(kw "macro", .boolean true)] else []))

/-- `(iteration ...)`'s arglists (core.jank:7602): the `:or` map holds `initk nil` (REPORT-2
R131). -/
def iterationArglists : Obj :=
  lst [vec [sym "step", sym "&", amap [(kw "keys", vec [sym "somef", sym "vf", sym "kf", sym "initk"]),
    (kw "or", amap [(sym "vf", sym "identity"), (sym "kf", sym "identity"), (sym "somef", sym "some?"),
      (sym "initk", .nil)])]]]

/-! ### Macros, as core.jank expands them

A macro's function gets jank's arguments (context.cpp `macroexpand1` 604: `&form` is `((args))`,
`&env` the macro's symbol, REPORT-2 R30), so `args` here starts with those two. -/

/-- `sigs` (core.jank:684): each arity's parameter vector (`&form &env` elided). -/
def sigsOf (fdecl : List Obj) : List Obj :=
  match fdecl.headD .nil with
  | .persistentVector .. => [fdecl.headD .nil]
  | _ => fdecl.filterMap fun a => match a.elems with
    | some (p :: _) => some p
    | _ => none

/-- core.jank `defn` (712): `(def ~(with-meta name m) ~(with-meta `(fn ~name ~@fdecl) {:rettag ..}))`
with `m` = `(conj (meta name) {:arglists '(sigs) :doc ...})`. -/
def defnMacro : MacroFn
  | _ :: _ :: name :: fdecl0 =>
    match name with
    | .symbol md _ _ =>
      let (doc, fdecl) := match fdecl0 with
        | .persistentString d :: rest => (some d, rest)
        | x => (none, x)
      let fdecl := match fdecl with
        | (.persistentArrayMap ..) :: rest => rest
        | x => x
      let arities := sigsOf fdecl
      let m : List (Obj × Obj) := [(kw "arglists", quoteO (lst arities))]
        ++ (match doc with | some d => [(kw "doc", str d)] | none => [])
      let base : List (Obj × Obj) := match md with
        | some (.persistentArrayMap _ kvs) => kvs
        | _ => []
      let merged := m.foldl (fun acc (k, v) => (acc.filter fun (k', _) => !k'.equiv k) ++ [(k, v)]) base
      let name' := name.setMeta (some (amap merged))
      .ok (lst [sym "def", name', lst (qsym "clojure.core" "fn" :: name.setMeta none :: fdecl)])
    | _ => .error "First argument to defn must be a symbol"
  | _ => .error "Wrong number of args passed to: defn"

/-- core.jank `defmacro` (808): `(do (clojure.core/defn name [&form &env ...] ...)
(clojure.core/reset-meta! (var name) (assoc (meta (var name)) :macro true)) (var name))`. -/
def defmacroMacro : MacroFn
  | _ :: _ :: name :: args =>
    let (pre, fdecl) := match args with
      | (d@(.persistentString _)) :: rest => ([d], rest)
      | x => ([], x)
    let fdecl := match fdecl.headD .nil with
      | .persistentVector .. => [lst fdecl]
      | _ => fdecl
    let addImplicit (fd : Obj) : Obj :=
      match fd.elems with
      | some (.persistentVector _ ps :: body) => lst (vec (sym "&form" :: sym "&env" :: ps) :: body)
      | _ => fd
    let fdecl := fdecl.map addImplicit
    .ok (lst [sym "do",
      lst (qsym "clojure.core" "defn" :: name :: pre ++ fdecl),
      lst [qsym "clojure.core" "reset-meta!", lst [sym "var", name],
           lst [sym "assoc", lst [sym "meta", lst [sym "var", name]], kw "macro", .boolean true]],
      lst [sym "var", name]])
  | _ => .error "Wrong number of args passed to: defmacro"

/-- core.jank `ns` (5581) for `(ns name refs*)` with `(:require libspec*)` references. -/
def nsMacro : MacroFn
  | _ :: _ :: name :: refs =>
    let refs := refs.filter fun r => match r with | .persistentString _ => false | _ => true
    let nameMeta := name.getMeta
    let nm := name.setMeta none
    let process (r : Obj) : Obj :=
      match r.elems with
      | some (.keyword _ k :: args) => lst (qsym "clojure.core" k :: args.map quoteO)
      | _ => lst [qsym "clojure.core" "comment"]
    let referClj := !refs.any fun r => match r.elems with
      | some (.keyword _ "refer-clojure" :: _) => true
      | _ => false
    .ok (lst ([sym "do", lst [qsym "clojure.core" "in-ns", quoteO nm]]
      ++ (match nameMeta with
          | some m => [lst [qsym "clojure.core" "reset-meta!", lst [qsym "clojure.core" "find-ns", quoteO nm], m]]
          | none => [])
      ++ [lst (sym "do" :: (if referClj && nm != sym "clojure.core" then [lst [qsym "clojure.core" "refer", quoteO (sym "clojure.core")]] else [])
              ++ refs.map process),
          lst [sym "if", lst [qsym "clojure.core" "=", quoteO nm, quoteO (sym "clojure.core")], .nil,
               lst [sym "do", lst [qsym "clojure.core" "swap!",
                       lst [qsym "clojure.core" "deref", lst [sym "var", qsym "clojure.core" "*loaded-libs*"]],
                       qsym "clojure.core" "conj", quoteO nm], .nil]]]))
  | _ => .error "Wrong number of args passed to: ns"

/-- `comment` (core.jank:932): nil. -/
def commentMacro : MacroFn
  | _ => .ok .nil

/-- `print`'s `:inline` (core.jank:592): `(list 'cpp/jank.runtime.print1 x)`, arity 1. -/
def printInline : MacroFn
  | [x] => .ok (lst [qsym "cpp" "jank.runtime.print1", x])
  | _ => .error "inline arity"

/-- Round 4. core.jank `binding` (2794): `(do (push-thread-bindings (hash-map (var x) v ...))
(try (do body...) (finally (pop-thread-bindings))))` — a `do`, where Clojure's is `(let [] ...)`. -/
def bindingMacro : MacroFn
  | _ :: _ :: (.persistentVector _ bs) :: body =>
    let rec pairs : List Obj → List Obj
      | x :: v :: rest => lst [sym "var", x] :: v :: pairs rest
      | _ => []
    .ok (lst [sym "do",
      lst [qsym "clojure.core" "push-thread-bindings", lst (qsym "clojure.core" "hash-map" :: pairs bs)],
      lst [sym "try", lst (sym "do" :: body), lst [sym "finally", lst [qsym "clojure.core" "pop-thread-bindings"]]]])
  | _ => .error "binding requires a vector for its binding"

/-- Round 4. core.jank `dotimes` (2694): `(let [n# (int n)] (loop [i 0] (when (< i n#) body...
(recur (unchecked-inc i)))))`. -/
def dotimesMacro : MacroFn
  | _ :: _ :: (.persistentVector _ [i, n]) :: body =>
    .ok (lst [qsym "clojure.core" "let", vec [sym "dotimes__n", lst [qsym "clojure.core" "int", n]],
      lst [qsym "clojure.core" "loop", vec [i, Obj.ofInt 0],
        lst ([qsym "clojure.core" "when", lst [qsym "clojure.core" "<", i, sym "dotimes__n"]] ++ body ++
          [lst [sym "recur", lst [qsym "clojure.core" "unchecked-inc", i]]])]])
  | _ => .error "dotimes requires a vector for its binding"

/-- The core macros: name, function. -/
def coreMacros : List (String × MacroFn) :=
  [("when", whenMacro), ("let", letMacro), ("loop", loopMacro), ("fn", fnMacro), ("or", orMacro),
   ("and", andMacro), ("defn", defnMacro), ("defmacro", defmacroMacro), ("ns", nsMacro),
   ("comment", commentMacro), ("binding", bindingMacro), ("dotimes", dotimesMacro)]

/-- `:inline` functions core.jank gives the vars (inc 1646, + 1372, * 1405, pos? 1664, print 592). -/
def coreInline : List (String × MacroFn × List Nat) :=
  [("inc", incInline, [1]), ("+", addInline, [2]), ("*", mulInline, [2]), ("pos?", posInline, [1]),
   ("print", printInline, [1])]

def builtinArglists : String → List (List String)
  | "println" | "print" | "prn" | "pr" | "str" | "vector" | "list" | "hash-map" => [["&", "more"]]
  | "pr-str" | "inc" | "count" | "first" | "rest" | "nil?" | "meta" | "deref" | "identity"
  | "ex-message" | "ex-data" | "the-ns" | "ns-name" | "find-ns" | "create-ns" | "symbol"
  | "keyword" | "in-ns" | "pos?" | "var-get" | "seq" => [["x"]]
  | "map" => [["f", "coll"]]
  | "ex-info" => [["msg", "map"]]
  | _ => [["x", "y"]]

def dynVars : List String := ["*ns*", "*file*", "*1", "*2", "*3", "*e", "*loaded-libs*"]

def coreFnNames : List String :=
  jBuiltins.filter fun n => !n.startsWith "clojure.string/"

/-- The process after start-up, as the nREPL server sees it: `clojure.core` (the vars above),
`clojure.string` (`join`, `blank?`), `user` (created by handler/eval.jank:8, with clojure.core
referred, 15–16). `*loaded-libs*`'s root is an atom (context.cpp:65). -/
def jankBase : JW := Id.run do
  let mut slots : Slots := []
  let mut coreMap : List (String × VarRef) := []
  for n in coreFnNames do
    let r := coreRef n
    let md := if n == "iteration" then coreMeta "clojure.core" (some iterationArglists) n
      else coreMeta "clojure.core" (some (arglistsOf (builtinArglists n))) n
    slots := slots.set r { root := some (bObj n), md }
    coreMap := coreMap ++ [(n, r)]
  for (n, _) in coreMacros do
    let r := coreRef n
    slots := slots.set r { root := some (bObj "identity"), md := coreMeta "clojure.core" (some (arglistsOf [["&", "body"]])) n true }
    coreMap := coreMap ++ [(n, r)]
  let (heap, libs) := ({} : Heap).newAtom (.persistentSortedSet none [sym "clojure.core"])
  for n in dynVars do
    let r := coreRef n
    let root := if n == "*file*" then some (str "NO_SOURCE_PATH")
      else if n == "*loaded-libs*" then some libs else some .nil
    slots := slots.set r { root, dynamic := true, md := coreMeta "clojure.core" none n }
    coreMap := coreMap ++ [(n, r)]
  let joinR : VarRef := ⟨"clojure.string", "join"⟩
  let blankR : VarRef := ⟨"clojure.string", "blank?"⟩
  let strMap : List (String × VarRef) := [("join", joinR), ("blank?", blankR)]
  let joinSlot : Slot := { root := some (bObj "clojure.string/join")
                           md := coreMeta "clojure.string" (some (arglistsOf [["coll"], ["separator", "coll"]])) "Returns a string of all elements in coll." }
  let blankSlot : Slot := { root := some (bObj "clojure.string/blank?")
                            md := coreMeta "clojure.string" (some (arglistsOf [["s"]])) "True if s is nil, empty, or contains only whitespace." }
  slots := (slots.set joinR joinSlot).set blankR blankSlot
  let nss : List NsCell := [{ name := "clojure.core", mappings := coreMap },
    { name := "clojure.string", mappings := strMap }, { name := "user", mappings := coreMap }]
  return { nss, slots, heap }

/-- A new connection thread's bindings: the frame `future` conveys (core.cpp:1091 → the accept
loop's frame, itself conveyed from the frame context.cpp:107 pushes: `*ns*`, `*1`, `*2`, `*3`,
`*e`), each value in a new box (context.cpp:727–735). -/
def connTB (h : Heap) (connNs : String) : Heap × TB :=
  let (h, nso) := h.nsObj connNs
  (h, ({} : TB).push [(vNs, nso), (v1, .nil), (v2, .nil), (v3, .nil), (vE, .nil)])

/-! ## The analyzer's view of the runtime -/

/-- Is a var a macro (`(:macro (meta var))`, context.cpp:625). -/
def isMacroMeta (md : Obj) : Bool := (metaGet md "macro").truthy

mutual

/-- Evaluates an analyzed expression (the meaning `Jank.Analyzer.Eval.evalE` gives it, with this
process's runtime). -/
partial def evalE (i : ExprId) (env : List (BindingId × Val)) (selfs : List (FnCtxId × Obj)) : EM Flow := do
  etick
  let a := (← get).w.arena
  let e := a.expr i
  match e.data with
  | .primitiveLiteral d => pure (.val (.obj d))
  | .cppLiteral d =>
    let t := literalType d false
    match d with
    | .smallInteger v => pure (.val (.nat t (.i v.toInt)))
    | .integer v => pure (.val (.nat t (.i v.toInt)))
    | .boolean b => pure (.val (.nat t (.b b)))
    | .persistentString s => pure (.val (.nat t (.cs s)))
    | _ => throw (.unsupported "cpp literal")
  | .localReference _ b =>
    match env.lookup b with
    | some v => pure (.val v)
    | none => throw (.unsupported s!"unbound local {b}")
  | .varRef _ vr => pure (.val (.obj (.var vr.ns vr.name)))
  | .varDeref _ vr =>
    -- evaluate.cpp:364 `var->deref()`: the thread binding, else the root (an unbound root is
    -- the `var_unbound_root` object).
    let s ← get
    match s.tb.deref s.w.slots vr with
    | some o => pure (.val (.obj o))
    | none => pure (.val (.obj (.opaque .varUnboundRoot 0)))
  | .recursionReference ctx =>
    match selfs.lookup ctx with
    | some o => pure (.val (.obj o))
    | none => throw (.unsupported "recursion reference without its function")
  | .function _ _ ars _ _ =>
    let s ← get
    let k := s.w.closures.size
    let ctxs := ars.map (·.fnCtx)
    let self := closureObj k
    let arityFrames := ars.filterMap (·.frame)
    let captured := arityFrames.flatMap fun fr => ((a.frame fr).captures.filterMap fun (_, c) =>
      (env.lookup c.originatingBinding).map (c.binding, ·))
    set { s with w := { s.w with closures := s.w.closures.push { fnExpr := i, env := captured ++ env, selfs := selfs ++ ctxs.map (·, self) } } }
    pure (.val (.obj self))
  | .do_ vs =>
    let mut last : Flow := .val (.obj .nil)
    for v in vs do
      last ← evalE v env selfs
      if let .recur _ := last then return last
    pure last
  | .let pairs body kind =>
    let mut env := env
    let mut shadows : List (BindingId × CT) := []
    for (b, v) in pairs do
      let x ← evalVal v env selfs
      if kind == .loopWithRecur then
        let t := mutableType (exprType a v 10000)
        let x' ← eliftE (assignTo t x)
        env := (b, x') :: env
        shadows := shadows ++ [(b, t)]
      else env := (b, x) :: env
    if kind != .loopWithRecur then return ← evalE body env selfs
    let mut cur := env
    for _ in [0:100000] do
      match ← evalE body cur selfs with
      | .val v => return .val v
      | .recur args =>
        let mut nenv := cur
        for ((b, t), x) in shadows.zip args do
          nenv := (b, ← eliftE (assignTo t x)) :: nenv
        cur := nenv
    throw .fuel
  | .if_ t c th el =>
    let cv ← evalVal c env selfs
    let truthy := match cv with
      | .obj o => o.truthy
      | .nat _ (.b b) => b
      | .nat _ (.i x) => x != 0
      | .nat _ (.d f) => f != 0.0
      | .nat _ (.cs _) => true
    let branch := if truthy then some th else el
    let r ← match branch with
      | some x => evalE x env selfs
      | none => pure (.val (.obj .nil))
    match r with
    | .recur args => pure (.recur args)
    | .val v => pure (.val (← eliftE (assignTo t.toCT v)))
  | .recur _ args _ _ =>
    let mut vs := []
    for x in args do vs := vs ++ [← evalVal x env selfs]
    pure (.recur vs)
  | .def name value =>
    -- evaluate.cpp:333: intern, `set_meta(eval(name->get_meta()))`, `set_dynamic`, bind the root.
    let (ns, n) := symKey name
    let vr : VarRef := ⟨ns, n⟩
    let md ← evalMeta (name.getMeta.getD .nil)
    modify fun s => { s with w := { s.w with slots := s.w.slots.modify vr fun sl =>
      { sl with md, dynamic := (metaGet md "dynamic").truthy } } }
    match value with
    | some v =>
      let x ← evalVal v env selfs
      modify fun s => { s with w := { s.w with slots := s.w.slots.modify vr fun sl => { sl with root := some x.toObj } } }
    | none => pure ()
    pure (.val (.obj (.var ns n)))
  | .vector xs md =>
    let vs ← xs.mapM fun x => evalVal x env selfs
    let m ← md.mapM fun x => evalVal x env selfs
    pure (.val (.obj (.persistentVector (m.map (·.toObj)) (vs.map (·.toObj)))))
  | .list xs md =>
    let vs ← xs.mapM fun x => evalVal x env selfs
    let m ← md.mapM fun x => evalVal x env selfs
    pure (.val (.obj (.persistentList (m.map (·.toObj)) (vs.map (·.toObj)))))
  | .set xs md =>
    let vs ← xs.mapM fun x => evalVal x env selfs
    let m ← md.mapM fun x => evalVal x env selfs
    pure (.val (.obj (.persistentHashSet (m.map (·.toObj)) (vs.map (·.toObj)))))
  | .map kvs md =>
    let vs ← kvs.mapM fun (k, v) => do pure ((← evalVal k env selfs).toObj, (← evalVal v env selfs).toObj)
    let m ← md.mapM fun x => evalVal x env selfs
    pure (.val (.obj (.persistentArrayMap (m.map (·.toObj)) vs)))
  | .cppConversion t ct v pol =>
    let x ← evalVal v env selfs
    match pol with
    | .intoObject =>
      if isVoid ct.toCT then return .val (.obj .nil)
      pure (.val (.obj x.toObj))
    | .fromObject =>
      match x with
      | .obj o =>
        if isAnyObject t.toCT then
          if typedMatches t.toCT o then pure (.val (.obj o))
          else throw (.stdex s!"invalid object type (expected {t.toCT.spelling} found {reprStr o.type})")
        else pure (.val (.nat t.toCT (← eliftE (fromObject t.toCT o))))
      | .nat _ n => pure (.val (.nat t.toCT n))
  | .cppCall t src args _ =>
    let fname := match (a.expr src).data with
      | .cppValue _ _ _ (.named n) _ => n
      | _ => ""
    let vs ← args.mapM fun x => evalVal x env selfs
    evalCppCall t.toCT fname vs
  | .call src args _ =>
    let f ← evalVal src env selfs
    -- evaluate.cpp:379: a var in call position is dereferenced.
    let f ← match f.toObj with
      | .var ns n => do
        let s ← get
        pure (Val.obj ((s.tb.deref s.w.slots ⟨ns, n⟩).getD .nil))
      | _ => pure f
    let vs ← args.mapM fun x => evalVal x env selfs
    pure (.val (.obj (← invoke f.toObj (vs.map (·.toObj)))))
  | .namedRecursion rref _ args =>
    let f ← evalVal rref env selfs
    let vs ← args.mapM fun x => evalVal x env selfs
    pure (.val (.obj (← invoke f.toObj (vs.map (·.toObj)))))
  | .throw_ (some v) =>
    let x ← evalVal v env selfs
    throw (.thrown x.toObj)
  | .cppConstructorCall t _ [arg] _ =>
    -- Round 4 (from round 2's Eval.lean): `build_cpp_call`'s primitive cast (processor.cpp 252/267),
    -- what a `recur` into a native-typed loop local becomes (REPORT-2 R24).
    match ← evalVal arg env selfs with
    | .nat _ n => pure (.val (.nat t.toCT (← eliftE (convNative t.toCT n))))
    | .obj o => pure (.val (.nat t.toCT (← eliftE (fromObject t.toCT o))))
  | .try_ body cs fin =>
    -- Round 4. cpp_processor.cpp gen(try) 1053–1101, gen(catch) 1105–1127, gen(finally) 1129–1139:
    --   { auto const fin_fn{...}; jank::util::scope_exit guard{ fin_fn, true };
    --     try { body } catch(T e) { handler } ... catch(...) { guard.release(); fin_fn(); throw; }
    --     guard.release(); fin_fn(); }
    -- A `catch(object_ref e)` catches what `throw` threw (`throw static_cast<object_ref>(v)`, gen(throw)
    -- 1024–1050); a catch-all (`:default`, the void type) is `catch(...)` with `object_ref e;` — nil.
    -- A handler that throws leaves the try statement: the armed guard runs fin_fn while unwinding, and
    -- an exception from it then calls std::terminate (REPORT D24).
    let tryRun (x : EM Val) : EM (Except Fail Val) :=
      tryCatch (do let v ← x; pure (Except.ok v)) (fun f => pure (Except.error f))
    let runFin : EM Unit := match fin with
      | some fe => do discard <| evalE fe env selfs
      | none => pure ()
    match ← tryRun (evalVal body env selfs) with
    | .ok v => runFin; pure (.val v)
    | .error f =>
      if !f.isUser then throw f
      let pick := cs.find? fun c =>
        if isVoid c.type.toCT then true
        else if isAnyObject c.type.toCT then (match f with | .thrown _ => true | _ => false)
        else false
      match pick with
      | none =>
        -- `catch(...) { guard.release(); fin_fn(); throw; }` (or no catch-all and no finally: it propagates)
        runFin
        throw f
      | some c =>
        let eObj : Obj := if isVoid c.type.toCT then .nil else (match f with | .thrown o => o | _ => .nil)
        let cframe := (a.expr c.body).frame.getD 0
        let bid := ((a.frame cframe).locals.find? (·.1.equiv c.sym)).bind (·.2.head?)
        let env' := match bid with | some b => (b, Val.obj eObj) :: env | none => env
        match ← tryRun (evalVal c.body env' selfs) with
        | .ok v => runFin; pure (.val v)
        | .error f2 =>
          match fin with
          | none => throw f2
          | some fe =>
            match ← tryRun (do discard <| evalE fe env selfs; pure (Val.obj .nil)) with
            | .ok _ => throw f2
            | .error _ => throw (.unsupported "CRASH std::terminate: finally threw while a catch handler's exception unwound (D24)")
  | _ => throw (.unsupported s!"expression {reprStr e.kind}")

partial def evalVal (i : ExprId) (env : List (BindingId × Val)) (selfs : List (FnCtxId × Obj)) : EM Val := do
  match ← evalE i env selfs with
  | .val v => pure v
  | .recur _ => throw (.error "codegen" "recur outside of a loop or function")

/-- `context::eval(meta)` of a def's metadata (evaluate.cpp:336): a map of constants, `(quote x)`
evaluating to `x`. -/
partial def evalMeta (o : Obj) : EM Obj := do
  match o with
  | .persistentArrayMap _ kvs | .persistentHashMap _ kvs =>
    pure (.persistentArrayMap none (← kvs.mapM fun (k, v) => do pure (← evalMeta k, ← evalMeta v)))
  | .persistentList _ [.symbol _ "" "quote", x] => pure x
  | .persistentVector _ xs => pure (.persistentVector none (← xs.mapM evalMeta))
  | .symbol .. => throw (.unsupported "a symbol in def metadata")
  | .persistentList _ (_ :: _) => throw (.unsupported "a call in def metadata")
  | x => pure x

/-- `jank::runtime::<fn>` called from a `cpp_call` (inline expansions). -/
partial def evalCppCall (t : CT) (fname : String) (vs : List Val) : EM Flow := do
  match fname, vs with
  | "jank.runtime.inc", [.nat _ (.i x)] =>
    if Obj.isLongRange (x + 1) then pure (.val (.nat t (.i (x + 1)))) else throw (.stdex "Overflow on increment.")
  | "jank.runtime.inc", [.obj o] => pure (.val (.obj (← callBuiltin "inc" [o])))
  | "jank.runtime.add", [.nat lt l, .nat rt r] =>
    match getCommonType lt rt with
    | some ct =>
      let l' ← eliftE (convNative ct l)
      let r' ← eliftE (convNative ct r)
      match l', r' with
      | .i x, .i y => pure (.val (.nat ct (← eliftE (convNative ct (.i (x + y))))))
      | _, _ => throw (.unsupported "add")
    | none => throw (.unsupported "add")
  | "jank.runtime.add", [x, y] => pure (.val (.obj (← callBuiltin "+" [x.toObj, y.toObj])))
  | "jank.runtime.mul", [x, y] => pure (.val (.obj (← callBuiltin "*" [x.toObj, y.toObj])))
  | "jank.runtime.is_pos", [x] =>
    match ← callBuiltin "pos?" [x.toObj] with
    | .boolean b => pure (.val (.nat t (.b b)))
    | _ => throw (.unsupported "is_pos")
  | "jank.runtime.print1", [x] =>
    -- core.cpp:161 `print1`: one `fwrite` of `to_string`.
    let s ← strOf x.toObj
    emit (.out s.toUTF8.toList)
    pure (.val (.obj .nil))
  | "jank.runtime.get", [m, k] => pure (.val (.obj (builtinGet m.toObj k.toObj)))
  | "jank.runtime.get", [m, k, d] => pure (.val (.obj (builtinGet m.toObj k.toObj d.toObj)))
  | _, _ => throw (.unsupported s!"C++ call {fname}")

/-- `to_string` of an object, realizing a lazy sequence (which may throw). -/
partial def strOf (o : Obj) : EM String := do
  let o ← realize o
  pure (strObj .jank (← heapM) o)

/-- `to_code_string`, realizing lazy sequences. -/
partial def prOf (o : Obj) : EM String := do
  let o ← realize o
  pure (prObj .jank (← heapM) o)

/-- Realizes `map`'s lazy sequences inside a value (printing walks them). -/
partial def realize (o : Obj) : EM Obj := do
  match o with
  | .opaque .lazySequence k =>
    let some l := (← heapM).lazies[k]? | throw (.unsupported "lazy")
    let mut out := []
    for x in l.xs do
      out := out ++ [← realize (← invoke l.f [x])]
    pure (.persistentList none out)
  | .persistentVector m xs => pure (.persistentVector m (← xs.mapM realize))
  | .persistentList m xs => pure (.persistentList m (← xs.mapM realize))
  | x => pure x

/-- The runtime functions (C++ `jank::runtime::*` and core.jank fns), with jank's behavior. -/
partial def callBuiltin (n : String) (args : List Obj) : EM Obj := do
  match n, args with
  | "println", xs =>
    -- core.cpp:169: `fwrite` of the `to_string`s joined by spaces, then `putc('\n')`.
    if xs.isEmpty then emit (.out [10]); return .nil
    let parts ← xs.mapM strOf
    emit (.out (" ".intercalate parts).toUTF8.toList)
    emit (.out [10])
    pure .nil
  | "print", [x] =>
    emit (.out (← strOf x).toUTF8.toList); pure .nil
  | "print", x :: more =>
    -- core.jank:592 arity [x & more]: print1 x, print1 " ", then core.cpp `print` of more.
    emit (.out (← strOf x).toUTF8.toList)
    emit (.out [32])
    let parts ← more.mapM strOf
    emit (.out (" ".intercalate parts).toUTF8.toList)
    pure .nil
  | "print", [] => throw (.stdex "Wrong number of args (0) passed to print")
  | "prn", xs =>
    if xs.isEmpty then emit (.out [10]); return .nil
    let parts ← xs.mapM prOf
    emit (.out (" ".intercalate parts).toUTF8.toList)
    emit (.out [10])
    pure .nil
  | "pr", xs =>
    if xs.isEmpty then return .nil
    let parts ← xs.mapM prOf
    emit (.out (" ".intercalate parts).toUTF8.toList)
    pure .nil
  | "pr-str", [x] => pure (str (← prOf x))
  | "pr-str", xs => throw (.stdex s!"Wrong number of args ({xs.length}) passed to pr-str")
  | "str", xs =>
    let parts ← xs.mapM fun x => match x with
      | .nil => pure ""
      | x => strOf x
    pure (str (String.join parts))
  | "ex-info", [.persistentString m, d] => newEx m d
  | "ex-info", _ => throw (.stdex "ex-info: invalid arguments")
  | "ex-message", [.opaque .exceptionInfo k] =>
    pure (match (← heapM).exs[k]? with
      | some e => str e.msg
      | none => .nil)
  | "ex-message", [_] => pure .nil
  | "ex-data", [.opaque .exceptionInfo k] =>
    pure (((← heapM).exs[k]?).map (·.data) |>.getD .nil)
  | "ex-data", [_] => pure .nil
  | "in-ns", [.symbol _ "" nm] =>
    -- core.cpp:819: `current_ns_var->set(intern_ns(sym)).expect_ok(); return {};` (nil).
    internNs nm
    let (h, o) := (← heapM).nsObj nm
    setHeap h
    let s ← get
    match s.tb.set vNs o with
    | .ok tb => set { s with tb }
    | .error m => throw (.error "runtime" m)
    pure .nil
  | "in-ns", _ => throw (.stdex "in-ns: invalid object type (expected symbol)")
  | "create-ns", [.symbol _ "" nm] =>
    internNs nm
    let (h, o) := (← heapM).nsObj nm
    setHeap h
    pure o
  | "find-ns", [.symbol _ "" nm] =>
    if ((← get).w.nss.find? (·.name == nm)).isSome then
      let (h, o) := (← heapM).nsObj nm
      setHeap h
      pure o
    else pure .nil
  | "the-ns", [x] =>
    match x with
    | .opaque .ns _ => pure x
    | .symbol _ "" nm =>
      if ((← get).w.nss.find? (·.name == nm)).isSome then
        let (h, o) := (← heapM).nsObj nm
        setHeap h
        pure o
      else throw (.thrown (← newEx s!"No namespace: {nm} found"))
    | _ => throw (.stdex "the-ns: invalid argument")
  | "ns-name", [x] =>
    match (← heapM).nsName? x with
    | some nm => pure (sym nm)
    | none => throw (.stdex "ns-name: invalid object type (expected ns)")
  | "refer", [.symbol _ "" from_] =>
    -- core.jank:4717: every public var of `from_` through `ns::refer` (ns.cpp:174).
    let s ← get
    let cur := curNsName s
    let some src := s.w.nss.find? (·.name == from_) | throw (.thrown (← newEx "Unknown namespace."))
    let publics := src.mappings.filter fun (_, r) => r.ns == from_ && !(metaGet (s.w.slots.get r).md "private").truthy
    let mut nss := s.w.nss
    for (nm, r) in publics do
      let tgt := (nss.find? (·.name == cur)).getD { name := cur }
      match tgt.mappings.lookup nm with
      | some found =>
        if r.ns != found.ns && found.ns != "clojure.core" then
          throw (.error "runtime" s!"{nm} already refers to #'{found.ns}/{found.name} in ns {cur}")
      | none => pure ()
      nss := nss.map fun c => if c.name == cur then { c with mappings := (nm, r) :: c.mappings.filter (·.1 != nm) } else c
    modify fun s => { s with w := { s.w with nss } }
    pure .nil
  | "require", specs =>
    -- load-libs (core.jank:4875) for libs already loaded: `(alias as lib)` for `[lib :as as]`.
    for sp in specs do
      match sp with
      | .persistentVector _ [.symbol _ "" lib, .keyword "" "as", .symbol _ "" as_] =>
        discard <| callBuiltin "alias" [sym as_, sym lib]
      | .symbol _ "" lib =>
        if ((← get).w.nss.find? (·.name == lib)).isNone then
          throw (.thrown (← newEx s!"Could not locate {lib}"))
      | _ => throw (.unsupported "require spec")
    pure .nil
  | "alias", [.symbol _ "" as_, .symbol _ "" lib] =>
    let s ← get
    let cur := curNsName s
    if (s.w.nss.find? (·.name == lib)).isNone then throw (.thrown (← newEx s!"No namespace: {lib} found"))
    modify fun s => { s with w := { s.w with nss := s.w.nss.map fun c =>
      if c.name == cur then { c with aliases := (as_, lib) :: c.aliases.filter (·.1 != as_) } else c } }
    pure .nil
  | "reset-meta!", [.var ns nm, m] =>
    modify fun s => { s with w := { s.w with slots := s.w.slots.modify ⟨ns, nm⟩ fun sl => { sl with md := m } } }
    pure m
  | "reset-meta!", [.opaque .ns _, m] => pure m
  | "reset-meta!", _ => throw (.stdex "Objects of this type are not metadatable.")
  | "meta", [.var ns nm] => pure ((← get).w.slots.get ⟨ns, nm⟩).md
  | "meta", [x] => pure (x.getMeta.getD .nil)
  | "assoc", [m, k, v] => pure (m.assoc k v)
  | "conj", [.persistentSortedSet md xs, x] =>
    pure (.persistentSortedSet md (if xs.any (·.equiv x) then xs else xs ++ [x]))
  | "conj", [.persistentVector md xs, x] => pure (.persistentVector md (xs ++ [x]))
  | "conj", [.nil, x] => pure (.persistentList none [x])
  | "conj", [.persistentList md xs, x] => pure (.persistentList md (x :: xs))
  | "deref", [.var ns nm] =>
    let s ← get
    pure ((s.tb.deref s.w.slots ⟨ns, nm⟩).getD (.opaque .varUnboundRoot 0))
  | "deref", [.opaque .atom k] => pure (((← heapM).atoms[k]?).getD .nil)
  | "var-get", [.var ns nm] =>
    let s ← get
    pure ((s.tb.deref s.w.slots ⟨ns, nm⟩).getD (.opaque .varUnboundRoot 0))
  | "swap!", (.opaque .atom k) :: f :: more =>
    let old := ((← heapM).atoms[k]?).getD .nil
    let nv ← invoke f (old :: more)
    let h ← heapM
    setHeap { h with atoms := h.atoms.set! k nv }
    pure nv
  | "map", [f, coll] =>
    let xs := coll.elems.getD []
    let (h, o) := (← heapM).newLazy { f, xs }
    setHeap h
    pure o
  | "symbol", [.persistentString s] => pure (sym s)
  | "symbol", [x@(.symbol ..)] => pure x
  | "keyword", [.persistentString s] => pure (kw s)
  | "identity", [x] => pure x
  | "hash-map", xs =>
    let rec pairs : List Obj → List (Obj × Obj)
      | k :: v :: rest => (k, v) :: pairs rest
      | _ => []
    pure (.persistentHashMap none (pairs xs))
  | "list*", xs => pure (.persistentList none xs)
  | "seq", [x] => pure (match x.elems with | some [] => .nil | some ys => .persistentList none ys | none => .nil)
  | "vec", [x] => pure (.persistentVector none (x.elems.getD []))
  | "doall", [x] => realize x
  | "clojure.string/join", [coll] =>
    let parts ← (coll.elems.getD []).mapM strOf
    pure (str (String.join parts))
  | "clojure.string/join", [sep, coll] =>
    let parts ← (coll.elems.getD []).mapM strOf
    pure (str ((← strOf sep).intercalate parts))
  | "clojure.string/blank?", [x] =>
    match x with
    | .nil => pure (.boolean true)
    | .persistentString s => pure (.boolean (s.toUTF8.toList.all Jank.NreplServer.cIsspace))
    | _ => throw (.stdex "blank?: not a string")
  | "iteration", _ => pure .nil
  | "push-thread-bindings", [m] =>
    -- context.cpp push_thread_bindings 706–747: every var must be dynamic (else an error result,
    -- `expect_ok` throws), then a frame copied from the current one with new boxes.
    let kvs := match m with
      | .persistentHashMap _ kvs | .persistentArrayMap _ kvs => kvs
      | _ => []
    let s ← get
    let mut bs : List (VarRef × Obj) := []
    for (k, v) in kvs do
      match k with
      | .var ns n =>
        if !(s.w.slots.get ⟨ns, n⟩).dynamic then
          throw (.stdex s!"Can't dynamically bind non-dynamic var: #'{ns}/{n}")
        bs := bs ++ [(⟨ns, n⟩, v)]
      | _ => throw (.stdex "push-thread-bindings: invalid object type (expected var)")
    set { s with tb := s.tb.push bs }
    pure .nil
  | "pop-thread-bindings", [] =>
    -- context.cpp pop_thread_bindings 750–760: nothing to pop is a no-op.
    modify fun s => { s with tb := s.tb.pop }
    pure .nil
  | "int", [x] =>
    match x with
    | .smallInteger _ | .integer _ => pure x
    | _ => throw (.unsupported "int of a non-integer")
  | "long", [x] =>
    match x with
    | .smallInteger _ | .integer _ => pure x
    | _ => throw (.unsupported "long of a non-integer")
  | "unchecked-inc", [x] =>
    match x with
    | .smallInteger v => pure (.smallInteger (v + 1))
    | .integer v => pure (.integer (v + 1))
    | _ => throw (.unsupported "unchecked-inc")
  | name, xs =>
    match builtin name xs with
    | some (.ok r) => pure r
    | some (.error m) => throw (.stdex m)
    | none => throw (.stdex s!"Wrong number of args ({xs.length}) passed to {name}")

/-- `intern_ns` (context.cpp:401): a new namespace has no mappings. -/
partial def internNs (nm : String) : EM Unit := do
  let s ← get
  if (s.w.nss.find? (·.name == nm)).isNone then
    set { s with w := { s.w with nss := s.w.nss ++ [({ name := nm } : NsCell)] } }

/-- Calls a function object with argument objects. -/
partial def invoke (f : Obj) (args : List Obj) : EM Obj := do
  etick
  match f with
  | .opaque .nativeFunctionWrapper k => callBuiltin (jBuiltins.getD k "") args
  | .opaque .jitClosure k =>
    let s ← get
    let some c := s.w.closures[k]? | throw (.unsupported "closure")
    let a := s.w.arena
    let arities := match (a.expr c.fnExpr).data with
      | .function _ _ ars _ _ => ars
      | _ => []
    let n := args.length
    let fixed := arities.find? fun ar => !(a.fnCtx ar.fnCtx).isVariadic && ar.params.length == n
    let variadic := arities.find? fun ar => (a.fnCtx ar.fnCtx).isVariadic && ar.params.length - 1 ≤ n
    let some ar := fixed <|> variadic | throw (.stdex s!"Wrong number of args ({n}) passed to a function")
    let isVar := (a.fnCtx ar.fnCtx).isVariadic
    let pbs := paramBindings a (ar.frame.getD 0)
    let bind (xs : List Obj) : List (BindingId × Val) :=
      if isVar then
        let req := ar.params.length - 1
        let restV : Obj := if xs.length > req then .persistentList none (xs.drop req) else .nil
        (pbs.zip ((xs.take req).map Val.obj ++ [Val.obj restV])) ++ c.env
      else (pbs.zip (xs.map Val.obj)) ++ c.env
    let mut cur := args
    for _ in [0:10000] do
      match ← evalE ar.body (bind cur) c.selfs with
      | .val v => return v.toObj
      | .recur vs =>
        cur := vs.map (·.toObj)
        if isVar then
          let req := ar.params.length - 1
          cur := (cur.take req) ++ ((cur.drop req).headD .nil |>.elems |>.getD [])
    throw .fuel
  | .keyword .. =>
    match args with
    | [m] => pure (builtinGet m f)
    | [m, d] => pure (builtinGet m f d)
    | _ => throw (.stdex "keyword called with the wrong number of args")
  | .var ns n =>
    let s ← get
    invoke ((s.tb.deref s.w.slots ⟨ns, n⟩).getD .nil) args
  | _ => throw (.stdex s!"{prObj .jank (← heapM) f} is not callable")

end

/-! ## The analyzer, on this process -/

/-- A user macro's function, as the analyzer calls it (`apply_to(var->deref(), args)`,
context.cpp:635): the closure run on the state at the analysis (its output is dropped: the
grammar's macros print nothing). -/
def closureMacroFn (s : ES) (f : Obj) : MacroFn := fun args =>
  match (invoke f args).run { s with out := #[], fuel := 2000 } with
  | .ok o _ => .ok o
  | .error e s' => .error (e.show s'.w.heap)

/-- The analyzer's `Runtime` for this process and thread: namespaces, var cells (macro, private,
dynamic flags from each var's metadata; macro functions; core `:inline`s), the current namespace
(the thread's `*ns*`). -/
def analyzerRt (s : ES) : Runtime :=
  let cells : List VarCell := s.w.slots.map fun (r, sl) =>
    let isM := isMacroMeta sl.md
    let core := r.ns == "clojure.core"
    let macroFn : Option MacroFn :=
      if !isM then none
      else if core then (coreMacros.lookup r.name)
      else match sl.root with
        | some f => some (closureMacroFn s f)
        | none => none
    let inl := if core then coreInline.find? (·.1 == r.name) else none
    { ns := r.ns, name := r.name, isMacro := isM, private_ := (metaGet sl.md "private").truthy
      dynamic := sl.dynamic, macroFn, inline := inl.map (·.2.1), inlineArities := inl.map (·.2.2)
      bound := sl.root.isSome }
  { namespaces := s.w.nss, vars := cells, currentNs := curNsName s }

/-- After an analysis: its namespaces (interned vars) and arena become the process's; each new var
gets an unbound cell. -/
def afterAnalysis (s : ES) (st : AnState) : ES :=
  let slots := st.rt.vars.foldl (fun acc c =>
    if (acc.lookup c.ref).isSome then acc else acc.set c.ref {}) s.w.slots
  { s with w := { s.w with nss := st.rt.namespaces, slots, arena := st.arena } }

/-- `analyze::processor an_prc; pass::optimize(an_prc.analyze(form, statement).expect_ok())`
(context_dynamic.cpp:67–70): a fresh processor whose arena is the process's. -/
def analyzeForm (s : ES) (form : Obj) : ES × Except Fail ExprId :=
  let st0 := initialState (analyzerRt s)
  let st0 := { st0 with arena := s.w.arena }
  let (a, root) := st0.arena.addFrame { type := .root }
  let st0 := { st0 with arena := a, rootFrame := root }
  let (r, st1) := runAnalysis (do let e ← analyzeTop form .statement; optimize e) st0
  let s' := afterAnalysis s st1
  match r with
  | .ok (.ok e) => (s', .ok e)
  | .ok (.error e) => (s', .error (.error e.kind e.message))
  | .error (.thrown e) => (s', .error (.error e.kind e.message))
  | .error (.ub w) => (s', .error (.ub w))
  | .error .fuel => (s', .error .fuel)

/-- `evaluate::eval(expr)` of a top-level form: a native result is boxed (evaluate.cpp:206). -/
def evalTopForm (s : ES) (e : ExprId) : ES × Except Fail Obj :=
  match (evalVal e [] []).run s with
  | .ok v s' => (s', .ok v.toObj)
  | .error f s' => (s', .error f)

/-! ## `eval_string` and `safe_eval` -/

/-- How one form's reading ended (parse.cpp `next`). -/
inductive ReadOut where
  | form (o : Obj)
  | eof
  | error (msg : String)
  /-- The reader never returns (REPORT-2 R1: a NUL byte). -/
  | hang (what : String)
  /-- The parser's recursion overflows the stack: the process dies. -/
  | crash (what : String)
  deriving Inhabited

/-- One call of `processor::next` on the parser state `p`, under the thread's `*ns*` and `*file*`
(the `source_to_meta` of what it builds). -/
def readNext (p : Jank.Read.S) (curNs file : String) : ReadOut × Jank.Read.S :=
  let (r, p') := (Jank.Read.nextForm (p.lex.file.size + 8)).run p
  match r with
  | .ok none => (.eof, p')
  | .ok (some v) =>
    match jankForm curNs file v with
    | some o => (.form o, p')
    | none => (.error "model: a value outside the grammar", p')
  | .err m => (.error m, p')
  | .hang w => (.hang w, p')
  | .crash w => (.crash w, p')

/-- What `safe_eval` returns and leaves. -/
inductive EvalEnd where
  /-- `eval_string` returned a value (or none, unwrapped to a zeroed object: `.real0`). -/
  | ok (v : Obj)
  /-- An exception: `*e` is set to this object. -/
  | failed (e : Obj)
  /-- The connection thread never returns. -/
  | hang (what : String)
  /-- The process dies. -/
  | crash (what : String)
  /-- Outside the model. -/
  | unsupported (what : String)
  deriving Inhabited

/-- `safe_eval`'s handlers (evaluate.cpp:750–775): the object `*e` is set to. -/
def failObj (s : ES) (f : Fail) : ES × Obj :=
  match f with
  | .thrown o =>
    match o with
    | .opaque .exceptionInfo _ => (s, o)
    | _ =>
      let (h, e) := s.w.heap.newEx { msg := prObj .jank s.w.heap o, origin := "thrown object" }
      ({ s with w := { s.w with heap := h } }, e)
  | .error k m =>
    let (h, e) := s.w.heap.newEx { msg := "", data := .nil, origin := s!"error_ref {k}: {m}" }
    ({ s with w := { s.w with heap := h } }, e)
  | .stdex m =>
    let (h, e) := s.w.heap.newEx { msg := m, origin := "std::exception" }
    ({ s with w := { s.w with heap := h } }, e)
  | other =>
    let (h, e) := s.w.heap.newEx { msg := other.show s.w.heap, origin := "model" }
    ({ s with w := { s.w with heap := h } }, e)

/-- What follows a form's output: the next read (the form's value), or the end (its failure). -/
inductive EvAfter where
  | next (v : Obj)
  | fail (f : Fail)
  deriving Inhabited

/-- The phases of one `eval_string`, each a step of the connection thread. -/
inductive EvPhase where
  /-- `++it` / `begin()`: read the next form. -/
  | read
  /-- Analyze a form just read. -/
  | analyze (o : Obj)
  /-- Evaluate an analyzed form. -/
  | eval (e : ExprId)
  /-- Its output events, one `fwrite`/`putc` per step, then what follows. -/
  | emit (evs : List OutEv) (after : EvAfter)
  /-- `eval_string` returned (or threw): `safe_eval`'s bookkeeping is next. -/
  | done (r : Except Fail (Option Obj))
  deriving Inhabited

structure EvRun where
  parser : Jank.Read.S
  phase : EvPhase := .read
  noOp : Bool := true
  ret : Obj := .nil
  /-- Forms read, for stories. -/
  forms : List Obj := []
  deriving Inhabited

/-- Starts `eval_string(code, p)`: the lexer and parser over the code's bytes, the first token
lexed (`lex::processor::begin`, parse.cpp's `token_current`). -/
def EvRun.start (code : List UInt8) : EvRun :=
  { parser := Jank.Read.S.start code.toArray .utf8 }

/-- One step of `eval_string`. Output events are returned for the caller to apply (one per
step); a `.done` run does not move. -/
def EvRun.step (r : EvRun) (s : ES) (file : String) : EvRun × ES × Option OutEv :=
  match r.phase with
  | .read =>
    let (o, p') := readNext r.parser (curNsName s) file
    let r := { r with parser := p' }
    match o with
    | .form f => ({ r with phase := .analyze f, forms := r.forms ++ [f] }, s, none)
    | .eof => ({ r with phase := .done (.ok (if r.noOp then none else some r.ret)) }, s, none)
    | .error m =>
      if m.startsWith "model:" then ({ r with phase := .done (.error (.unsupported m)) }, s, none)
      else ({ r with phase := .done (.error (.error "parse" m)) }, s, none)
    | .hang w => ({ r with phase := .done (.error (.unsupported s!"HANG {w}")) }, s, none)
    | .crash w => ({ r with phase := .done (.error (.unsupported s!"CRASH {w}")) }, s, none)
  | .analyze f =>
    let (s', e) := analyzeForm s f
    match e with
    | .ok e => ({ r with phase := .eval e, noOp := false }, s', none)
    | .error x => ({ r with phase := .done (.error x), noOp := false }, s', none)
  | .eval e =>
    let (s', v) := evalTopForm { s with out := #[] } e
    let evs := s'.out.toList
    let s' := { s' with out := #[] }
    match v with
    | .ok v => ({ r with phase := .emit evs (.next v) }, s', none)
    | .error f => ({ r with phase := .emit evs (.fail f) }, s', none)
  | .emit [] (.next v) => ({ r with phase := .read, ret := v }, s, none)
  | .emit [] (.fail f) => ({ r with phase := .done (.error f) }, s, none)
  | .emit (ev :: rest) after => ({ r with phase := .emit rest after }, s, some ev)
  | .done _ => (r, s, none)

def EvRun.isDone (r : EvRun) : Bool :=
  match r.phase with
  | .done _ => true
  | _ => false

end Jank.R4.Nrepl
