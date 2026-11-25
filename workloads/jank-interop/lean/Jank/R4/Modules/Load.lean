import Determinismo
import Jank.R4.Modules.Munge

/-!
# Round 4, modules: `require`, `use`, `load`, `refer`, `alias` and `ns`, both sides

jank 7135b7708, `src/jank/clojure/core.jank`:
- `alias` 4708, `refer` 4717–4755 (no check that `:only`/`:refer` is sequential; `(rename sym sym)`),
  `*loaded-libs*` 4769, `*pending-paths*` 4775, `check-cyclic-dependency` 4788, `load` 4801–4812
  (its argument goes to `context::load_module` as a **module name**: no root-directory, no `/`),
  `load-one` 4814, `load-all` 4825, `load-lib` 4836–4873 (`verbose` read, never used), `load-libs`
  4875–4889 (a non-libspec argument throws "not a libspec": no prefix lists), `require` 4900,
  `use` 4968, `refer-clojure` 4979, `ns` 5581–5645; `throw-if` 4704 throws `ex-info "Assertion
  failed."`.
- C++: `context::load_module` (context.cpp 325–350: binds `*ns*` and `*current-module*`, calls
  `loader::load`, turns exceptions into an error result, which `.expect_ok` rethrows);
  `loader::load` (loader_dynamic.cpp 721–777: evaluates the file, then `set_is_loaded`, which
  conjs the module onto the **current binding** of `*loaded-libs*`); `ns::refer` (ns.cpp
  174–192), `ns::add_alias` (135–155), `ns::intern_owned_var` (65–103, the `def` path).
- `run-main` (main.cpp 83–115): `load_module(target)` directly (not through `require`: no
  `*pending-paths*` entry, no `*loaded-libs*` check), then `-main` is applied with `*ns*` as the
  context left it (the constructor's binding of `clojure.core`, context.cpp 107–113).

Clojure 1.12 (`clojure-ref`): core.clj `refer` 4243–4276 (`:only`/`:refer` must be Sequential),
`alias` 4290, `load-one` 5956, `load-all` 5969, `load-lib` 5981–6026 (prefix, `:verbose` prints),
`load-libs` 6028–6049 (prefix lists), `check-cyclic-dependency` 6051, `require` 6066, `use` 6156,
`load` 6172–6187 (a path: absolute `/x/y`, or relative to `root-directory` of `*ns*`), `ns` 5817;
Namespace.java `reference`/`checkReplacement`/`intern`; clojure.main `main-opt` 511–517 and
`initialize` 503–509 (`-m` runs `-main` in `user`).
-/

namespace Jank.R4.Modules.Load

open Determinismo

/-- Which implementation runs. -/
inductive Side where | jank | clj
  deriving Repr, BEq, Inhabited

structure VarRef where
  ns : String
  name : String
  deriving Repr, BEq, Inhabited, Ord

structure NsSt where
  name : String
  maps : List (String × VarRef) := []
  aliases : List (String × String) := []
  deriving Repr, BEq, Inhabited

inductive Opt where
  | as (a : String)
  | asAlias (a : String)
  | refer (syms : List String)
  /-- `:refer #{...}`: a set (not Sequential). -/
  | referSet (syms : List String)
  | referAll
  deriving Repr, BEq, Inhabited

inductive Libspec where
  | sym (l : String)
  | vec (l : String) (opts : List Opt)
  /-- A prefix list `(p a [b :as x])`. -/
  | prefix (p : String) (items : List Libspec)
  deriving Repr, BEq, Inhabited

inductive Flag where | reload | reloadAll | verbose
  deriving Repr, BEq, Inhabited

inductive Clause where
  | require (specs : List Libspec)
  | use (specs : List Libspec)
  | referClojure (exclude : List String)
  deriving Repr, BEq, Inhabited

inductive Form where
  | ns (name : String) (clauses : List Clause)
  | require (specs : List Libspec) (flags : List Flag)
  | use (specs : List Libspec) (flags : List Flag)
  | refer (lib : String) (only : Option (List String)) (asSet : Bool)
  | alias (a lib : String)
  | defv (sym : String)
  | print (tag : String)
  | load (arg : String)
  | inNs (n : String)
  | removeNs (n : String)
  /-- `(println (str *ns*))` -/
  | printNs
  | boom
  /-- A reference to a var (`(f)`), resolved in `*ns*` (an alias or namespace qualifies it);
  prints the var it reached. -/
  | ref (sym : String)
  /-- `(create-ns 'n)` -/
  | createNs (n : String)
  /-- AOT only: `_jank_var("ns/sym")` (codegen/api.cpp 11–14 → context.cpp 491–515 →
  ns.cpp 26–47), run by a compiled module's load fn before its first form (cpp_processor.cpp
  2084–2160). -/
  | internLifted (ns sym : String)
  /-- A reference compiled in namespace `ns` (a fn body: resolved when its module was analyzed,
  whatever `*ns*` is when it runs). -/
  | refIn (ns sym : String)
  deriving Repr, BEq, Inhabited

/-- Library sources, by lib name (`a`, `b`, `x.y`, …). -/
abbrev Files := List (String × List Form)

structure St where
  nss : List NsSt
  cur : String := "user"
  libs : List String := ["clojure.core"]
  pending : List String := []
  out : List String := []
  /-- Each evaluation of a file, in order. -/
  evals : List String := []
  fuel : Nat := 40
  verbose : Bool := false
  deriving Repr, Inhabited

/-- What was thrown (the kind only: messages differ by design). -/
structure Err where
  kind : String
  deriving Repr, BEq, Inhabited

abbrev M := EStateM Err St

def throwK {α} (k : String) : M α := throw { kind := k }

def coreNs : NsSt :=
  { name := "clojure.core", maps := [("inc", ⟨"clojure.core", "inc"⟩), ("map", ⟨"clojure.core", "map"⟩)] }

def corePublics : List (String × VarRef) := coreNs.maps

def initialSt : St :=
  { nss := [coreNs, { name := "user", maps := corePublics }] }

def findNs (s : St) (n : String) : Option NsSt := s.nss.find? (·.name == n)

def setNs (n : NsSt) : M Unit :=
  modify fun s => { s with nss := if s.nss.any (·.name == n.name) then s.nss.map (fun x => if x.name == n.name then n else x) else s.nss ++ [n] }

def theNs (n : String) : M NsSt := do
  match findNs (← get) n with
  | some x => pure x
  | none => throwK "no-namespace"

def createNs (n : String) : M Unit := do
  if (findNs (← get) n).isNone then setNs { name := n }

def removeNs (n : String) : M Unit :=
  modify fun s => { s with nss := s.nss.filter (·.name != n) }

/-- `binding` of one piece of state: restored on the way out, also when throwing. -/
def withState {α β} (get' : St → α) (set' : St → α → St) (v : α) (body : M β) : M β := do
  let old := get' (← get)
  modify (set' · v)
  tryCatch (do let r ← body; modify (set' · old); pure r)
    (fun e => do modify (set' · old); throw e)

def emit (line : String) : M Unit := modify fun s => { s with out := s.out ++ [line] }

/-- Public vars interned in a namespace (`ns-publics`), sorted by name. -/
def publics (n : NsSt) : List (String × VarRef) :=
  ((n.maps.filter fun (k, v) => v.ns == n.name && v.name == k).toArray.qsort (fun a b => a.1 < b.1)).toList

/-- `ns::refer` (jank) and `Namespace.reference` (Clojure 1.12). -/
def nsRefer (side : Side) (cur : String) (sym : String) (v : VarRef) : M Unit := do
  let n ← theNs cur
  match n.maps.lookup sym with
  | some old =>
    match side with
    | .jank =>
      if v.ns != old.ns && old.ns != "clojure.core" then throwK "refer-conflict"
      setNs { n with maps := (sym, v) :: n.maps.filter (·.1 != sym) }
    | .clj =>
      if old == v then pure ()
      else if old.ns == cur && old.name == sym then pure ()   -- interned mapping: kept (REJECTED)
      else setNs { n with maps := (sym, v) :: n.maps.filter (·.1 != sym) }  -- WARNING, replaced
  | none => setNs { n with maps := (sym, v) :: n.maps }

/-- `refer`: core.jank 4717 / core.clj 4243. `only = none` refers every public var. -/
def refer (side : Side) (lib : String) (only : Option (List String)) (asSet : Bool) (exclude : List String := []) : M Unit := do
  let n ← match findNs (← get) lib with | some x => pure x | none => throwK "no-namespace"
  if side == .clj && asSet && only.isSome then throwK "refer-not-sequential"
  let pubs := publics n
  let todo := only.getD (pubs.map (·.1))
  for sym in todo do
    if !exclude.contains sym then
      match pubs.lookup sym with
      | none => throwK (if n.maps.any (·.1 == sym) then "refer-private" else "refer-missing")
      | some v => nsRefer side (← get).cur sym v

def alias (a lib : String) : M Unit := do
  let target ← theNs lib
  let n ← theNs (← get).cur
  match n.aliases.lookup a with
  | some t => if t != target.name then throwK "alias-conflict"
  | none => setNs { n with aliases := n.aliases ++ [(a, target.name)] }

/-- `def`: `intern_owned_var` / `Namespace.intern`. -/
def defv (sym : String) : M Unit := do
  let s ← get
  let n ← theNs s.cur
  match n.maps.lookup sym with
  | some v => if v.ns == n.name then pure () else setNs { n with maps := (sym, ⟨n.name, sym⟩) :: n.maps.filter (·.1 != sym) }
  | none => setNs { n with maps := (sym, ⟨n.name, sym⟩) :: n.maps }

def inNs (n : String) : M Unit := do createNs n; modify fun s => { s with cur := n }

/-- Analysis-time resolution of a symbol (`resolve`): `q/name` through an alias or a namespace
name; `name` through the current namespace's mappings. -/
def resolveSym (sym : String) : M VarRef := do
  let s ← get
  let n ← theNs s.cur
  match sym.splitOn "/" with
  | [q, name] =>
    let target := (n.aliases.lookup q).getD q
    match findNs s target with
    | none => throwK "unresolved"
    | some tn =>
      match tn.maps.lookup name with
      | some v => if v.ns == tn.name then pure v else throwK "unresolved"
      | none => throwK "unresolved"
  | _ =>
    match n.maps.lookup sym with
    | some v => pure v
    | none => throwK "unresolved"

/-- `context::intern_var` of a qualified name: the namespace is created if missing; an existing
mapping (even a referred var) is returned; otherwise a new var of that namespace is mapped. -/
def internVar (ns sym : String) : M Unit := do
  createNs ns
  let n ← theNs ns
  match n.maps.lookup sym with
  | some _ => pure ()
  | none => setNs { n with maps := (sym, ⟨ns, sym⟩) :: n.maps }

def checkCyclic (path : String) : M Unit := do
  let p := (← get).pending
  if p.drop 1 |>.contains path then throwK "cyclic-load"

mutual

/-- Evaluate one file's forms (jank `eval_string` form by form; Clojure `Compiler.load`). -/
partial def evalFile (side : Side) (files : Files) (lib : String) (forms : List Form) : M Unit := do
  let s ← get
  if s.fuel == 0 then throwK "fuel"
  modify fun s => { s with fuel := s.fuel - 1, evals := s.evals ++ [lib] }
  withState (·.cur) (fun s v => { s with cur := v }) s.cur do
    for f in forms do evalForm side files f

/-- jank `load` (4801) and Clojure `load` (6172): one path. -/
partial def loadPath (side : Side) (files : Files) (arg : String) : M Unit := do
  let s ← get
  let path := match side with
    | .jank => arg
    | .clj => if arg.startsWith "/" then arg else rootDirectory s.cur ++ "/" ++ arg
  if side == .clj && s.verbose then emit s!"(clojure.core/load \"{path}\")"
  checkCyclic path
  if (← get).pending.head? == some path then pure ()
  else
    withState (·.pending) (fun s v => { s with pending := v }) (path :: (← get).pending) do
      match side with
      | .jank =>
        -- context::load_module(path, latest) → loader::load: the argument is a module name.
        match files.lookup (patchModule path) with
        | none => throwK "module-not-found"
        | some forms =>
          evalFile side files path forms
          modify fun s => { s with libs := if s.libs.contains path then s.libs else s.libs ++ [path] }
      | .clj =>
        -- RT.load(path without its leading /): the resource named by root-resource.
        match files.find? (fun (l, _) => rootResource l == path) with
        | none => throwK "file-not-found"
        | some (l, forms) => evalFile side files l forms

partial def loadOne (side : Side) (files : Files) (lib : String) (needNs req : Bool) : M Unit := do
  loadPath side files (match side with | .jank => lib | .clj => rootResource lib)
  if needNs && (findNs (← get) lib).isNone then throwK "ns-not-found-after-load"
  if req then modify fun s => { s with libs := if s.libs.contains lib then s.libs else s.libs ++ [lib] }

partial def loadAll (side : Side) (files : Files) (lib : String) (needNs req : Bool) : M Unit := do
  let outer := (← get).libs
  let inner ← withState (·.libs) (fun s v => { s with libs := v }) [] do
    loadOne side files lib needNs req
    pure (← get).libs
  modify fun s => { s with libs := outer ++ inner.filter (!outer.contains ·) }

/-- `load-lib` with options (the libspec's options plus the flags). -/
partial def loadLib (side : Side) (files : Files) (lib : String) (opts : List Opt) (flags : List Flag) (use : Bool) : M Unit := do
  let s ← get
  let as := opts.findSome? (fun o => match o with | .as a => some a | _ => none)
  let asAlias := opts.findSome? (fun o => match o with | .asAlias a => some a | _ => none)
  let reload := flags.contains .reload
  let reloadAll := flags.contains .reloadAll
  let verbose := flags.contains .verbose
  let loaded := s.libs.contains lib
  let needNs := as.isSome || use
  let undefinedOnEntry := (findNs s lib).isNone
  let doLoad : Option (M Unit) :=
    if reloadAll then some (loadAll side files lib needNs true)
    else if reload then some (loadOne side files lib needNs true)
    else if !loaded then
      if needNs then some (loadOne side files lib needNs true)
      else if asAlias.isSome then some (createNs lib)
      else some (loadOne side files lib needNs true)
    else none
  let body : M Unit := do
    match doLoad with
    | some act =>
      tryCatch act (fun e => do
        if undefinedOnEntry then removeNs lib
        throw e)
    | none => if needNs && (findNs (← get) lib).isNone then throwK "ns-not-found"
    if side == .clj && needNs && (← get).verbose then emit s!"(clojure.core/in-ns '{(← get).cur})"
    if let some a := as then
      if side == .clj && (← get).verbose then emit s!"(clojure.core/alias '{a} '{lib})"
      alias a lib
    if let some a := asAlias then
      if side == .clj && (← get).verbose then emit s!"(clojure.core/alias '{a} '{lib})"
      alias a lib
    let referOpt := opts.findSome? (fun o => match o with
      | .refer xs => some (some xs, false) | .referSet xs => some (some xs, true) | .referAll => some (none, false) | _ => none)
    if use || referOpt.isSome then
      if side == .clj && (← get).verbose then emit s!"(clojure.core/refer '{lib})"
      match referOpt with
      | some (only, isSet) => refer side lib only isSet
      | none => refer side lib none false
  match side with
  | .clj => withState (·.verbose) (fun s v => { s with verbose := v }) (s.verbose || verbose) body
  | .jank => body

/-- `load-libs` (jank 4875 / Clojure 6028). -/
partial def loadLibs (side : Side) (files : Files) (specs : List Libspec) (flags : List Flag) (use : Bool) : M Unit := do
  if specs.isEmpty then throwK "nothing-to-load"
  for spec in specs do
    match spec, side with
    | .sym l, _ => loadLib side files l [] flags use
    | .vec l opts, _ => loadLib side files l opts flags use
    | .prefix _ _, .jank => throwK "not-a-libspec"
    | .prefix p items, .clj =>
      for it in items do
        match it with
        | .sym l => if (l.splitOn ".").length > 1 then throwK "prefix-period" else loadLib side files (p ++ "." ++ l) [] flags use
        | .vec l opts => if (l.splitOn ".").length > 1 then throwK "prefix-period" else loadLib side files (p ++ "." ++ l) opts flags use
        | .prefix _ _ => throwK "not-a-libspec"

partial def evalForm (side : Side) (files : Files) : Form → M Unit
  | .ns name clauses => do
    inNs name
    if name != "clojure.core" && !(clauses.any fun c => match c with | .referClojure _ => true | _ => false) then
      refer side "clojure.core" none false
    for c in clauses do
      match c with
      | .require specs => loadLibs side files specs [] false
      | .use specs => loadLibs side files specs [] true
      | .referClojure ex => refer side "clojure.core" none false ex
    if name != "clojure.core" then
      modify fun s => { s with libs := if s.libs.contains name then s.libs else s.libs ++ [name] }
  | .require specs flags => loadLibs side files specs flags false
  | .use specs flags => loadLibs side files specs flags true
  | .refer lib only asSet => refer side lib only asSet
  | .alias a lib => alias a lib
  | .defv sym => defv sym
  | .print tag => emit tag
  | .load arg => loadPath side files arg
  | .inNs n => inNs n
  | .removeNs n => removeNs n
  | .printNs => do emit s!"*ns* {(← get).cur}"
  | .boom => throwK "boom"
  | .ref sym => do let v ← resolveSym sym; emit s!"ref {v.ns}/{v.name}"
  | .createNs n => createNs n
  | .internLifted ns sym => internVar ns sym
  | .refIn ns sym => do
    let v ← withState (·.cur) (fun s v => { s with cur := v }) ns (resolveSym sym)
    emit s!"ref {v.ns}/{v.name}"

end

/-- What a program of top-level forms (at the REPL, in `user`) leaves behind. -/
structure Outcome where
  /-- Per form: none = ok, some kind = threw. -/
  results : List (Option String)
  out : List String
  evals : List String
  nss : List String
  aliases : List (String × List (String × String))
  maps : List (String × List (String × VarRef))
  libs : List String
  cur : String
  deriving Repr, BEq, Inhabited

/-- Outcomes compared up to what was thrown: whether a form threw, not the exception's kind or
message (they differ by design: ex-info "Assertion failed." against Clojure's exceptions). -/
def Outcome.norm (o : Outcome) : Outcome :=
  { o with results := o.results.map (·.map fun _ => "threw") }

def sortS (l : List String) : List String := (l.toArray.qsort (· < ·)).toList

def observe (s : St) (results : List (Option String)) : Outcome :=
  let interesting (n : NsSt) := (n.maps.toArray.qsort (fun a b => a.1 < b.1)).toList
  { results, out := s.out, evals := s.evals,
    nss := sortS (s.nss.map (·.name)),
    aliases := (s.nss.map fun n => (n.name, (n.aliases.toArray.qsort (fun a b => a.1 < b.1)).toList)).toArray.qsort (fun a b => a.1 < b.1) |>.toList,
    maps := (s.nss.filter (·.name != "clojure.core") |>.map fun n => (n.name, interesting n)).toArray.qsort (fun a b => a.1 < b.1) |>.toList,
    libs := sortS s.libs, cur := s.cur }

/-- Run top-level forms one by one (each REPL form catches its own exception). -/
def runTop (side : Side) (files : Files) (prog : List Form) : Outcome := Id.run do
  let mut s := initialSt
  let mut results : List (Option String) := []
  for f in prog do
    match (evalForm side files f).run s with
    | .ok _ s' => s := s'; results := results ++ [none]
    | .error e s' => s := s'; results := results ++ [some e.kind]
  return observe s results

/-- `jank run-main l` (main.cpp 83–115) against `clojure -M -m l` (clojure.main 511–517):
jank loads the module directly and calls `-main` with `*ns*` = clojure.core; Clojure requires it
from `user` and calls `-main` there. `-main`'s body is `main`. -/
def runMain (side : Side) (files : Files) (l : String) (main0 : List Form) : Outcome := Id.run do
  let main := main0.map fun f => match f with | .ref sym => Form.refIn l sym | f => f
  let s0 := initialSt
  let act : M Unit := match side with
    | .jank => do
      modify fun s => { s with cur := "clojure.core" }
      withState (·.cur) (fun s v => { s with cur := v }) "clojure.core" do
        match files.lookup (patchModule l) with
        | none => throwK "module-not-found"
        | some forms =>
          evalFile side files l forms
          modify fun s => { s with libs := if s.libs.contains l then s.libs else s.libs ++ [l] }
      for f in main do evalForm side files f
    | .clj => do
      loadLibs side files [.sym l] [] false
      for f in main do evalForm side files f
  match act.run s0 with
  | .ok _ s => observe s [none]
  | .error e s => observe s [some e.kind]

end Jank.R4.Modules.Load
