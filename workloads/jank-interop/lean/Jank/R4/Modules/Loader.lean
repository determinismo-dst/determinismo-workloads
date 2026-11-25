import Determinismo
import Jank.R4.Modules.Munge
import Jank.R3.Search.Common

/-!
# Round 4, modules: the module loader's index and lookup

jank 7135b7708, `runtime/module/loader_dynamic.cpp`:

- `register_entry` (181–241): the extension of the file (`.jank`, `.cljc`, `.cpp`, `.o`; anything
  else is ignored) picks a slot of the entry keyed by `path_to_module(module_path)`; an existing
  key gets that slot **overwritten** (`res.first->second.jank = entry`).
- `register_relative_entry` / `register_directory` (243–268): every regular file under a
  directory, keyed by its path relative to the directory (`recursive_directory_iterator` order).
- `register_jar` (270–295): every non-directory entry of a JAR, keyed by its entry name.
- `register_path` (297–325): an empty or missing path is skipped; a directory is walked; a path
  ending in `.jar` is a JAR; anything else is registered as one file keyed by its whole canonical
  path (so a `.zip` registers nothing: `.zip` is not a module extension).
- `register_module_path` (327–364): the module path split on `:` (`loader.hpp` 180), each part
  registered in order; `skip_jar` skips parts ending in `.jar`.
- `loader::loader` (393–415): the user's `--module-path`, then the build directory, jank's
  `src/jank`, and three development paths, in that order.
- `find_module` (513–537): look the module up; on a miss, register the module path again
  (without JARs) and look again.
- `loader::find` (544–641): every `_` of the module becomes `-` (547–549); the source is the
  `.jank` slot, else the `.cljc` slot ("no source files" error otherwise); `origin::source`
  returns it; otherwise an `.o` outside any archive is taken when its mtime is at least the
  source's (only when the output target is `object` while compiling).
- `loader::load` (721–777): a managed load fn (registered by AOT code) runs first; otherwise
  `find`, then `load_jank`/`load_cljc` (eval the file) or `load_o`; then `set_is_loaded`.

Clojure 1.12 (the spec): `load` → `RT.load` (RT.java 437–470) asks the class loader for
`<root-resource>.class`, `.clj`, `.cljc`; the class path is searched in order and the **first**
element holding the resource wins (`ClassLoader.getResource`). jank's book
(`differences-from-clojure.md`, "Compilation model") calls the module path jank's class path and
says a module is backed by a `.jank` or `.cljc` file; `--help` (cli.cpp 122–124) documents "A colon
separated list of directories, JAR files, and ZIP files to search for modules." The spec here
reads `.jank` where Clojure reads `.clj`.
-/

namespace Jank.R4.Modules

open Determinismo

/-- One element of a module path. Files are given with a modification time. -/
inductive Elem where
  | dir (path : String) (files : List (String × Nat))
  | jar (path : String) (entries : List String)
  | zip (path : String) (entries : List String)
  | file (path : String) (mtime : Nat)
  | missing (path : String)
  deriving Repr, BEq, Inhabited

def Elem.path : Elem → String
  | .dir p _ | .jar p _ | .zip p _ | .file p _ | .missing p => p

/-- `file_entry` (loader.hpp): the archive it lives in, if any, and its path. -/
structure FileEntry where
  archive : Option String
  path : String
  mtime : Nat
  deriving Repr, BEq, Inhabited

/-- `loader::entry`: one slot per module type. -/
structure Entry where
  jank : Option FileEntry := none
  cljc : Option FileEntry := none
  cpp : Option FileEntry := none
  o : Option FileEntry := none
  deriving Repr, BEq, Inhabited

/-- `native_unordered_map<immutable_string, entry>` as an association list. -/
abbrev Entries := List (String × Entry)

def Entries.get? (es : Entries) (k : String) : Option Entry := (es.find? (·.1 == k)).map (·.2)

def Entries.upsert (es : Entries) (k : String) (f : Entry → Entry) : Entries :=
  match es.find? (·.1 == k) with
  | some _ => es.map fun (k', e) => if k' == k then (k', f e) else (k', e)
  | none => es ++ [(k, f {})]

/-- loader_dynamic.cpp 181–241 `register_entry`. -/
def registerEntry (es : Entries) (modulePath : String) (e : FileEntry) : Entries :=
  match extension e.path with
  | ".jank" => es.upsert (pathToModule modulePath) fun x => { x with jank := some e }
  | ".cljc" => es.upsert (pathToModule modulePath) fun x => { x with cljc := some e }
  | ".cpp" => es.upsert (pathToModule modulePath) fun x => { x with cpp := some e }
  | ".o" => es.upsert (pathToModule modulePath) fun x => { x with o := some e }
  | _ => es

/-- loader_dynamic.cpp 297–325 `register_path` for one element (`skipJar`: 349, 359). -/
def registerElem (es : Entries) (skipJar : Bool) : Elem → Entries
  | .missing _ => es
  | .dir root files =>
    files.foldl (fun acc (rel, t) => registerEntry acc rel { archive := none, path := root ++ "/" ++ rel, mtime := t }) es
  | .jar p entries =>
    if skipJar then es
    else entries.foldl (fun acc n => registerEntry acc n { archive := some p, path := n, mtime := 0 }) es
  -- Not a directory and not `.jar`: registered as one file keyed by its whole path (318–324).
  | .zip p _ => registerEntry es p { archive := none, path := p, mtime := 0 }
  | .file p t => registerEntry es p { archive := none, path := p, mtime := t }

def registerModulePath (es : Entries) (path : List Elem) (skipJar : Bool) : Entries :=
  path.foldl (fun acc e => registerElem acc skipJar e) es

/-- loader_dynamic.cpp 513–537 `find_module`. -/
def findModule (es : Entries) (path : List Elem) (m : String) : Option Entry × Entries :=
  match es.get? m with
  | some e => (some e, es)
  | none =>
    let es' := registerModulePath es path true
    (es'.get? m, es')

inductive ModType where | o | cpp | jank | cljc
  deriving Repr, BEq, Inhabited

inductive FindErr where
  | notFound (m : String)
  | binaryWithoutSource (m : String)
  deriving Repr, BEq, Inhabited

/-- What `find` picked: the module type and the file. -/
structure Found where
  type : ModType
  file : FileEntry
  deriving Repr, BEq, Inhabited

/-- loader_dynamic.cpp 544–641 `loader::find`. `latest` is `origin::latest`; `compiling` is
`*compile-files*`; `objectTarget` is `--output-target object`. -/
def find (es : Entries) (path : List Elem) (m : String) (latest compiling objectTarget : Bool) :
    Except FindErr Found × Entries :=
  let (found, es') := findModule es path (patchModule m)
  match found with
  | none => (.error (.notFound m), es')
  | some e =>
    let src : Option (ModType × FileEntry) :=
      match e.jank, e.cljc with
      | some f, _ => some (.jank, f)
      | none, some f => some (.cljc, f)
      | none, none => none
    match src with
    | none => (.error (.binaryWithoutSource m), es')
    | some (st, sf) =>
      if !latest then (.ok ⟨st, sf⟩, es')
      else
        let hasO := match e.o with | some f => f.archive.isNone | none => false
        let compiled := if compiling then (if objectTarget && hasO then e.o else none)
                        else if hasO then e.o else none
        match compiled with
        | some cf => if cf.mtime ≥ sf.mtime then (.ok ⟨.o, cf⟩, es') else (.ok ⟨st, sf⟩, es')
        | none => (.ok ⟨st, sf⟩, es')

/-- The loader as built at start-up (393–415) for a given module path. -/
def initial (path : List Elem) : Entries := registerModulePath [] path false

/-- jank: the source file a `require` of `m` loads (the `.o` is a cache of it). -/
def jankSource (path : List Elem) (m : String) : Option FileEntry :=
  match (find (initial path) path m false false false).1 with
  | .ok f => some f.file
  | .error _ => none

/-! ## Clojure's side -/

/-- The class path elements that can hold resources: directories, JARs and ZIPs (a plain file
is not a class path element). -/
def elemHas (e : Elem) (res : String) : Option FileEntry :=
  match e with
  | .dir root files => (files.find? (·.1 == res)).map fun (_, t) => { archive := none, path := root ++ "/" ++ res, mtime := t }
  | .jar p entries | .zip p entries => if entries.contains res then some { archive := some p, path := res, mtime := 0 } else none
  | .file _ _ | .missing _ => none

def firstHaving (path : List Elem) (res : String) : Option FileEntry :=
  path.findSome? (elemHas · res)

/-- Clojure: `RT.load` of `root-resource`: the first element holding `<r>.jank` (Clojure's
`.clj`), else the first holding `<r>.cljc`. -/
def cljSource (path : List Elem) (lib : String) : Option FileEntry :=
  let r := (rootResource lib).drop 1 |>.toString
  match firstHaving path (r ++ ".jank") with
  | some f => some f
  | none => firstHaving path (r ++ ".cljc")

/-! ## The search world: module paths of up to three elements, and a lib to require -/

/-- Relative file names the world draws from. -/
def relNames : List String :=
  ["a.jank", "a.cljc", "b_c.jank", "b-c.jank", "x/y.jank", "a_PLUS_b.jank", "a.o", "x/y_z.cljc"]

def libNames : List String := ["a", "b-c", "b_c", "x.y", "a+b", "a_PLUS_b", "x.y-z"]

/-- Classify a disagreement. -/
def classify (path : List Elem) (lib : String) (j c : Option FileEntry) : String :=
  match j, c with
  | some jf, some cf =>
    if jf == cf then "agree"
    -- Both found a file for the module, and they differ: the index kept the later registration
    -- (a later element, or a later file of the same directory or JAR mapping to the same module).
    else "F8 the later module-path element (or same-module twin file) wins"
  | some jf, none =>
    if (jf.path.splitOn "-").length > 1 || (jf.path.splitOn "_").length > 1 then "lenient: jank finds a file Clojure's root-resource does not name"
    else s!"unexplained-jank-only {jf.path}"
  | none, some cf =>
    if cf.archive.isSome && path.any (fun e => match e with | .zip p _ => some p == cf.archive | _ => false) then "F9 a ZIP on the module path registers nothing"
    else if (lib.splitOn "_").length > 1 || (cf.path.splitOn "_PLUS_").length > 1 then "F-munge: a file name holding a munge escape is indexed under its demunged name"
    else s!"unexplained-clojure-only {cf.path} (lib {lib})"
  | none, none => "agree"

structure LW where
  decisions : Decisions

instance : Chaotic LW where
  decisions w := w.decisions
  setDecisions w d := { w with decisions := d }

def drawElem (i : Nat) : EStateM Stop LW Elem := do
  let kind ← decide s!"elem{i}.kind" 4
  let n ← decide s!"elem{i}.files" 3
  let mut fs : List String := []
  for k in [0:n] do
    let f ← decide s!"elem{i}.file{k}" relNames.length
    let nm := relNames[f]!
    if !fs.contains nm then fs := fs ++ [nm]
  match kind with
  | 0 => pure (.dir s!"/p{i}" (fs.map (·, 1)))
  | 1 => pure (.jar s!"/p{i}.jar" fs)
  | 2 => pure (.zip s!"/p{i}.zip" fs)
  | _ => pure (.file s!"/p{i}/a.jank" 1)

def loaderBody (maxElems : Nat) : EStateM Stop LW Unit := do
  let n ← decide "elems" (maxElems + 1)
  let mut path : List Elem := []
  for i in [0:n] do
    path := path ++ [← drawElem i]
  let l ← decide "lib" libNames.length
  let lib := libNames[l]!
  let j := jankSource path lib
  let c := cljSource path lib
  if j != c then
    let cls := classify path lib j c
    if cls != "agree" then
      violate cls s!"module path {repr path}; (require '{lib}): jank loads {repr (j.map (·.path))}, Clojure {repr (c.map (·.path))}"

def loaderRun (maxElems : Nat) (source : Source) : Ended :=
  match (loaderBody maxElems).run { decisions := { source } } with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }
  | .error (.nodeDown _) w => { taken := w.decisions.taken, violation := none }

end Jank.R4.Modules
