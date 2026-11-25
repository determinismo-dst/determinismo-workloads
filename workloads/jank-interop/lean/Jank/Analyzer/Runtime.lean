import Jank.Analyzer.Expr

/-!
# The runtime the analyzer consults

Objects (`Obj`) operations the analyzer calls (`runtime::meta`, `get`, `assoc`, `dissoc`, `first`,
`rest`, `cons`, `with_meta_graceful`, `strip_source_from_meta`, `object_source`), and the parts of
`runtime::context` (`src/cpp/jank/runtime/context.cpp`) and `runtime::ns`
(`src/cpp/jank/runtime/ns.cpp`) the analyzer uses: namespaces as maps from names to vars,
`qualify_symbol`, `find_var`, `resolve_ns`, `intern_owned_var`, `unique_string`,
`unique_namespaced_string`, `macroexpand1`, `macroexpand`.

A macro's function is a Lean function from the argument list `apply_to` passes it.
-/

namespace Jank.Analyzer

/-! ## Objects -/

def kw (name : String) : Obj := .keyword "" name
def str (s : String) : Obj := .persistentString s

/-- `runtime::meta(o)`: the metadata of a metadatable object, else nil. -/
def Obj.getMeta : Obj → Option Obj
  | .symbol m .. | .persistentList m _ | .persistentVector m _ | .persistentArrayMap m _
  | .persistentHashMap m _ | .persistentSortedMap m _ | .persistentHashSet m _
  | .persistentSortedSet m _ | .cons m .. | .lazySequence m _ => m
  | _ => none

/-- `behavior::metadatable`. -/
def Obj.metadatable : Obj → Bool
  | .symbol .. | .persistentList .. | .persistentVector .. | .persistentArrayMap ..
  | .persistentHashMap .. | .persistentSortedMap .. | .persistentHashSet ..
  | .persistentSortedSet .. | .cons .. | .lazySequence .. => true
  | _ => false

/-- `with_meta` on a metadatable object (nil meta is no meta). -/
def Obj.setMeta (o : Obj) (m : Option Obj) : Obj :=
  let m := match m with | some .nil => none | x => x
  match o with
  | .symbol _ n s => .symbol m n s
  | .persistentList _ xs => .persistentList m xs
  | .persistentVector _ xs => .persistentVector m xs
  | .persistentArrayMap _ kvs => .persistentArrayMap m kvs
  | .persistentHashMap _ kvs => .persistentHashMap m kvs
  | .persistentSortedMap _ kvs => .persistentSortedMap m kvs
  | .persistentHashSet _ xs => .persistentHashSet m xs
  | .persistentSortedSet _ xs => .persistentSortedSet m xs
  | .cons _ f r => .cons m f r
  | .lazySequence _ xs => .lazySequence m xs
  | x => x

/-- `with_meta_graceful` (core/meta.cpp:64): objects that cannot hold meta are returned as is. -/
def withMetaGraceful (o : Obj) (m : Obj) : Obj :=
  if o.metadatable then o.setMeta (some m) else o

/-- Metadata-insensitive equality (`runtime::equal` on the forms the analyzer compares: symbols,
keywords, scalars). -/
partial def Obj.equiv : Obj → Obj → Bool
  | .symbol _ n1 s1, .symbol _ n2 s2 => n1 == n2 && s1 == s2
  | .persistentList _ a, .persistentList _ b => a.length == b.length && (a.zip b).all fun (x, y) => x.equiv y
  | .persistentVector _ a, .persistentVector _ b => a.length == b.length && (a.zip b).all fun (x, y) => x.equiv y
  | .smallInteger a, .smallInteger b => a == b
  | .integer a, .integer b => a == b
  | .smallInteger a, .integer b => a.signExtend 64 == b
  | .integer a, .smallInteger b => a == b.signExtend 64
  | a, b => a == b

/-- `runtime::get(m, k)` on a map (array or hash), nil otherwise. -/
def Obj.get (m : Obj) (k : Obj) : Obj :=
  match m with
  | .persistentArrayMap _ kvs | .persistentHashMap _ kvs | .persistentSortedMap _ kvs =>
    match kvs.find? (fun (k', _) => k'.equiv k) with
    | some (_, v) => v
    | none => .nil
  | _ => .nil

def Obj.getOpt (m : Option Obj) (k : Obj) : Obj := match m with | some m => m.get k | none => .nil

/-- `runtime::assoc` on a map (nil → a new map). -/
def Obj.assoc (m : Obj) (k v : Obj) : Obj :=
  match m with
  | .persistentArrayMap md kvs =>
    if kvs.any (·.1.equiv k) then .persistentArrayMap md (kvs.map fun (k', v') => if k'.equiv k then (k', v) else (k', v'))
    else .persistentArrayMap md (kvs ++ [(k, v)])
  | .persistentHashMap md kvs =>
    if kvs.any (·.1.equiv k) then .persistentHashMap md (kvs.map fun (k', v') => if k'.equiv k then (k', v) else (k', v'))
    else .persistentHashMap md (kvs ++ [(k, v)])
  | _ => .persistentArrayMap none [(k, v)]

/-- `runtime::dissoc`. -/
def Obj.dissoc (m : Obj) (k : Obj) : Obj :=
  match m with
  | .persistentArrayMap md kvs => .persistentArrayMap md (kvs.filter fun (k', _) => !k'.equiv k)
  | .persistentHashMap md kvs => .persistentHashMap md (kvs.filter fun (k', _) => !k'.equiv k)
  | x => x

/-- `runtime::is_empty` on a map. -/
def Obj.isEmptyMap : Obj → Bool
  | .persistentArrayMap _ [] | .persistentHashMap _ [] | .nil => true
  | _ => false

/-- `runtime::truthy`. -/
def Obj.truthy : Obj → Bool
  | .nil | .boolean false => false
  | _ => true

/-- The elements of a seqable object, in sequence order (`seq`). -/
def Obj.elems : Obj → Option (List Obj)
  | .nil => some []
  | .persistentList _ xs | .persistentVector _ xs | .persistentHashSet _ xs
  | .persistentSortedSet _ xs | .lazySequence _ xs | .seqOf _ xs => some xs
  | .persistentArrayMap _ kvs | .persistentHashMap _ kvs | .persistentSortedMap _ kvs =>
    some (kvs.map fun (k, v) => .persistentVector none [k, v])
  | .cons _ f r => (r.elems).map (f :: ·)
  | .persistentString s => some (s.toList.map fun c => .character (String.singleton c))
  | _ => none

/-- `object_behavior::sequence_like`: lists, conses, lazy sequences and other sequences. -/
def Obj.sequenceLike : Obj → Bool
  | .persistentList .. | .cons .. | .lazySequence .. | .seqOf .. => true
  | _ => false

/-- `object_behavior::seqable`. -/
def Obj.seqable (o : Obj) : Bool := o.elems.isSome

/-- `behavior::sequential` (`is_sequential`): lists, vectors and sequences. -/
def Obj.sequential : Obj → Bool
  | .persistentList .. | .persistentVector .. | .cons .. | .lazySequence .. | .seqOf .. => true
  | _ => false

/-- `behavior::map_like` / `set_like`. -/
def Obj.mapLike : Obj → Bool
  | .persistentArrayMap .. | .persistentHashMap .. | .persistentSortedMap .. => true
  | _ => false
def Obj.setLike : Obj → Bool
  | .persistentHashSet .. | .persistentSortedSet .. => true
  | _ => false

/-- `first`. -/
def Obj.first (o : Obj) : Obj := match o.elems with | some (x :: _) => x | _ => .nil
/-- `rest` (core/seq.cpp:351): the empty list when nothing is left. -/
def Obj.rest (o : Obj) : Obj :=
  match o.elems with
  | some (_ :: xs) => .persistentList none xs
  | _ => .persistentList none []
/-- `next`: nil when nothing is left. -/
def Obj.next (o : Obj) : Obj :=
  match o.elems with
  | some (_ :: x :: xs) => .persistentList none (x :: xs)
  | _ => .nil
/-- `runtime::cons(head, tail)` (core/seq.cpp:371): a one-element list when `tail` is nil, else a
`cons` cell. -/
def consObj (head tail : Obj) : Obj :=
  match tail with
  | .nil => .persistentList none [head]
  | _ => .cons none head tail
/-- `count`. -/
def Obj.count (o : Obj) : Nat := (o.elems.getD []).length

/-- The reader's source metadata (`:jank/source`), attached to every form read from a file. -/
def sourceMeta : Obj :=
  .persistentArrayMap none [(kw "jank/source",
    .persistentArrayMap none [(kw "file", str "user.jank"), (kw "start", .nil), (kw "end", .nil)])]

/-- `meta_source(meta) != read::source::unknown()` (core/meta.cpp:116): the meta has
`:jank/source` with a `:file`. -/
def hasSource (md : Option Obj) : Bool :=
  !((Obj.getOpt md (kw "jank/source")).get (kw "file") == .nil)

/-- `object_source(o) != unknown` (core/meta.cpp:161). -/
def Obj.hasSource (o : Obj) : Bool := Jank.Analyzer.hasSource o.getMeta

/-- `strip_source_from_meta` (core/meta.cpp:229): dissoc `:jank/source`; empty → nil. -/
def stripSourceFromMeta (md : Obj) : Obj :=
  let res := md.dissoc (kw "jank/source")
  if res.isEmptyMap then .nil else res

/-! ## Vars and namespaces -/

/-- The argument list `apply_to` passes to a macro's function. -/
abbrev MacroFn := List Obj → Except String Obj

/-- What the analyzer reads of a var: its metadata (`:macro`, `:private`, `:dynamic`, `:inline`,
`:inline-arities`) and, for a macro, its root function. -/
structure VarCell where
  ns : String
  name : String
  isMacro : Bool := false
  private_ : Bool := false
  dynamic : Bool := false
  /-- `(:inline meta)`: a function of the call's arguments. -/
  inline : Option MacroFn := none
  /-- `(:inline-arities meta)`: a set of arities. -/
  inlineArities : Option (List Nat) := none
  /-- `var->deref()` when the var is a macro. -/
  macroFn : Option MacroFn := none
  /-- The spec side only: Clojure's own expansion of a macro whose jank expansion differs in
  shape (e.g. `case`), when the meaning is the same. -/
  cljMacroFn : Option MacroFn := none
  /-- Bound (has a root). -/
  bound : Bool := false

def VarCell.ref (v : VarCell) : VarRef := ⟨v.ns, v.name⟩

/-- `runtime::ns`: `vars` maps an unqualified name to a var (interned or referred), `aliases` a
name to a namespace name; `symbol_counter` feeds unique names. -/
structure NsCell where
  name : String
  mappings : List (String × VarRef) := []
  aliases : List (String × String) := []
  referredCppGlobals : List (String × Obj) := []
  symbolCounter : Nat := 0

/-- The runtime context (`runtime::context`). -/
structure Runtime where
  namespaces : List NsCell
  vars : List VarCell
  currentNs : String := "user"
  /-- Warnings printed (`intern_owned_var` replacing a referred var). -/
  warnings : List String := []

namespace Runtime

def findNs (rt : Runtime) (name : String) : Option NsCell := rt.namespaces.find? (·.name == name)

def setNs (rt : Runtime) (n : NsCell) : Runtime :=
  { rt with namespaces := rt.namespaces.map fun m => if m.name == n.name then n else m }

def var? (rt : Runtime) (r : VarRef) : Option VarCell := rt.vars.find? (·.ref == r)

def current (rt : Runtime) : NsCell := (rt.findNs rt.currentNs).getD { name := rt.currentNs }

/-- `context::resolve_ns` (context.cpp:449): an alias of the current namespace, else a namespace by
name. -/
def resolveNs (rt : Runtime) (target : String) : Option NsCell :=
  match rt.current.aliases.lookup target with
  | some n => rt.findNs n
  | none => rt.findNs target

/-- `context::qualify_symbol` (context.cpp:116). -/
def qualifySymbol (rt : Runtime) (ns name : String) : String × String :=
  if ns.isEmpty then (rt.current.name, name)
  else match rt.resolveNs ns with
    | some n => (n.name, name)
    | none => (ns, name)

/-- `ns::find_var` (ns.cpp:117) on an unqualified name. -/
def nsFindVar (n : NsCell) (name : String) : Option VarRef := n.mappings.lookup name

/-- `context::find_var` (context.cpp:136). -/
def findVar (rt : Runtime) (ns name : String) : Option VarRef :=
  if !ns.isEmpty then
    match rt.findNs ns with
    | none => none
    | some n => nsFindVar n name
  else nsFindVar rt.current name

/-- `ns::intern_owned_var` (ns.cpp:65): an existing var of this namespace is returned; a referred
var of another namespace is replaced (with a warning). -/
def internOwnedVar (rt : Runtime) (nsName name : String) : Runtime × VarRef :=
  let n := (rt.findNs nsName).getD { name := nsName }
  let rt := if (rt.findNs nsName).isNone then { rt with namespaces := rt.namespaces ++ [n] } else rt
  let r : VarRef := ⟨nsName, name⟩
  match n.mappings.lookup name with
  | some v => if v.ns == nsName then (rt, v) else
    let rt := { rt with warnings := rt.warnings ++ [s!"'{name}' already referred to #'{v.ns}/{v.name}'"] }
    let rt := rt.setNs { n with mappings := (name, r) :: n.mappings.filter (·.1 != name) }
    let rt := if (rt.var? r).isNone then { rt with vars := rt.vars ++ [{ ns := nsName, name }] } else rt
    (rt, r)
  | none =>
    let rt := rt.setNs { n with mappings := (name, r) :: n.mappings }
    let rt := if (rt.var? r).isNone then { rt with vars := rt.vars ++ [{ ns := nsName, name }] } else rt
    (rt, r)

/-- `runtime::munge_and_replace(name, "\\.", "_")`: munge, then dots to underscores (only `-` and
`.` occur in the modeled names). -/
def mungeNs (s : String) : String := (s.replace "-" "_").replace "." "_"

/-- `context::unique_namespaced_string(prefix)` (context.cpp:361): `"{ns}${prefix}_{++counter}"`
(non-Windows). -/
def uniqueNamespacedString (rt : Runtime) (pfx : String) : Runtime × String :=
  let n := rt.current
  let c := n.symbolCounter + 1
  (rt.setNs { n with symbolCounter := c }, s!"{mungeNs n.name}${pfx}_{c}")

/-- `context::unique_string(prefix)` (context.cpp:380): `"{prefix}_{++counter}"`. -/
def uniqueString (rt : Runtime) (pfx : String) : Runtime × String :=
  let n := rt.current
  let c := n.symbolCounter + 1
  (rt.setNs { n with symbolCounter := c }, s!"{pfx}_{c}")

/-- `ns::find_referred_global` (ns.cpp:194). -/
def findReferredGlobal (rt : Runtime) (name : String) : Option Obj := rt.current.referredCppGlobals.lookup name

end Runtime

/-- Why macroexpansion threw. -/
abbrev MacroError := String

/-- `context::macroexpand1` (context.cpp:604), returning `none` when it returns `o` itself (not a
macro form). The macro's function gets `cons(cons(rest(o), nil), o)`: a list whose first element
is `(rest o)` wrapped in a one-element list, followed by every element of `o` (the macro's own
symbol first). So `&form` is `((args...))` and `&env` is the macro's symbol. A macro never gets
`o` itself, so its result is never identical to `o`. -/
def macroexpand1Step (rt : Runtime) (o : Obj) : Except MacroError (Option Obj) :=
  if !o.sequenceLike then .ok none
  else match o.first with
    | .symbol _ ns name =>
      let (qns, qname) := rt.qualifySymbol ns name
      match rt.findVar qns qname with
      | none => .ok none
      | some r => match rt.var? r with
        | none => .ok none
        | some v =>
          if !v.isMacro then .ok none
          else
            let args := consObj (consObj o.rest .nil) o
            match v.macroFn with
            | some f => (f (args.elems.getD [])).map some
            | none => .error s!"var {v.ns}/{v.name} is unbound"
    | _ => .ok none

/-- `context::macroexpand1`. -/
def macroexpand1 (rt : Runtime) (o : Obj) : Except MacroError Obj :=
  (macroexpand1Step rt o).map (·.getD o)

/-- `context::macroexpand` (context.cpp:639): expand until the result is the same object (C++
pointer identity: `macroexpand1Step` returned `none`); the expansion of a form with source info
gets `:jank/macro-expansion (quote o)` in its meta. -/
def macroexpand (rt : Runtime) : Nat → Obj → Except MacroError Obj
  | 0, _ => .error "macroexpansion fuel exhausted"
  | fuel + 1, o => do
    match ← macroexpand1Step rt o with
    | none => .ok o
    | some expanded =>
      let expanded :=
        if o.hasSource then
          let md := (expanded.getMeta.getD .nil).assoc (kw "jank/macro-expansion")
            (.persistentList none [Obj.s "quote", o])
          withMetaGraceful expanded md
        else expanded
      macroexpand rt fuel expanded

end Jank.Analyzer
