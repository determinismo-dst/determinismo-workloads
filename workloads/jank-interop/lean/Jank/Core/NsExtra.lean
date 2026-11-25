import Determinismo

/-!
# Namespaces: what fork C's `Jank.Ns` left out

Fork C covered `intern` (C7), `remove-ns` (C8), `def` over a referred var and `ns-unmap`, and
modeled `refer` throwing on a conflict as its docstring says (its RC9). This file adds the
operations around lookup and reloading, replicated from jank 7135b7708 (paths under `upstream-main/compiler+runtime/`; every file below is
unchanged since f3d82d654):

- `src/cpp/jank/runtime/ns.cpp`: `intern_owned_var` (65), `find_var` (117), `add_alias` (136),
  `find_alias` (163), `refer` (174);
- `src/cpp/jank/runtime/context.cpp`: `qualify_symbol` (116), `find_var` (136), `intern_ns` (401),
  `find_ns` (433), `resolve_ns` (444);
- `src/cpp/jank/runtime/core.cpp`: `in_ns` (819), `find_var` (835), `ns_resolve` (865),
  `alias` (872), `refer` (892);
- core.jank: `in-ns` (4587), `find-var` (4604), `ns-resolve` (4675), `resolve` (4686), `alias`
  (4708), `refer` (4717), the `ns` macro (5581: `(in-ns 'name)` then `(refer 'clojure.core)`
  unless `:refer-clojure` is given).

Clojure 1.12: `Namespace.java` (`reference` 126, `checkReplacement` 106, `findInternedVar`
229, `addAlias` 246), `Var.find` (Var.java 143), `Compiler.maybeResolveIn` (7952) and
`namespaceFor` (7890), `RT.inNamespace` (RT.java 244: returns the namespace).

Spec for `refer` on a name already interned here: `Namespace.reference` keeps the interned
mapping and throws nothing (it prints "REJECTED" only when the new var is not clojure.core's),
which is what makes re-evaluating an `ns` form work; `refer`'s docstring ("Throws an exception if
name is already mapped to something else in the current namespace") is not what 1.12 does — the
spec here is the implementation, with that caveat recorded.
-/

namespace Jank.Core.NsExtra

open Determinismo

structure VarId where
  ns : String
  name : String
  deriving BEq, Repr, Inhabited

def VarId.code (v : VarId) : String := s!"#'{v.ns}/{v.name}"

structure St where
  current : String := "user"
  namespaces : List String := ["clojure.core", "user", "a", "other"]
  mappings : List ((String × String) × VarId) := []
  aliases : List ((String × String) × String) := []
  deriving Inhabited

def St.lookup (s : St) (ns sym : String) : Option VarId :=
  (s.mappings.find? fun (k, _) => k == (ns, sym)).map (·.2)

def St.map (s : St) (ns sym : String) (v : VarId) : St :=
  { s with mappings := s.mappings.map (fun (k, w) => if k == (ns, sym) then (k, v) else (k, w)) ++
      (if s.mappings.any (·.1 == (ns, sym)) then [] else [((ns, sym), v)]) }

def St.alias? (s : St) (ns a : String) : Option String :=
  (s.aliases.find? fun (k, _) => k == (ns, a)).map (·.2)

/-- clojure.core's publics in this world. -/
def corePublics : List String := ["inc", "map"]

/-- The start: clojure.core interns `inc` and `map`; `other` interns `y`; `user` and `a` refer
clojure.core; `a` aliases `s` to `other`. -/
def start : St :=
  let s : St := {}
  let s := corePublics.foldl (fun s n => s.map "clojure.core" n ⟨"clojure.core", n⟩) s
  let s := s.map "other" "y" ⟨"other", "y"⟩
  let s := corePublics.foldl (fun s n => s.map "user" n ⟨"clojure.core", n⟩) s
  let s := corePublics.foldl (fun s n => s.map "a" n ⟨"clojure.core", n⟩) s
  { s with aliases := [(("a", "s"), "other")] }

/-- What an operation printed (its value), or that it threw. -/
abbrev Out := Except String String

/-! ## jank -/

/-- ns.cpp 65 `intern_owned_var` (what `def` reaches through codegen): a var of this namespace is
returned; any other mapping is replaced by a new var of this namespace (with a warning). -/
def jankDef (s : St) (name : String) : St :=
  match s.lookup s.current name with
  | some v => if v.ns == s.current then s else s.map s.current name ⟨s.current, name⟩
  | none => s.map s.current name ⟨s.current, name⟩

/-- ns.cpp 174 `refer(sym, var)`: an existing var mapping whose namespace differs from the new
var's and is not clojure.core is an error (expect_ok throws, core.cpp 892); else the mapping is set. -/
def jankReferOne (s : St) (sym : String) (v : VarId) : Except String St :=
  match s.lookup s.current sym with
  | some found =>
    if v.ns != found.ns && found.ns != "clojure.core" then
      .error s!"{sym} already refers to {found.code} in ns {s.current}"
    else .ok (s.map s.current sym v)
  | none => .ok (s.map s.current sym v)

/-- core.jank 4717 `refer` of every public of clojure.core (what `(ns x)` does, 5581), in order;
the first error is thrown. -/
def jankReferCore (s : St) : Except String St :=
  corePublics.foldlM (fun s n => jankReferOne s n ⟨"clojure.core", n⟩) s

/-- context.cpp 116 `qualify_symbol`: an unqualified symbol takes the *current* namespace; a
qualified one has its namespace resolved through the *current* namespace's aliases, then by name
(`resolve_ns` 444), and is left as it is when neither finds it. -/
def jankQualify (s : St) (ns name : String) : String × String :=
  if ns.isEmpty then (s.current, name)
  else match s.alias? s.current ns with
    | some target => (target, name)
    | none => (ns, name)

/-- context.cpp 136 `find_var`: a qualified symbol looks its namespace up by name only (no
alias), then `ns::find_var` of the bare name: any mapping, referred vars included; unqualified:
the current namespace's mapping. -/
def jankContextFindVar (s : St) (ns name : String) : Option VarId :=
  if ns.isEmpty then s.lookup s.current name
  else if s.namespaces.contains ns then s.lookup ns name
  else none

/-- ns.cpp 117 `ns::find_var`: qualified → `qualify_symbol` then context `find_var`; else the
namespace's own mapping (any). -/
def jankNsFindVar (s : St) (inNs ns name : String) : Option VarId :=
  if !ns.isEmpty then
    let (q, n) := jankQualify s ns name
    jankContextFindVar s q n
  else s.lookup inNs name

def optCode : Option VarId → String
  | some v => v.code
  | none => "nil"

/-- core.cpp 835 `find_var` → context `find_var`. -/
def jankFindVar (s : St) (ns name : String) : Out := .ok (optCode (jankContextFindVar s ns name))

/-- core.cpp 865 `ns_resolve(ns, sym)` → `n->find_var(sym)`. -/
def jankNsResolve (s : St) (inNs ns name : String) : Out :=
  if s.namespaces.contains inNs then .ok (optCode (jankNsFindVar s inNs ns name))
  else .error "The provided value was not resolvable as a namespace."

/-- core.cpp 819 `in_ns`: sets `*ns*` (creating the namespace), returns nil. -/
def jankInNs (s : St) (name : String) : St × Out :=
  ({ s with current := name, namespaces := if s.namespaces.contains name then s.namespaces else s.namespaces ++ [name] }, .ok "nil")

/-! ## Clojure -/

/-- `Namespace.findInternedVar` (229): a var mapping whose namespace is this one. -/
def cljFindInterned (s : St) (ns name : String) : Option VarId :=
  match s.lookup ns name with
  | some v => if v.ns == ns then some v else none
  | none => none

/-- `Compiler` def → `Namespace.intern`: replaces a referred mapping (fork C: agrees with jank). -/
def cljDef (s : St) (name : String) : St := jankDef s name

/-- `Namespace.reference` (126) with `checkReplacement` (106): the same var → nothing; an
interned mapping → kept, no exception; anything else → replaced (a warning). -/
def cljReferOne (s : St) (sym : String) (v : VarId) : Except String St :=
  match s.lookup s.current sym with
  | some found =>
    if found == v then .ok s
    else if found.ns == s.current && found.name == sym then .ok s
    else .ok (s.map s.current sym v)
  | none => .ok (s.map s.current sym v)

def cljReferCore (s : St) : Except String St :=
  corePublics.foldlM (fun s n => cljReferOne s n ⟨"clojure.core", n⟩) s

/-- `Var.find` (143): an unqualified symbol and an unknown namespace throw; else the interned var. -/
def cljFindVar (s : St) (ns name : String) : Out :=
  if ns.isEmpty then .error "Symbol must be namespace-qualified"
  else if !s.namespaces.contains ns then .error s!"No such namespace: {ns}"
  else .ok (optCode (cljFindInterned s ns name))

/-- `maybeResolveIn(n, sym)` (7952) with `namespaceFor(n, sym)` (7890): the *given* namespace's
aliases, then by name; the interned var there. Unqualified: `n.getMapping(sym)`. -/
def cljNsResolve (s : St) (inNs ns name : String) : Out :=
  if !s.namespaces.contains inNs then .error s!"No namespace: {inNs} found"
  else if ns.isEmpty then .ok (optCode (s.lookup inNs name))
  else
    let target := (s.alias? inNs ns).getD ns
    if !s.namespaces.contains target then .ok "nil"
    else .ok (optCode (cljFindInterned s target name))

/-- `RT.inNamespace` (244): returns the namespace. -/
def cljInNs (s : St) (name : String) : St × Out :=
  ({ s with current := name, namespaces := if s.namespaces.contains name then s.namespaces else s.namespaces ++ [name] }, .ok s!"#namespace[{name}]")

/-! ## The world -/

inductive Op where
  | defInc
  | reloadNs
  | aliasS
  | findVarCurrentInc
  | findVarUnqualified
  | findVarNoNs
  | nsResolveA
  | resolveS
  | inNsB
  deriving Repr, BEq, Inhabited

def ops : List Op :=
  [.defInc, .reloadNs, .aliasS, .findVarCurrentInc, .findVarUnqualified, .findVarNoNs, .nsResolveA,
   .resolveS, .inNsB]

def Op.code (cur : String) : Op → String
  | .defInc => "(def inc 1)"
  | .reloadNs => s!"(ns {cur})"
  | .aliasS => "(alias 's 'clojure.core)"
  | .findVarCurrentInc => s!"(find-var '{cur}/inc)"
  | .findVarUnqualified => "(find-var 'map)"
  | .findVarNoNs => "(find-var 'nope/x)"
  | .nsResolveA => "(ns-resolve 'a 's/y)"
  | .resolveS => "(resolve 's/map)"
  | .inNsB => "(in-ns 'b)"

/-- One operation on each side: the new state and what it printed. A thrown operation leaves the
state as the replica left it up to the throw. -/
def step (jank : Bool) (s : St) : Op → St × Out
  | .defInc => (if jank then jankDef s "inc" else cljDef s "inc", .ok s!"#'{s.current}/inc")
  | .reloadNs =>
    -- `(ns x)` = `(in-ns 'x)` then `(refer 'clojure.core)`; for the current namespace
    match (if jank then jankReferCore s else cljReferCore s) with
    | .ok s' => (s', .ok "nil")
    | .error e => (s, .error e)
  | .aliasS =>
    match s.alias? s.current "s" with
    | some t => if t == "clojure.core" then (s, .ok "nil") else (s, .error "alias exists")
    | none => ({ s with aliases := s.aliases ++ [((s.current, "s"), "clojure.core")] }, .ok "nil")
  | .findVarCurrentInc => (s, if jank then jankFindVar s s.current "inc" else cljFindVar s s.current "inc")
  | .findVarUnqualified => (s, if jank then jankFindVar s "" "map" else cljFindVar s "" "map")
  | .findVarNoNs => (s, if jank then jankFindVar s "nope" "x" else cljFindVar s "nope" "x")
  | .nsResolveA => (s, if jank then jankNsResolve s "a" "s" "y" else cljNsResolve s "a" "s" "y")
  | .resolveS => (s, if jank then jankNsResolve s s.current "s" "map" else cljNsResolve s s.current "s" "map")
  | .inNsB => if jank then jankInNs s "b" else cljInNs s "b"

def showOut : Out → String
  | .ok v => v
  | .error e => s!"throws ({e})"

def sameOut (a b : Out) : Bool :=
  match a, b with
  | .ok x, .ok y => x == y
  | .error _, .error _ => true
  | _, _ => false

structure World where
  decisions : Decisions := {}

instance : Chaotic World where
  decisions w := w.decisions
  setDecisions w d := { w with decisions := d }

/-- `n` operations drawn; after each, both outputs must agree. -/
def body (n : Nat) : EStateM Stop World Unit := do
  let mut j := start
  let mut c := start
  let mut prog : List String := []
  for i in List.range n do
    let op := ops.getD (← decide (σ := World) s!"ns.op{i}" ops.length) .defInc
    prog := prog ++ [op.code j.current]
    let (j', oj) := step true j op
    let (c', oc) := step false c op
    j := j'
    c := c'
    if !sameOut oj oc then
      violate (σ := World) "namespace operations as Clojure's"
        s!"{" ".intercalate prog}: Clojure {showOut oc}, jank {showOut oj}"

def runBody (n : Nat) (source : Source) : Ended :=
  match (body n).run { decisions := { source } } with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }
  | .error (.nodeDown _) w => { taken := w.decisions.taken, violation := none }

/-- Every program of `n` operations: the ones that disagree, grouped by the first disagreeing
operation's text. -/
def table (n : Nat) : List (String × Nat × String) := Id.run do
  let mut groups : List (String × Nat × String) := []
  let rec progs : Nat → List (List Op)
    | 0 => [[]]
    | k + 1 => (progs k).flatMap fun p => ops.map fun o => p ++ [o]
  for p in progs n do
    let mut j := start
    let mut c := start
    let mut text : List String := []
    for op in p do
      text := text ++ [op.code j.current]
      let (j', oj) := step true j op
      let (c', oc) := step false c op
      j := j'
      c := c'
      if !sameOut oj oc then
        let key := op.code "<ns>"
        let detail := s!"{" ".intercalate text}: Clojure {showOut oc}, jank {showOut oj}"
        groups := match groups.find? (·.1 == key) with
          | some _ => groups.map fun (k, m, d) => if k == key then (k, m + 1, d) else (k, m, d)
          | none => groups ++ [(key, 1, detail)]
        break
  return groups

/-- After `(def inc 1)` in `user`, re-evaluating `(ns user)` throws in jank. -/
theorem reload_after_shadowing_throws :
    (match jankReferCore (jankDef start "inc") with | .ok _ => false | .error _ => true) = true ∧
    (match cljReferCore (cljDef start "inc") with | .ok _ => true | .error _ => false) = true := by
  decide

end Jank.Core.NsExtra
