import Determinismo

/-!
# Namespaces: `intern`, `def`, `refer`, `ns-unmap`, `remove-ns`

jank (commit 7135b7708; every file cited below is unchanged since f3d82d654):

- core.jank `intern` (4984): `(cpp/jank.runtime.intern_var (to_qualified_symbol ns name))` →
  core.cpp `intern_var` (789) → context.cpp `intern_var` (492) → ns.cpp `ns::intern_var` (26):
  whatever the namespace maps the name to — a var referred from another namespace included — is
  returned (`if(found_var && found_var->is_some()) return expect_object<var>(*found_var);`), and
  `intern` then binds *that* var's root (`var_bind_root`).
- `def` → codegen/api.cpp 18 → `ns::intern_owned_var` (ns.cpp 65): a var of another namespace
  is replaced by a new one of this namespace, with a warning.
- `refer` (core.jank 4717) → ns.cpp `ns::refer` (175): throws when the name maps to a var of
  another namespace that is not clojure.core (as refer's docstring says).
- `ns-unmap` → ns.cpp `unmap` (110).
- `remove-ns` (core.jank 4610) → core.cpp `remove_ns` (840) → context.cpp `remove_ns` (420): no
  check of the name.

Clojure 1.12 (Namespace.java): `intern` keeps an interned mapping, and replaces a referred var
with a new var of this namespace (`checkReplacement`: a warning); `remove` throws
"Cannot remove clojure namespace" for clojure.core (remove-ns's docstring: "Cannot be used to
remove the clojure namespace").
-/

namespace Jank.Ns

open Determinismo

/-- A var: its namespace and name. -/
structure VarId where
  ns : String
  name : String
  deriving BEq, Repr, Inhabited

def VarId.code (v : VarId) : String := s!"#'{v.ns}/{v.name}"

structure NsState where
  namespaces : List String := ["clojure.core", "user", "other"]
  /-- (namespace, symbol) → var. -/
  mappings : List ((String × String) × VarId) := []
  /-- A var's root value. -/
  roots : List (String × String × Nat) := []
  /-- The operation threw (a catchable exception). -/
  threw : Bool := false
  deriving Inhabited

def NsState.lookup (s : NsState) (ns sym : String) : Option VarId :=
  (s.mappings.find? fun (k, _) => k == (ns, sym)).map (·.2)

def NsState.map (s : NsState) (ns sym : String) (v : VarId) : NsState :=
  { s with mappings := ((ns, sym), v) :: s.mappings.filter (·.1 != (ns, sym)) }

def NsState.unmap (s : NsState) (ns sym : String) : NsState :=
  { s with mappings := s.mappings.filter (·.1 != (ns, sym)) }

def NsState.root (s : NsState) (v : VarId) : Option Nat :=
  (s.roots.find? fun (a, b, _) => a == v.ns && b == v.name).map (·.2.2)

def NsState.bindRoot (s : NsState) (v : VarId) (x : Nat) : NsState :=
  { s with roots := (v.ns, v.name, x) :: s.roots.filter fun (a, b, _) => !(a == v.ns && b == v.name) }

/-- clojure.core has `map` and `inc`; `other` has `f` and its own `map`; `user` refers
clojure.core (refer-clojure). -/
def initial : NsState :=
  let s : NsState := {}
  let s := s.map "clojure.core" "map" ⟨"clojure.core", "map"⟩ |>.bindRoot ⟨"clojure.core", "map"⟩ 1
  let s := s.map "clojure.core" "inc" ⟨"clojure.core", "inc"⟩ |>.bindRoot ⟨"clojure.core", "inc"⟩ 2
  let s := s.map "other" "f" ⟨"other", "f"⟩ |>.bindRoot ⟨"other", "f"⟩ 3
  let s := s.map "other" "map" ⟨"other", "map"⟩ |>.bindRoot ⟨"other", "map"⟩ 4
  let s := s.map "user" "map" ⟨"clojure.core", "map"⟩
  s.map "user" "inc" ⟨"clojure.core", "inc"⟩

inductive Op where
  | intern (sym : String) (v : Nat)
  | define (sym : String) (v : Nat)
  | referOther
  | unmap (sym : String)
  | removeCore
  deriving Repr, BEq, Inhabited

def Op.code : Op → String
  | .intern s v => s!"(intern 'user '{s} {v})"
  | .define s v => s!"(def {s} {v})"
  | .referOther => "(refer 'other)"
  | .unmap s => s!"(ns-unmap 'user '{s})"
  | .removeCore => "(remove-ns 'clojure.core)"

/-- jank, in namespace `user`. -/
def jankStep (s : NsState) : Op → NsState
  | .intern sym v =>
    -- ns::intern_var (ns.cpp 26): an existing mapping, whatever its namespace, is returned.
    match s.lookup "user" sym with
    | some var => s.bindRoot var v
    | none => (s.map "user" sym ⟨"user", sym⟩).bindRoot ⟨"user", sym⟩ v
  | .define sym v =>
    -- ns::intern_owned_var (ns.cpp 65): replaced unless it is this namespace's.
    match s.lookup "user" sym with
    | some var => if var.ns == "user" then s.bindRoot var v
      else (s.map "user" sym ⟨"user", sym⟩).bindRoot ⟨"user", sym⟩ v
    | none => (s.map "user" sym ⟨"user", sym⟩).bindRoot ⟨"user", sym⟩ v
  | .referOther =>
    -- core.jank refer → ns::refer (ns.cpp 175) for f and map.
    ["f", "map"].foldl (fun s sym =>
      if s.threw then s else
      let var : VarId := ⟨"other", sym⟩
      match s.lookup "user" sym with
      | some found => if var.ns != found.ns && found.ns != "clojure.core" then { s with threw := true }
        else s.map "user" sym var
      | none => s.map "user" sym var) s
  | .unmap sym => s.unmap "user" sym
  | .removeCore =>
    -- context.cpp remove_ns (420): no check.
    { s with namespaces := s.namespaces.erase "clojure.core" }

/-- Clojure, in namespace `user` (Namespace.java). -/
def cljStep (s : NsState) : Op → NsState
  | .intern sym v =>
    match s.lookup "user" sym with
    | some var => if var.ns == "user" then s.bindRoot var v   -- isInternedMapping
      else (s.map "user" sym ⟨"user", sym⟩).bindRoot ⟨"user", sym⟩ v  -- checkReplacement: replace
    | none => (s.map "user" sym ⟨"user", sym⟩).bindRoot ⟨"user", sym⟩ v
  | .define sym v =>
    -- DefExpr: lookupVar → currentNS().intern(sym): the same as intern.
    match s.lookup "user" sym with
    | some var => if var.ns == "user" then s.bindRoot var v
      else (s.map "user" sym ⟨"user", sym⟩).bindRoot ⟨"user", sym⟩ v
    | none => (s.map "user" sym ⟨"user", sym⟩).bindRoot ⟨"user", sym⟩ v
  | .referOther =>
    -- refer's docstring: throws when the name is mapped to something else (jank does so; the
    -- 1.12 implementation warns instead): modeled as jank, outside this comparison.
    jankStep s .referOther
  | .unmap sym => s.unmap "user" sym
  | .removeCore => { s with threw := true }   -- "Cannot remove clojure namespace"

/-- What a program can observe: user's names, clojure.core's roots, whether clojure.core is found. -/
def observe (s : NsState) : String :=
  let names := ["map", "inc", "f", "y"].map fun sym =>
    match s.lookup "user" sym with
    | some v => s!"{sym}→{v.code}={(s.root v).getD 0}"
    | none => s!"{sym}→unbound"
  let core := ["map", "inc"].map fun sym => s!"clojure.core/{sym}={(s.root ⟨"clojure.core", sym⟩).getD 0}"
  s!"{" ".intercalate names}; {" ".intercalate core}; (find-ns 'clojure.core) {if s.namespaces.contains "clojure.core" then "found" else "nil"}{if s.threw then "; threw" else ""}"

structure World where
  decisions : Decisions := {}

instance : Chaotic World where
  decisions w := w.decisions
  setDecisions w d := { w with decisions := d }

def syms : List String := ["map", "inc", "f", "y"]

def drawOp : EStateM Stop World Op := do
  match ← decide (σ := World) "ns.op" 5 with
  | 0 => pure (.intern (syms.getD (← decide (σ := World) "ns.sym" 4) "y") 7)
  | 1 => pure (.define (syms.getD (← decide (σ := World) "ns.sym" 4) "y") 8)
  | 2 => pure .referOther
  | 3 => pure (.unmap (syms.getD (← decide (σ := World) "ns.sym" 4) "y"))
  | _ => pure .removeCore

/-- jank with the two differences fixed (intern replacing a referred var, remove-ns refusing
clojure.core): to check that nothing else differs within the bounds. -/
def fixedStep (s : NsState) : Op → NsState
  | .intern sym v => cljStep s (.intern sym v)
  | .removeCore => { s with threw := true }
  | op => jankStep s op

def body (ops : Nat) (fixed : Bool := false) : EStateM Stop World Unit := do
  let mut j := initial
  let mut c := initial
  let mut prog : Array String := #["(in-ns 'user)"]
  for _ in List.range ops do
    let op ← drawOp
    prog := prog.push op.code
    -- A throwing operation leaves the state as it was (each top-level form on its own).
    let j' := if fixed then fixedStep j op else jankStep j op
    let c' := cljStep c op
    let jThrew := j'.threw; let cThrew := c'.threw
    j := if jThrew then j else j'
    c := if cThrew then c else c'
    if jThrew != cThrew || observe j != observe c then
      violate (σ := World) "namespaces as Clojure's"
        s!"{" ".intercalate prog.toList}: Clojure {if cThrew then "throws; " else ""}{observe c}; jank {if jThrew then "throws; " else ""}{observe j}"

def run (ops : Nat) (source : Source) (fixed : Bool := false) : Ended :=
  match (body ops fixed).run { decisions := { source } } with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }
  | .error (.nodeDown _) w => { taken := w.decisions.taken, violation := none }

/-- jank's `intern` binds the root of whatever var the name maps to, another namespace's
included (ns.cpp 33–38). -/
theorem jank_intern_binds_found (s : NsState) (sym : String) (v : Nat) (var : VarId)
    (h : s.lookup "user" sym = some var) : jankStep s (.intern sym v) = s.bindRoot var v := by
  simp [jankStep, h]

/-- Clojure's interns a new var of the namespace instead (Namespace.intern, checkReplacement). -/
theorem clj_intern_replaces_referred (s : NsState) (sym : String) (v : Nat) (var : VarId)
    (h : s.lookup "user" sym = some var) (h2 : var.ns ≠ "user") :
    cljStep s (.intern sym v) = (s.map "user" sym ⟨"user", sym⟩).bindRoot ⟨"user", sym⟩ v := by
  simp [cljStep, h, h2]

end Jank.Ns
