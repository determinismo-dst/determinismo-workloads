import Determinismo

/-!
# Multimethods and hierarchies: jank's `multi_function` beside Clojure's `MultiFn`

jank (commit 7135b7708; every file cited below is unchanged since f3d82d654):

- core.jank `defmulti` (4071): the hierarchy option defaults to `#'global-hierarchy`, a var
  (as in Clojure); `derive`/`underive`/`isa?`/`parents` (4179–4272) are Clojure's code
  (written again in jank; Java classes aside).
- obj/multi_function.cpp:
  - `reset_cache` (137): `cached_hierarchy = hierarchy;` — the var itself. Clojure's
    `resetCache` stores `hierarchy.deref()`, the hierarchy map.
  - `get_method` (247): `if(cached_hierarchy != hierarchy.deref()) reset_cache();` — a var is never
    its own value, so every call resets the cache to the method table (the cache never keeps a
    computed entry: a performance note, not a semantic one).
  - `find_and_cache_best_method` (261): `is_a(cached_hierarchy, …)` (which derefs: 224, correct)
    and `is_dominant(cached_hierarchy, …)` → `is_preferred(cached_hierarchy, x, y)` (189), which
    walks `parents.call(hierarchy, y)` and `parents.call(hierarchy, x)` with the *var*:
    `(parents h tag)` is `(not-empty (get (:parents h) tag))` (core.jank 4198), and
    `(:parents #'global-hierarchy)` is nil (`object::get` returns nil for a non-map,
    object.cpp 190). So a preference reaches dispatch only when it names the two dispatch values
    themselves; one declared on an ancestor is never seen.
  - `prefer_method` (162) calls `is_preferred(hierarchy.deref(), y, x)`: the map, correct.
- Clojure (MultiFn.java): `prefers(hierarchy, x, y)` walks the parents of y and of x in the
  hierarchy *map* (`findAndCacheBestMethod` passes `cachedHierarchy`, the deref'd map).
-/

namespace Jank.Multi

open Determinismo

/-- Tags: `::t0` … `::t4`. -/
abbrev Tag := Nat

def tagCode (t : Tag) : String := s!"::t{t}"

/-- A hierarchy (make-hierarchy): parents, ancestors, descendants as association lists. -/
structure H where
  parents : List (Tag × List Tag) := []
  ancestors : List (Tag × List Tag) := []
  descendants : List (Tag × List Tag) := []
  deriving Repr, Inhabited

def look (m : List (Tag × List Tag)) (k : Tag) : List Tag := (m.lookup k).getD []

def put (m : List (Tag × List Tag)) (k : Tag) (v : List Tag) : List (Tag × List Tag) :=
  (k, v) :: m.filter (·.1 != k)

/-- `derive` (core.jank 4239–4265, core.clj alike): `tf` adds `target` and its `targets` to
`source` and every one of its `sources`. none: it threw. -/
def derive (h : H) (tag parent : Tag) : Option H :=
  if tag == parent then none
  else if (look h.parents tag).contains parent then some h
  else if (look h.ancestors tag).contains parent then none          -- already has ... as ancestor
  else if (look h.ancestors parent).contains tag then none          -- cyclic derivation
  else
    let union (a b : List Tag) : List Tag := b.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) a
    -- tf: for each k in (cons source (sources source)), (assoc ret k (reduce conj (get targets k #{})
    -- (cons target (targets target)))).
    let tf (m : List (Tag × List Tag)) (source : Tag) (sources : List (Tag × List Tag))
        (target : Tag) (targets : List (Tag × List Tag)) : List (Tag × List Tag) :=
      (source :: look sources source).foldl
        (fun ret k => put ret k (union (look targets k) (target :: look targets target))) m
    some { parents := put h.parents tag ((look h.parents tag) ++ [parent]),
           ancestors := tf h.ancestors tag h.descendants parent h.ancestors,
           descendants := tf h.descendants parent h.ancestors tag h.descendants }

/-- `isa?` (core.jank 4179): equal, or an ancestor. -/
def isa (h : H) (child parent : Tag) : Bool :=
  child == parent || (look h.ancestors child).contains parent

/-- A multimethod's tables: methods (dispatch value → method, in iteration order; `none` is
`:default`), preferences. -/
structure MM where
  methods : List (Option Tag) := []
  prefers : List (Tag × List Tag) := []
  deriving Repr, Inhabited

/-- `is_preferred` / `prefers`, with the hierarchy the parents lookups see: `some h` (a map:
Clojure, and jank's `prefer_method`), `none` (the var: jank's dispatch, whose `(:parents var)`
is nil). -/
def prefers (mm : MM) (hier : Option H) : Nat → Tag → Tag → Bool
  | 0, _, _ => false
  | f + 1, x, y =>
    (look mm.prefers x).contains y
    || (match hier with | some h => (look h.parents y).any (prefers mm hier f x) | none => false)
    || (match hier with | some h => (look h.parents x).any (fun p => prefers mm hier f p y) | none => false)

def dominates (mm : MM) (h : H) (hier : Option H) (x y : Tag) : Bool :=
  prefers mm hier 16 x y || isa h x y

/-- What a call ended with. -/
inductive Out where
  | method (t : Tag)
  | deflt
  | noMethod
  | ambiguous (a b : Tag)
  deriving BEq, DecidableEq, Inhabited

def Out.code : Out → String
  | .method t => s!"the {tagCode t} method"
  | .deflt => "the :default method"
  | .noMethod => "throws: no method"
  | .ambiguous a b => s!"throws: multiple methods ({tagCode a}, {tagCode b}) and neither is preferred"

/-- `find_and_cache_best_method` (multi_function.cpp 261) / `findAndCacheBestMethod`, with the
hierarchy the preference walk sees. -/
def bestMethod (mm : MM) (h : H) (hier : Option H) (dv : Tag) : Out := Id.run do
  let mut best : Option Tag := none
  for e in mm.methods do
    if let some k := e then
      if isa h dv k then
        match best with
        | none => best := some k
        | some b => if dominates mm h hier k b then best := some k
        let b := best.getD k
        if !dominates mm h hier b k then return .ambiguous k b
  match best with
  | some b => return .method b
  | none => return (if mm.methods.contains none then .deflt else .noMethod)

def jankCall (mm : MM) (h : H) (dv : Tag) : Out := bestMethod mm h none dv
def cljCall (mm : MM) (h : H) (dv : Tag) : Out := bestMethod mm h (some h) dv

/-- `(get-method f dv)`: core.jank 4158 → core.cpp `get_method` (613) →
`multi_function::get_fn` (233), which throws when no method applies. Clojure's
`.getMethod` returns nil (get-method's docstring: "or nil if none apply and no default"). -/
def jankGetMethod (mm : MM) (h : H) (dv : Tag) : Out :=
  match jankCall mm h dv with
  | .noMethod => .ambiguous dv dv  -- stands for "throws: no method" (get_fn)
  | o => o

def cljGetMethod (mm : MM) (h : H) (dv : Tag) : Out :=
  match cljCall mm h dv with
  | .noMethod => .deflt            -- stands for nil
  | o => o

def getMethodCode : Out → String
  | .deflt => "nil (or the :default method)"
  | .ambiguous a b => if a == b then "throws: no method" else Out.code (.ambiguous a b)
  | o => o.code

/-! ## The search: a program of derives, defmethods, prefer-methods, then a call -/

structure World where
  decisions : Decisions := {}

instance : Chaotic World where
  decisions w := w.decisions
  setDecisions w d := { w with decisions := d }

def tags : Nat := 4

def body (derives defs prefs : Nat) (getMethod : Bool := false) : EStateM Stop World Unit := do
  let mut h : H := {}
  let mut lines : Array String := #["(defmulti f identity)"]
  for _ in List.range derives do
    let c ← decide (σ := World) "multi.derive.child" tags
    let p ← decide (σ := World) "multi.derive.parent" tags
    if let some h' := derive h c p then
      h := h'
      lines := lines.push s!"(derive {tagCode c} {tagCode p})"
  let mut mm : MM := {}
  for _ in List.range defs do
    let k ← decide (σ := World) "multi.defmethod" (tags + 1)
    let dv : Option Tag := if k == tags then none else some k
    if !mm.methods.contains dv then
      mm := { mm with methods := mm.methods ++ [dv] }
      lines := lines.push s!"(defmethod f {match dv with | some t => tagCode t | none => ":default"} [_] {match dv with | some t => s!":{t}" | none => ":default"})"
  for _ in List.range prefs do
    let x ← decide (σ := World) "multi.prefer.x" tags
    let y ← decide (σ := World) "multi.prefer.y" tags
    -- prefer_method (162) / preferMethod: throws when y is already preferred to x; both check
    -- with the hierarchy map.
    if x != y && !prefers mm (some h) 16 y x then
      mm := { mm with prefers := put mm.prefers x ((look mm.prefers x) ++ [y]) }
      lines := lines.push s!"(prefer-method f {tagCode x} {tagCode y})"
  let dv ← decide (σ := World) "multi.call" tags
  let j := jankCall mm h dv
  let c := cljCall mm h dv
  if j != c then
    violate (σ := World) "multimethod dispatch as Clojure's"
      s!"{" ".intercalate lines.toList} (f {tagCode dv}): Clojure {c.code}, jank {j.code}"
  if getMethod then
    let jg := jankGetMethod mm h dv
    let cg := cljGetMethod mm h dv
    -- (the :default method and nil are told apart by whether a :default method exists)
    let same := match jg, cg with
      | .deflt, .deflt => true
      | a, b => a == b
    if !same || (jg == .ambiguous dv dv) then
      violate (σ := World) "get-method as Clojure's"
        s!"{" ".intercalate lines.toList} (get-method f {tagCode dv}): Clojure {getMethodCode cg}, jank {getMethodCode jg}"

def run (derives defs prefs : Nat) (source : Source) (getMethod : Bool := false) : Ended :=
  match (body derives defs prefs getMethod).run { decisions := { source } } with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }
  | .error (.nodeDown _) w => { taken := w.decisions.taken, violation := none }

/-! ## Theorems -/

/-- Without preferences, jank's dispatch is Clojure's (the bug is confined to the walk). -/
theorem no_prefs_same (methods : List (Option Tag)) (h : H) (dv : Tag) :
    jankCall { methods, prefers := [] } h dv = cljCall { methods, prefers := [] } h dv := by
  have hp : ∀ (hier : Option H) f x y, prefers { methods, prefers := [] } hier f x y = false := by
    intro hier f
    induction f with
    | zero => intro x y; rfl
    | succ n ih =>
      intro x y
      cases hier <;> simp [prefers, look, ih]
  simp [jankCall, cljCall, bestMethod, dominates, hp]

/-- The shrunk example: `::t2` derives from `::t0` and `::t1`, `::t1` from `::t3`, methods on
`::t0` and `::t1`, `(prefer-method f ::t0 ::t3)`. -/
def exH : H := ((((derive {} 2 0).getD {}) |> (derive · 2 1) |>.getD {}) |> (derive · 1 3) |>.getD {})
def exMM : MM := { methods := [some 0, some 1], prefers := [(0, [3])] }

theorem example_clojure : cljCall exMM exH 2 = .method 0 := by decide
theorem example_jank : jankCall exMM exH 2 = .ambiguous 1 0 := by decide

end Jank.Multi
