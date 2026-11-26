/-
  Round 7: prefab children with the OnInstantiate traits (Copy, Inherit,
  DontInherit) and auto overrides, instantiated through both hierarchy
  storages, transcribed from flecs v4.2.0 (round 5's spawner model had Copy
  components only; round 6's had a DontFragment auto override only).

  `Parent` children (`ecs_new_w_parent`): the TreeSpawner
  (addons/prefab/instantiate.c 424-440):
  - the instance child's table (`flecs_prefab_spawner_build_type`,
    tree_spawner.c 10-60): `Parent`, the prefab child's ids except those
    whose record has the Inherit or DontInherit trait (27-31), an
    `AUTO_OVERRIDE | C` id as plain C (33-42: its record has no trait flags,
    component_index.c 286-290), and `(IsA, prefab child)` (60);
  - `flecs_spawner_instantiate` (226-350) appends the instance child to that
    table: a column whose component a base provides through the IsA pair is
    copy-constructed from it (`flecs_table_invoke_ctor`, storage/table.c
    944-972), the others are constructed; a Sparse component is constructed
    in the sparse set (`flecs_sparse_on_add`, component_actions.c 153-177);
  - then `flecs_instantiate_sparse(..., emit_non_sparse = true)`
    (instantiate.c 73-133) walks the prefab child's table type: every id
    with type info that is not DontInherit (101-103) — Inherit ids
    included — gets, for a Sparse component, its value copied into the
    instance child's sparse storage after `ecs_assert(dst_ptr != NULL)`
    (119-124), and then `flecs_notify_on_set_w_cr` (component_actions.c
    641-702), which for a component with an `on_set` hook looks up the
    instance child's table in the component's table cache and asserts it is
    there (672-681, the assert at 679).
  `ChildOf` children: `flecs_instantiate_children` (instantiate.c 135-299):
  the instance child gets the prefab child's ids except DontInherit ones
  (171-184), `AUTO_OVERRIDE | C` as C (193-207), values copied from the
  prefab child's columns (209-215), Sparse values by
  `flecs_instantiate_sparse(..., false)`.

  Documented (ComponentTraits.md "OnInstantiate trait"; PrefabsManual.md
  "Auto Overriding", "Prefab Hierarchies"; HierarchiesManual.md "With a
  Parent hierarchy, instance children will inherit from the prefab
  children. Instantiating a prefab with a ChildOf hierarchy copies the
  prefab child components to the instance child"):
  - ChildOf: the instance child owns every non-DontInherit component of the
    prefab child, with its value, and every auto-overridden one;
  - Parent: it owns the Copy components and the auto-overridden ones (the
    prefab child's value, or a constructed one), inherits the Inherit ones
    through `(IsA, prefab child)`, and has no DontInherit one.
  The nodes are fixed before instantiation (changes after it are F39).
-/
import FlecsLean.Search2

namespace Flecs.Spawn7

inductive Storage | table | sparse
  deriving Repr, BEq, Inhabited, DecidableEq

inductive Trait | copy | inherit | dontInherit
  deriving Repr, BEq, Inhabited, DecidableEq

structure Comp where
  storage : Storage := .table
  hook : Bool := false
  trait : Trait := .copy
  deriving Repr, BEq, Inhabited, DecidableEq

inductive Hier | childOf | parent
  deriving Repr, BEq, Inhabited, DecidableEq

structure Child where
  /-- the components the prefab child owns, (component, value), by id -/
  own : List (Nat × Nat) := []
  /-- the components it auto-overrides (`ECS_AUTO_OVERRIDE | C` ids) -/
  auto : List Nat := []
  deriving Repr, BEq, Inhabited, DecidableEq

structure Prog where
  comps : Array Comp
  hier : Hier
  children : Array Child
  deriving Inhabited, BEq, DecidableEq

def showComp (i : Nat) (c : Comp) : String :=
  let s := match c.storage with | .table => "table" | .sparse => "Sparse"
  let t := match c.trait with | .copy => "Copy" | .inherit => "Inherit" | .dontInherit => "DontInherit"
  s!"C{i} ({s}, {t}{if c.hook then ", on_set hook" else ""})"

instance : Repr Prog := ⟨fun p _ => .text s!"{match p.hier with | .childOf => "ChildOf" | .parent => "Parent"} hierarchy; {(List.range p.comps.size).map (fun i => showComp i (p.comps.getD i default))}; prefab children {p.children.toList.map (fun c => s!"owns {c.own}, auto overrides {c.auto}")}"⟩

/-- What an instance child ends up with: the components it owns with their
    values, and those it sees through `(IsA, prefab child)`. -/
structure Got where
  owns : List (Nat × Nat)
  inherits : List (Nat × Nat)
  deriving Repr, BEq, Inhabited, DecidableEq

/-- Sorting by component id, structurally (the kernel cannot evaluate
    `mergeSort`, which is well-founded recursion). -/
def insertC (x : Nat × Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => [x]
  | y :: ys => if x.1 ≤ y.1 then x :: y :: ys else y :: insertC x ys

def norm : List (Nat × Nat) → List (Nat × Nat)
  | [] => []
  | x :: xs => insertC x (norm xs)

theorem mem_insertC (a x : Nat × Nat) (l : List (Nat × Nat)) :
    a ∈ insertC x l ↔ a = x ∨ a ∈ l := by
  induction l with
  | nil => simp [insertC]
  | cons y ys ih =>
    simp only [insertC]
    split
    · simp
    · simp only [List.mem_cons, ih]
      constructor
      · rintro (h | h | h) <;> simp [h]
      · rintro (h | h | h) <;> simp [h]

theorem mem_norm (a : Nat × Nat) (l : List (Nat × Nat)) : a ∈ norm l ↔ a ∈ l := by
  induction l with
  | nil => simp [norm]
  | cons x xs ih => simp [norm, mem_insertC, ih]

def valOf (ch : Child) (c : Nat) : Nat := ((ch.own.find? (·.1 == c)).map (·.2)).getD 0

/-- A component of the prefab child's type that `flecs_instantiate_sparse`
    asserts on: not DontInherit, not in the instance child's table `ty`, and
    Sparse (the sparse copy) or with an on_set hook (the OnSet
    notification). -/
def offends (comps : Array Comp) (ty : List Nat) (c : Nat) : Bool :=
  let x := comps.getD c default
  x.trait != .dontInherit && !ty.contains c && (x.storage == .sparse || x.hook)

/-- The spawner's table for the instance child (tree_spawner.c 10-60). -/
def spawnerType (p : Prog) (ch : Child) : List Nat :=
  ((ch.own.map (·.1)).filter (fun c => (p.comps.getD c default).trait == .copy) ++ ch.auto).eraseDups

/-- What flecs does for prefab child `k`: the asserts, or the result. -/
def instChild (p : Prog) (k : Nat) : Except String Got := do
  let ch := p.children.getD k default
  let comp := fun c => p.comps.getD c default
  match p.hier with
  | .childOf =>
    let ids := (ch.own.map (·.1)).filter (fun c => (comp c).trait != .dontInherit) ++ ch.auto
    let ids := ids.eraseDups
    return { owns := norm (ids.map (fun c => (c, valOf ch c))), inherits := [] }
  | .parent =>
    -- flecs_prefab_spawner_build_type: the record's trait flags filter
    -- plain ids; AUTO_OVERRIDE ids pass
    let ty := spawnerType p ch
    -- flecs_instantiate_sparse over the prefab child's type, in id order:
    -- the first component that asserts
    let bad := (norm ch.own).find? (fun (c, _) => offends p.comps ty c)
    if let some (c, _) := bad then
      let x := comp c
      if x.storage == .sparse then
        throw s!"prefab child {k} has C{c} (Sparse, {if x.trait == .inherit then "Inherit" else "Copy"}), which the instance child's spawner table leaves out (tree_spawner.c 27-31): flecs_instantiate_sparse copies every non-DontInherit component of the prefab child's type and asserts that the instance child has it in the sparse set (instantiate.c 119-124: ecs_assert(dst_ptr != NULL, ECS_INTERNAL_ERROR))"
      else
        throw s!"prefab child {k} has C{c} (table, Inherit, on_set hook), which the instance child's spawner table leaves out (tree_spawner.c 27-31): flecs_instantiate_sparse notifies OnSet for every non-DontInherit component of the prefab child's type, and flecs_notify_on_set_w_cr asserts that the instance child's table holds a component with an on_set hook (component_actions.c 672-681: ecs_assert(elem != NULL, ECS_INTERNAL_ERROR) at 679)"
    let inh := (ch.own.filter (fun (c, _) => (comp c).trait == .inherit && !ty.contains c))
    return { owns := norm (ty.map (fun c => (c, valOf ch c))), inherits := norm inh }

/-- The documented outcome for prefab child `k`. -/
def wantChild (p : Prog) (k : Nat) : Got :=
  let ch := p.children.getD k default
  let comp := fun c => p.comps.getD c default
  match p.hier with
  | .childOf =>
    let ids := ((ch.own.map (·.1)).filter (fun c => (comp c).trait != .dontInherit) ++ ch.auto).eraseDups
    { owns := norm (ids.map (fun c => (c, valOf ch c))), inherits := [] }
  | .parent =>
    let ownIds := ((ch.own.map (·.1)).filter (fun c => (comp c).trait == .copy) ++ ch.auto).eraseDups
    { owns := norm (ownIds.map (fun c => (c, valOf ch c))),
      inherits := norm (ch.own.filter (fun (c, _) => (comp c).trait == .inherit && !ch.auto.contains c)) }

/-- Properties: P1 (no internal assert) and P-SP3 (an instance child owns,
    inherits and lacks the components the traits say). -/
def check (p : Prog) : List (String × String) := Id.run do
  for k in [0:p.children.size] do
    match instChild p k with
    | .error e => return [("P1 no-crash", e)]
    | .ok g =>
      let w := wantChild p k
      if g != w then
        return [("P-SP3 instance children follow the OnInstantiate traits", s!"prefab child {k}: its instance child owns {g.owns} and inherits {g.inherits}; the traits say owns {w.owns}, inherits {w.inherits}")]
  return []

section
variable {m : Type → Type} [Monad m] [Pick m]

def genProg (ncomp nchild : Nat) : m Prog := do
  let mut cs := #[]
  for _ in [0:ncomp] do
    let s ← pickOf "si.storage" #[Storage.table, .sparse]
    let h := (← Pick.pick "si.hook" 2) == 1
    let t ← pickOf "si.trait" #[Trait.copy, .inherit, .dontInherit]
    cs := cs.push { storage := s, hook := h, trait := t }
  let hier ← pickOf "si.hier" #[Hier.parent, .childOf]
  let mut ch := #[]
  for _ in [0:nchild] do
    let mut own := []
    let mut auto := []
    for c in [0:ncomp] do
      -- 0 nothing, 1 owns, 2 owns and auto overrides, 3 auto overrides only
      match (← Pick.pick "si.has" 4) with
      | 1 => own := own ++ [(c, c + 1)]
      | 2 => own := own ++ [(c, c + 1)]; auto := auto ++ [c]
      | 3 => auto := auto ++ [c]
      | _ => pure ()
    ch := ch.push { own, auto }
  return { comps := cs, hier, children := ch }

end

def shrink (p : Prog) : List Prog :=
  (List.range p.children.size).map (fun i => { p with children := p.children.eraseIdx! i }) ++
  (List.range p.children.size).flatMap (fun i =>
    let c := p.children.getD i default
    (List.range c.own.length).map (fun j => { p with children := p.children.set! i { c with own := c.own.eraseIdx j } }) ++
    (List.range c.auto.length).map (fun j => { p with children := p.children.set! i { c with auto := c.auto.eraseIdx j } }))

/-- The C tests' programs: C0 = Position (Copy), C1 = the component under
    test. -/
def cases : List (String × Prog) := [
  ("prefab_parent_child_inherit_on_set_hook: an Inherit table component with an on_set hook on a Parent child",
    { comps := #[{}, { trait := .inherit, hook := true }], hier := .parent,
      children := #[{ own := [(0, 1), (1, 2)] }] }),
  ("control: the same component on a ChildOf child",
    { comps := #[{}, { trait := .inherit, hook := true }], hier := .childOf,
      children := #[{ own := [(0, 1), (1, 2)] }] }),
  ("control: without the hook (flecs's NonFragmentingChildOf_instantiate_w_inherit)",
    { comps := #[{}, { trait := .inherit }], hier := .parent,
      children := #[{ own := [(0, 1), (1, 2)] }] }),
  ("control: with the hook, auto-overridden (flecs's NonFragmentingChildOf_instantiate_w_auto_override, with a hook)",
    { comps := #[{}, { trait := .inherit, hook := true }], hier := .parent,
      children := #[{ own := [(0, 1), (1, 2)], auto := [1] }] }),
  ("prefab_parent_child_inherit_sparse: an Inherit Sparse component on a Parent child",
    { comps := #[{}, { trait := .inherit, storage := .sparse }], hier := .parent,
      children := #[{ own := [(0, 1), (1, 2)] }] }),
  ("control: the same component on a ChildOf child",
    { comps := #[{}, { trait := .inherit, storage := .sparse }], hier := .childOf,
      children := #[{ own := [(0, 1), (1, 2)] }] }),
  ("control: a Copy Sparse component on a Parent child",
    { comps := #[{}, { storage := .sparse }], hier := .parent,
      children := #[{ own := [(0, 1), (1, 2)] }] }),
  ("control: a DontInherit component with an on_set hook on a Parent child",
    { comps := #[{}, { trait := .dontInherit, hook := true }], hier := .parent,
      children := #[{ own := [(0, 1), (1, 2)] }] }) ]

end Flecs.Spawn7
