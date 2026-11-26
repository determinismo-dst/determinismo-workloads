/-
  Round 5: the tree spawner (addons/prefab/tree_spawner.c, flecs v4.2.0)
  against the ChildOf instantiation path.

  A prefab whose children are in a `Parent` hierarchy (`ecs_new_w_parent`)
  is instantiated through a `TreeSpawner` (instantiate.c 424-440):
  - the first instantiation builds it (`flecs_prefab_spawner_build`,
    tree_spawner.c 199-224): for every child, the table an instance child
    goes to, from the child's table at that moment
    (`flecs_prefab_spawner_build_type`, 10-60: the child's components
    except Inherit/DontInherit ones, `AUTO_OVERRIDE` ids as plain ids, the
    `(IsA, child)` pair);
  - every instantiation (`flecs_spawner_instantiate`, 226-350) puts each
    instance child in its cached table: the table's components are
    initialized from the prefab child through `(IsA, child)` when it still
    has them, constructed otherwise; then `flecs_instantiate_sparse`
    (instantiate.c 73-133) walks the prefab child's current table: a Sparse
    component's value is copied into the instance child's sparse storage,
    which asserts that the instance child has it (119-124), and OnSet is
    notified, which for a component with an `on_set` hook asserts that the
    instance child's table has the component (component_actions.c 672-687);
  - nothing rebuilds the spawner when a prefab child's components change;
    only a change of the children set is refused
    (`flecs_tree_spawner_assert_not_instantiated`, tree_spawner.c 166-197).
  A `ChildOf` hierarchy instantiates each child from its current table
  (instantiate.c 135-299).

  Components here have the default OnInstantiate trait (Copy: "the
  component is copied to the instance", ComponentTraits.md "OnInstantiate
  trait"), a storage (table or fragmenting Sparse), and maybe an on_set hook.
-/
import FlecsLean.Search2

namespace Flecs.Spawn

inductive Storage | table | sparse
  deriving Repr, BEq, Inhabited, DecidableEq

structure Comp where
  storage : Storage := .table
  hook : Bool := false
  deriving Repr, BEq, Inhabited

inductive Hier | childOf | parent
  deriving Repr, BEq, Inhabited, DecidableEq

inductive Op
  /-- `ecs_new_w_pair(world, EcsIsA, prefab)` -/
  | inst
  /-- `ecs_set` on prefab child `k` -/
  | set (k c v : Nat)
  /-- `ecs_remove` on prefab child `k` -/
  | remove (k c : Nat)
  deriving Repr, BEq, Inhabited

structure Prog where
  comps : Array Comp
  hier : Hier
  /-- the prefab's children and their components at the start -/
  children : Array (List (Nat × Nat))
  ops : List Op
  deriving Inhabited

instance : Repr Prog := ⟨fun p _ => .text s!"{repr p.hier} hierarchy; components {p.comps.toList.map (fun c => (repr c.storage, if c.hook then "on_set hook" else "no hook"))}; prefab children {p.children.toList}; calls {p.ops.map (fun o => toString (repr o))}"⟩

def setOwn (own : List (Nat × Nat)) (c v : Nat) : List (Nat × Nat) :=
  (own.filter (·.1 != c)) ++ [(c, v)]

def sorted (own : List (Nat × Nat)) : List (Nat × Nat) :=
  own.mergeSort (fun a b => a.1 ≤ b.1)

/-- Run the program; the broken properties. -/
def check (p : Prog) : List (String × String) := Id.run do
  let mut children := p.children
  let mut cache : Option (Array (List Nat)) := none
  let mut n := 0
  for op in p.ops do
    match op with
    | .set k c v =>
      if k < children.size && c < p.comps.size then
        children := children.modify k (fun o => setOwn o c v)
    | .remove k c =>
      if k < children.size then children := children.modify k (fun o => o.filter (·.1 != c))
    | .inst =>
      n := n + 1
      let mut got : Array (List (Nat × Nat)) := #[]
      match p.hier with
      | .childOf => got := children
      | .parent =>
        -- flecs_prefab_spawner_build on the first instantiation
        let types := match cache with
          | some t => t
          | none => children.map (fun o => o.map (·.1))
        cache := some types
        for k in [0:children.size] do
          let ty := types.getD k []
          let cur := children.getD k []
          -- the cached table's components: the prefab child's value through
          -- (IsA, child) when it still has it, else constructed (0)
          let own := ty.map (fun c => (c, ((cur.find? (·.1 == c)).map (·.2)).getD 0))
          -- flecs_instantiate_sparse over the prefab child's current table
          for (c, _) in cur do
            let comp := p.comps.getD c default
            if !ty.contains c then
              if comp.storage == .sparse then
                return [("P1 no-crash", s!"instance {n}: prefab child {k} has Sparse C{c}, which the spawner's cached table for it lacks: flecs_instantiate_sparse asserts (instantiate.c 122-124: ecs_assert(dst_ptr != NULL, ECS_INTERNAL_ERROR))")]
              if comp.hook then
                return [("P1 no-crash", s!"instance {n}: prefab child {k} has C{c} (on_set hook), which the spawner's cached table for it lacks: flecs_notify_on_set_w_cr asserts (component_actions.c 677-679: ecs_assert(elem != NULL, ECS_INTERNAL_ERROR))")]
          got := got.push own
      -- P-SP1
      for k in [0:children.size] do
        let want := sorted (children.getD k [])
        let hv := sorted (got.getD k [])
        if want != hv then
          return [("P-SP1 instance children copy the prefab children", s!"instance {n}: its child for prefab child {k} owns {hv}, the prefab child owns {want} (ComponentTraits.md \"OnInstantiate trait\": Copy); the tree spawner's tables were built at the first instantiation (tree_spawner.c 199-224) and are not rebuilt when a prefab child's components change")]
  return []

/-- The components each instance's children own, without the asserts: for
    the theorems. -/
def instances (p : Prog) : List (Array (List (Nat × Nat))) := Id.run do
  let mut children := p.children
  let mut cache : Option (Array (List Nat)) := none
  let mut out := []
  for op in p.ops do
    match op with
    | .set k c v =>
      if k < children.size && c < p.comps.size then
        children := children.modify k (fun o => setOwn o c v)
    | .remove k c =>
      if k < children.size then children := children.modify k (fun o => o.filter (·.1 != c))
    | .inst =>
      match p.hier with
      | .childOf => out := out ++ [children]
      | .parent =>
        let types := match cache with
          | some t => t
          | none => children.map (fun o => o.map (·.1))
        cache := some types
        let mut got := #[]
        for k in [0:children.size] do
          let cur := children.getD k []
          got := got.push ((types.getD k []).map (fun c => (c, ((cur.find? (·.1 == c)).map (·.2)).getD 0)))
        out := out ++ [got]
  return out

section
variable {m : Type → Type} [Monad m] [Pick m]

def genProg (ncomp nchild len : Nat) : m Prog := do
  let mut cs := #[]
  for _ in [0:ncomp] do
    let s ← pickOf "sp.storage" #[Storage.table, .sparse]
    let h := (← Pick.pick "sp.hook" 2) == 1
    cs := cs.push { storage := s, hook := h }
  let hier ← pickOf "sp.hier" #[Hier.parent, .childOf]
  let mut ch := #[]
  for _ in [0:nchild] do
    let mask ← Pick.pick "sp.child" (2 ^ ncomp)
    ch := ch.push ((List.range ncomp).filter (fun c => (mask >>> c) % 2 == 1) |>.map (fun c => (c, 1)))
  let mut ops := []
  for _ in [0:len] do
    let op ← match (← Pick.pick "sp.call" 3) with
      | 0 => pure Op.inst
      | 1 => pure (Op.set (← Pick.pick "sp.k" nchild) (← Pick.pick "sp.c" ncomp) 2)
      | _ => pure (Op.remove (← Pick.pick "sp.k" nchild) (← Pick.pick "sp.c" ncomp))
    ops := ops ++ [op]
  return { comps := cs, hier, children := ch, ops }

end

def shrink (p : Prog) : List Prog :=
  (List.range p.ops.length).map (fun i => { p with ops := p.ops.eraseIdx i })

/-- The C tests' programs: C0 = Position, C1 = Velocity. -/
def cases : List (String × Prog) := [
  ("tree_spawner_stale_child_type: Velocity set on the prefab child after the first instance",
    { comps := #[{}, {}], hier := .parent, children := #[[(0, 1)]],
      ops := [.inst, .set 0 1 3, .inst] }),
  ("the same with a ChildOf hierarchy (control)",
    { comps := #[{}, {}], hier := .childOf, children := #[[(0, 1)]],
      ops := [.inst, .set 0 1 3, .inst] }),
  ("tree_spawner_stale_sparse_assert: a Sparse component set on the prefab child after the first instance",
    { comps := #[{}, { storage := .sparse }], hier := .parent, children := #[[(0, 1)]],
      ops := [.inst, .set 0 1 3, .inst] }),
  ("a component removed from the prefab child after the first instance",
    { comps := #[{}, {}], hier := .parent, children := #[[(0, 1), (1, 2)]],
      ops := [.inst, .remove 0 1, .inst] }) ]

end Flecs.Spawn

/-
  Round 6: prefab hierarchies with both storages, nested children, and auto
  overrides of DontFragment components, against `flecs_instantiate`
  (addons/prefab/instantiate.c 393-480) and the spawner build
  (tree_spawner.c 63-114).

  - `flecs_instantiate` (424-440): when the prefab's `(ChildOf, prefab)`
    record has ordered children and at least one `Parent` child
    (`flecs_component_has_non_fragmenting_childof`,
    non_fragmenting_childof.h 46-51), the instance is built by the
    TreeSpawner and the function returns.  Otherwise each ChildOf child is
    instantiated (`flecs_instantiate_children`, 135-299), which instantiates
    that child's own children recursively (291-294).
  - The spawner's walk (`flecs_prefab_spawner_build_from_cr`, 63-114) keeps
    a child only when its table has `Parent` (79-81), and descends into a
    kept child through the ordered children of `(ChildOf, child)` (104-113),
    which only exist when that record has the OrderedChildren flag, which a
    `Parent` child sets (non_fragmenting_childof.c 43-45; ordered_children.c
    21-44 then also lists the ChildOf children).
  - An auto override (`ECS_AUTO_OVERRIDE | C`) on a prefab child becomes
    the plain id C in the instance child's type: in the spawner
    (`flecs_prefab_spawner_build_type`, tree_spawner.c 33-42) and in the
    ChildOf path (`flecs_instantiate_children`, instantiate.c 191-202).  The
    `ECS_AUTO_OVERRIDE | C` record has no trait flags
    (`flecs_component_get_flags_intern`, component_index.c 287-291), so the
    Inherit/DontInherit filters (tree_spawner.c 27-31; instantiate.c
    175-181) let it through.  A DontFragment C then reaches
    `flecs_table_find_or_create`, whose `flecs_table_init` asserts
    "table type cannot contain DontFragment components"
    (storage/table.c 249-259).  On the prefab itself the auto override only
    flags the table (table_graph.c 739-746) and `flecs_instantiate_
    override_dont_fragment` adds the component (instantiate.c 370-391).
-/
namespace Flecs.Spawn6

inductive Kind | childOf | parent
  deriving Repr, BEq, Inhabited, DecidableEq

structure Node where
  /-- the node's parent: 0 is the prefab, k > 0 is node k -/
  parent : Nat
  kind : Kind
  /-- `ecs_auto_override` of a DontFragment component on the node -/
  autoDF : Bool := false
  deriving Repr, BEq, Inhabited, DecidableEq

structure Prog where
  /-- node k + 1 is `nodes[k]`; a node's parent is created before it -/
  nodes : Array Node
  /-- `ecs_auto_override` of the DontFragment component on the prefab -/
  rootAutoDF : Bool := false
  deriving Inhabited, BEq, DecidableEq

instance : Repr Prog := ⟨fun p _ => .text s!"prefab{if p.rootAutoDF then " (auto override DontFragment)" else ""}; nodes {(List.range p.nodes.size).map (fun i => let n := p.nodes.getD i default; s!"{i + 1}: {repr n.kind} child of {n.parent}{if n.autoDF then " (auto override DontFragment)" else ""}")}"⟩

def kids (p : Prog) (n : Nat) : List Nat :=
  (List.range p.nodes.size).filterMap (fun i => if (p.nodes.getD i default).parent == n then some (i + 1) else none)

def node (p : Prog) (k : Nat) : Node := p.nodes.getD (k - 1) default

def hasParentKid (p : Prog) (n : Nat) : Bool :=
  (kids p n).any (fun k => (node p k).kind == Kind.parent)

/-- The spawner's walk below `n` (tree_spawner.c 63-114). -/
def spawnerF (p : Prog) : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, n =>
    (kids p n).flatMap (fun k =>
      if (node p k).kind != Kind.parent then []
      else k :: (if hasParentKid p k then spawnerF p fuel k else []))

/-- `flecs_instantiate` of node `n`: the prefab nodes that get an instance
    counterpart. -/
def instF (p : Prog) : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, n =>
    if hasParentKid p n then spawnerF p fuel n
    else (kids p n).flatMap (fun k => k :: instF p fuel k)

def instantiated (p : Prog) : List Nat := instF p (p.nodes.size + 2) 0

/-- Every prefab node below the prefab. -/
def descendants (p : Prog) : List Nat := (List.range p.nodes.size).map (· + 1)

def check (p : Prog) : List (String × String) := Id.run do
  let got := instantiated p
  -- P1: no internal assert
  for k in got do
    if (node p k).autoDF then
      let path := if (node p k).kind == Kind.parent then "flecs_prefab_spawner_build_type (tree_spawner.c 33-42)" else "flecs_instantiate_children (instantiate.c 191-202)"
      return [("P1 no-crash", s!"prefab node {k} ({repr (node p k).kind}) auto-overrides a DontFragment component: {path} puts the plain id in the instance child's type and flecs_table_init asserts \"table type cannot contain DontFragment components\" (storage/table.c 249-259)")]
  -- P-SP2: every prefab node has a counterpart in the instance
  let missing := (descendants p).filter (fun k => !got.contains k)
  if !missing.isEmpty then
    let why := missing.map (fun k =>
      let par := (node p k).parent
      if hasParentKid p par && (node p k).kind == Kind.childOf then
        s!"node {k} is a ChildOf child of {if par == 0 then "the prefab" else s!"node {par}"}, which has Parent children: the TreeSpawner builds that level and skips children whose table has no Parent (tree_spawner.c 79-81)"
      else s!"node {k} is below node {par}, which the TreeSpawner built without descending into it (tree_spawner.c 99-113)")
    return [("P-SP2 instances get every prefab child", s!"the instance has no counterpart for prefab nodes {missing} ({why}); HierarchiesManual.md \"Hierarchy storage\": \"A single parent can contain children that use both ChildOf and Parent hierarchies\", \"Prefab instantiation works with both storages\"")]
  return []

section
variable {m : Type → Type} [Monad m] [Pick m]

def genProg (n : Nat) : m Prog := do
  let mut nodes := #[]
  for i in [0:n] do
    let par ← Pick.pick "sp6.parent" (i + 1)
    let kind ← pickOf "sp6.kind" #[Kind.childOf, .parent]
    let a := (← Pick.pick "sp6.auto" 2) == 1
    nodes := nodes.push { parent := par, kind, autoDF := a }
  let r := (← Pick.pick "sp6.rootauto" 2) == 1
  return { nodes, rootAutoDF := r }

end

def shrink (p : Prog) : List Prog :=
  -- drop the last node (no node has it as parent), or clear a flag
  (if p.nodes.size > 0 && (kids p p.nodes.size).isEmpty then [{ p with nodes := p.nodes.pop }] else []) ++
  (List.range p.nodes.size).filterMap (fun i =>
    let x := p.nodes.getD i default
    if x.autoDF then some { p with nodes := p.nodes.set! i { x with autoDF := false } } else none) ++
  (if p.rootAutoDF then [{ p with rootAutoDF := false }] else [])

def cases : List (String × Prog) := [
  ("prefab_mixed_children_instance: a ChildOf child and a Parent child",
    { nodes := #[{ parent := 0, kind := .childOf }, { parent := 0, kind := .parent }] }),
  ("control: two ChildOf children",
    { nodes := #[{ parent := 0, kind := .childOf }, { parent := 0, kind := .childOf }] }),
  ("control: two Parent children",
    { nodes := #[{ parent := 0, kind := .parent }, { parent := 0, kind := .parent }] }),
  ("a Parent child with a ChildOf grandchild",
    { nodes := #[{ parent := 0, kind := .parent }, { parent := 1, kind := .childOf }] }),
  ("a ChildOf child with a Parent grandchild (instantiated by the child's own spawner)",
    { nodes := #[{ parent := 0, kind := .childOf }, { parent := 1, kind := .parent }] }),
  ("prefab_child_auto_override_dont_fragment: a ChildOf child auto-overrides a DontFragment component",
    { nodes := #[{ parent := 0, kind := .childOf, autoDF := true }] }),
  ("prefab_child_auto_override_dont_fragment: a Parent child auto-overrides a DontFragment component",
    { nodes := #[{ parent := 0, kind := .parent, autoDF := true }] }),
  ("control: the prefab itself auto-overrides it",
    { nodes := #[{ parent := 0, kind := .childOf }], rootAutoDF := true }) ]

end Flecs.Spawn6
