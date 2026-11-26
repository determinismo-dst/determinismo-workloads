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
