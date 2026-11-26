/-
  Round 4: overrides of Sparse and DontFragment components inherited
  through IsA, transcribed from flecs v4.2.0:
  - `ecs_search_relation` (search.c 403-434) through
    `flecs_table_search_relation` (308-389),
    `flecs_table_search_relation_pairs` (250-306) and
    `flecs_table_search_relation_for_tgt` (204-248).  For a DontFragment
    component the last one checks the target's sparse set and stops
    (216-221); for every other component it searches the target's table,
    recursively through the target's own IsA pairs (222-232);
  - `flecs_get_base_component` (addons/prefab/instantiate.c 485-555), used
    by `ecs_get_id` (entity.c 1585-1625) and `ecs_has_id`
    (entity.c 2213-2229): for a DontFragment component it checks the
    base's sparse set, then recurses into the base's bases (531-538);
  - `flecs_component_sparse_override` (storage/sparse_storage.c 415-443),
    called by `flecs_component_sparse_insert` (445-489) when a Sparse or
    DontFragment component is added: the new value is copied from the base
    `ecs_search_relation(..., EcsIsA, EcsUp, &base)` finds, or constructed
    when it finds none;
  - instantiation (`flecs_instantiate_dont_fragment`, instantiate.c 301-368):
    an instance gets a copy of the DontFragment components its base owns,
    unless the component is DontInherit, or Inherit (the instance then
    inherits it); Copy-trait table and Sparse components are copied from
    the bases (table_graph.c 718-790).

  The world: entities with an ordered list of IsA targets and the
  components they own, with values.  Components have a storage (table,
  Sparse, DontFragment) and an OnInstantiate trait (Copy, Inherit,
  DontInherit).  Table components are not the subject here; their override
  path (round 3, F24) is replaced by the documented result.
-/
import FlecsLean.Search2

namespace Flecs.IDF

inductive Storage | table | sparse | dontFragment
  deriving Repr, BEq, Inhabited, DecidableEq

inductive Trait | copy | inherit | dontInherit
  deriving Repr, BEq, Inhabited, DecidableEq

structure Comp where
  storage : Storage
  trait : Trait
  deriving Repr, BEq, Inhabited

structure Ent where
  isa : List Nat := []
  own : List (Nat × Nat) := []   -- (component, value)
  /-- round 5: components with `ECS_AUTO_OVERRIDE | C` in the entity's
      type (`ecs_auto_override`, entity.c 1444-1453) -/
  auto : List Nat := []
  deriving Repr, Inhabited

structure St where
  comps : Array Comp
  ents : Array Ent := #[]
  deriving Inhabited

def owns (st : St) (e c : Nat) : Option Nat :=
  ((st.ents.getD e default).own.find? (·.1 == c)).map (·.2)

/-- `flecs_table_search_relation_for_tgt` and its recursion
    (search.c 204-306): the base whose value an override copies.  `fuel`
    bounds the depth (flecs: FLECS_DAG_DEPTH_MAX). -/
def searchUpF (st : St) (c : Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, e =>
    let comp := st.comps.getD c default
    -- flecs_type_can_inherit_id (search.c 169-200): DontInherit never
    if comp.trait == .dontInherit then none
    else (st.ents.getD e default).isa.findSome? fun b =>
      if comp.storage == .dontFragment then
        -- 216-221: the target's sparse set only
        if (owns st b c).isSome then some b else none
      else
        -- 222-232: the target's table, self then up
        if (owns st b c).isSome then some b else searchUpF st c fuel b

def searchUp (st : St) (e c : Nat) : Option Nat := searchUpF st c 17 e

/-- `flecs_get_base_component` (instantiate.c 485-555): the inherited
    value `ecs_get` returns. -/
def baseComponentF (st : St) (c : Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, e =>
    -- 499-501: only Inherit components are inherited
    if (st.comps.getD c default).trait != .inherit then none
    else (st.ents.getD e default).isa.findSome? fun b =>
      match owns st b c with
      | some v => some v
      | none => baseComponentF st c fuel b

def baseComponent (st : St) (e c : Nat) : Option Nat := baseComponentF st c 17 e

/-- `ecs_get_id`: owned, else inherited. -/
def get (st : St) (e c : Nat) : Option Nat :=
  match owns st e c with
  | some v => some v
  | none => baseComponent st e c

def setOwn (st : St) (e c v : Nat) : St :=
  { st with ents := st.ents.modify e (fun x =>
      { x with own := (x.own.filter (·.1 != c)) ++ [(c, v)] }) }

/-- The documented value of a component an instance gets from its bases
    when it is instantiated or overridden: the value `ecs_get` returns. -/
def expectedOverride (st : St) (e c : Nat) : Option Nat := baseComponent st e c

inductive Op
  | new
  /-- `ecs_add_pair(e, EcsIsA, b)`, b < e -/
  | isa (e b : Nat)
  | set (e c v : Nat)
  /-- `ecs_add_id(e, c)`: an override when e inherits c -/
  | add (e c : Nat)
  | remove (e c : Nat)
  /-- round 5: `ecs_auto_override_id(e, c)` -/
  | autoOverride (e c : Nat)
  deriving Repr, BEq, Inhabited

/-- Round 5: `flecs_add_overrides_for_base` (storage/table_graph.c 718-791),
    run when an entity gets `(IsA, b)`: the components that the base's type
    and, recursively, the types of its own IsA targets auto-override, in
    visit order, each with the entity that holds the flag.  For a fragmenting
    component the id is added to the instance's type (749-768); for a
    DontFragment one only the base's table is flagged
    (`EcsTableOverrideDontFragment`, 739-746). -/
def autoVisit (st : St) : Nat → Nat → List (Nat × Nat)
  | 0, _ => []
  | fuel + 1, b =>
    let x := st.ents.getD b default
    (x.auto.map (fun c => (c, b))) ++ x.isa.flatMap (fun bb => autoVisit st fuel bb)

/-- The first entity, depth-first through the IsA targets of `e` (self
    excluded), that owns `c`: where a fragmenting override takes its value
    (the table's override copy; the documented value). -/
def ownerUpF (st : St) (c : Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, e =>
    (st.ents.getD e default).isa.findSome? fun b =>
      if (owns st b c).isSome then some b else ownerUpF st c fuel b

/-- Run one call; returns the new state and the broken properties. -/
def step (st : St) (op : Op) : St × List (String × String) := Id.run do
  match op with
  | .new => return ({ st with ents := st.ents.push {} }, [])
  | .isa e b =>
    if e ≥ st.ents.size || b ≥ e then return (st, [])
    if (st.ents.getD e default).isa.contains b then return (st, [])
    let st0 := { st with ents := st.ents.modify e (fun x => { x with isa := x.isa ++ [b] }) }
    -- instantiation: Copy components of the base hierarchy are copied
    -- (table and Sparse: table_graph.c 718-790 through every base;
    -- DontFragment: instantiate.c 301-368, the components b owns)
    let mut st := st0
    -- round 5: auto overrides of fragmenting components (the table graph)
    let visit := autoVisit st0 17 b
    for (c, _) in visit do
      let comp := st.comps.getD c default
      if comp.storage == .dontFragment || comp.trait == .dontInherit then continue
      if (owns st e c).isSome then continue
      let v := ((ownerUpF st0 c 17 e).bind (fun bb => owns st0 bb c)).getD 0
      st := setOwn st e c v
    for c in [0:st.comps.size] do
      let comp := st.comps.getD c default
      if (owns st e c).isSome then continue
      if comp.trait != .copy then continue
      let src : Option Nat := if comp.storage == .dontFragment then owns st0 b c
        else match owns st0 b c with
          | some v => some v
          | none => (searchUp st0 b c).bind (fun bb => owns st0 bb c)
      if let some v := src then st := setOwn st e c v
    -- round 5: flecs_instantiate (addons/prefab/instantiate.c 393-415) for
    -- the direct base b: `flecs_instantiate_override_dont_fragment`
    -- (370-391) reads only b's own table: an `ecs_add_id` of each
    -- DontFragment component b auto-overrides, which copies from the base
    -- `ecs_search_relation` finds (sparse_storage.c 415-443) or constructs
    let stA := st
    for c in (stA.ents.getD b default).auto do
      let comp := st.comps.getD c default
      if comp.storage != .dontFragment then continue
      if (owns st e c).isSome then continue
      let v := match searchUp st e c with
        | some bb => (owns st bb c).getD 0
        | none => 0
      st := setOwn st e c v
    -- P-I3: an instance owns every component its base, or a base of its
    -- base, auto-overrides (PrefabsManual.md "Auto Overriding", "Prefab
    -- Variants"), as it does for table components
    let mut out := []
    for (c, holder) in visit do
      let comp := st.comps.getD c default
      if comp.trait == .dontInherit then continue
      if (owns st e c).isNone then
        out := out ++ [("P-I3 auto override is owned", s!"entity {e} (IsA {b}) does not own C{c}, which entity {holder} auto-overrides ({repr comp.storage}, {repr comp.trait}): flecs_instantiate_override_dont_fragment (instantiate.c 370-391) reads only the direct base's table, and the table graph only flags the base that holds AUTO_OVERRIDE (table_graph.c 739-746); ecs_get returns the inherited {repr (get st e c)}")]
    return (st, out.eraseDups)
  | .set e c v =>
    if e ≥ st.ents.size then return (st, [])
    return (setOwn st e c v, [])
  | .remove e c =>
    if e ≥ st.ents.size then return (st, [])
    return ({ st with ents := st.ents.modify e (fun x => { x with own := x.own.filter (·.1 != c) }) }, [])
  | .autoOverride e c =>
    if e ≥ st.ents.size then return (st, [])
    let x := st.ents.getD e default
    if x.auto.contains c then return (st, [])
    return ({ st with ents := st.ents.modify e (fun x => { x with auto := x.auto ++ [c] }) }, [])
  | .add e c =>
    if e ≥ st.ents.size then return (st, [])
    if (owns st e c).isSome then return (st, [])
    let comp := st.comps.getD c default
    let before := get st e c
    let value : Nat :=
      if comp.storage == .table then
        -- table components: the documented result (round 3 models the
        -- table override cache itself)
        (expectedOverride st e c).getD 0
      else
        -- flecs_component_sparse_override (sparse_storage.c 415-443)
        match searchUp st e c with
        | some b => (owns st b c).getD 0
        | none => 0   -- flecs_type_info_ctor
    let st' := setOwn st e c value
    let mut out := []
    -- P-I2 (PrefabsManual.md "Component Overriding", ComponentTraits.md
    -- "OnInstantiate trait"): the override starts from the inherited value
    if let some v := before then
      if v != value then
        let path := match searchUp st e c with
          | some b => s!"ecs_search_relation finds base {b}"
          | none => "ecs_search_relation finds no base, so the component is constructed (sparse_storage.c 433-434)"
        out := out ++ [("P-I2 override copies the inherited value", s!"entity {e} inherited C{c} = {v} (ecs_get), but ecs_add overrides it with {value}: {path}; ({repr comp.storage}, {repr comp.trait})")]
    return (st', out)

structure Prog where
  comps : Array Comp
  ops : List Op
  deriving Inhabited

def run (p : Prog) : List (String × String) := Id.run do
  let mut st : St := { comps := p.comps }
  for op in p.ops do
    let (st', vs) := step st op
    st := st'
    if !vs.isEmpty then return vs
  return []

def check (p : Prog) : List (String × String) := run p

section
variable {m : Type → Type} [Monad m] [Pick m]

def genOp (ncomp nents : Nat) : m Op := do
  match (← Pick.pick "idf.call" 5) with
  | 0 => return .isa (← Pick.pick "idf.e" nents) (← Pick.pick "idf.b" nents)
  | 1 => return .set (← Pick.pick "idf.e" nents) (← Pick.pick "idf.c" ncomp) (← pickOf "idf.v" #[5, 7])
  | 2 => return .add (← Pick.pick "idf.e" nents) (← Pick.pick "idf.c" ncomp)
  | 3 => return .remove (← Pick.pick "idf.e" nents) (← Pick.pick "idf.c" ncomp)
  | _ => return .isa (← Pick.pick "idf.e" nents) (← Pick.pick "idf.b" nents)

/-- Round 5: the call menu with `ecs_auto_override`. -/
def genOpAuto (ncomp nents : Nat) : m Op := do
  match (← Pick.pick "idf.call" 4) with
  | 0 => return .isa (← Pick.pick "idf.e" nents) (← Pick.pick "idf.b" nents)
  | 1 => return .set (← Pick.pick "idf.e" nents) (← Pick.pick "idf.c" ncomp) (← pickOf "idf.v" #[5, 7])
  | 2 => return .autoOverride (← Pick.pick "idf.e" nents) (← Pick.pick "idf.c" ncomp)
  | _ => return .add (← Pick.pick "idf.e" nents) (← Pick.pick "idf.c" ncomp)

def genProgAuto (ncomp nents len : Nat) : m Prog := do
  let mut cs := #[]
  for _ in [0:ncomp] do
    let s ← pickOf "idf.storage" #[Storage.table, .sparse, .dontFragment]
    let t ← pickOf "idf.trait" #[Trait.copy, .inherit, .dontInherit]
    cs := cs.push { storage := s, trait := t }
  let mut ops := (List.range nents).map (fun _ => Op.new)
  for _ in [0:len] do ops := ops ++ [← genOpAuto ncomp nents]
  return { comps := cs, ops }

/-- `ncomp` components with drawn storage and trait, `nents` entities,
    `len` calls. -/
def genProg (ncomp nents len : Nat) : m Prog := do
  let mut cs := #[]
  for _ in [0:ncomp] do
    let s ← pickOf "idf.storage" #[Storage.table, .sparse, .dontFragment]
    let t ← pickOf "idf.trait" #[Trait.copy, .inherit, .dontInherit]
    cs := cs.push { storage := s, trait := t }
  let mut ops := (List.range nents).map (fun _ => Op.new)
  for _ in [0:len] do ops := ops ++ [← genOp ncomp nents]
  return { comps := cs, ops }

end

def shrink (p : Prog) : List Prog :=
  (List.range p.ops.length).filterMap (fun i =>
    if p.ops.getD i .new == .new then none else some { p with ops := p.ops.eraseIdx i })

instance : Repr Prog := ⟨fun p _ => .text s!"components {p.comps.toList.map (fun c => (repr c.storage, repr c.trait))}; calls {p.ops.filter (· != .new) |>.map (fun o => toString (repr o))}"⟩

/-- The C test's program and the wrong-base variant. -/
def cases : List (String × Prog) := [
  ("override_dont_fragment_2_levels (DontFragment)",
    { comps := #[{ storage := .dontFragment, trait := .inherit }],
      ops := [.new, .new, .new, .set 0 0 5, .isa 1 0, .isa 2 1, .add 2 0] }),
  ("override_dont_fragment_2_levels (Sparse control)",
    { comps := #[{ storage := .sparse, trait := .inherit }],
      ops := [.new, .new, .new, .set 0 0 5, .isa 1 0, .isa 2 1, .add 2 0] }),
  ("override_dont_fragment_2_levels (1 level control)",
    { comps := #[{ storage := .dontFragment, trait := .inherit }],
      ops := [.new, .new, .set 0 0 5, .isa 1 0, .add 1 0] }),
  ("two bases: the deeper base comes first, a direct base owns another value",
    { comps := #[{ storage := .dontFragment, trait := .inherit }],
      ops := [.new, .new, .new, .new, .set 0 0 5, .set 2 0 7, .isa 1 0, .isa 3 1, .isa 3 2, .add 3 0] }),
  -- round 5: auto_override_dont_fragment_variant.c
  ("auto_override_dont_fragment_variant (DontFragment, Inherit)",
    { comps := #[{ storage := .dontFragment, trait := .inherit }],
      ops := [.new, .new, .new, .set 0 0 50, .autoOverride 0 0, .isa 1 0, .isa 2 1] }),
  ("auto_override_dont_fragment_variant (table component control)",
    { comps := #[{ storage := .table, trait := .inherit }],
      ops := [.new, .new, .new, .set 0 0 50, .autoOverride 0 0, .isa 1 0, .isa 2 1] }),
  ("auto_override_dont_fragment_variant (one level control)",
    { comps := #[{ storage := .dontFragment, trait := .inherit }],
      ops := [.new, .new, .set 0 0 50, .autoOverride 0 0, .isa 1 0] }) ]

end Flecs.IDF
