/-
  Round 6: OnSet events for inherited components, transcribed from flecs
  v4.2.0, against ObserversManual.md "OnSet and Inheritance".

  One component C with the `(OnInstantiate, Inherit)` trait and a storage
  (table, fragmenting Sparse, DontFragment); one OnSet observer with the
  default source for C, `self|up(IsA)` (validator.c 1613-1616), so it sits in
  the `self_up` list of its event id record.

  The calls and the events flecs delivers for them:
  - `ecs_set(e, C, v)`: OnSet for e itself (component_actions.c 641-702),
    then the propagation of `flecs_emit` (observable.c 1312-1317):
    `flecs_propagate_entities` -> `flecs_emit_propagate` (440-475) ->
    `flecs_emit_propagate_id` (378-438) walks the tables of `(IsA, e)` and
    `flecs_emit_propagate_id_for_range` (310-376) invokes the observer for
    every entity of a table unless the table owns C
    (`owned = flecs_component_get_table(cr, table) != NULL`, 323), then
    recurses into the entities of that table that are targets themselves,
    again unless the table owns C (361).  A DontFragment component is never
    in a table type, so `owned` is always false for it.  The event's source
    is e (`it->sources[0]`, 598-599).
  - `ecs_add_pair(e, EcsIsA, b)`: `flecs_emit` forwards the ids reachable
    through `(IsA, b)` (1196-1237, `flecs_emit_forward`, 799-888) with
    `er_onset`: `flecs_reachable_cache_ensure` (708-780) lists the Inherit
    ids of b's table type, and for each `(IsA, bb)` pair of b's table the
    reachable ids of `(IsA, bb)` that b's table does not have (741-765);
    for each listed element `flecs_emit_forward_id` (613-706) invokes the
    OnSet observers only when the element has a column in its source's
    table (`if (storage_i != -1)`, 685-701; `ecs_table_type_to_column_index`
    is -1 for a Sparse component, storage/table.c 162-165) and, for the
    self|up list, when e's table does not own C (693-696).  Instantiation
    (`flecs_instantiate_dont_fragment`, instantiate.c 301-368) skips Inherit
    components of a base the instance has an IsA pair to (313-316), so it
    emits nothing for them.
  - `ecs_remove(e, C)` when e owns C: the documented OnSet for the value now
    inherited (round 3's model and flecs's own `Sparse_on_set_after_remove_
    override`, run with and without DontFragment, cover this path; it is
    taken as documented here).

  `ecs_get` (`flecs_get_base_component`, instantiate.c 485-555): an entity
  sees its own value, else the first base in type order (IsA pairs are
  sorted by target id), depth first.  That entity is the documented
  "primary source" ("the lowest entity id of all base entities that provide
  the component").
-/
import FlecsLean.Search2

namespace Flecs.OSI

inductive Storage | table | sparse | dontFragment
  deriving Repr, BEq, Inhabited, DecidableEq

structure Ent where
  /-- IsA targets in table type order (ascending ids) -/
  isa : List Nat := []
  /-- the value of C the entity owns -/
  own : Option Nat := none
  deriving Repr, BEq, Inhabited, DecidableEq

abbrev St := Array Ent

def ent (st : St) (e : Nat) : Ent := st.getD e default

/-- Depth bound for every walk (flecs: FLECS_DAG_DEPTH_MAX); targets are
    always lower ids, so no walk is deeper than the entity count. -/
def depth : Nat := 8

/-- `ecs_get_id` / `flecs_get_base_component`: the entity whose value of C
    `e` sees. -/
def srcF (st : St) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, e =>
    match (ent st e).own with
    | some _ => some e
    | none => (ent st e).isa.findSome? (fun b => srcF st fuel b)

def src (st : St) (e : Nat) : Option Nat := srcF st depth e

/-- `flecs_reachable_cache_ensure` for `(IsA, tgt)`, restricted to C: the
    sources of the listed elements, in list order.  C (a component id) sorts
    before the `(IsA, bb)` pairs in tgt's table type. -/
def reachF (st : St) (stor : Storage) : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, tgt =>
    let x := ent st tgt
    let own : List Nat := if stor != Storage.dontFragment && x.own.isSome then [tgt] else []
    let sub := x.isa.flatMap (fun bb => reachF st stor fuel bb)
    -- 744-751: only the elements whose id tgt's table does not have
    own ++ (if own.isEmpty then sub else [])

def reach (st : St) (stor : Storage) (tgt : Nat) : List Nat := reachF st stor depth tgt

/-- `flecs_emit_propagate` from the entity `x` down: (entity, source) for
    every entity of an `(IsA, x)` table that does not own C, and below it. -/
def propF (st : St) (stor : Storage) (source : Nat) : Nat → Nat → List (Nat × Nat)
  | 0, _ => []
  | fuel + 1, x =>
    (List.range st.size).flatMap (fun y =>
      if (ent st y).isa.contains x then
        let owned := stor != Storage.dontFragment && (ent st y).own.isSome
        if owned then [] else (y, source) :: propF st stor source fuel y
      else [])

def insertSorted (b : Nat) : List Nat → List Nat
  | [] => [b]
  | x :: xs => if b < x then b :: x :: xs else x :: insertSorted b xs

inductive Op
  /-- `ecs_set(world, e, C, {v})` -/
  | set (e v : Nat)
  /-- `ecs_add_pair(world, e, EcsIsA, b)`, b < e -/
  | isa (e b : Nat)
  /-- `ecs_remove(world, e, C)` -/
  | remove (e : Nat)
  deriving Repr, BEq, Inhabited, DecidableEq

/-- One call: the new state and the OnSet events flecs delivers to the
    observer, as (entity, source). -/
def step (stor : Storage) (st : St) (op : Op) : St × List (Nat × Nat) :=
  match op with
  | .set e v =>
    if e ≥ st.size then (st, []) else
    let st' := st.modify e (fun x => { x with own := some v })
    (st', (e, e) :: propF st' stor e depth e)
  | .isa e b =>
    if e ≥ st.size || b ≥ e || (ent st e).isa.contains b then (st, []) else
    let st' := st.modify e (fun x => { x with isa := insertSorted b x.isa })
    -- flecs_emit_forward_id: OnSet only for an element with a column
    -- (689) and, for the self|up observers, when e's table does not own C
    let owned := stor != Storage.dontFragment && (ent st' e).own.isSome
    let evs := if stor == Storage.table && !owned then (reach st' stor b).map (fun s => (e, s)) else []
    (st', evs)
  | .remove e =>
    if e ≥ st.size || (ent st e).own.isNone then (st, []) else
    let st' := st.modify e (fun x => { x with own := none })
    (st', match src st' e with | some s => [(e, s)] | none => [])

/-- The documented OnSet events of a call (ObserversManual.md "OnSet and
    Inheritance"): "Adding an IsA pair" (the entity newly inherits C, from a
    new primary source), "Removing an Override", "Setting an Inherited
    Component" (every entity that inherits C from the entity that was set),
    and the set entity itself ("OnSet Events"). -/
def expected (pre post : St) (op : Op) : List (Nat × Nat) :=
  match op with
  | .set e _ =>
    if e ≥ pre.size then [] else
    (e, e) :: ((List.range post.size).filter (fun x => x != e && src post x == some e)).map (fun x => (x, e))
  | .isa e _ =>
    if (ent post e).own.isNone && src pre e != src post e then
      match src post e with | some s => [(e, s)] | none => []
    else []
  | .remove e =>
    if (ent pre e).own.isSome then
      match src post e with | some s => [(e, s)] | none => []
    else []

def showOp : Op → String
  | .set e v => s!"ecs_set(e{e}, C, {v})"
  | .isa e b => s!"ecs_add_pair(e{e}, EcsIsA, e{b})"
  | .remove e => s!"ecs_remove(e{e}, C)"

/-- The properties of one call. -/
def checkStep (stor : Storage) (pre : St) (op : Op) : St × List (String × String) := Id.run do
  let (post, evs) := step stor pre op
  let want := expected pre post op
  let mut out := []
  -- P-OS1: every documented OnSet is delivered
  for (x, s) in want do
    if !evs.contains (x, s) then
      let why := match op with
        | .isa _ b =>
          if stor == Storage.dontFragment then
            s!"the reachable ids of (IsA, e{b}) are its table's type, which a DontFragment component is never in (observable.c 708-781), and flecs_instantiate_dont_fragment skips Inherit components (instantiate.c 313-316)"
          else if stor == Storage.sparse then
            s!"flecs_emit_forward_id invokes OnSet observers only for an element with a column in its source's table (observable.c 689: storage_i != -1); a Sparse component has none (storage/table.c 162-165)"
          else "the forwarded elements do not include it"
        | _ => "the propagation does not reach it"
      out := out ++ [("P-OS1 documented OnSet is delivered", s!"after {showOp op} ({repr stor}): entity e{x} now sees C from e{s} (ObserversManual.md \"OnSet and Inheritance\"), but no OnSet observer was invoked for it: {why}")]
  -- P-OS2: a delivered OnSet carries the entity's new source, for an
  -- entity whose value changed, once
  let mut seen : List (Nat × Nat) := []
  for (x, s) in evs do
    let cur := src post x
    if seen.contains (x, s) then
      out := out ++ [("P-OS2 OnSet reports the entity's value", s!"after {showOp op} ({repr stor}): the OnSet observer was invoked twice for e{x} with source e{s} (each path to the source is propagated or forwarded separately)")]
    else if cur != some s then
      let why := match op with
        | .set _ _ =>
          if stor == Storage.dontFragment && (ent post x).own.isSome then
            s!"e{x} owns C, but flecs_emit_propagate_id_for_range decides ownership by the table (observable.c 324: flecs_component_get_table), and a DontFragment component is in no table"
          else s!"the propagation walks every (IsA, target) table below e{s} that does not own C (observable.c 310-364), including entities whose primary source is another base"
        | .isa _ _ => s!"flecs_emit_forward forwards every reachable element of the new pair (observable.c 784-808), without asking whether another base already provides C"
        | .remove _ => "the re-exposed base"
      let has := match cur with | some c => s!"e{c}" | none => "nothing"
      -- the overriding entity first in the text, so that signatures (which
      -- keep a detail's start) tell the two forms apart
      let lead := if (ent post x).own.isSome then s!"e{x} owns C, yet " else ""
      out := out ++ [("P-OS2 OnSet reports the entity's value", s!"after {showOp op} ({repr stor}): {lead}the OnSet observer was invoked for e{x} with source e{s}, but ecs_get(e{x}, C) reads the value of {has}: {why}")]
    else if src pre x == cur && (ent pre x).own == (ent post x).own &&
        (match op with | .set e _ => cur != some e | _ => true) then
      out := out ++ [("P-OS2 OnSet reports the entity's value", s!"after {showOp op} ({repr stor}): the OnSet observer was invoked for e{x} with source e{s}, whose value of C did not change (\"no OnSet event is generated\")")]
    seen := seen ++ [(x, s)]
  return (post, out)

structure Prog where
  storage : Storage
  nents : Nat
  ops : List Op
  deriving Inhabited

instance : Repr Prog := ⟨fun p _ => .text s!"C {repr p.storage} Inherit; {p.nents} entities; calls {p.ops.map showOp}"⟩

/-- Every violation of every call (the calls go on after one). -/
def run (p : Prog) : List (String × String) := Id.run do
  let mut st : St := Array.replicate p.nents {}
  let mut out := []
  for op in p.ops do
    let (st', vs) := checkStep p.storage st op
    out := out ++ vs
    st := st'
  return out.eraseDups

def check (p : Prog) : List (String × String) := run p

/-- Every event of a program, call by call (for the cases and theorems). -/
def trace (p : Prog) : List (List (Nat × Nat)) := Id.run do
  let mut st : St := Array.replicate p.nents {}
  let mut out := []
  for op in p.ops do
    let (st', evs) := step p.storage st op
    out := out ++ [evs]
    st := st'
  return out

section
variable {m : Type → Type} [Monad m] [Pick m]

def genOp (nents : Nat) : m Op := do
  match (← Pick.pick "osi.call" 3) with
  | 0 => return .set (← Pick.pick "osi.e" nents) (← pickOf "osi.v" #[1, 2])
  | 1 => return .isa (← Pick.pick "osi.e" nents) (← Pick.pick "osi.b" nents)
  | _ => return .remove (← Pick.pick "osi.e" nents)

def genProg (nents len : Nat) : m Prog := do
  let s ← pickOf "osi.storage" #[Storage.table, .sparse, .dontFragment]
  let mut ops := []
  for _ in [0:len] do ops := ops ++ [← genOp nents]
  return { storage := s, nents, ops }

end

def shrink (p : Prog) : List Prog :=
  (List.range p.ops.length).map (fun i => { p with ops := p.ops.eraseIdx i })

/-- The C tests' programs (e0 base, e1 variant or second base, e2 instance). -/
def cases : List (String × Prog) := [
  ("isa_onset_dont_fragment: one level (DontFragment)",
    { storage := .dontFragment, nents := 2, ops := [.set 0 10, .isa 1 0] }),
  ("isa_onset_dont_fragment: two levels (DontFragment)",
    { storage := .dontFragment, nents := 3, ops := [.set 0 10, .isa 1 0, .isa 2 1] }),
  ("isa_onset_sparse: one level (Sparse)",
    { storage := .sparse, nents := 2, ops := [.set 0 10, .isa 1 0] }),
  ("isa_onset_sparse: two levels (Sparse)",
    { storage := .sparse, nents := 3, ops := [.set 0 10, .isa 1 0, .isa 2 1] }),
  ("control: one and two levels (table component)",
    { storage := .table, nents := 3, ops := [.set 0 10, .isa 1 0, .isa 2 1] }),
  ("set_base_onset_dont_fragment_override: the base is set after the instance overrides (DontFragment)",
    { storage := .dontFragment, nents := 2, ops := [.set 0 10, .isa 1 0, .set 1 20, .set 0 30] }),
  ("control: the same with a table component",
    { storage := .table, nents := 2, ops := [.set 0 10, .isa 1 0, .set 1 20, .set 0 30] }),
  ("control: the same with a Sparse component",
    { storage := .sparse, nents := 2, ops := [.set 0 10, .isa 1 0, .set 1 20, .set 0 30] }),
  ("isa_second_base_onset: a second base that is not the primary source (table component)",
    { storage := .table, nents := 3, ops := [.set 0 10, .set 1 20, .isa 2 0, .isa 2 1] }),
  ("isa_second_base_onset: the non-primary base is set (table component)",
    { storage := .table, nents := 3, ops := [.set 0 10, .set 1 20, .isa 2 0, .isa 2 1, .set 1 30] }),
  ("control: the second base becomes the primary source (lower id, added last)",
    { storage := .table, nents := 3, ops := [.set 0 10, .set 1 20, .isa 2 1, .isa 2 0] }),
  ("a variant with two bases that both provide C: one IsA add, two OnSet events",
    { storage := .table, nents := 4, ops := [.set 0 10, .set 1 20, .isa 2 0, .isa 2 1, .isa 3 2] }) ]

end Flecs.OSI
