/-
  Round 8: OnAdd and OnRemove for a component reached through the
  hierarchy, with both storages: `ChildOf` pairs (fragmenting) and the
  `Parent` component (non-fragmenting), transcribed from flecs v4.2.0.
  Round 7's `EvInh` had IsA only; its ChildOf forms (F48 (b), F50 (b)) were
  read, not modelled.

  One component C (table or DontFragment storage) and observers with the
  term `C(self|up ChildOf)` for OnAdd and for OnRemove, and observers on the
  pair `(ChildOf, *)` for OnAdd and OnRemove.  Each entity's hierarchy
  storage is fixed: `ChildOf` (`ecs_add_pair(e, EcsChildOf, p)`) or `Parent`
  (`ecs_set(e, EcsParent, {p})`, `ecs_new_w_parent`).

  The paths:
  - Setting or removing C on x: `flecs_emit` propagates down
    (`flecs_emit_propagate`, observable.c 440-475; `flecs_emit_propagate_id`,
    378-438).  For a `(ChildOf, x)` record with Parent children it walks
    `ordered_children`, one row each (389-418, with `notify` true when a
    user observer exists, 395-404); else the record's tables (419-431).
    `flecs_emit_propagate_id_for_range` (310-376) skips the self|up
    observers of an owned table and stops below it; ownership is by table
    (`flecs_component_get_table`, 324), so a DontFragment C is never owned.
  - Adding `(ChildOf, p)` to x (ChildOf storage): OnAdd for the pair, then
    `flecs_emit_forward` (799-888): the reachable list of `(ChildOf, p)`
    (`flecs_reachable_cache_ensure`, 708-780: p's table type, and for a
    `(ChildOf, pp)` pair or the `Parent` component, recursively the
    reachable list of pp's record, 740-759) gets OnAdd for x unless x's
    table owns it (`flecs_emit_forward_id`, 613-706, 662-681), then the
    downward propagation from x (835-888).  A DontFragment C is never in a
    table type: nothing is reachable.
  - Replacing `(ChildOf, q)` by `(ChildOf, p)` (exclusive): the table move
    emits OnRemove for the removed pair first (`flecs_actions_move_remove`,
    component_actions.c 435-...), with the same forward, then the OnAdd.
  - The `Parent` component: its OnSet (and OnRemove) is re-emitted as the
    OnAdd (OnRemove) of `(ChildOf, parent)` (observable.c 1160-1183:
    `pdesc.event = event == EcsOnSet ? EcsOnAdd : event`).  Setting it
    again to another parent runs the `on_replace` hook
    (`flecs_on_replace_parent`, storage/non_fragmenting_childof.c 113-197:
    the ordered children, the name index, the depth) and then OnSet: the
    OnAdd of `(ChildOf, p)` and its forward.  No OnRemove of `(ChildOf, q)`
    is emitted anywhere, and nothing forwards q's components as removed.

  Documented (ObserversManual.md "OnAdd Events", "OnRemove Events", "Event
  Propagation", "Event Forwarding": "adding a pair results in forwarded
  OnAdd events, and removing a pair results in forwarded OnRemove events";
  HierarchiesManual.md: "Relationship traversal works for both storages
  (`Position(up)` ...)", "Queries with `ChildOf` terms work with both
  storages"):
  - P-EV1: a delivered OnAdd or OnRemove names the source up traversal
    finds, once;
  - P-EV2: an entity that gains C gets an OnAdd, one that loses C an
    OnRemove;
  - P-EV6 (new): a `(ChildOf, *)` observer gets OnAdd for the new parent
    and OnRemove for the old one when an entity's parent changes, with
    either storage (flecs's own `Observer_on_add_childof_wildcard_w_parent_
    component` expects the OnAdd of the new parent after a reparent, and
    `Observer_on_remove_childof_w_parent_component` the OnRemove when the
    Parent component is removed).
-/
import FlecsLean.Search2

namespace Flecs.EvHier

inductive Stor | table | dontFragment
  deriving Repr, BEq, Inhabited, DecidableEq

inductive HS | childOf | parent
  deriving Repr, BEq, Inhabited, DecidableEq

def HS.show : HS → String | .childOf => "ChildOf" | .parent => "Parent"

structure E where
  own : Option Nat := none
  par : Option Nat := none
  deriving Repr, BEq, Inhabited, DecidableEq

abbrev St := Array E

def ent (st : St) (x : Nat) : E := st.getD x {}

def depth : Nat := 6

def children (st : St) (x : Nat) : List Nat :=
  (List.range st.size).filter (fun y => (ent st y).par == some x)

/-- `C(self|up ChildOf)`: x's own C, else the nearest ancestor's. -/
def src (st : St) : Nat → Nat → Option Nat
  | 0, _ => none
  | f + 1, x => if (ent st x).own.isSome then some x else
      match (ent st x).par with
      | some p => src st f p
      | none => none

def tableOwns (stor : Stor) (st : St) (x : Nat) : Bool :=
  stor == .table && (ent st x).own.isSome

/-- The propagation below x with source s: every descendant reached, until
    a table that owns C (observable.c 310-376). -/
def prop (stor : Stor) (st : St) (s : Nat) : Nat → Nat → List (Nat × Nat)
  | 0, _ => []
  | f + 1, x => (children st x).flatMap (fun y =>
      if tableOwns stor st y then [] else (y, s) :: prop stor st s f y)

/-- The reachable list of `(ChildOf, p)` (observable.c 708-780): C from
    the nearest of p and its ancestors whose table has it. -/
def reach (stor : Stor) (st : St) (p : Nat) : List Nat :=
  if stor == .dontFragment then [] else (src st depth p).toList

inductive Ev | onAdd | onRemove | pairAdd | pairRemove
  deriving Repr, BEq, Inhabited, DecidableEq

def Ev.show : Ev → String
  | .onAdd => "OnAdd" | .onRemove => "OnRemove"
  | .pairAdd => "OnAdd (ChildOf, *)" | .pairRemove => "OnRemove (ChildOf, *)"

inductive Op
  /-- `ecs_set(world, x, C, {v})` -/
  | set (x v : Nat)
  /-- `ecs_remove(world, x, C)` -/
  | remove (x : Nat)
  /-- x's parent becomes p (p < x): `ecs_add_pair(x, EcsChildOf, p)` or
      `ecs_set(x, EcsParent, {p})`, by x's storage -/
  | link (x p : Nat)
  /-- `ecs_remove_pair(x, EcsChildOf, EcsWildcard)` or
      `ecs_remove(x, EcsParent)` -/
  | unlink (x : Nat)
  deriving Repr, BEq, Inhabited, DecidableEq

structure Prog where
  stor : Stor
  hs : Array HS
  ops : List Op
  deriving Inhabited

def showOp (hs : Array HS) : Op → String
  | .set x v => s!"ecs_set(e{x}, C, {v})"
  | .remove x => s!"ecs_remove(e{x}, C)"
  | .link x p => if hs.getD x .childOf == .childOf then s!"ecs_add_pair(e{x}, EcsChildOf, e{p})" else s!"ecs_set(e{x}, EcsParent, {"{"}e{p}{"}"})"
  | .unlink x => if hs.getD x .childOf == .childOf then s!"ecs_remove_pair(e{x}, EcsChildOf, *)" else s!"ecs_remove(e{x}, EcsParent)"

def sshow : Stor → String | .table => "table" | .dontFragment => "DontFragment"

instance : Repr Prog := ⟨fun p _ => .text s!"C {sshow p.stor}; storages {(List.range p.hs.size).map (fun x => s!"e{x}:{(p.hs.getD x .childOf).show}")}; calls {p.ops.map (showOp p.hs)}"⟩

/-- The forward of a pair `(ChildOf, p)` added to (or removed from) x, in
    the state where the pair is present: x's event unless its table owns
    C, then the downward propagation from x (observable.c 799-888). -/
def forward (stor : Stor) (st : St) (k : Ev) (x p : Nat) : List (Ev × Nat × Nat) :=
  let r := reach stor st p
  if tableOwns stor st x then [] else
  r.map (fun s => (k, x, s)) ++ r.flatMap (fun s => (prop stor st s depth x).map (fun (y, s') => (k, y, s')))

/-- One call: the new state and the events delivered, as (event, entity,
    source); a pair event's "source" is the parent. -/
def step (stor : Stor) (hs : Array HS) (st : St) (op : Op) : St × List (Ev × Nat × Nat) :=
  match op with
  | .set x v =>
    if x ≥ st.size then (st, []) else
    let had := (ent st x).own.isSome
    let st' := st.modify x (fun e => { e with own := some v })
    if had then (st', []) else
    (st', (Ev.onAdd, x, x) :: (prop stor st' x depth x).map (fun (y, s) => (Ev.onAdd, y, s)))
  | .remove x =>
    if x ≥ st.size || (ent st x).own.isNone then (st, []) else
    let evs := (Ev.onRemove, x, x) :: (prop stor st x depth x).map (fun (y, s) => (Ev.onRemove, y, s))
    (st.modify x (fun e => { e with own := none }), evs)
  | .link x p =>
    if x ≥ st.size || p ≥ x then (st, []) else
    -- Round 9: setting the Parent component to the parent the entity already
    -- has: the on_replace hook does nothing (non_fragmenting_childof.c
    -- 138-144), but flecs_copy_id still emits OnSet (entity.c 838-839),
    -- which observable.c 1160-1183 re-emits as the OnAdd of (ChildOf, p),
    -- with its forward.  With ChildOf storage the add is a no-op.
    if (ent st x).par == some p then
      (if hs.getD x .childOf == .parent then (st, (Ev.pairAdd, x, p) :: forward stor st .onAdd x p) else (st, []))
    else
    let old := (ent st x).par
    let st' := st.modify x (fun e => { e with par := some p })
    let add := (Ev.pairAdd, x, p) :: forward stor st' .onAdd x p
    if hs.getD x .childOf == .childOf then
      match old with
      -- the move: OnRemove for (ChildOf, q) and its forward, then the add
      | some q => (st', (Ev.pairRemove, x, q) :: forward stor st .onRemove x q ++ add)
      | none => (st', add)
    -- Parent: on_replace, then OnSet -> OnAdd (ChildOf, p): no OnRemove
    else (st', add)
  | .unlink x =>
    if x ≥ st.size then (st, []) else
    match (ent st x).par with
    | none => (st, [])
    | some q =>
      let st' := st.modify x (fun e => { e with par := none })
      (st', (Ev.pairRemove, x, q) :: forward stor st .onRemove x q)

/-- The documented events of a call (P-EV2, P-EV6). -/
def expected (pre post : St) (op : Op) : List (Ev × Nat × Nat) := Id.run do
  let mut out := []
  for y in List.range post.size do
    match src pre depth y, src post depth y with
    | none, some s => out := out ++ [(Ev.onAdd, y, s)]
    | some s, none => out := out ++ [(Ev.onRemove, y, s)]
    | _, _ => pure ()
  match op with
  | .link x p =>
    if (ent pre x).par != (ent post x).par then
      if let some q := (ent pre x).par then out := out ++ [(Ev.pairRemove, x, q)]
      out := out ++ [(Ev.pairAdd, x, p)]
  | .unlink x =>
    if let some q := (ent pre x).par then out := out ++ [(Ev.pairRemove, x, q)]
  | _ => pure ()
  return out

def why (stor : Stor) (hs : Array HS) (op : Op) (k : Ev) : String :=
  match op with
  | .link x _ =>
    if hs.getD x .childOf == .parent && (k == .onRemove || k == .pairRemove) then
      "setting the Parent component to another parent runs its on_replace hook (non_fragmenting_childof.c 113-197) and emits OnSet, which observable.c 1160-1183 re-emits as the OnAdd of (ChildOf, new parent) only: nothing emits the OnRemove of (ChildOf, old parent) or forwards the old parent's components as removed"
    else if stor == .dontFragment then
      "the reachable ids of (ChildOf, p) are p's table type and its ancestors' (observable.c 708-780), which a DontFragment component is never in"
    else "the forward does not reach it"
  | .set _ _ | .remove _ =>
    if stor == .dontFragment then "flecs_emit_propagate_id_for_range decides ownership by the table (observable.c 324); a DontFragment component is in no table"
    else "the propagation does not reach it"
  | .unlink _ => if stor == .dontFragment then "nothing is reachable for a DontFragment component (observable.c 708-780)" else "the forward does not reach it"

def checkStep (stor : Stor) (hs : Array HS) (pre : St) (op : Op) : St × List (String × String) := Id.run do
  let (post, got) := step stor hs pre op
  let mut out := []
  let o := showOp hs op
  let mut seen : List (Ev × Nat × Nat) := []
  for (k, x, s) in got do
    -- Round 9, P-EV7: an OnAdd only when the entity gains the id
    -- (ObserversManual.md "OnAdd Events": "An event only fires when the
    -- component is actually added to the entity, so not on each add
    -- operation")
    if k == .pairAdd && (ent pre x).par == some s then
      out := out ++ [("P-EV7 OnAdd only when added", s!"pair: after {o}, the (ChildOf, *) OnAdd observer was invoked for e{x} and e{s}, but e{x}'s parent was already e{s} ({(hs.getD x .childOf).show} storage): the on_replace hook skips an unchanged parent (non_fragmenting_childof.c 138-144), yet flecs_copy_id emits OnSet (entity.c 838-839), which observable.c 1160-1183 re-emits as OnAdd (ChildOf, parent)")]
    let sameParent := match op with | .link x' p' => (ent pre x').par == some p' | _ => false
    if sameParent && k == .onAdd && src pre depth x == some s && src post depth x == some s then
      out := out ++ [("P-EV7 OnAdd only when added", s!"component: after {o}, the OnAdd observer was invoked for e{x} with source e{s}, but e{x} already had C from e{s} ({sshow stor}): the re-emitted OnAdd of an unchanged (ChildOf, parent) forwards the parent's components again (observable.c 1160-1183, 799-888)")]
    if k == .pairAdd || k == .pairRemove then
      seen := seen ++ [(k, x, s)]; continue
    if seen.contains (k, x, s) then
      out := out ++ [("P-EV1 OnAdd/OnRemove follow up traversal", s!"twice: after {o} ({sshow stor}), {k.show} for e{x} with source e{s} twice")]
    else if x != s then
      let view := if k == .onAdd then src post depth x else src pre depth x
      if view != some s then
        let lead := if (k == .onAdd && (ent post x).own.isSome) || (k == .onRemove && (ent pre x).own.isSome) then "owner: " else "other source: "
        let has := match view with | some c => s!"e{c}" | none => "nothing"
        out := out ++ [("P-EV1 OnAdd/OnRemove follow up traversal", s!"{lead}after {o} ({sshow stor}), the {k.show} observer was invoked for e{x} with source e{s}, but {if k == .onAdd then "after" else "before"} the call e{x}'s C is {has}: {why stor hs op k}")]
    seen := seen ++ [(k, x, s)]
  for (k, x, s) in expected pre post op do
    if !got.contains (k, x, s) then
      if k == .pairAdd || k == .pairRemove then
        out := out ++ [("P-EV6 ChildOf pair events with both storages", s!"missing {k.show}: after {o}, e{x}'s parent was e{s} and is {match (ent post x).par with | some p => s!"e{p}" | none => "none"} ({(hs.getD x .childOf).show} storage), but the (ChildOf, *) {if k == .pairAdd then "OnAdd" else "OnRemove"} observer was not invoked for e{x} and e{s}: {why stor hs op k}")]
      else
        out := out ++ [("P-EV2 OnAdd/OnRemove delivered", s!"missing {k.show}: after {o} ({sshow stor}), e{x} ({(hs.getD x .childOf).show} storage) {if k == .onAdd then "now has" else "no longer has"} C (from e{s}), but the {k.show} observer was not invoked for it: {why stor hs op k}")]
  return (post, out)

def check (p : Prog) : List (String × String) := Id.run do
  let mut st : St := Array.replicate p.hs.size {}
  let mut out := []
  for op in p.ops do
    let (st', vs) := checkStep p.stor p.hs st op
    out := out ++ vs
    st := st'
  return out.eraseDups

def trace (p : Prog) : List (List (Ev × Nat × Nat)) := Id.run do
  let mut st : St := Array.replicate p.hs.size {}
  let mut out := []
  for op in p.ops do
    let (st', e) := step p.stor p.hs st op
    out := out ++ [e]
    st := st'
  return out

section
variable {m : Type → Type} [Monad m] [Pick m]

def genOp (nents : Nat) : m Op := do
  match (← Pick.pick "eh.call" 4) with
  | 0 => return .set (← Pick.pick "eh.e" nents) 1
  | 1 => return .remove (← Pick.pick "eh.e" nents)
  | 2 => return .link (← Pick.pick "eh.e" nents) (← Pick.pick "eh.p" nents)
  | _ => return .unlink (← Pick.pick "eh.e" nents)

def genProg (nents len : Nat) : m Prog := do
  let stor ← pickOf "eh.storage" #[Stor.table, .dontFragment]
  let mut hs := #[]
  for _ in [0:nents] do hs := hs.push (← pickOf "eh.hs" #[HS.childOf, .parent])
  let mut ops := []
  for _ in [0:len] do ops := ops ++ [← genOp nents]
  return { stor, hs, ops }

end

def shrink (p : Prog) : List Prog :=
  (List.range p.ops.length).map (fun i => { p with ops := p.ops.eraseIdx i })

/-- The C tests' programs.  e0, e1 parents; e2 the child; e3 a grandchild. -/
def cases : List (String × Prog) := [
  ("parent_reparent_on_remove (F57): e0 has C, e2 = Parent child of e0, then Parent set to e1 (no C)",
    { stor := .table, hs := #[.childOf, .childOf, .parent], ops := [.set 0 1, .link 2 0, .link 2 1] }),
  ("control: the same with ChildOf storage",
    { stor := .table, hs := #[.childOf, .childOf, .childOf], ops := [.set 0 1, .link 2 0, .link 2 1] }),
  ("F57 with a grandchild e3 (Parent child of e2)",
    { stor := .table, hs := #[.childOf, .childOf, .parent, .parent], ops := [.set 0 1, .link 2 0, .link 3 2, .link 2 1] }),
  ("control: the Parent component removed (OnRemove forwarded)",
    { stor := .table, hs := #[.childOf, .childOf, .parent], ops := [.set 0 1, .link 2 0, .unlink 2] }),
  ("F50 (b) with Parent storage: e0 has C (DontFragment), e2 = ecs_new_w_parent(e0)",
    { stor := .dontFragment, hs := #[.childOf, .childOf, .parent], ops := [.set 0 1, .link 2 0] }),
  ("F50 (b), ChildOf storage (round 7, confirmed)",
    { stor := .dontFragment, hs := #[.childOf, .childOf, .childOf], ops := [.set 0 1, .link 2 0] }),
  ("F48 (b) with Parent storage: e2 (Parent child of e0) owns C (DontFragment), e3 child of e2; C set on e0",
    { stor := .dontFragment, hs := #[.childOf, .childOf, .parent, .parent], ops := [.set 2 1, .link 2 0, .link 3 2, .set 0 1] }),
  ("control: the same with a table component",
    { stor := .table, hs := #[.childOf, .childOf, .parent, .parent], ops := [.set 2 1, .link 2 0, .link 3 2, .set 0 1] }),
  ("parent_set_same_parent_on_add (round 9): e0 has C; e2 = Parent child of e0, e3 = Parent child of e2; Parent of e2 set to e0 again",
    { stor := .table, hs := #[.childOf, .childOf, .parent, .parent], ops := [.set 0 1, .link 2 0, .link 3 2, .link 2 0] }),
  ("control (round 9): the same with ChildOf storage",
    { stor := .table, hs := #[.childOf, .childOf, .childOf, .childOf], ops := [.set 0 1, .link 2 0, .link 3 2, .link 2 0] }) ]

end Flecs.EvHier
