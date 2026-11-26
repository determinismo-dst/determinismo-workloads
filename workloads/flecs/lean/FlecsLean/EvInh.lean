/-
  Round 7: OnAdd, OnRemove and OnSet events for inherited components, the
  three events together, transcribed from flecs v4.2.0 (round 6's OnSetInh
  had OnSet only).

  One component C with `(OnInstantiate, Inherit)` and a storage (table,
  fragmenting Sparse, DontFragment); one observer per event with the default
  term for C, `self|up(IsA)` (validator.c 1613-1616), so each sits in the
  `self_up` list of its event id record.  Every entity is a plain entity
  (no prefabs: `flecs_ignore_observer`, observer.c 253-274, would drop the
  events of prefab entities, and the expectations with them).

  The calls and the events flecs delivers for them:
  - `ecs_set(e, C, v)` when e does not own C: the OnAdd of the add
    (`flecs_actions_on_add_intern`, component_actions.c 286-331; for a
    DontFragment component `flecs_sparse_on_add` reports the new element,
    114-177), then OnSet (641-702).  `flecs_emit` (observable.c 1009-1395)
    invokes the observer for e, then, because e's table holds an entity
    that is the target of a traversable pair (`has_observed`, 1133),
    `flecs_propagate_entities` (571-611) -> `flecs_emit_propagate`
    (440-475) -> `flecs_emit_propagate_id` (378-438) ->
    `flecs_emit_propagate_id_for_range` (310-376): for every entity of
    every `(IsA, e)` table, the self|up observers unless the table owns C
    (`owned = flecs_component_get_table(cr, table) != NULL`, 324; a
    DontFragment component is in no table, so never owned), and the walk
    goes on below every entity of such a table unless it is owned (361).
    When e already owns C, only the OnSet part.
  - `ecs_remove(e, C)` when e owns C: OnRemove for e and the same
    propagation (component_actions.c 333-367), then the OnSet for the value
    now inherited (`flecs_emit_on_set_for_override_on_remove`, observable.c
    951-1002), for e only.
  - `ecs_add_pair(e, EcsIsA, b)`: `flecs_emit` forwards the ids reachable
    through `(IsA, b)` (1196-1237; `flecs_emit_forward`, 799-888):
    `flecs_reachable_cache_ensure` (708-780) lists the Inherit ids of b's
    table type (and, recursively, those of b's own bases that b's table
    does not have); for each element `flecs_emit_forward_id` (613-706)
    invokes the OnAdd observers of the self|up list unless e's table owns
    C (662-681), then the OnSet observers when the element has a column
    (`storage_i != -1`, 684-701; none for a Sparse component).  Then, when
    e is the target of a traversable pair, every element whose id e's
    table does not have is propagated down from e with the OnAdd observers
    only (`er`, 835-888) and the element's source.
  - `ecs_remove_pair(e, EcsIsA, b)`: the same forward with the OnRemove
    observers and no OnSet (`er_fwd` stays NULL, 1196-1237), and the same
    downward propagation.  The override pass (1329-1370) skips the pair: it
    has no type info.

  What the documentation says should be delivered (ObserversManual.md
  "OnAdd Events", "OnRemove Events", "OnSet and Inheritance", "Event
  Propagation", "Event Forwarding"):
  - OnAdd when an entity gets C: its own (an add), or inherited, when it had
    none before; the source is the one up traversal finds ("Only reachable
    components are forwarded ... this ensures consistency with the behavior
    of up traversal in queries"; "Events propagate until a leaf entity is
    found, or an entity with the propagated component is found");
  - OnRemove when an entity's own C is removed, or when it inherited C and
    no longer has it;
  - OnSet in the documented scenarios (round 6), and here also for the
    inheritors of an entity in such a scenario, whose value changes the
    same way (P-OS3: "To ensure that OnSet events can be used reliably to
    detect component changes, events can be produced by operations that
    change inheritance relationships").
-/
import FlecsLean.OnSetInh

namespace Flecs.EvInh
open Flecs.OSI

inductive Ev | onAdd | onRemove | onSet
  deriving Repr, BEq, Inhabited, DecidableEq

def Ev.show : Ev → String
  | .onAdd => "OnAdd" | .onRemove => "OnRemove" | .onSet => "OnSet"

inductive Op
  /-- `ecs_set(world, e, C, {v})` -/
  | set (e v : Nat)
  /-- `ecs_add_pair(world, e, EcsIsA, b)`, b < e -/
  | isa (e b : Nat)
  /-- `ecs_remove(world, e, C)` -/
  | remove (e : Nat)
  /-- `ecs_remove_pair(world, e, EcsIsA, b)` -/
  | unIsa (e b : Nat)
  deriving Repr, BEq, Inhabited, DecidableEq

def showOp : Op → String
  | .set e v => s!"ecs_set(e{e}, C, {v})"
  | .isa e b => s!"ecs_add_pair(e{e}, EcsIsA, e{b})"
  | .remove e => s!"ecs_remove(e{e}, C)"
  | .unIsa e b => s!"ecs_remove_pair(e{e}, EcsIsA, e{b})"

/-- The entity owns C (in its table, or in the sparse set). -/
def owns (st : St) (e : Nat) : Bool := (ent st e).own.isSome

/-- `flecs_component_get_table(cr, table) != NULL`: the entity's table has
    C in its type. -/
def tableOwns (stor : Storage) (st : St) (e : Nat) : Bool :=
  stor != Storage.dontFragment && owns st e

/-- e is the target of an `(IsA, e)` pair (`EcsEntityIsTraversable`). -/
def hasInheritors (st : St) (e : Nat) : Bool :=
  (List.range st.size).any (fun y => (ent st y).isa.contains e)

def sshow : Storage → String
  | .table => "table" | .sparse => "Sparse" | .dontFragment => "DontFragment"

def evs (k : Ev) (l : List (Nat × Nat)) : List (Ev × Nat × Nat) := l.map (fun (x, s) => (k, x, s))

/-- One call: the new state and the events flecs delivers to the three
    observers, as (event, entity, source), in order. -/
def step (stor : Storage) (st : St) (op : Op) : St × List (Ev × Nat × Nat) :=
  match op with
  | .set e v =>
    if e ≥ st.size then (st, []) else
    let had := owns st e
    let st' := st.modify e (fun x => { x with own := some v })
    let prop := propF st' stor e depth e
    let add := if had then [] else (Ev.onAdd, e, e) :: evs .onAdd prop
    (st', add ++ (Ev.onSet, e, e) :: evs .onSet prop)
  | .remove e =>
    if e ≥ st.size || !owns st e then (st, []) else
    let prop := propF st stor e depth e
    let st' := st.modify e (fun x => { x with own := none })
    let ovr := match src st' e with | some s => [(Ev.onSet, e, s)] | none => []
    (st', (Ev.onRemove, e, e) :: evs .onRemove prop ++ ovr)
  | .isa e b =>
    if e ≥ st.size || b ≥ e || (ent st e).isa.contains b then (st, []) else
    let st' := st.modify e (fun x => { x with isa := insertSorted b x.isa })
    let r := reach st' stor b
    let owned := tableOwns stor st' e
    -- flecs_emit_forward_id, element by element: OnAdd, then OnSet when
    -- the element has a column
    let fwd := r.flatMap (fun s =>
      if owned then [] else
      (Ev.onAdd, e, s) :: (if stor == Storage.table then [(Ev.onSet, e, s)] else []))
    -- 835-888: the downward propagation, with the OnAdd observers only
    let down := if hasInheritors st' e && !owned then
      r.flatMap (fun s => evs .onAdd (propF st' stor s depth e)) else []
    (st', fwd ++ down)
  | .unIsa e b =>
    if e ≥ st.size || !(ent st e).isa.contains b then (st, []) else
    let r := reach st stor b
    let owned := tableOwns stor st e
    let fwd := if owned then [] else r.map (fun s => (Ev.onRemove, e, s))
    let down := if hasInheritors st e && !owned then
      r.flatMap (fun s => evs .onRemove (propF st stor s depth e)) else []
    let st' := st.modify e (fun x => { x with isa := x.isa.erase b })
    (st', fwd ++ down)

/-- The documented OnAdd and OnRemove events of a call. -/
def expectedAR (pre post : St) : List (Ev × Nat × Nat) := Id.run do
  let mut out := []
  for x in List.range post.size do
    let op := owns pre x
    let oq := owns post x
    if !op && oq then out := out ++ [(Ev.onAdd, x, x)]
    else if !op && !oq then
      match src pre x, src post x with
      | none, some s => out := out ++ [(Ev.onAdd, x, s)]
      | some s, none => out := out ++ [(Ev.onRemove, x, s)]
      | _, _ => pure ()
    if op && !oq then out := out ++ [(Ev.onRemove, x, x)]
  return out

/-- P-OS3: the inheritors (not the entity of the call) of an entity whose
    value of C changes in a documented OnSet scenario ("Adding an IsA pair",
    "Removing an Override"), when their own value changes with it. -/
def expectedOS3 (pre post : St) (op : Op) : List (Nat × Nat) :=
  let e := match op with | .isa e _ => some e | .remove e => some e | _ => none
  match e with
  | none => []
  | some e =>
    (List.range post.size).filterMap (fun x =>
      if x == e || owns post x || src pre x == src post x then none
      else match src post x with | some s => some (x, s) | none => none)

def why (stor : Storage) (op : Op) : String :=
  match op with
  | .set _ _ | .remove _ =>
    if stor == Storage.dontFragment then
      "flecs_emit_propagate_id_for_range decides ownership by the table (observable.c 324), and a DontFragment component is in no table, so the propagation neither skips an owner nor stops below it"
    else "flecs_emit_propagate walks every (IsA, target) table below the entity (observable.c 310-376), without asking whether another base provides C first"
  | .isa _ _ | .unIsa _ _ =>
    "flecs_emit_forward forwards and propagates every reachable element of the pair (observable.c 799-888), without asking whether another base already provides C"

/-- The properties of one call. -/
def checkStep (stor : Storage) (pre : St) (op : Op) : St × List (String × String) := Id.run do
  let (post, got) := step stor pre op
  let mut out := []
  -- P-EV1: a delivered OnAdd/OnRemove names the source up traversal finds,
  -- for an entity that gains or loses C, once
  let mut seen : List (Ev × Nat × Nat) := []
  for (k, x, s) in got do
    if k == Ev.onSet then continue
    if seen.contains (k, x, s) then
      out := out ++ [("P-EV1 OnAdd/OnRemove follow up traversal", s!"twice: after {showOp op} ({sshow stor}), the {k.show} observer was invoked twice for e{x} with source e{s} (each path to the source is propagated separately)")]
    else if x == s then
      let ok := if k == Ev.onAdd then !owns pre x && owns post x else owns pre x && !owns post x
      if !ok then
        out := out ++ [("P-EV1 OnAdd/OnRemove follow up traversal", s!"self: after {showOp op} ({sshow stor}), {k.show} for e{x} itself, whose own C did not change")]
    else
      let view := if k == Ev.onAdd then src post x else src pre x
      if view != some s then
        let lead := if (k == Ev.onAdd && owns post x) || (k == Ev.onRemove && owns pre x) then "owner: " else "other source: "
        let has := match view with | some c => s!"e{c}" | none => "nothing"
        let when := if k == Ev.onAdd then "after" else "before"
        out := out ++ [("P-EV1 OnAdd/OnRemove follow up traversal", s!"{lead}after {showOp op} ({sshow stor}), the {k.show} observer was invoked for e{x} with source e{s}, but {when} the call e{x}'s C is {has} (its own, or the first base up traversal finds): {why stor op}")]
      else if k == Ev.onRemove && src post x != none && !owns pre x then
        out := out ++ [("P-EV4 OnRemove only when C is gone", s!"still has C: after {showOp op} ({sshow stor}), the OnRemove observer was invoked for e{x} with source e{s}, yet e{x} still sees C from e{(src post x).getD 0}")]
    seen := seen ++ [(k, x, s)]
  -- P-EV2: every documented OnAdd/OnRemove is delivered
  for (k, x, s) in expectedAR pre post do
    if !got.contains (k, x, s) then
      let w := match op with
        | .isa _ b | .unIsa _ b =>
          if stor == Storage.dontFragment then
            s!"the reachable ids of (IsA, e{b}) are its table's type, which a DontFragment component is never in (observable.c 708-780)"
          else "the forward does not reach it"
        | _ => "the propagation does not reach it"
      out := out ++ [("P-EV2 OnAdd/OnRemove delivered", s!"missing {k.show}: after {showOp op} ({sshow stor}), e{x} {if k == Ev.onAdd then "now has" else "no longer has"} C (from e{s}), but the {k.show} observer was not invoked for it: {w}")]
  -- P-OS1 and P-OS2 (round 6), on this model's OnSet events
  let sets := got.filterMap (fun (k, x, s) => if k == Ev.onSet then some (x, s) else none)
  let osiOp : Option OSI.Op := match op with
    | .set e v => some (.set e v) | .isa e b => some (.isa e b) | .remove e => some (.remove e) | .unIsa _ _ => none
  if let some o := osiOp then
    for (x, s) in OSI.expected pre post o do
      if !sets.contains (x, s) then
        out := out ++ [("P-OS1 documented OnSet is delivered", s!"(round 6, F41) after {showOp op} ({sshow stor}): no OnSet for e{x} from e{s}")]
  let mut seenS : List (Nat × Nat) := []
  for (x, s) in sets do
    if seenS.contains (x, s) || src post x != some s then
      out := out ++ [("P-OS2 OnSet reports the entity's value", s!"(round 6, F42/F43) after {showOp op} ({sshow stor}): OnSet for e{x} with source e{s}")]
    seenS := seenS ++ [(x, s)]
  -- P-OS3: the inheritors of the entity of a documented scenario
  for (x, s) in expectedOS3 pre post op do
    if !sets.contains (x, s) then
      let saw := match src pre x with | some c => s!"e{c}'s value" | none => "nothing"
      let ar := if got.any (fun (k, y, _) => y == x && k != Ev.onSet) then
        " (the same call delivered it an OnAdd or OnRemove)" else ""
      out := out ++ [("P-OS3 OnSet reaches inheritors whose value changes", s!"inheritor: after {showOp op} ({sshow stor}), e{x} inherits C through e{match op with | .isa e _ => e | .remove e => e | _ => 0} and its value changed from {saw} to e{s}'s, but no OnSet observer was invoked for it{ar}: the forward propagates only the OnAdd observers down (observable.c 835-888) and the override's OnSet is emitted for the entity alone (951-1002)")]
  return (post, out)

structure Prog where
  storage : Storage
  nents : Nat
  ops : List Op
  deriving Inhabited

instance : Repr Prog := ⟨fun p _ => .text s!"C {sshow p.storage} Inherit; {p.nents} entities; calls {p.ops.map showOp}"⟩

def check (p : Prog) : List (String × String) := Id.run do
  let mut st : St := Array.replicate p.nents {}
  let mut out := []
  for op in p.ops do
    let (st', vs) := checkStep p.storage st op
    out := out ++ vs
    st := st'
  return out.eraseDups

/-- The events of a program, call by call. -/
def trace (p : Prog) : List (List (Ev × Nat × Nat)) := Id.run do
  let mut st : St := Array.replicate p.nents {}
  let mut out := []
  for op in p.ops do
    let (st', e) := step p.storage st op
    out := out ++ [e]
    st := st'
  return out

section
variable {m : Type → Type} [Monad m] [Pick m]

def genOp (nents : Nat) : m Op := do
  match (← Pick.pick "ev.call" 4) with
  | 0 => return .set (← Pick.pick "ev.e" nents) (← pickOf "ev.v" #[1, 2])
  | 1 => return .isa (← Pick.pick "ev.e" nents) (← Pick.pick "ev.b" nents)
  | 2 => return .remove (← Pick.pick "ev.e" nents)
  | _ => return .unIsa (← Pick.pick "ev.e" nents) (← Pick.pick "ev.b" nents)

def genProg (nents len : Nat) : m Prog := do
  let s ← pickOf "ev.storage" #[Storage.table, .sparse, .dontFragment]
  let mut ops := []
  for _ in [0:len] do ops := ops ++ [← genOp nents]
  return { storage := s, nents, ops }

end

def shrink (p : Prog) : List Prog :=
  (List.range p.ops.length).map (fun i => { p with ops := p.ops.eraseIdx i })

/-- The C tests' programs: e0 and e1 bases, e2 the instance (or variant),
    e3 the instance of the variant. -/
def cases : List (String × Prog) := [
  ("propagate_on_add_remove_dont_fragment_owner: e1 owns C, e1 IsA e0, then C is set on and removed from e0 (DontFragment)",
    { storage := .dontFragment, nents := 2, ops := [.set 1 20, .isa 1 0, .set 0 10, .remove 0] }),
  ("control: the same with a table component",
    { storage := .table, nents := 2, ops := [.set 1 20, .isa 1 0, .set 0 10, .remove 0] }),
  ("control: the same with a Sparse component",
    { storage := .sparse, nents := 2, ops := [.set 1 20, .isa 1 0, .set 0 10, .remove 0] }),
  ("the owner's inheritor e2 (DontFragment): the propagation does not stop at e1",
    { storage := .dontFragment, nents := 3, ops := [.set 1 20, .isa 1 0, .isa 2 1, .set 0 10, .remove 0] }),
  ("propagate_on_add_remove_second_base: e2 IsA e0 (C), IsA e1; C set on and removed from e1 (table)",
    { storage := .table, nents := 3, ops := [.set 0 10, .isa 2 0, .isa 2 1, .set 1 20, .remove 1] }),
  ("forward_on_add_second_base: e2 IsA e0 (C), then IsA e1 (C), then the pair is removed (table)",
    { storage := .table, nents := 3, ops := [.set 0 10, .set 1 20, .isa 2 0, .isa 2 1, .unIsa 2 1] }),
  ("forward_on_add_remove_dont_fragment: e1 IsA e0 (C), then the pair is removed (DontFragment)",
    { storage := .dontFragment, nents := 2, ops := [.set 0 10, .isa 1 0, .unIsa 1 0] }),
  ("control: the same with a table component",
    { storage := .table, nents := 2, ops := [.set 0 10, .isa 1 0, .unIsa 1 0] }),
  ("control: the same with a Sparse component",
    { storage := .sparse, nents := 2, ops := [.set 0 10, .isa 1 0, .unIsa 1 0] }),
  ("inheritor_onset_variant_gains_base: e2 IsA e1, then e1 IsA e0 (C) (table)",
    { storage := .table, nents := 3, ops := [.set 0 10, .isa 2 1, .isa 1 0] }),
  ("inheritor_onset_override_removed: e1 IsA e0 (C), e1 owns C, e2 IsA e1; C removed from e1 (table)",
    { storage := .table, nents := 3, ops := [.set 0 10, .isa 1 0, .set 1 20, .isa 2 1, .remove 1] }),
  ("control: e2 IsA e1 after e1 IsA e0 (the documented scenario)",
    { storage := .table, nents := 3, ops := [.set 0 10, .isa 1 0, .isa 2 1] }) ]

end Flecs.EvInh
