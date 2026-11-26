/-
  Round 9: `select_or` over an unwritten `$this` whose chain has up and
  self|up terms, with the iterator's field state, transcribed from flecs
  v4.2.0.  Round 7's `OrVM` had self terms only and compared entity sets;
  this model follows what a result says about its field:
  `it->ids`, `it->trs`, `it->columns`, `it->sources` and the field's bit in
  `it->up_fields` (the "source set" flag).

  The ops, for one Or field (all terms of a chain share it):
  - self select, `flecs_query_select_w_id` (query/engine/eval.c 52-133):
    `flecs_query_set_match` (eval_utils.c 383-399) sets `ids` and `trs`, and
    `flecs_query_it_set_tr` (eval_utils.c 359-369) sets the column only when
    `!sources[f] && !(up_fields & bit)`, else -1.  It touches neither the
    source nor the flag.
  - up select, `flecs_query_up_select` (eval_up.c 124-283) with self=false:
    before each table it resets `sources[f] = 0` (205-207), selects a table
    with the component that has traversable entities (`flecs_query_up_
    select_table`, 11-66), sets `sources[f]` to each traversable entity
    (`flecs_query_up_find_next_traversable`, 69-120, 96-99), and yields the
    tables of the down cache (trav_down_cache.c: breadth first; a table that
    owns the component and has traversable entities is a leaf) with
    `flecs_set_source_set_flag` (eval_utils.c 52-59, eval_up.c 280).  When
    it is exhausted, `sources[f]` is 0 again; the flag stays set.
  - self|up select: the same with self=true: each table with the component
    is yielded first with the flag reset and the column restored
    (eval_up.c 220-231); the down cache skips tables that own it.
  - with forms ($this written, used by the duplicate check):
    `flecs_query_with` (eval.c 150-249: `set_match`), `flecs_query_up_with`
    (eval_up.c 452-546: on success `flecs_query_up_set_fields`, 285-301,
    sets source, tr, id and the flag; on failure nothing),
    `flecs_query_self_up_with` (548-590: resets the flag first, even when
    it then fails; on a self match source 0, flag reset, column restored).
  - `flecs_query_select_or` (eval.c 1390-1508): a result of the first term
    is yielded as is (1418-1420).  A result of a later term is checked
    against the earlier terms ($this marked written, 1461-1467; a failing
    term falls through to the next, `flecs_query_end_block_or`,
    compiler_term.c 282-305).  A duplicate skips the result (1473-1477, 1488-1490)
    without restoring anything.  Otherwise only `ids`, `trs` and `columns`
    of the field are restored (1492-1495).
  - At the yield a debug build checks the columns (`flecs_iter_assert_
    columns`, eval_iter.c 253-273): `columns[f]` must be `tr->column` when
    `tr && !sources[f] && !(up_fields & bit)`, else -1.
  - `ecs_field` (iter.c 112-160): a column >= 0 reads `it->table`'s column;
    else `flecs_field_shared` (206-246) reads the source entity's table; a
    source 0 is `flecs_entities_get(world, 0)`, which asserts "entity 0
    does not exist" (entity_index.c 74-75) in a debug build and reads a NULL
    table in a release build.  A source whose table lacks the id reads a
    NULL table record (243-244).

  Property P-OR1 (new): a result of an Or chain describes the term that
  matched it: `ecs_field_src` is 0 for a self match and the matched
  ancestor for an up match (Queries.md "Source": "Returns 0, meaning entity
  is stored in it.entities"; flecs.h `ecs_field_src`: "the entity on which
  the field was matched"), and `ecs_field` reads that entity's component
  (Queries.md "Or Operator": "We can only use ecs_field if the field type is
  the same for all results").  P-OR2: each entity once (the duplicate
  check's purpose, eval.c 1424-1426).  P1: no crash or abort.
-/
import FlecsLean.Search2

namespace Flecs.OrUp

/-- An entity: its own components (0 = Position, 1 = Velocity, both data
    components) and its ChildOf parent. -/
structure E where
  own : List Nat := []
  par : Option Nat := none
  deriving Repr, BEq, Inhabited, DecidableEq

inductive K | self | up | selfUp
  deriving Repr, BEq, Inhabited, DecidableEq

def K.show : K → String | .self => "" | .up => "(up)" | .selfUp => "(self|up)"

def cname (c : Nat) : String := if c == 0 then "Position" else "Velocity"

structure Prog where
  ents : Array E
  alts : List (K × Nat)
  deriving Inhabited, BEq

def ent (p : Prog) (x : Nat) : E := p.ents.getD x {}

/-- A table: own components and parent; entities in row order.  Tables are
    created in the order of their first entity. -/
structure Tab where
  own : List Nat
  par : Option Nat
  ents : List Nat
  deriving Repr, BEq, Inhabited

def tables (p : Prog) : Array Tab := Id.run do
  let mut ts : Array Tab := #[]
  for x in List.range p.ents.size do
    let e := ent p x
    match ts.findIdx? (fun t => t.own == e.own && t.par == e.par) with
    | some i => ts := ts.modify i (fun t => { t with ents := t.ents ++ [x] })
    | none => ts := ts.push { own := e.own, par := e.par, ents := [x] }
  return ts

def tabOf (ts : Array Tab) (x : Nat) : Nat := (ts.findIdx? (·.ents.contains x)).getD 0

def colOf (t : Tab) (c : Nat) : Int :=
  match t.own.idxOf? c with | some i => i | none => -1

def hasChildren (p : Prog) (x : Nat) : Bool := p.ents.any (·.par == some x)

def traversable (p : Prog) (t : Tab) : Bool := t.ents.any (hasChildren p)

/-- The nearest strict ancestor that owns c. -/
def upSrc (p : Prog) (c : Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | f + 1, x => match (ent p x).par with
    | none => none
    | some q => if (ent p q).own.contains c then some q else upSrc p c f q

def chainOk (p : Prog) (x : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | f + 1, y => match (ent p y).par with
    | none => true
    | some q => q != x && q < p.ents.size && chainOk p x f q

def acyclic (p : Prog) : Bool :=
  (List.range p.ents.size).all fun x => chainOk p x (p.ents.size + 1) x

/-- The down cache of `(ChildOf, x)` for c (trav_down_cache.c): the tables
    of x's children (table cache order), skipping tables that own c when
    `self`, a traversable table that owns c being a leaf otherwise; then,
    breadth first, the walk below the non-leaf tables' traversable
    entities. -/
def downElems (p : Prog) (ts : Array Tab) (c : Nat) (self : Bool) : Nat → Nat → List Nat
  | 0, _ => []
  | f + 1, x =>
    let lvl := (List.range ts.size).filter fun i =>
      let t := ts.getD i default
      t.par == some x && !(self && t.own.contains c)
    let below := lvl.flatMap fun i =>
      let t := ts.getD i default
      let leaf := !self && traversable p t && t.own.contains c
      if leaf then [] else (t.ents.filter (hasChildren p)).flatMap (downElems p ts c self f)
    lvl ++ below

/-- The field's state in the iterator. -/
structure F where
  ids : Nat := 0
  tr : Option (Nat × Nat) := none
  col : Int := -1
  src : Option Nat := none
  up : Bool := false
  deriving Repr, BEq, Inhabited

/-- `flecs_query_it_set_tr` + `it->ids`: `flecs_query_set_match`. -/
def setMatch (ts : Array Tab) (f : F) (t c : Nat) : F :=
  { f with tr := some (t, c), ids := c,
           col := if f.src.isNone && !f.up then colOf (ts.getD t default) c else -1 }

/-- One step of a select: a change of the field state, then maybe a result
    (table, expected source). -/
abbrev Step := (F → F) × Option (Nat × Option Nat)

def tablesWith (ts : Array Tab) (c : Nat) : List Nat :=
  (List.range ts.size).filter (fun i => (ts.getD i default).own.contains c)

def selectSteps (p : Prog) (ts : Array Tab) : K × Nat → List Step
  | (.self, c) => (tablesWith ts c).map fun t => ((fun (f : F) => setMatch ts f t c), some (t, none))
  | (.up, c) =>
    let per := (tablesWith ts c).flatMap fun t =>
      let tab := ts.getD t default
      let start : Step := ((fun (f : F) => setMatch ts { f with src := none } t c), none)
      if !traversable p tab then [start] else
      start :: (tab.ents.filter (hasChildren p)).flatMap fun x =>
        ((fun (f : F) => { f with src := some x, col := -1 }), none) ::
        (downElems p ts c false (p.ents.size + 1) x).map fun d =>
          ((fun (f : F) => { f with up := true, col := -1 }), some (d, some x))
    per ++ [((fun (f : F) => { f with src := none }), none)]
  | (.selfUp, c) =>
    let per := (tablesWith ts c).flatMap fun t =>
      let tab := ts.getD t default
      ((fun (f : F) => let f := setMatch ts { f with src := none } t c
                 { f with up := false, col := colOf tab c }), some (t, none)) ::
      (tab.ents.filter (hasChildren p)).flatMap fun x =>
        ((fun (f : F) => { f with src := some x, col := -1 }), none) ::
        (downElems p ts c true (p.ents.size + 1) x).map fun d =>
          ((fun (f : F) => { f with up := true, col := -1 }), some (d, some x))
    per ++ [((fun (f : F) => { f with src := none }), none)]

/-- A with form on table d: success, and the field state after it (kept
    even on failure: `flecs_query_self_up_with` resets the flag first). -/
def withAlt (p : Prog) (ts : Array Tab) (f : F) (d : Nat) : K × Nat → Bool × F
  | (k, c) =>
    let tab := ts.getD d default
    let x := tab.ents.headD 0
    let upw : F → Bool × F := fun f =>
      match upSrc p c (p.ents.size + 1) x with
      | some s => (true, { f with src := some s, tr := some (tabOf ts s, c), col := -1, ids := c, up := true })
      | none => (false, f)
    match k with
    | .self => if tab.own.contains c then (true, setMatch ts f d c) else (false, f)
    | .up => upw f
    | .selfUp =>
      let f := { f with up := false }
      if tab.own.contains c then
        (true, { setMatch ts f d c with src := none, up := false, col := colOf tab c })
      else upw f

/-- A yielded result: the term index, the table, the expected source, and
    the field state. -/
structure R where
  alt : Nat
  tab : Nat
  exp : Option Nat
  f : F
  deriving Repr, Inhabited

/-- `flecs_query_select_or`: every result of the chain. -/
def run (p : Prog) : List R := Id.run do
  let ts := tables p
  let mut f : F := {}
  let mut out : List R := []
  let mut i := 0
  for a in p.alts do
    for (g, res) in selectSteps p ts a do
      f := g f
      match res with
      | none => pure ()
      | some (d, exp) =>
        if i == 0 then out := out ++ [{ alt := i, tab := d, exp, f }]
        else
          let prev := f
          let mut dup := false
          for b in p.alts.take i do
            if dup then continue
            let (ok, f') := withAlt p ts f d b
            f := f'
            if ok then dup := true
          if !dup then
            f := { f with ids := prev.ids, tr := prev.tr, col := prev.col }
            out := out ++ [{ alt := i, tab := d, exp, f }]
    i := i + 1
  return out

/-- What `ecs_field` reads for a result: some (entity, component) read, or
    none for a crash; `abort` when a debug build asserts first. -/
inductive Read | value (x c : Nat) | entity0 | nullRecord
  deriving Repr, BEq, Inhabited

def read (p : Prog) (ts : Array Tab) (r : R) : Read :=
  let tab := ts.getD r.tab default
  if r.f.col ≥ 0 then .value (tab.ents.headD 0) (tab.own.getD r.f.col.toNat 0)
  else match r.f.src with
    | none => .entity0
    | some s => if (ent p s).own.contains r.f.ids then .value s r.f.ids else .nullRecord

def expectedCol (ts : Array Tab) (f : F) : Int :=
  match f.tr with
  | some (t, c) => if f.src.isNone && !f.up then colOf (ts.getD t default) c else -1
  | none => -1

def showSrc : Option Nat → String | none => "0" | some s => s!"e{s}"

instance : Repr Prog := ⟨fun p _ =>
  let es := (List.range p.ents.size).map fun x =>
    let e := ent p x
    s!"e{x}:[{", ".intercalate (e.own.map cname)}]{match e.par with | some q => s!" ChildOf e{q}" | none => ""}"
  let q := " || ".intercalate (p.alts.map fun (k, c) => s!"{cname c}{k.show}")
  .text s!"{es}; query {q}"⟩

def check (p : Prog) : List (String × String) := Id.run do
  if !acyclic p || p.alts.isEmpty then return []
  let ts := tables p
  let rs := run p
  let q := " || ".intercalate (p.alts.map fun (k, c) => s!"{cname c}{k.show}")
  let mut out := []
  let mut seen : List Nat := []
  let mut aborted := false
  for r in rs do
    let tab := ts.getD r.tab default
    let (k, c) := p.alts.getD r.alt default
    let who := s!"result {tab.ents.map (s!"e{·}")} from term {r.alt + 1} ({cname c}{k.show}) of {q}"
    let st := s!"columns {r.f.col}, source {showSrc r.f.src}, up flag {r.f.up}"
    for x in tab.ents do
      if seen.contains x then
        out := out ++ [("P-OR2 each entity once", s!"{who}: e{x} returned twice")]
    seen := seen ++ tab.ents
    let ec := expectedCol ts r.f
    if r.f.col != ec then
      out := out ++ [("P1 no crash or abort", s!"abort (debug): {who}: {st}; flecs_iter_assert_columns expects {ec} (eval_iter.c 253-273): the duplicate check's flecs_query_self_up_with reset the up flag (eval_up.c 557) after select_or saved the column, and select_or restores only ids, trs and columns (eval.c 1492-1495)")]
      aborted := true
      break
    if r.f.src != r.exp then
      out := out ++ [("P-OR1 an Or result names its source", s!"wrong source: {who}: ecs_field_src is {showSrc r.f.src}, expected {showSrc r.exp} ({st}): select_or restores only ids, trs and columns (eval.c 1492-1495); the source {if r.f.src.isSome then "was written by an earlier term's duplicate check (flecs_query_up_set_fields, eval_up.c 285-301)" else "is reset but the up flag set by an earlier up term stays (eval_up.c 280)"}")]
    let want := match r.exp with | none => (tab.ents.headD 0, c) | some s => (s, c)
    match read p ts r with
    | .value x c' =>
      if (x, c') != want then
        out := out ++ [("P-OR1 an Or result names its source", s!"wrong value: {who}: ecs_field reads {cname c'} of e{x}, expected {cname want.2} of e{want.1} ({st})")]
    | .entity0 =>
      out := out ++ [("P1 no crash or abort", s!"crash: {who}: {st}: ecs_field takes the shared path with source 0, flecs_entities_get(world, 0): debug assert \"entity 0 does not exist\" (entity_index.c 74-75), release NULL table; the up flag was left set by term {(p.alts.findIdx? (·.1 != .self)).getD 0 + 1}'s select (eval_up.c 280) and select (eval.c 129) computes the column with it (eval_utils.c 366-368)")]
    | .nullRecord =>
      out := out ++ [("P1 no crash or abort", s!"crash: {who}: {st}: ecs_field reads {cname r.f.ids} from the stale source, whose table lacks it: flecs_component_get_table returns NULL (iter.c 242-244)")]
  -- every entity that matches a term is returned (a debug abort ends the
  -- iteration, so the rest is not checked then)
  for x in List.range (if aborted then 0 else p.ents.size) do
    let e := ent p x
    let m := p.alts.any fun (k, c) => match k with
      | .self => e.own.contains c
      | .up => (upSrc p c (p.ents.size + 1) x).isSome
      | .selfUp => e.own.contains c || (upSrc p c (p.ents.size + 1) x).isSome
    if m && !seen.contains x then
      out := out ++ [("P-OR2 each entity once", s!"missing: e{x} matches {q} but is not returned")]
  return out.eraseDups

section
variable {m : Type → Type} [Monad m] [Pick m]

def genProg (nents nalts : Nat) : m Prog := do
  let mut es := #[]
  for _ in [0:nents] do
    let own ← pickOf "ou.own" #[[], [0], [1], [0, 1]]
    let pk ← Pick.pick "ou.par" (nents + 1)
    es := es.push { own, par := if pk == 0 then none else some (pk - 1) }
  let mut alts := []
  for _ in [0:nalts] do
    let k ← pickOf "ou.kind" #[K.self, .up, .selfUp]
    let c ← Pick.pick "ou.comp" 2
    alts := alts ++ [(k, c)]
  return { ents := es, alts }

end

/-- Strictly smaller candidates only (a candidate equal to the program would
    make `gshrink` loop). -/
def shrink (p : Prog) : List Prog :=
  ((List.range p.ents.size).filter (fun i => !(ent p i).own.isEmpty)).map (fun i => { p with ents := p.ents.modify i (fun e => { e with own := [] }) }) ++
  ((List.range p.ents.size).filter (fun i => (ent p i).par.isSome)).map (fun i => { p with ents := p.ents.modify i (fun e => { e with par := none }) })

/-- The C tests' programs (tables in the order the tests create them). -/
def cases : List (String × Prog) := [
  ("query_or_up_then_self_fields (b): e0 = c [Velocity] ChildOf e2; e1 = e [Velocity]; e2 = p [Position, Velocity]; Position(up) || Velocity",
    { ents := #[{ own := [1], par := some 2 }, { own := [1] }, { own := [0, 1] }], alts := [(.up, 0), (.self, 1)] }),
  ("query_or_up_then_self_fields (a): e0 = p [Position]; e1 = c ChildOf e0; e2 = e [Velocity]; Position(up) || Velocity",
    { ents := #[{ own := [0] }, { par := some 0 }, { own := [1] }], alts := [(.up, 0), (.self, 1)] }),
  ("query_or_self_up_then_self_columns (c): the same world, Position(self|up) || Velocity",
    { ents := #[{ own := [0] }, { par := some 0 }, { own := [1] }], alts := [(.selfUp, 0), (.self, 1)] }),
  ("control: Velocity || Position(up), the self term first",
    { ents := #[{ own := [0] }, { par := some 0 }, { own := [1] }], alts := [(.self, 1), (.up, 0)] }),
  ("control: Position(up) || Velocity without the child (the up term yields nothing)",
    { ents := #[{ own := [0] }, { }, { own := [1] }], alts := [(.up, 0), (.self, 1)] }),
  ("flecs's Traversal_this_or_w_up shape with components: Position(up) || Velocity(up)",
    { ents := #[{ own := [0] }, { own := [1] }, { par := some 0 }, { par := some 1 }], alts := [(.up, 0), (.up, 1)] }),
  ("query_or_self_then_up_fields (d): e0 = x [Velocity]; e1 = D [Position] ChildOf e0; e2 = D2 ChildOf e0; Position || Velocity(up)",
    { ents := #[{ own := [1] }, { own := [0], par := some 0 }, { par := some 0 }], alts := [(.self, 0), (.up, 1)] }),
  ("control (d): Velocity(up) alone",
    { ents := #[{ own := [1] }, { own := [0], par := some 0 }, { par := some 0 }], alts := [(.up, 1)] }) ]

end Flecs.OrUp
