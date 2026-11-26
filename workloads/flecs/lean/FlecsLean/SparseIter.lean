/-
  Round 9: iterating a DontFragment component (query/engine/eval_sparse.c)
  while an immediate system changes the component's set, transcribed from
  flecs v4.2.0.

  The storage: a DontFragment component keeps its entities in a sparse set
  (`cr->sparse`).  Its dense array is in insertion order; a removal swaps
  the removed id with the last one and shrinks the count
  (`flecs_sparse_remove`, datastructures/sparse.c 398-...;
  `flecs_sparse_swap_dense`, 177-191).  A removal moves no entity between
  tables, so no table lock sees it.

  The two iterators:
  - The trivial sparse search (`flecs_query_trivial_sparse_search`,
    eval_sparse.c 506-618), used when every term is a self `$this` And term
    on a DontFragment component (validator.c 1902-1942; an uncached query,
    which a system query with no cacheable term is: api.c 149-160).  It
    walks the dense array FORWARD from `op_ctx->cur`, re-reading the count
    at each call, and copies up to FLECS_QUERY_SPARSE_BATCH_SIZE (1024,
    query/types.h 373) ids into a batch (561-575).
  - The VM's sparse select (`flecs_query_sparse_select_id`, 121-182), used
    for a DontFragment term that finds `$this` in a query that is not
    trivial (`Df, Position` uncached).  It walks the dense array BACKWARD
    from the count at its first call, grouping ids of the same table at
    adjacent rows into one range (159-175).  It asserts `cur < count`
    ("sparse iterator invalidated while iterating", 145-146).

  Systems.md "Immediate systems": "Operations passed the iterator's world
  execute immediately"; the only limitation on what they touch is that
  "operations on the iterated over entity must still be deferred".
  Queries.md "Iteration" (C++ each): table locking exists so that moving
  entities does not cause "iterating an entity twice, or missing an
  entity".  With table storage, removing a component from an entity of an
  earlier or a later table neither skips nor repeats another entity.

  flecs's own `DontFragment_add_to_self_while_iterate` (test/query/src/
  DontFragment.c 6427-6469) adds a DontFragment tag to the entities of the
  current result while iterating, without deferring: changing a
  DontFragment id moves no entity, so it is allowed during iteration.  The
  VM's backward walk is what makes removing the current result's id safe:
  the id that moves into its slot was already returned.

  Property P-IT4 (new): removing a DontFragment component during an
  iteration over it (from the current result, or, in an immediate system,
  from another entity) neither skips nor repeats another entity: every
  entity that has the component when the iteration starts is returned
  exactly once, unless it lost the component before its turn (then not at
  all).
-/
import FlecsLean.Search2

namespace Flecs.SparseIter

inductive Mode | trivial | vm
  deriving Repr, BEq, Inhabited, DecidableEq

structure Prog where
  /-- the table of each entity (0: [Position], 1: [Position, Tag]); its row
      is its rank among the entities of that table -/
  tabOf : Array Nat
  mode : Mode
  /-- the batch size, standing for 1024 -/
  batch : Nat := 1
  /-- at the k-th callback: `ecs_remove(it->world, e_x, Df)` -/
  removes : List (Option Nat)
  /-- each callback first removes Df from every entity of its result (the
      "remove while iterating" loop; flecs's own
      `DontFragment_add_to_self_while_iterate` adds a DontFragment id to the
      iterated entities) -/
  removeCur : Bool := false
  deriving Inhabited, BEq

instance : Repr Prog := ⟨fun p _ =>
  .text s!"tables {p.tabOf.toList}; {match p.mode with | .trivial => s!"trivial sparse search, batch {p.batch}" | .vm => "VM sparse select (Df, Position)"}; removes at callbacks {p.removes.map (fun o => match o with | some x => s!"e{x}" | none => "-")}{if p.removeCur then "; each callback removes Df from its result" else ""}"⟩

def rowOf (p : Prog) (x : Nat) : Nat :=
  ((List.range x).filter (fun y => p.tabOf.getD y 0 == p.tabOf.getD x 0)).length

/-- swap-remove: the removed id's slot takes the last id -/
def sparseRemove (d : Array Nat) (x : Nat) : Array Nat :=
  match d.findIdx? (· == x) with
  | none => d
  | some i =>
    let last := d.size - 1
    let d := if i == last then d else d.set! i (d.getD last 0)
    d.pop

structure Out where
  visits : List Nat := []
  removedBefore : List Nat := []
  abort : Bool := false
  deriving Repr, Inhabited

/-- Apply the callback's operations. -/
def callbackOp (p : Prog) (k : Nat) (cur : List Nat) (d : Array Nat) (o : Out) : Array Nat × Out :=
  let d := if p.removeCur then cur.foldl sparseRemove d else d
  match p.removes.getD k none with
  | some x =>
    if !d.contains x then (d, o) else
    let o := if o.visits.contains x then o else { o with removedBefore := o.removedBefore ++ [x] }
    (sparseRemove d x, o)
  | none => (d, o)

def runTrivial (p : Prog) : Out := Id.run do
  let mut d : Array Nat := (List.range p.tabOf.size).toArray
  let mut cur := 0
  let mut o : Out := {}
  let b := max p.batch 1
  let mut done := false
  for k in [0:p.tabOf.size + 1] do
    if done then continue
    let count := d.size
    -- for (; cur < count && n < BATCH; cur ++) (eval_sparse.c 561)
    let batch := (List.range b).filterMap (fun j => if cur + j < count then some (d.getD (cur + j) 0) else none)
    cur := cur + batch.length
    if batch.isEmpty then done := true; continue
    o := { o with visits := o.visits ++ batch }
    let (d', o') := callbackOp p k batch d o
    d := d'; o := o'
  return o

/-- The grouping loop of `flecs_query_sparse_select_id` (159-175): the
    range (row, count) and the new cursor. -/
def groupRange (p : Prog) (d : Array Nat) (t : Nat) : Nat → Nat × Nat × Nat → Nat × Nat × Nat
  | 0, s => s
  | f + 1, (cur, row, count) =>
    if cur == 0 then (cur, row, count) else
    let e' := d.getD (cur - 1) 0
    if p.tabOf.getD e' 0 != t then (cur, row, count) else
    let r' := rowOf p e'
    if r' + 1 == row then groupRange p d t f (cur - 1, row - 1, count + 1)
    else if r' == row + count then groupRange p d t f (cur - 1, row, count + 1)
    else (cur, row, count)

def runVM (p : Prog) : Out := Id.run do
  let mut d : Array Nat := (List.range p.tabOf.size).toArray
  let mut cur := d.size
  let mut o : Out := {}
  let mut done := false
  for k in [0:p.tabOf.size + 1] do
    if done then continue
    if cur == 0 then done := true; continue
    cur := cur - 1
    if cur ≥ d.size then
      o := { o with abort := true }
      done := true; continue
    let e := d.getD cur 0
    let t := p.tabOf.getD e 0
    let (cur', row, count) := groupRange p d t p.tabOf.size (cur, rowOf p e, 1)
    cur := cur'
    let res := (List.range p.tabOf.size).filter (fun y => p.tabOf.getD y 0 == t && rowOf p y ≥ row && rowOf p y < row + count)
    o := { o with visits := o.visits ++ res }
    let (d', o') := callbackOp p k res d o
    d := d'; o := o'
  return o

def run (p : Prog) : Out := match p.mode with | .trivial => runTrivial p | .vm => runVM p

def check (p : Prog) : List (String × String) := Id.run do
  let o := run p
  let it := match p.mode with
    | .trivial => s!"the trivial sparse search (batch {p.batch} standing for 1024)"
    | .vm => "the VM's sparse select (Df, Position, uncached)"
  let mut out := []
  if o.abort then
    out := out ++ [("P1 no crash or abort", s!"abort (debug): {it}: \"sparse iterator invalidated while iterating\" (eval_sparse.c 145-146)")]
  for x in List.range p.tabOf.size do
    let n := (o.visits.filter (· == x)).length
    if n > 1 then
      out := out ++ [("P-IT4 removing a DontFragment id while iterating", s!"twice: {it} returns e{x} {n} times: removing an unvisited entity's Df swapped the last dense id (already returned: the select walks backward, eval_sparse.c 140-149) into its slot (sparse.c 177-191)")]
    else if n == 0 && !o.removedBefore.contains x && !o.abort then
      out := out ++ [("P-IT4 removing a DontFragment id while iterating", s!"skipped: {it} never returns e{x}, which had Df until its turn: removing a returned entity's Df swapped a later id into a slot the forward walk had passed (eval_sparse.c 561-575, sparse.c 177-191)")]
  return out

section
variable {m : Type → Type} [Monad m] [Pick m]

def genProg (nents nops : Nat) : m Prog := do
  let mut ts := #[]
  for _ in [0:nents] do ts := ts.push (← Pick.pick "si9.tab" 2)
  let mode ← pickOf "si9.mode" #[Mode.trivial, .vm]
  let batch ← if mode == .trivial then (do return (← Pick.pick "si9.batch" 2) + 1) else pure 1
  let removeCur ← pickOf "si9.self" #[false, true]
  let mut rs := []
  for _ in [0:nops] do
    let k ← Pick.pick "si9.rm" (nents + 1)
    rs := rs ++ [if k == 0 then none else some (k - 1)]
  return { tabOf := ts, mode, batch, removes := rs, removeCur }

end

def shrink (p : Prog) : List Prog :=
  ((List.range p.removes.length).filter (fun i => (p.removes.getD i none).isSome)).map (fun i => { p with removes := p.removes.set i none }) ++
  (if p.removeCur then [{ p with removeCur := false }] else [])

def cases : List (String × Prog) := [
  ("sparse_remove_while_iterating (trivial): 5 entities, batch 2 (1024); each callback removes Df from its result",
    { tabOf := #[0, 0, 0, 0, 0], mode := .trivial, batch := 2, removes := [], removeCur := true }),
  ("control: the same loop over the VM's select",
    { tabOf := #[0, 1, 0, 1, 0], mode := .vm, removes := [], removeCur := true }),
  ("sparse_immediate_remove_iteration (VM): a0, b0, a1, b1 in [Position] and [Position, Tag]; the first callback removes Df from a0",
    { tabOf := #[0, 1, 0, 1], mode := .vm, removes := [some 0] }),
  ("sparse_immediate_remove_iteration (trivial): 5 entities, batch 2 (1024); the second callback removes Df from e0",
    { tabOf := #[0, 0, 0, 0, 0], mode := .trivial, batch := 2, removes := [none, some 0] }),
  ("control: trivial, the first callback removes a later entity",
    { tabOf := #[0, 0, 0, 0, 0], mode := .trivial, batch := 2, removes := [some 4] }),
  ("control: VM, a callback removes an entity already returned",
    { tabOf := #[0, 1, 0, 1], mode := .vm, removes := [none, some 3] }) ]

end Flecs.SparseIter
