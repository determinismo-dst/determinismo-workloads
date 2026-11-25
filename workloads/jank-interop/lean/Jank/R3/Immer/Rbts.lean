/-!
# immer's `rbts` (relaxed radix balanced tree, regular case): `immer::vector` as jank uses it

jank's vectors are `immer::vector<object_ref, jank::memory_policy>` (runtime/detail/type.hpp);
`memory_policy = immer::memory_policy<heap_policy<gc_heap>, no_refcount_policy,
default_lock_policy, gc_transience_policy, false>` (include/cpp/jank/type.hpp). So:

- `B = default_bits = 5` (config.hpp:136); `BL = derive_bits_leaf<object_ref, MP, 5>`
  (rbts/node.hpp:1017): the leaf space is `max_sizeof_inner - offsetof(leaf.buffer)` =
  `8 (relaxed*) + 32 * 8` = 264 bytes, 33 `object_ref`s, `log2(33) = 5`. So `BL = 5`: 32-wide
  leaves and inner nodes, as Clojure's.
- `no_refcount_policy` (refcount/no_refcount_policy.hpp): `unique()` is false and `dec()` is false,
  so `can_mutate(e)` is exactly `ownee.token_ == e` and nothing is ever deleted through `dec()`.
- `gc_transience_policy` (transience/gc_transience_policy.hpp): an `owner` holds a token, a fresh
  1-byte GC allocation per `owner()` (`make_token_`); the copy constructor gives both sides fresh
  tokens; the move constructor copies the token; `edit` is the token pointer; a node's `ownee`
  holds the token it was created under (`nullptr` for nodes built by persistent operations).
- `use_transient_rvalues` is false (memory_policy.hpp: `get_use_transient_rvalues_v` of
  `no_refcount_policy`), so persistent operations never mutate.
- `IMMER_TAGGED_NODE=0` (CMakeLists.txt:113): a node does not record whether it is a leaf.

Only `rbtree` (rbts/rbtree.hpp) is used by `immer::vector`: regular positions only (no relaxed
nodes, which only `flex_vector` builds).

## The replica

A node is a value with an identity (`id`, a fresh allocation number) and the token it is owned by
(`tok`, 0 is `nullptr`). Its physical slots are a list: a leaf's elements, an inner node's
children. A write past the end appends (padding with a default for an uninitialized gap); a
`destroy_n` of a leaf's last slots truncates (those slots are dead until rewritten).

Mutation in place under an owner is modeled as replacing the node by its updated copy with the
same `id` and `tok`. That is the C++ semantics exactly when the mutated node is reachable only
along the mutation path; `Jank.R3.Immer.Aliasing` checks that premise on every step of every
searched timeline (no node owned by a live transient's token is reachable twice or from a
persistent value).

Every function recurses on a level number `k` (an inner position at level `k` has shift
`5 * (k + 1)`; level-0 inner nodes have leaf children), so all definitions are structural.
Allocation threads the next free id `n`. Code paths cite rbts/rbtree.hpp, rbts/operations.hpp,
rbts/position.hpp and rbts/node.hpp of immer 282629d0.
-/

namespace Jank.R3.Immer.Rbts

/-- A node: a leaf (`leaf()` buffer) or an inner node (`inner()` buffer). -/
inductive Node (α : Type) where
  | leaf (id : Nat) (tok : Nat) (xs : List α)
  | inner (id : Nat) (tok : Nat) (cs : List (Node α))
  deriving Repr

variable {α : Type}

/-- What a garbage pointer is read as (an uninitialized slot). -/
def Node.dummy : Node α := .inner 0 0 []

instance : Inhabited (Node α) := ⟨Node.dummy⟩

def Node.id : Node α → Nat
  | .leaf i _ _ => i
  | .inner i _ _ => i

def Node.tok : Node α → Nat
  | .leaf _ t _ => t
  | .inner _ t _ => t

def Node.cs : Node α → List (Node α)
  | .inner _ _ cs => cs
  | .leaf .. => []

def Node.xs : Node α → List α
  | .leaf _ _ xs => xs
  | .inner .. => []

def Node.isLeaf : Node α → Bool
  | .leaf .. => true
  | .inner .. => false

/-- `node->inner()[i]` (a dummy when the slot was never written). -/
def Node.child (n : Node α) (i : Nat) : Node α := n.cs.getD i Node.dummy

/-- `ownee(this).can_mutate(e)` (refs().unique() is false under no_refcount_policy). -/
def Node.canMutate (n : Node α) (e : Nat) : Bool := n.tok == e

/-- A write to slot `i` of a physical buffer. -/
def setAt {β : Type} (d : β) (l : List β) (i : Nat) (x : β) : List β :=
  if i < l.length then l.set i x else l ++ List.replicate (i - l.length) d ++ [x]

/-- `std::copy(src, src + n, dst)` / `uninitialized_copy` of the first `n` slots. -/
def copyN {β : Type} (d : β) (l : List β) (n : Nat) : List β :=
  l.take n ++ List.replicate (n - l.length) d

def leafCopy [Inhabited α] (n : Node α) (cnt : Nat) : List α := copyN default n.xs cnt
def childCopy (n : Node α) (cnt : Nat) : List (Node α) := copyN Node.dummy n.cs cnt

/-- In-place write of a leaf slot (same identity). -/
def Node.writeLeaf [Inhabited α] (n : Node α) (i : Nat) (x : α) : Node α :=
  .leaf n.id n.tok (setAt default n.xs i x)

/-- In-place write of a child slot (same identity). -/
def Node.writeChild (n : Node α) (i : Nat) (c : Node α) : Node α :=
  .inner n.id n.tok (setAt Node.dummy n.cs i c)

/-! ## Positions (rbts/position.hpp) -/

/-- Inner positions: `regular_sub_pos` (root), `regular_pos` (last child), `full_pos`. -/
inductive IPos where
  | sub (size : Nat)
  | reg (size : Nat)
  | full
  deriving Repr, BEq

/-- Leaf positions: `leaf_sub_pos` (the tail), `leaf_pos` (last leaf), `full_leaf_pos`. -/
inductive LPos where
  | leafSub (count : Nat)
  | leaf (size : Nat)
  | fullLeaf
  deriving Repr, BEq

/-- `count()`. -/
def IPos.count (sh : Nat) : IPos → Nat
  | .sub size => ((size - 1) >>> sh) + 1              -- subindex(size_ - 1) + 1
  | .reg size => (((size - 1) >>> sh) &&& 31) + 1     -- index(size_ - 1) + 1
  | .full => 32

/-- `size()`. -/
def IPos.size (sh : Nat) : IPos → Nat
  | .sub size => size
  | .reg size => size
  | .full => 32 <<< sh

def LPos.count : LPos → Nat
  | .leafSub c => c
  | .leaf size => ((size - 1) &&& 31) + 1
  | .fullLeaf => 32

/-- `index(idx)` of an inner position. -/
def iIndex (sh idx : Nat) : Nat := (idx >>> sh) &&& 31

/-- `index(idx)` of a leaf position. -/
def lIndex (idx : Nat) : Nat := idx &&& 31

/-- `towards_oh_ch_regular` / `full_pos::towards_oh` (and `last_oh_regular`, which is the
`is_full = false` case): the position of child `offset` when its children are inner nodes. -/
def IPos.towardsI (p : IPos) (sh offset : Nat) : IPos :=
  match p with
  | .full => .full
  | _ => if offset + 1 != p.count sh then .full else .reg (p.size sh)

/-- The same when the children are leaves (`shift == BL`). -/
def IPos.towardsL (p : IPos) (sh offset : Nat) : LPos :=
  match p with
  | .full => .fullLeaf
  | _ => if offset + 1 != p.count sh then .fullLeaf else .leaf (p.size sh)

/-! ## The tree (rbts/rbtree.hpp) -/

structure Tree (α : Type) where
  size : Nat
  shift : Nat
  root : Node α
  tail : Node α
  deriving Repr

/-- `empty_root()` and `empty_tail()`: static nodes (ids 1 and 2, no owner). -/
instance : Inhabited (Tree α) := ⟨{ size := 0, shift := 5, root := .inner 1 0 [], tail := .leaf 2 0 [] }⟩

def emptyRoot : Node α := .inner 1 0 []
def emptyTail : Node α := .leaf 2 0 []

/-- `rbtree()`: `{0, BL, empty_root(), empty_tail()}`. -/
def Tree.empty : Tree α := { size := 0, shift := 5, root := emptyRoot, tail := emptyTail }

/-- The first id an allocation may take (after the two static nodes). -/
def firstId : Nat := 3

/-- `tail_offset()`: `size ? (size - 1) & ~mask<BL> : 0`. -/
def tailOffset (size : Nat) : Nat := if size = 0 then 0 else ((size - 1) >>> 5) <<< 5

/-- The level of a root at `shift` (`shift = 5 * (level + 1)`). -/
def levelOf (shift : Nat) : Nat := shift / 5 - 1

/-! ### `make_path` / `make_path_e` (rbts/node.hpp) -/

/-- `make_path(shift, node)` with `shift = 5 * k` (`make_inner_n(1)` per level, no owner) or
`make_path_e(e, ...)` (`make_inner_e(e)`, owned by `e`). -/
def makePath (tok : Nat) : (k : Nat) → Node α → Nat → Node α × Nat
  | 0, node, n => (node, n)
  | k + 1, node, n =>
    let id := n
    let (c, n) := makePath tok k node (n + 1)
    (.inner id tok [c], n)

/-! ### Reads -/

/-- `visit_regular_descent` down to the leaf (`regular_descent_pos<Shift>::descend`, then
`leaf_descent_pos`): the leaf holding `idx`, or none on a kind mismatch. -/
def descendLeaf : (k : Nat) → Node α → Nat → Option (Node α)
  | 0, node, idx =>
    match node with
    | .inner _ _ cs =>
      match cs[iIndex 5 idx]? with
      | some l@(.leaf ..) => some l
      | _ => none
    | .leaf .. => none
  | k + 1, node, idx =>
    match node with
    | .inner _ _ cs =>
      match cs[iIndex (5 * (k + 2)) idx]? with
      | some c => descendLeaf k c idx
      | none => none
    | .leaf .. => none

/-- `rbtree::array_for(index)` (`descend(array_for_visitor)`): the buffer holding `idx`. Shifts
past `BL + 5 * 5` are `IMMER_UNREACHABLE` (no `IMMER_DESCENT_DEEP`): none. -/
def Tree.arrayFor (t : Tree α) (idx : Nat) : Option (List α) :=
  if idx ≥ tailOffset t.size then
    match t.tail with
    | .leaf _ _ xs => some xs
    | .inner .. => none
  else if t.shift > 30 then none
  else (descendLeaf (levelOf t.shift) t.root idx).map Node.xs

/-- `rbtree::get(index)` (`operator[]`): `descend(get_visitor)`, `leaf()[idx & mask<BL>]`. -/
def Tree.get (t : Tree α) (idx : Nat) : Option α :=
  (t.arrayFor idx).bind (·[lIndex idx]?)

/-- `rbtree_iterator` from `begin()` to `end()`: element `i` is `array_for(i)[i & mask<BL>]`
(the iterator caches `array_for` per leaf base `i & ~mask<BL>`; the tree does not change while a
persistent vector is iterated). -/
def Tree.iter (t : Tree α) : List (Option α) :=
  (List.range t.size).map fun i => (t.arrayFor i).bind (·[lIndex i]?)

/-! ### `push_back` (persistent; rbtree.hpp `push_back`, operations.hpp `push_tail_visitor`) -/

/-- `push_tail_visitor::visit_regular` at a position of size `size` (absolute: the root's
`regular_sub_pos` covers `[0, tail_off)`, and `last_oh_regular` passes `p.size()` on). -/
def pushTail : (k : Nat) → Nat → Node α → Node α → Nat → Node α × Nat
  | k, size, node, tail, n =>
    let sh := 5 * (k + 1)
    let idx := iIndex sh (size - 1)
    let newIdx := iIndex sh (size + 32 - 1)
    -- `make_inner_n(count)` first.
    let pid := n
    let n := n + 1
    let (child, n) :=
      if idx == newIdx then
        match k with
        | 0 => (Node.dummy, n)  -- `make_leaf_pos(...).visit`: `visit_leaf` is IMMER_UNREACHABLE
        | k' + 1 => pushTail k' size (node.child idx) tail n
      else makePath 0 k tail n
    -- `new_parent->inner()[new_idx] = ...; do_copy_inner(new_parent, pos.node(), new_idx)`.
    (.inner pid 0 (setAt Node.dummy (childCopy node newIdx) newIdx child), n)

/-- `rbtree::push_back(value) const`. -/
def Tree.pushBack [Inhabited α] (t : Tree α) (x : α) (n : Nat) : Tree α × Nat :=
  let tailOff := tailOffset t.size
  let ts := t.size - tailOff
  if ts < 32 then
    -- `copy_leaf_emplace(tail, ts, value)`: `copy_leaf_n(ts + 1, tail, ts)`, then slot ts.
    ({ t with size := t.size + 1, tail := .leaf n 0 (leafCopy t.tail ts ++ [x]) }, n + 1)
  else
    -- `make_leaf_n(1, value)`
    let newTail : Node α := .leaf n 0 [x]
    let n := n + 1
    if tailOff == 32 <<< t.shift then
      let rid := n
      let (path, n) := makePath 0 (t.shift / 5) t.tail (n + 1)
      ({ size := t.size + 1, shift := t.shift + 5, root := .inner rid 0 [t.root, path],
         tail := newTail }, n)
    else if tailOff != 0 then
      let (r, n) := pushTail (levelOf t.shift) tailOff t.root t.tail n
      ({ t with size := t.size + 1, root := r, tail := newTail }, n)
    else
      let (r, n) := makePath 0 (t.shift / 5) t.tail n
      ({ t with size := t.size + 1, root := r, tail := newTail }, n)

/-! ### `update` / `assoc` (persistent; operations.hpp `update_visitor`) -/

/-- `update_visitor::visit_leaf`: `copy_leaf(pos.node(), pos.count())`, slot `index(idx)` set. -/
def updLeaf [Inhabited α] (p : LPos) (node : Node α) (idx : Nat) (x : α) (n : Nat) : Node α × Nat :=
  (.leaf n 0 (setAt default (leafCopy node p.count) (lIndex idx) x), n + 1)

/-- `update_visitor::visit_regular`: `make_inner_n(count)`, the child updated through
`towards_oh_ch`, then `do_copy_inner_replace(node, pos.node(), count, offset, child)`. -/
def updInner [Inhabited α] : (k : Nat) → IPos → Node α → Nat → α → Nat → Node α × Nat
  | 0, p, node, idx, x, n =>
    let sh := 5
    let offset := iIndex sh idx
    let cnt := p.count sh
    let nid := n
    let (child, n) := updLeaf (p.towardsL sh offset) (node.child offset) idx x (n + 1)
    (.inner nid 0 (setAt Node.dummy (childCopy node cnt) offset child), n)
  | k + 1, p, node, idx, x, n =>
    let sh := 5 * (k + 2)
    let offset := iIndex sh idx
    let cnt := p.count sh
    let nid := n
    let (child, n) := updInner k (p.towardsI sh offset) (node.child offset) idx x (n + 1)
    (.inner nid 0 (setAt Node.dummy (childCopy node cnt) offset child), n)

/-- `rbtree::assoc(idx, value)` = `update(idx, constantly value)`. -/
def Tree.assoc [Inhabited α] (t : Tree α) (idx : Nat) (x : α) (n : Nat) : Tree α × Nat :=
  let tailOff := tailOffset t.size
  if idx ≥ tailOff then
    let (nt, n) := updLeaf (.leafSub (t.size - tailOff)) t.tail (idx - tailOff) x n
    ({ t with tail := nt }, n)
  else
    let (nr, n) := updInner (levelOf t.shift) (.sub tailOff) t.root idx x n
    ({ t with root := nr }, n)

/-! ### `take` (persistent; operations.hpp `slice_right_visitor`) -/

/-- `slice_right_visitor` result: new shift, new root (`nullptr` = none), new tail size, tail. -/
abbrev Slice (α : Type) := Nat × Option (Node α) × Nat × Node α

/-- `slice_right_visitor::visit_leaf`. -/
def sliceLeaf [Inhabited α] (p : LPos) (node : Node α) (last : Nat) (n : Nat) : Slice α × Nat :=
  let old := p.count
  let new := lIndex last + 1
  if new == old then ((0, none, new, node), n)
  else ((0, none, new, .leaf n 0 (leafCopy node new)), n + 1)

/-- `slice_right_visitor<Collapse>::visit_regular`. The child is visited with `this_t` (same
`Collapse`) when collapsing at index 0, else with `no_collapse_t`; level 0's children are leaves. -/
def sliceInner [Inhabited α] : (k : Nat) → Bool → IPos → Node α → Nat → Nat → Slice α × Nat
  | 0, collapse, p, node, last, n =>
    let idx := iIndex 5 last
    if collapse && idx == 0 then sliceLeaf (p.towardsL 5 idx) (node.child idx) last n
    else
      let ((_, next, ts, tail), n) := sliceLeaf (p.towardsL 5 idx) (node.child idx) last n
      match next with
      | some nx => ((5, some (.inner n 0 (setAt Node.dummy (childCopy node idx) idx nx)), ts, tail), n + 1)
      | none =>
        if idx == 0 then ((5, none, ts, tail), n)
        else if collapse && idx == 1 && 5 > 5 then ((0, some (node.child 0), ts, tail), n)
        else ((5, some (.inner n 0 (childCopy node idx)), ts, tail), n + 1)
  | k + 1, collapse, p, node, last, n =>
    let sh := 5 * (k + 2)
    let idx := iIndex sh last
    if collapse && idx == 0 then sliceInner k collapse (p.towardsI sh idx) (node.child idx) last n
    else
      let ((_, next, ts, tail), n) := sliceInner k false (p.towardsI sh idx) (node.child idx) last n
      match next with
      | some nx =>
        -- `copy_inner_n(idx + 1, pos.node(), idx); newn->inner()[idx] = next`
        ((sh, some (.inner n 0 (setAt Node.dummy (childCopy node idx) idx nx)), ts, tail), n + 1)
      | none =>
        if idx == 0 then ((sh, none, ts, tail), n)
        else if collapse && idx == 1 && sh > 5 then ((sh - 5, some (node.child 0), ts, tail), n)
        else ((sh, some (.inner n 0 (childCopy node idx)), ts, tail), n + 1)

/-- `rbtree::take(new_size) const`. -/
def Tree.take [Inhabited α] (t : Tree α) (newSize : Nat) (n : Nat) : Tree α × Nat :=
  let tailOff := tailOffset t.size
  if newSize == 0 then (Tree.empty, n)
  else if newSize ≥ t.size then (t, n)
  else if newSize > tailOff then
    ({ t with size := newSize, tail := .leaf n 0 (leafCopy t.tail (newSize - tailOff)) }, n + 1)
  else
    let ((ns, nr, _, nt), n) := sliceInner (levelOf t.shift) true (.sub tailOff) t.root (newSize - 1) n
    match nr with
    | some r => ({ size := newSize, shift := ns, root := r, tail := nt }, n)
    | none => ({ size := newSize, shift := 5, root := emptyRoot, tail := nt }, n)

/-! ## Transient operations (vector_transient.hpp; `_mut` functions) -/

/-- `ensure_mutable_tail(e, n)`. -/
def Tree.ensureMutableTail [Inhabited α] (t : Tree α) (e cnt : Nat) (n : Nat) : Tree α × Nat :=
  if t.tail.canMutate e then (t, n)
  else ({ t with tail := .leaf n e (leafCopy t.tail cnt) }, n + 1)

/-- `push_tail_mut_visitor<Mutating>::visit_regular`. -/
def pushTailMut : (k : Nat) → Bool → Nat → Nat → Node α → Node α → Nat → Node α × Nat
  | k, mutating, e, size, node, tail, n =>
    let sh := 5 * (k + 1)
    let idx := iIndex sh (size - 1)
    let newIdx := iIndex sh (size + 32 - 1)
    let mutate := mutating && node.canMutate e
    if mutate then
      let (child, n) :=
        if idx == newIdx then
          match k with
          | 0 => (Node.dummy, n)  -- visit_leaf: IMMER_UNREACHABLE
          | k' + 1 => pushTailMut k' true e size (node.child idx) tail n
        else makePath e k tail n
      (node.writeChild newIdx child, n)
    else
      -- `make_inner_e(e)` first, then the child (`this_no_mut_t`), then `do_copy_inner`.
      let pid := n
      let n := n + 1
      let (child, n) :=
        if idx == newIdx then
          match k with
          | 0 => (Node.dummy, n)
          | k' + 1 => pushTailMut k' false e size (node.child idx) tail n
        else makePath e k tail n
      (.inner pid e (setAt Node.dummy (childCopy node newIdx) newIdx child), n)

/-- `rbtree::push_back_mut(e, value)`. -/
def Tree.pushBackMut [Inhabited α] (t : Tree α) (e : Nat) (x : α) (n : Nat) : Tree α × Nat :=
  let tailOff := tailOffset t.size
  let ts := t.size - tailOff
  if ts < 32 then
    let (t, n) := t.ensureMutableTail e ts n
    ({ t with size := t.size + 1, tail := t.tail.writeLeaf ts x }, n)
  else
    let newTail : Node α := .leaf n e [x]  -- make_leaf_e(e, value)
    let n := n + 1
    if tailOff == 32 <<< t.shift then
      let rid := n
      let (path, n) := makePath e (t.shift / 5) t.tail (n + 1)
      ({ size := t.size + 1, shift := t.shift + 5, root := .inner rid e [t.root, path],
         tail := newTail }, n)
    else if tailOff != 0 then
      let (r, n) := pushTailMut (levelOf t.shift) true e tailOff t.root t.tail n
      ({ t with size := t.size + 1, root := r, tail := newTail }, n)
    else
      let (r, n) := makePath e (t.shift / 5) t.tail n
      ({ t with size := t.size + 1, root := r, tail := newTail }, n)

/-- `get_mut_visitor::visit_leaf` followed by the write of `assoc_mut`'s value. -/
def getMutLeaf [Inhabited α] (p : LPos) (e : Nat) (node : Node α) (idx : Nat) (x : α) (n : Nat) :
    Node α × Nat :=
  if node.canMutate e then (node.writeLeaf (lIndex idx) x, n)
  else (.leaf n e (setAt default (leafCopy node p.count) (lIndex idx) x), n + 1)

/-- `get_mut_visitor::visit_regular` (`*location = new_node` when the node is copied). -/
def getMutInner [Inhabited α] : (k : Nat) → IPos → Nat → Node α → Nat → α → Nat → Node α × Nat
  | 0, p, e, node, idx, x, n =>
    let sh := 5
    let offset := iIndex sh idx
    let cnt := p.count sh
    if node.canMutate e then
      let (c, n) := getMutLeaf (p.towardsL sh offset) e (node.child offset) idx x n
      (node.writeChild offset c, n)
    else
      let copy : Node α := .inner n e (childCopy node cnt)  -- copy_inner_e(e, node, count)
      let (c, n) := getMutLeaf (p.towardsL sh offset) e (copy.child offset) idx x (n + 1)
      (copy.writeChild offset c, n)
  | k + 1, p, e, node, idx, x, n =>
    let sh := 5 * (k + 2)
    let offset := iIndex sh idx
    let cnt := p.count sh
    if node.canMutate e then
      let (c, n) := getMutInner k (p.towardsI sh offset) e (node.child offset) idx x n
      (node.writeChild offset c, n)
    else
      let copy : Node α := .inner n e (childCopy node cnt)
      let (c, n) := getMutInner k (p.towardsI sh offset) e (copy.child offset) idx x (n + 1)
      (copy.writeChild offset c, n)

/-- `rbtree::assoc_mut(e, idx, value)` = `update_mut` through `get_mut(e, idx)`. -/
def Tree.assocMut [Inhabited α] (t : Tree α) (e : Nat) (idx : Nat) (x : α) (n : Nat) : Tree α × Nat :=
  let tailOff := tailOffset t.size
  if idx ≥ tailOff then
    let (t, n) := t.ensureMutableTail e (t.size - tailOff) n
    ({ t with tail := t.tail.writeLeaf (lIndex idx) x }, n)
  else
    let (r, n) := getMutInner (levelOf t.shift) (.sub tailOff) e t.root idx x n
    ({ t with root := r }, n)

/-- `slice_right_mut_visitor<..., Mutating>::visit_leaf`. -/
def sliceMutLeaf [Inhabited α] (p : LPos) (mutating : Bool) (e : Nat) (node : Node α) (last : Nat)
    (n : Nat) : Slice α × Nat :=
  let old := p.count
  let new := lIndex last + 1
  let mutate := mutating && node.canMutate e
  if new == old then ((0, none, new, node), n)
  else if mutate then ((0, none, new, .leaf node.id node.tok (node.xs.take new)), n)  -- destroy_n
  else ((0, none, new, .leaf n e (leafCopy node new)), n + 1)                        -- copy_leaf_e

/-- `slice_right_mut_visitor<Collapse, Mutating>::visit_regular`. The child visitor is `this_t`
or `no_mut_t` (collapsing) and `no_collapse_t` or `no_collapse_no_mut_t` (not collapsing): its
`Mutating` is this node's `mutate`. -/
def sliceMutInner [Inhabited α] : (k : Nat) → Bool → Bool → Nat → IPos → Node α → Nat → Nat → Slice α × Nat
  | k, collapse, mutating, e, p, node, last, n =>
    let sh := 5 * (k + 1)
    let idx := iIndex sh last
    let mutate := mutating && node.canMutate e
    let down (c : Bool) (n : Nat) : Slice α × Nat :=
      match k with
      | 0 => sliceMutLeaf (p.towardsL sh idx) mutate e (node.child idx) last n
      | k' + 1 => sliceMutInner k' c mutate e (p.towardsI sh idx) (node.child idx) last n
    if collapse && idx == 0 then down collapse n
    else
      let ((_, next, ts, tail), n) := down false n
      match next with
      | some nx =>
        if mutate then ((sh, some (node.writeChild idx nx), ts, tail), n)
        else ((sh, some (.inner n e (setAt Node.dummy (childCopy node idx) idx nx)), ts, tail), n + 1)
      | none =>
        if idx == 0 then ((sh, none, ts, tail), n)
        else if collapse && idx == 1 && sh > 5 then ((sh - 5, some (node.child 0), ts, tail), n)
        else if mutate then ((sh, some node, ts, tail), n)
        else ((sh, some (.inner n e (childCopy node idx)), ts, tail), n + 1)

/-- `rbtree::take_mut(e, new_size)`. -/
def Tree.takeMut [Inhabited α] (t : Tree α) (e : Nat) (newSize : Nat) (n : Nat) : Tree α × Nat :=
  let tailOff := tailOffset t.size
  if newSize == 0 then (Tree.empty, n)  -- `*this = {}`
  else if newSize ≥ t.size then (t, n)
  else if newSize > tailOff then
    let newts := newSize - tailOff
    if t.tail.canMutate e then
      ({ t with size := newSize, tail := .leaf t.tail.id t.tail.tok (t.tail.xs.take newts) }, n)
    else ({ t with size := newSize, tail := .leaf n e (leafCopy t.tail newts) }, n + 1)
  else
    let ((ns, nr, _, nt), n) :=
      sliceMutInner (levelOf t.shift) true true e (.sub tailOff) t.root (newSize - 1) n
    match nr with
    | some r => ({ size := newSize, shift := ns, root := r, tail := nt }, n)
    | none => ({ size := newSize, shift := 5, root := emptyRoot, tail := nt }, n)

/-! ## `immer::vector` and `immer::vector_transient` -/

/-- A transient: its tree and its owner's token (vector_transient inherits `owner`). -/
structure Transient (α : Type) where
  tree : Tree α
  tok : Nat
  deriving Repr

/-- `vector::transient() const&`: `transient_type{impl_}`: a fresh owner token, the tree shared. -/
def Tree.transient (t : Tree α) (n : Nat) : Transient α × Nat := ({ tree := t, tok := n }, n + 1)

/-- `vector_transient()`: a fresh owner, the empty tree. -/
def Transient.empty (n : Nat) : Transient α × Nat := ({ tree := Tree.empty, tok := n }, n + 1)

/-- `vector_transient::persistent() &`: `owner_t::operator=(owner_t{})` (a fresh token for the
transient), then `persistent_type{impl_}` (the tree shared). -/
def Transient.persistent (t : Transient α) (n : Nat) : Tree α × Transient α × Nat :=
  (t.tree, { t with tok := n }, n + 1)

def Transient.pushBack [Inhabited α] (t : Transient α) (x : α) (n : Nat) : Transient α × Nat :=
  let (tr, n) := t.tree.pushBackMut t.tok x n
  ({ t with tree := tr }, n)

def Transient.set [Inhabited α] (t : Transient α) (i : Nat) (x : α) (n : Nat) : Transient α × Nat :=
  let (tr, n) := t.tree.assocMut t.tok i x n
  ({ t with tree := tr }, n)

def Transient.take [Inhabited α] (t : Transient α) (k : Nat) (n : Nat) : Transient α × Nat :=
  let (tr, n) := t.tree.takeMut t.tok k n
  ({ t with tree := tr }, n)

/-- `rbtree::from_range(first, last)`: a local `owner_t{}` and `push_back_mut` of each element
(`vector(Iter, Sent)`, used by `subvec`). -/
def Tree.fromList [Inhabited α] (xs : List α) (n : Nat) : Tree α × Nat :=
  let e := n
  xs.foldl (fun (acc : Tree α × Nat) x => acc.1.pushBackMut e x acc.2) (Tree.empty, n + 1)

/-! ## Well-formedness and the elements a tree holds (the abstraction used by checks and proofs)

A regular tree: the root covers `[0, tail_off)` densely; every leaf below it is full (32); an
inner node at shift `s` covering `m` elements has `ceil(m / 2^s)` children, all full but the last.
-/

/-- Number of children of an inner node at shift `sh` covering `m` elements. -/
def childCount (sh m : Nat) : Nat := (m + 2 ^ sh - 1) / 2 ^ sh

/-- Elements covered by child `j` of an inner node at shift `sh` covering `m`. -/
def childSize (sh m j : Nat) : Nat := min (2 ^ sh) (m - j * 2 ^ sh)

/-- The elements of a leaf covering `m` (its first `m` slots). -/
def leafElems (node : Node α) (m : Nat) : List α := node.xs.take m

/-- The elements of an inner node at level `k` covering `m`. -/
def elemsI : (k : Nat) → Node α → Nat → List α
  | 0, node, m => (List.range (childCount 5 m)).flatMap fun j => leafElems (node.child j) (childSize 5 m j)
  | k + 1, node, m =>
    (List.range (childCount (5 * (k + 2)) m)).flatMap fun j =>
      elemsI k (node.child j) (childSize (5 * (k + 2)) m j)

/-- Well-formed leaf covering `m` (tree leaves: `m = 32`). -/
def wfLeaf (node : Node α) (m : Nat) : Bool := node.isLeaf && decide (m ≤ node.xs.length) && decide (m ≤ 32)

/-- Well-formed inner node at level `k` covering `m > 0` elements, every leaf full. -/
def wfI : (k : Nat) → Node α → Nat → Bool
  | 0, node, m =>
    !node.isLeaf && decide (0 < m) && decide (m ≤ 2 ^ 10) && decide (m % 32 = 0) &&
      decide (childCount 5 m ≤ node.cs.length) &&
      (List.range (childCount 5 m)).all fun j => wfLeaf (node.child j) 32
  | k + 1, node, m =>
    !node.isLeaf && decide (0 < m) && decide (m ≤ 2 ^ (5 * (k + 3))) && decide (m % 32 = 0) &&
      decide (childCount (5 * (k + 2)) m ≤ node.cs.length) &&
      (List.range (childCount (5 * (k + 2)) m)).all fun j =>
        wfI k (node.child j) (childSize (5 * (k + 2)) m j)

/-- A well-formed tree: shift a multiple of 5 from 5 to 30, root covers `tail_off` (fits under
the root), the tail holds the rest (1 to 32 when nonempty). -/
def Tree.wf (t : Tree α) : Bool :=
  let tailOff := tailOffset t.size
  decide (t.shift % 5 = 0) && decide (5 ≤ t.shift) && decide (t.shift ≤ 30) &&
    wfLeaf t.tail (t.size - tailOff) &&
    (tailOff == 0 || (decide (tailOff ≤ 32 <<< t.shift) && wfI (levelOf t.shift) t.root tailOff))

/-- The elements, in order. -/
def Tree.toList (t : Tree α) : List α :=
  let tailOff := tailOffset t.size
  (if tailOff == 0 then [] else elemsI (levelOf t.shift) t.root tailOff) ++
    leafElems t.tail (t.size - tailOff)

/-! ## Identity: the nodes a value reaches (for the aliasing checks) -/

/-- `(id, tok)` of every node reachable through valid positions of an inner node at level `k`
covering `m`. -/
def reachI : (k : Nat) → Node α → Nat → List (Nat × Nat)
  | 0, node, m => (node.id, node.tok) ::
      (List.range (childCount 5 m)).map fun j => ((node.child j).id, (node.child j).tok)
  | k + 1, node, m => (node.id, node.tok) ::
      (List.range (childCount (5 * (k + 2)) m)).flatMap fun j =>
        reachI k (node.child j) (childSize (5 * (k + 2)) m j)

def Tree.reach (t : Tree α) : List (Nat × Nat) :=
  let tailOff := tailOffset t.size
  (t.tail.id, t.tail.tok) :: (if tailOff == 0 then [] else reachI (levelOf t.shift) t.root tailOff)

end Jank.R3.Immer.Rbts
