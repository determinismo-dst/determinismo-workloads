/-!
# immer's CHAMP (`detail/hamts/champ.hpp`, `node.hpp`, `champ_iterator.hpp`): `immer::map` and
`immer::set` as jank uses them

jank: `immer::map<object_ref, object_ref, std::hash<object_ref>, std::equal_to<object_ref>,
memory_policy>` and `immer::set<object_ref, std::hash<object_ref>, std::equal_to<object_ref>,
memory_policy>` (runtime/detail/type.hpp). `std::hash<object_ref>` is `jank::hash::visit(o)` =
`o.to_hash()`, a `u32` returned as `size_t` (runtime/object.cpp:369); `std::equal_to<object_ref>`
is `runtime::equal(lhs, rhs)` = `lhs.equal(rhs)` (object.cpp:381, core/equal.cpp:19).

So `hash_t = size_t` (64 bits, node.hpp `decltype(Hash{}(...))`), `B = default_bits = 5`,
`bitmap_t = uint32_t` (hamts/bits.hpp), `max_depth = (64 + 5 - 1) / 5 = 13`,
`max_shift = 65`. A jank hash has its upper 32 bits zero: levels 7 to 12 (shifts 35-60) always
take index 0, and two keys reach a collision node only when their 32-bit hashes are equal.

`immer::map` stores `std::pair<K, V>` with `hash_key` (hash of `.first`) and `equal_key`
(`Equal{}(a.first, b.first)` / `Equal{}(a.first, key)`); `immer::set` stores `K` with `Hash` and
`Equal` directly (map.hpp, set.hpp). Every comparison is `Equal{}(stored, query)`.

## The replica

As in `Rbts`: nodes carry an identity (`id`) and an owner token (`tok`, 0 = `nullptr`); the
values array of an inner node is its own object (`values_t`: refs, ownee, buffer) that can be
shared by two nodes (`copy_inner_replace` → `make_inner_n(n, src->values)`), so it carries its own
`id` and `tok`. Mutation in place is replacement with the same identity; `delete_inner` /
`delete_collision` (`GC_free` through `gc_heap::deallocate`, gc_heap.hpp) record the freed id.
Recursion is on the number of levels left (`rem`: shift = 65 - 5 * rem; `rem = 0` is the collision
level).
-/

namespace Jank.R3.Immer.Champ

/-- A `values_t`: identity, owner token, the value buffer. -/
structure Vals (α : Type) where
  id : Nat
  tok : Nat
  xs : List α
  deriving Repr

inductive Node (α : Type) where
  /-- An inner node: `nodemap`, `datamap`, the `values` pointer (none = `nullptr`), children. -/
  | inner (id tok : Nat) (nodemap datamap : Nat) (vals : Option (Vals α)) (cs : List (Node α))
  | collision (id tok : Nat) (xs : List α)
  deriving Repr

variable {α : Type}

def Node.dummy : Node α := .inner 0 0 0 0 none []
instance : Inhabited (Node α) := ⟨Node.dummy⟩

def Node.id : Node α → Nat
  | .inner i .. => i
  | .collision i .. => i

def Node.tok : Node α → Nat
  | .inner _ t .. => t
  | .collision _ t _ => t

def Node.nodemap : Node α → Nat
  | .inner _ _ nm .. => nm
  | .collision .. => 0

def Node.datamap : Node α → Nat
  | .inner _ _ _ dm .. => dm
  | .collision .. => 0

def Node.vals : Node α → Option (Vals α)
  | .inner _ _ _ _ v _ => v
  | .collision .. => none

def Node.values : Node α → List α
  | .inner _ _ _ _ (some v) _ => v.xs
  | _ => []

def Node.cs : Node α → List (Node α)
  | .inner _ _ _ _ _ cs => cs
  | .collision .. => []

def Node.collisions : Node α → List α
  | .collision _ _ xs => xs
  | .inner .. => []

def Node.child (n : Node α) (i : Nat) : Node α := n.cs.getD i Node.dummy

/-- `popcount`. -/
def popcount (x : Nat) : Nat := (List.range 32).countP fun i => x.testBit i

def Node.dataCount (n : Node α) : Nat := popcount n.datamap
def Node.childrenCount (n : Node α) : Nat := popcount n.nodemap
/-- `data_count(bit)`: `popcount(datamap & (bit - 1))`. -/
def Node.dataCountBit (n : Node α) (bit : Nat) : Nat := popcount (n.datamap &&& (bit - 1))
def Node.childrenCountBit (n : Node α) (bit : Nat) : Nat := popcount (n.nodemap &&& (bit - 1))

/-- `node->can_mutate(e)`. -/
def Node.canMutate (n : Node α) (e : Nat) : Bool := n.tok == e
/-- `can_mutate(values_t*, e)` (a null values pointer: its ownee read is UB; never reached). -/
def Node.canMutateValues (n : Node α) (e : Nat) : Bool :=
  match n.vals with
  | some v => v.tok == e
  | none => false

/-- The hash and equality a champ is instantiated with. `eq stored query`. -/
structure Cfg (α : Type) (κ : Type) where
  hashT : α → Nat
  hashK : κ → Nat
  eqTT : α → α → Bool
  eqTK : α → κ → Bool

/-- The allocation state: next id, ids passed to `GC_free`. -/
structure Al where
  next : Nat := 3
  freed : List Nat := []
  deriving Repr

abbrev M := StateM Al

def fresh : M Nat := modifyGet fun s => (s.next, { s with next := s.next + 1 })
def free (id : Nat) : M Unit := modify fun s => { s with freed := id :: s.freed }

def maxShift : Nat := 65

/-- `(hash & (mask << shift)) >> shift`. -/
def idxAt (hash shift : Nat) : Nat := (hash &&& (31 <<< shift)) >>> shift
def bitAt (hash shift : Nat) : Nat := 1 <<< idxAt hash shift

/-- `x & ~bit` on a `uint32_t` bitmap. -/
def clearBit (x bit : Nat) : Nat := x &&& (0xFFFFFFFF ^^^ bit)

/-- Set `i` of a list (in range). -/
def setL {β : Type} (l : List β) (i : Nat) (x : β) : List β := l.set i x
def insertAt {β : Type} (l : List β) (i : Nat) (x : β) : List β := l.take i ++ [x] ++ l.drop i
def eraseAt {β : Type} (l : List β) (i : Nat) : List β := l.take i ++ l.drop (i + 1)

/-! ## Node constructors and copies (node.hpp) -/

/-- `make_inner_n(n, nv)` with values from `xs` (fresh `values_t`, no owner) or `nullptr`. -/
def mkInner (nodemap datamap : Nat) (xs : List α) (cs : List (Node α)) : M (Node α) := do
  let id ← fresh
  if xs.isEmpty then pure (.inner id 0 nodemap datamap none cs)
  else
    let vid ← fresh
    pure (.inner id 0 nodemap datamap (some { id := vid, tok := 0, xs }) cs)

/-- `make_inner_n(n, src->values)`: shares the values array. -/
def mkInnerShared (nodemap datamap : Nat) (v : Option (Vals α)) (cs : List (Node α)) : M (Node α) := do
  let id ← fresh
  pure (.inner id 0 nodemap datamap v cs)

def mkCollision (xs : List α) : M (Node α) := do
  let id ← fresh
  pure (.collision id 0 xs)

/-- `owned(n, e)`. -/
def owned (n : Node α) (e : Nat) : Node α :=
  match n with
  | .inner id _ nm dm v cs => .inner id e nm dm v cs
  | .collision id _ xs => .collision id e xs

/-- `owned_values(n, e)` (the values pointer must be non-null; if null, the C++ writes through
`nullptr`: recorded by leaving the node unowned, and caught by the checks). -/
def ownedValues (n : Node α) (e : Nat) : Node α :=
  match n with
  | .inner id _ nm dm (some v) cs => .inner id e nm dm (some { v with tok := e }) cs
  | .inner id _ nm dm none cs => .inner id e nm dm none cs
  | .collision id _ xs => .collision id e xs

/-- `owned_values_safe(n, e)`. -/
def ownedValuesSafe (n : Node α) (e : Nat) : Node α := ownedValues n e

/-- `copy_collision_insert(src, v)`: `v` first, then the old ones. -/
def copyCollisionInsert (src : Node α) (v : α) : M (Node α) := mkCollision (v :: src.collisions)

/-- `move_collision_insert(src, v)`: the same, then `delete_collision(src)`. -/
def moveCollisionInsert (src : Node α) (v : α) : M (Node α) := do
  let r ← mkCollision (v :: src.collisions)
  free src.id
  pure r

/-- `copy_collision_remove(src, v)`. -/
def copyCollisionRemove (src : Node α) (pos : Nat) : M (Node α) := mkCollision (eraseAt src.collisions pos)

def moveCollisionRemove (src : Node α) (pos : Nat) : M (Node α) := do
  let r ← mkCollision (eraseAt src.collisions pos)
  free src.id
  pure r

/-- `copy_collision_replace(src, pos, v)`: `v` first, then those before `pos`, then those after. -/
def copyCollisionReplace (src : Node α) (pos : Nat) (v : α) : M (Node α) :=
  mkCollision (v :: eraseAt src.collisions pos)

/-- `copy_inner_replace(src, offset, child)`: the values array shared. -/
def copyInnerReplace (src : Node α) (offset : Nat) (child : Node α) : M (Node α) :=
  mkInnerShared src.nodemap src.datamap src.vals (setL (src.cs.take src.childrenCount) offset child)

/-- `copy_inner_replace_value(src, offset, v)`. -/
def copyInnerReplaceValue (src : Node α) (offset : Nat) (v : α) : M (Node α) :=
  mkInner src.nodemap src.datamap (setL (src.values.take src.dataCount) offset v) (src.cs.take src.childrenCount)

/-- `copy_inner_replace_merged(src, bit, voffset, node)`. -/
def copyInnerReplaceMerged (src : Node α) (bit voffset : Nat) (node : Node α) : M (Node α) :=
  let noffset := src.childrenCountBit bit
  mkInner (src.nodemap ||| bit) (clearBit src.datamap bit)
    (eraseAt (src.values.take src.dataCount) voffset)
    (insertAt (src.cs.take src.childrenCount) noffset node)

/-- `move_inner_replace_merged(e, src, bit, voffset, node)`: the same, then `delete_inner(src)`. -/
def moveInnerReplaceMerged (src : Node α) (bit voffset : Nat) (node : Node α) : M (Node α) := do
  let r ← copyInnerReplaceMerged src bit voffset node
  free src.id
  pure r

/-- `copy_inner_replace_inline(src, bit, noffset, value)`. -/
def copyInnerReplaceInline (src : Node α) (bit noffset : Nat) (value : α) : M (Node α) :=
  let voffset := src.dataCountBit bit
  mkInner (clearBit src.nodemap bit) (src.datamap ||| bit)
    (insertAt (src.values.take src.dataCount) voffset value)
    (eraseAt (src.cs.take src.childrenCount) noffset)

def moveInnerReplaceInline (src : Node α) (bit noffset : Nat) (value : α) : M (Node α) := do
  let r ← copyInnerReplaceInline src bit noffset value
  free src.id
  pure r

/-- `copy_inner_remove_value(src, bit, voffset)`. -/
def copyInnerRemoveValue (src : Node α) (bit voffset : Nat) : M (Node α) :=
  mkInner src.nodemap (clearBit src.datamap bit) (eraseAt (src.values.take src.dataCount) voffset)
    (src.cs.take src.childrenCount)

def moveInnerRemoveValue (src : Node α) (bit voffset : Nat) : M (Node α) := do
  let r ← copyInnerRemoveValue src bit voffset
  free src.id
  pure r

/-- `copy_inner_insert_value(src, bit, v)`. -/
def copyInnerInsertValue (src : Node α) (bit : Nat) (v : α) : M (Node α) :=
  let offset := src.dataCountBit bit
  mkInner src.nodemap (src.datamap ||| bit) (insertAt (src.values.take src.dataCount) offset v)
    (src.cs.take src.childrenCount)

def moveInnerInsertValue (src : Node α) (bit : Nat) (v : α) : M (Node α) := do
  let r ← copyInnerInsertValue src bit v
  free src.id
  pure r

/-- `ensure_mutable_values(e)` on a node that can mutate: the same values if they are owned by
`e`, else a fresh copy owned by `e`. -/
def ensureMutableValues (n : Node α) (e : Nat) : M (Node α) := do
  if n.canMutateValues e then pure n
  else
    let vid ← fresh
    match n with
    | .inner id t nm dm _ cs => pure (.inner id t nm dm (some { id := vid, tok := e, xs := n.values.take n.dataCount }) cs)
    | c => pure c

/-- Write value slot `i` in place (same identities). -/
def writeValue (n : Node α) (i : Nat) (x : α) : Node α :=
  match n with
  | .inner id t nm dm (some v) cs => .inner id t nm dm (some { v with xs := setL v.xs i x }) cs
  | other => other

/-- `make_merged(shift, v1, hash1, v2, hash2)` (and `make_merged_e`, `owned` = some e). -/
def makeMerged (own : Option Nat) : (rem : Nat) → α → Nat → α → Nat → M (Node α)
  | 0, v1, _, v2, _ => do
    let c ← mkCollision [v1, v2]
    pure (match own with | some e => owned c e | none => c)
  | r + 1, v1, h1, v2, h2 => do
    let shift := maxShift - 5 * (r + 1)
    let i1 := idxAt h1 shift
    let i2 := idxAt h2 shift
    if i1 == i2 then
      let merged ← makeMerged own r v1 h1 v2 h2
      let n ← mkInner (1 <<< i1) 0 [] [merged]
      pure (match own with | some e => owned n e | none => n)
    else
      let xs := if i1 < i2 then [v1, v2] else [v2, v1]
      let n ← mkInner 0 ((1 <<< i1) ||| (1 <<< i2)) xs []
      pure (match own with | some e => ownedValues n e | none => n)

/-! ## The tree -/

structure Champ (α : Type) where
  root : Node α
  size : Nat
  deriving Repr

/-- `champ::empty()`: a static node. -/
def Champ.empty : Champ α := { root := .inner 1 0 0 0 none [], size := 0 }

instance : Inhabited (Champ α) := ⟨Champ.empty⟩

/-- The first index in `xs` satisfying `p`. -/
def findIdx? {β : Type} (xs : List β) (p : β → Bool) : Option Nat := xs.findIdx? p

/-! ### `get` -/

/-- `champ::get<Project, Default>(k)`: the stored element `Equal`'s accepted, if any. The loop
runs `max_depth` times shifting `hash` right by `B`; then the collision node. -/
def getLoop (cfg : Cfg α κ) (k : κ) : (rem : Nat) → Node α → Nat → Option α
  | 0, node, _ => node.collisions.find? fun x => cfg.eqTK x k
  | r + 1, node, hash =>
    let bit := 1 <<< (hash &&& 31)
    if node.nodemap &&& bit != 0 then
      getLoop cfg k r (node.child (node.childrenCountBit bit)) (hash >>> 5)
    else if node.datamap &&& bit != 0 then
      let v? := node.values[node.dataCountBit bit]?
      match v? with
      | some v => if cfg.eqTK v k then some v else none
      | none => none
    else none

def Champ.get (cfg : Cfg α κ) (c : Champ α) (k : κ) : Option α := getLoop cfg k 13 c.root (cfg.hashK k)

/-! ### `add` (persistent) -/

/-- `champ::do_add(node, v, hash, shift)` → `(node, added)`. -/
def doAdd [Inhabited α] (cfg : Cfg α κ) : (rem : Nat) → Node α → α → Nat → M (Node α × Bool)
  | 0, node, v, _ => do
    match findIdx? node.collisions (fun x => cfg.eqTT x v) with
    | some pos => pure (← copyCollisionReplace node pos v, false)
    | none => pure (← copyCollisionInsert node v, true)
  | r + 1, node, v, hash => do
    let shift := maxShift - 5 * (r + 1)
    let bit := bitAt hash shift
    if node.nodemap &&& bit != 0 then
      let offset := node.childrenCountBit bit
      let (child, added) ← doAdd cfg r (node.child offset) v hash
      pure (← copyInnerReplace node offset child, added)
    else if node.datamap &&& bit != 0 then
      let offset := node.dataCountBit bit
      let val := node.values.getD offset default
      if cfg.eqTT val v then
        pure (← copyInnerReplaceValue node offset v, false)
      else
        let child ← makeMerged none r v hash val (cfg.hashT val)
        pure (← copyInnerReplaceMerged node bit offset child, true)
    else
      pure (← copyInnerInsertValue node bit v, true)

/-- `champ::add(v) const`. -/
def Champ.add [Inhabited α] (cfg : Cfg α κ) (c : Champ α) (v : α) : M (Champ α) := do
  let (root, added) ← doAdd cfg 13 c.root v (cfg.hashT v)
  pure { root, size := c.size + (if added then 1 else 0) }

/-! ### `add_mut` (transient) -/

/-- `champ::do_add_mut(e, node, v, hash, shift)` → `(node, added, mutated)`. -/
def doAddMut [Inhabited α] (cfg : Cfg α κ) (e : Nat) : (rem : Nat) → Node α → α → Nat → M (Node α × Bool × Bool)
  | 0, node, v, _ => do
    match findIdx? node.collisions (fun x => cfg.eqTT x v) with
    | some pos =>
      if node.canMutate e then
        -- `*fst = std::move(v)` in place
        match node with
        | .collision id t xs => pure (.collision id t (setL xs pos v), false, true)
        | other => pure (other, false, true)
      else
        let r ← copyCollisionReplace node pos v
        pure (owned r e, false, false)
    | none =>
      let mutate := node.canMutate e
      let r ← if mutate then moveCollisionInsert node v else copyCollisionInsert node v
      pure (owned r e, true, mutate)
  | r + 1, node, v, hash => do
    let shift := maxShift - 5 * (r + 1)
    let bit := bitAt hash shift
    if node.nodemap &&& bit != 0 then
      let offset := node.childrenCountBit bit
      let child := node.child offset
      if node.canMutate e then
        let (rn, added, _) ← doAddMut cfg e r child v hash
        match node with
        | .inner id t nm dm vs cs => pure (.inner id t nm dm vs (setL cs offset rn), added, true)
        | other => pure (other, added, true)
      else
        let (rn, added) ← doAdd cfg r child v hash
        let n ← copyInnerReplace node offset rn
        pure (owned n e, added, false)
    else if node.datamap &&& bit != 0 then
      let offset := node.dataCountBit bit
      let val := node.values.getD offset default
      if cfg.eqTT val v then
        if node.canMutate e then
          let n ← ensureMutableValues node e
          pure (writeValue n offset v, false, true)
        else
          let n ← copyInnerReplaceValue node offset v
          pure (ownedValues n e, false, false)
      else
        let mutate := node.canMutate e
        let mutateValues := mutate && node.canMutateValues e
        let hash2 := cfg.hashT val
        let child ← makeMerged (some e) r v hash val hash2
        let _ := mutateValues  -- `std::move(*val)` or a copy: the same object_ref
        let n ← if mutate then moveInnerReplaceMerged node bit offset child
                 else copyInnerReplaceMerged node bit offset child
        pure (ownedValuesSafe n e, true, mutate)
    else
      let mutate := node.canMutate e
      let n ← if mutate then moveInnerInsertValue node bit v else copyInnerInsertValue node bit v
      pure (ownedValues n e, true, mutate)

/-- `champ::add_mut(e, v)`. -/
def Champ.addMut [Inhabited α] (cfg : Cfg α κ) (e : Nat) (c : Champ α) (v : α) : M (Champ α) := do
  let (root, added, _) ← doAddMut cfg e 13 c.root v (cfg.hashT v)
  pure { root, size := c.size + (if added then 1 else 0) }

/-! ### `sub` (persistent) -/

/-- `sub_result`: nothing, a singleton (the element pointed to), or a tree. -/
inductive Sub (α : Type) where
  | nothing
  | singleton (x : α)
  | tree (n : Node α)

/-- `champ::do_sub(node, k, hash, shift)`. -/
def doSub [Inhabited α] (cfg : Cfg α κ) (k : κ) : (rem : Nat) → Node α → Nat → M (Sub α)
  | 0, node, _ => do
    let xs := node.collisions
    match findIdx? xs (fun x => cfg.eqTK x k) with
    | some cur =>
      if xs.length > 2 then pure (.tree (← copyCollisionRemove node cur))
      else pure (.singleton (xs.getD (if cur == 0 then 1 else 0) default))  -- fst + (cur == fst)
    | none => pure .nothing
  | r + 1, node, hash => do
    let shift := maxShift - 5 * (r + 1)
    let bit := bitAt hash shift
    if node.nodemap &&& bit != 0 then
      let offset := node.childrenCountBit bit
      match ← doSub cfg k r (node.child offset) hash with
      | .nothing => pure .nothing
      | .singleton x =>
        if node.datamap == 0 && node.childrenCount == 1 && shift > 0 then pure (.singleton x)
        else pure (.tree (← copyInnerReplaceInline node bit offset x))
      | .tree t => pure (.tree (← copyInnerReplace node offset t))
    else if node.datamap &&& bit != 0 then
      let offset := node.dataCountBit bit
      let val := node.values.getD offset default
      if cfg.eqTK val k then
        let nv := node.dataCount
        if node.nodemap != 0 || nv > 2 then pure (.tree (← copyInnerRemoveValue node bit offset))
        else if nv == 2 then
          let other := node.values.getD (if offset == 0 then 1 else 0) default
          if shift > 0 then pure (.singleton other)
          else pure (.tree (← mkInner 0 (clearBit node.datamap bit) [other] []))
        else pure (.tree Champ.empty.root)  -- `empty()`
      else pure .nothing
    else pure .nothing

/-- `champ::sub(k) const` (a singleton at the root is `IMMER_UNREACHABLE`: kept unchanged). -/
def Champ.sub [Inhabited α] (cfg : Cfg α κ) (c : Champ α) (k : κ) : M (Champ α) := do
  match ← doSub cfg k 13 c.root (cfg.hashK k) with
  | .tree t => pure { root := t, size := c.size - 1 }
  | _ => pure c

/-! ### `sub_mut` (transient) -/

/-- `sub_result_mut`: kind and data, `owned` (the singleton was moved into `store`), `mutated`. -/
structure SubMut (α : Type) where
  r : Sub α
  owned : Bool := false
  mutated : Bool := false

/-- `champ::do_sub_mut(e, node, k, hash, shift, store)`. -/
def doSubMut [Inhabited α] (cfg : Cfg α κ) (e : Nat) (k : κ) : (rem : Nat) → Node α → Nat → M (SubMut α)
  | 0, node, _ => do
    let mutate := node.canMutate e
    let xs := node.collisions
    match findIdx? xs (fun x => cfg.eqTK x k) with
    | some cur =>
      let other := xs.getD (if cur == 0 then 1 else 0) default
      if xs.length ≤ 2 then
        if mutate then
          free node.id  -- delete_collision(node) after moving the other into store
          pure { r := .singleton other, owned := true, mutated := true }
        else pure { r := .singleton other, owned := false, mutated := false }
      else
        let rn ← if mutate then moveCollisionRemove node cur else copyCollisionRemove node cur
        pure { r := .tree (owned rn e), mutated := mutate }
    | none => pure { r := .nothing }
  | r + 1, node, hash => do
    let mutate := node.canMutate e
    let shift := maxShift - 5 * (r + 1)
    let bit := bitAt hash shift
    if node.nodemap &&& bit != 0 then
      let offset := node.childrenCountBit bit
      let child := node.child offset
      let result ← if mutate then doSubMut cfg e k r child hash
        else do
          let s ← doSub cfg k r child hash
          pure { r := s, owned := false, mutated := false }
      match result.r with
      | .nothing => pure { r := .nothing }
      | .singleton x =>
        if node.datamap == 0 && node.childrenCount == 1 && shift > 0 then
          if mutate then free node.id
          pure { r := .singleton x, owned := result.owned, mutated := mutate }
        else
          let rn ← if mutate then moveInnerReplaceInline node bit offset x
                   else copyInnerReplaceInline node bit offset x
          pure { r := .tree (ownedValues rn e), mutated := mutate }
      | .tree t =>
        if mutate then
          match node with
          | .inner id tk nm dm vs cs => pure { r := .tree (.inner id tk nm dm vs (setL cs offset t)), mutated := true }
          | other => pure { r := .tree other, mutated := true }
        else
          let rn ← copyInnerReplace node offset t
          pure { r := .tree (owned rn e), mutated := false }
    else if node.datamap &&& bit != 0 then
      let offset := node.dataCountBit bit
      let val := node.values.getD offset default
      let mutateValues := mutate && node.canMutateValues e
      if cfg.eqTK val k then
        let nv := node.dataCount
        if node.nodemap != 0 || nv > 2 then
          let rn ← if mutate then moveInnerRemoveValue node bit offset else copyInnerRemoveValue node bit offset
          pure { r := .tree (ownedValuesSafe rn e), mutated := mutate }
        else if nv == 2 then
          let other := node.values.getD (if offset == 0 then 1 else 0) default
          if shift > 0 then
            if mutateValues then
              free node.id
              pure { r := .singleton other, owned := true, mutated := true }
            else pure { r := .singleton other, owned := false, mutated := false }
          else
            let rn ← mkInner 0 (clearBit node.datamap bit) [other] []
            if mutate then free node.id
            pure { r := .tree (ownedValues rn e), mutated := mutate }
        else
          if mutate then free node.id
          pure { r := .tree Champ.empty.root, mutated := mutate }
      else pure { r := .nothing }
    else pure { r := .nothing }

/-- `champ::sub_mut(e, k)`. -/
def Champ.subMut [Inhabited α] (cfg : Cfg α κ) (e : Nat) (c : Champ α) (k : κ) : M (Champ α) := do
  let res ← doSubMut cfg e k 13 c.root (cfg.hashK k)
  match res.r with
  | .tree t => pure { root := t, size := c.size - 1 }
  | _ => pure c

/-! ### Iteration (`champ_iterator`): a node's values, then its children, depth first -/

def iterNode : (rem : Nat) → Node α → List α
  | 0, node => node.collisions
  | r + 1, node =>
    node.values.take node.dataCount ++
      (node.cs.take node.childrenCount).flatMap (iterNode r)

def Champ.toList (c : Champ α) : List α := iterNode 13 c.root

/-! ### Checks (`do_check_champ` and more) -/

/-- Every stored element sits on its own hash path (`do_check_champ`): count of those that do. -/
def checkPaths (cfg : Cfg α κ) : (rem : Nat) → Node α → Nat → Nat → Nat
  | 0, node, pathHash, _ => (node.collisions.filter fun x => cfg.hashT x == pathHash).length
  | r + 1, node, pathHash, hashMask =>
    let depth := 13 - (r + 1)
    let shift := 5 * depth
    let kids := (List.range 32).filter (fun i => node.nodemap.testBit i)
    let kidCount := (kids.zip (node.cs.take node.childrenCount)).foldl (fun acc (i, c) =>
      acc + checkPaths cfg r c (pathHash ||| (i <<< shift)) ((hashMask <<< 5) ||| 31)) 0
    let datas := (List.range 32).filter (fun i => node.datamap.testBit i)
    let dataCount := (datas.zip (node.values.take node.dataCount)).countP fun (i, x) =>
      (cfg.hashT x &&& hashMask) == (pathHash ||| (i <<< shift))
    kidCount + dataCount

/-- `check_champ()`. -/
def Champ.checkChamp (cfg : Cfg α κ) (c : Champ α) : Bool := checkPaths cfg 13 c.root 0 31 == c.size

/-- Physical consistency: buffers hold at least the slots the bitmaps count. -/
def wfNode : (rem : Nat) → Node α → Bool
  | 0, node => match node with | .collision .. => node.collisions.length ≥ 2 | _ => false
  | r + 1, node =>
    match node with
    | .inner _ _ nm dm v cs =>
      decide (nm &&& dm = 0) && decide (nm < 2 ^ 32) && decide (dm < 2 ^ 32) &&
        decide (popcount nm ≤ cs.length) &&
        (match v with | some vs => decide (popcount dm ≤ vs.xs.length) | none => dm == 0) &&
        (cs.take (popcount nm)).all (wfNode r)
    | .collision .. => false

/-- `(id, tok)` of every object (nodes and values arrays) reachable through valid slots. -/
def reachNode : (rem : Nat) → Node α → List (Nat × Nat)
  | 0, node => [(node.id, node.tok)]
  | r + 1, node =>
    (node.id, node.tok) :: (match node.vals with | some v => if node.dataCount > 0 then [(v.id, v.tok)] else [] | none => []) ++
      (node.cs.take node.childrenCount).flatMap (reachNode r)

def Champ.reach (c : Champ α) : List (Nat × Nat) := reachNode 13 c.root

/-! ## `immer::map`, `immer::set` and their transients -/

/-- A transient: its champ and its owner token (map_transient / set_transient inherit `owner`). -/
structure Transient (α : Type) where
  champ : Champ α
  tok : Nat
  deriving Repr

/-- `transient() const&` → `transient_type{impl_}`: fresh owner token. -/
def Champ.transient (c : Champ α) : M (Transient α) := do pure { champ := c, tok := ← fresh }

/-- `map_transient()` / `set_transient()`: fresh owner, `impl_t::empty()`. -/
def Transient.empty : M (Transient α) := do pure { champ := Champ.empty, tok := ← fresh }

/-- `persistent() &`: `owner_t::operator=(owner_t{})` (fresh token), the champ shared. -/
def Transient.persistentL (t : Transient α) : M (Champ α × Transient α) := do
  pure (t.champ, { t with tok := ← fresh })

/-- `persistent() &&`: `std::move(impl_)`: the champ moved out (`champ(champ&&)` swaps with
`empty()`), the owner token kept. -/
def Transient.persistentR (t : Transient α) : Champ α × Transient α :=
  (t.champ, { t with champ := Champ.empty })

end Jank.R3.Immer.Champ
