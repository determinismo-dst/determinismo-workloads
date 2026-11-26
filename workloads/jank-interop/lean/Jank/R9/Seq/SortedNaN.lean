/-!
# Round 9, area Seq: sorted collections with a key that compares 0 with everything (T9-10)

`(compare ##NaN x)` is 0 for every number in both (Numbers.compare; number.cpp real::compare
342-356), so ##NaN is "equal" to every key of a sorted map or set. Which key it lands on is then the
search's choice.

**jank 94d32623**: `persistent_sorted_map` is `std::map<object_ref, object_ref, object_ref_compare>`
and the set `std::set<...>` (runtime/detail/type.hpp 49-65; type.cpp 6: `compare(l, r) < 0`).
persistent_sorted_map.cpp: `get` 60-68 and `find` 80-88 call `data.find`, `assoc` 95-101
`copy[key] = val`, `dissoc` 103-108 `copy.erase(key)`; persistent_sorted_set.cpp `disj` 198-203
`copy.erase(o)`. libstdc++ (bits/stl_tree.h, stl_map.h): `find` and `operator[]` are
`_M_lower_bound` (go left while `!less(node, k)`, remembering the node), then an equivalence test;
`erase(k)` erases `equal_range(k)`: `_M_equal_range` stops at the first node with neither
`less(node, k)` nor `less(k, node)`, then takes `_M_lower_bound` in its left subtree and
`_M_upper_bound` (go right while `!less(k, node)`) in its right subtree.

**Clojure 1.12.3**: PersistentTreeMap.entryAt (`get`, `contains?`), `add`/`replace` (`assoc`) and
`remove` (`dissoc`, the set's `disjoin`) stop at the first node whose `doCompare` is 0: the root.

Proved here for every tree (any shape, so for every insertion order and either balancing):
- ★ `jank_lower_bound_nan`: jank's `find`/`operator[]` land on the minimum key;
- ★ `jank_equal_range_nan`: jank's `erase` removes every element;
- ★ `clj_find_nan`: Clojure's search lands on the root.
So `(get (sorted-map 1 :a 2 :b 3 :c) ##NaN)` is :a in jank (the minimum) and :b in Clojure (the
root), `(dissoc m ##NaN)` is {} in jank, and `(assoc m ##NaN :x)` writes the minimum's value.
Clojure's tree shapes are not replicated: its results were run on Clojure 1.12.3.
-/

namespace Jank.R9.Seq.SortedNaN

/-- A search tree's keys: numbers and NaN. -/
inductive K where
  | num (v : Int)
  | nan
  deriving DecidableEq, Repr

/-- `compare(a, b) < 0`: false whenever a NaN takes part. -/
def less : K → K → Bool
  | .num a, .num b => decide (a < b)
  | _, _ => false

inductive Tree where
  | leaf
  | node (l : Tree) (k : K) (r : Tree)
  deriving Repr

def Tree.size : Tree → Nat
  | .leaf => 0
  | .node l _ r => l.size + 1 + r.size

def Tree.inorder : Tree → List K
  | .leaf => []
  | .node l k r => l.inorder ++ [k] ++ r.inorder

/-- `_M_lower_bound(x, y, k)` as an in-order index: the first node with `!less(node, k)`, or
`size` (y = end). -/
def lowerBound (p : K) : Tree → Nat
  | .leaf => 0
  | .node l k r => if !less k p then lowerBound p l else l.size + 1 + lowerBound p r

/-- `_M_upper_bound`: the first node with `less(k, node)`, as an in-order index. -/
def upperBound (p : K) : Tree → Nat
  | .leaf => 0
  | .node l k r => if less p k then upperBound p l else l.size + 1 + upperBound p r

theorem lowerBound_le (p : K) (t : Tree) : lowerBound p t ≤ t.size := by
  induction t with
  | leaf => simp [lowerBound, Tree.size]
  | node l k r ihl ihr =>
    simp only [lowerBound, Tree.size]
    split <;> omega

/-- `_M_equal_range`: descend until a node is equivalent to the probe; then the lower bound in its
left subtree and the upper bound in its right subtree. In-order indices [lo, hi). -/
def equalRange (p : K) : Tree → Nat × Nat
  | .leaf => (0, 0)
  | .node l k r =>
    if less k p then
      let (a, b) := equalRange p r
      (l.size + 1 + a, l.size + 1 + b)
    else if less p k then equalRange p l
    else (lowerBound p l, l.size + 1 + upperBound p r)

/-- ★ For every tree, the NaN probe's lower bound is index 0: `find` and `operator[]` land on the
minimum key (the first of the in-order walk). -/
theorem jank_lower_bound_nan (t : Tree) : lowerBound .nan t = 0 := by
  induction t with
  | leaf => rfl
  | node l k r ihl _ => cases k <;> simp [lowerBound, less, ihl]

theorem upper_bound_nan (t : Tree) : upperBound .nan t = t.size := by
  induction t with
  | leaf => rfl
  | node l k r _ ihr => cases k <;> simp [upperBound, less, ihr, Tree.size]

/-- ★ For every tree, `equal_range(NaN)` is the whole tree: `erase` removes every element. -/
theorem jank_equal_range_nan (t : Tree) : equalRange .nan t = (0, t.size) := by
  cases t with
  | leaf => rfl
  | node l k r =>
    cases k <;> simp [equalRange, less, jank_lower_bound_nan, upper_bound_nan, Tree.size]

/-- Clojure's PersistentTreeMap search: the first node whose compare is 0. -/
def cljFind (p : K) : Tree → Option K
  | .leaf => none
  | .node l k r =>
    if less p k then cljFind p l
    else if less k p then cljFind p r
    else some k

/-- ★ For every non-empty tree, Clojure's search for NaN stops at the root. -/
theorem clj_find_nan (l r : Tree) (k : K) : cljFind .nan (.node l k r) = some k := by
  cases k <;> simp [cljFind, less]

/-- The two land on the same key exactly when the root is the minimum (the root has no left
subtree): e.g. one key, or keys 1 then 2 inserted in order. -/
theorem same_key_iff_no_left (l r : Tree) (k : K) :
    ((.node l k r : Tree).inorder[lowerBound .nan (.node l k r)]? = cljFind .nan (.node l k r)) ↔
      (l.inorder.head? = none ∨ l.inorder.head? = some k) := by
  rw [jank_lower_bound_nan, clj_find_nan]
  cases h : l.inorder with
  | nil => simp [Tree.inorder, h]
  | cons x xs => simp [Tree.inorder, h]

end Jank.R9.Seq.SortedNaN
