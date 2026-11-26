import Jank.R8.Champ.Agree
import Jank.Hash

/-!
# Round 8, CHAMP: H8-1 on the replica (assoc/conj of a present key reorders a collision node)

immer's persistent `do_add` replaces a stored value `Equal` to the new one by
`copy_collision_replace` (node.hpp 495-523: the new value first, then the others in order), so in a
collision node (keys whose full hashes are equal) `assoc`/`conj` of a key already present moves it to
the front: the map's or set's `seq` order changes though its contents do not (and for a set, do not
change at all). `do_add_mut` writes in place when the transient owns the node, keeping the order
(`addMut_agree`, `InPlace`). Clojure keeps the order on both paths (HashCollisionNode.assoc
`cloneAndSet(array, idx + 1, val)` or `editAndSet`, PersistentHashSet.cons returns the set itself).

Keys: the longs 1 and 7676047846, whose jank hashes (hash.cpp `integer(i64)`, Murmur3 of the 64
bits, round 1's `Jank.Hash.integer`) are both 1392991556; jank's `=` on two longs is value equality
(`mapLawful`: a lawful equality, so none of jank's `=` defects is involved). jank's `hash-map` and
`hash-set` of several values build through a transient (`create_from_seq`: `transient.set` /
`transient.insert`, persistent_hash_map.cpp 55-71, persistent_hash_set.cpp 45-53); `assoc`
(persistent_hash_map.cpp 110-114) and `conj` (persistent_hash_set.cpp 149-154) are `do_add`;
`assoc!` (transient_hash_map.cpp 96-101) is `add_mut`. `keys` (core.jank 2316-2325) and `seq` walk
`champ_iterator` (replica `iterNode`: a collision node's list in order).

Every statement here is about the replica with these two keys (`decide +kernel`).
-/

namespace Jank.R8.Champ.Programs

open Jank.R3.Immer.Champ Jank.R6.Champ Jank.R7.Champ Jank.R8.Champ

/-- jank's hash of a long: `integer::to_hash` → hash.cpp `integer(i64)`. -/
def hLong (n : Int) : Nat := (Jank.Hash.integer (UInt64.ofInt n)).toNat

/-- `immer::map<object_ref, object_ref>` over long keys: a stored element is the pair (key, value);
`hash_key` and `equal_key` read the key (map.hpp); jank's `=` on longs compares values. Values `:a`
and `:b` are 0 and 1. -/
def mapCfg : Cfg (Int × Nat) Int where
  hashT p := hLong p.1
  hashK k := hLong k
  eqTT a b := a.1 == b.1
  eqTK a k := a.1 == k

def mapLawful : Lawful mapCfg where
  key := Prod.fst
  eqK a b := a == b
  hashT_key _ := rfl
  eqTT_key _ _ := rfl
  eqTK_key _ _ := rfl
  refl k := by simp
  symm a b h := by simp at h ⊢; omega
  trans a b c h1 h2 := by simp at h1 h2 ⊢; omega
  compat a b h := by simp at h; simp [mapCfg, h]

/-- `immer::set<object_ref>` over longs. -/
def setCfg : Cfg Int Int where
  hashT := hLong
  hashK := hLong
  eqTT a b := a == b
  eqTK a k := a == k

def k1 : Int := 1
def k2 : Int := 7676047846

/-- The premise, checked on jank by the control test: one full hash (and Clojure's, the same Murmur3). -/
theorem same_hash : hLong k1 = 1392991556 ∧ hLong k2 = 1392991556 := by decide +kernel

/-- Owner tokens: the `create_from_seq` transient's, and a `(transient (hash-map))`'s. -/
def tokCreate : Nat := 1000
def tokT : Nat := 1001

def keysOf (c : Champ (Int × Nat)) : List Int := c.toList.map Prod.fst

/-- `(hash-map k1 :a k2 :a)`: `create_from_seq`, two `transient.set`s. -/
def m0 : Champ (Int × Nat) :=
  ((do let c ← (Champ.empty : Champ (Int × Nat)).addMut mapCfg tokCreate (k1, 0)
       c.addMut mapCfg tokCreate (k2, 0)) : M _).run {} |>.1

/-- `(assoc m k :b)`. -/
def assocP (m : Champ (Int × Nat)) (k : Int) : Champ (Int × Nat) := ((m.add mapCfg (k, 1)).run {}).1

/-- vH1: `(keys (hash-map 1 :a 7676047846 :a))` is `(7676047846 1)`; after `(assoc m 1 :b)` it is
`(1 7676047846)`. Clojure: the same order before and after. -/
theorem vH1_map_reordered : keysOf m0 = [k2, k1] ∧ keysOf (assocP m0 k1) = [k1, k2] := by decide +kernel

/-- vH1 control: `(assoc m 7676047846 :b)` (the key first in its collision node) keeps the order. -/
theorem vH1_control_first_key : keysOf (assocP m0 k2) = [k2, k1] := by decide +kernel

/-- `(-> (transient (hash-map)) (assoc! 1 :a) (assoc! 7676047846 :a) (assoc! 1 :b) persistent!)`: the
transient owns every node it made, so the last `assoc!` writes in place. -/
def tChain : Champ (Int × Nat) :=
  ((do let c ← (Champ.empty : Champ (Int × Nat)).addMut mapCfg tokT (k1, 0)
       let c ← c.addMut mapCfg tokT (k2, 0)
       c.addMut mapCfg tokT (k1, 1)) : M _).run {} |>.1

/-- `(-> (hash-map) (assoc 1 :a) (assoc 7676047846 :a) (assoc 1 :b))`. -/
def pChain : Champ (Int × Nat) :=
  ((do let c ← (Champ.empty : Champ (Int × Nat)).add mapCfg (k1, 0)
       let c ← c.add mapCfg (k2, 0)
       c.add mapCfg (k1, 1)) : M _).run {} |>.1

/-- vH1c: the transient chain and the persistent chain hold the same entries in different orders
(under a lawful equality). Clojure: the same order. -/
theorem vH1_transient_vs_persistent :
    keysOf tChain = [k2, k1] ∧ keysOf pChain = [k1, k2] ∧ tChain.toList.Perm pChain.toList := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  rw [show tChain.toList = [(k2, 0), (k1, 1)] by decide +kernel,
    show pChain.toList = [(k1, 1), (k2, 0)] by decide +kernel]
  exact List.Perm.swap _ _ []

/-- `(hash-set 1 7676047846)`: `create_from_seq`, two `transient.insert`s. -/
def s0 : Champ Int :=
  ((do let c ← (Champ.empty : Champ Int).addMut setCfg tokCreate k1
       c.addMut setCfg tokCreate k2) : M _).run {} |>.1

/-- vH1b: `(seq (hash-set 1 7676047846))` is `(7676047846 1)`; `(seq (conj s 1))` is `(1 7676047846)`
(a set whose contents did not change). Clojure: `conj` of a member returns the set itself. -/
theorem vH1b_set_reordered : s0.toList = [k2, k1] ∧ ((s0.add setCfg k1).run {}).1.toList = [k1, k2] := by
  decide +kernel

/-- vH1b control: `(conj s 7676047846)` keeps the order. -/
theorem vH1b_control : ((s0.add setCfg k2).run {}).1.toList = [k2, k1] := by decide +kernel

/-- vH1b: `(assoc m 1 :a)`, the value it already has, reorders too (Clojure returns `m` itself). -/
theorem vH1b_same_value : keysOf ((m0.add mapCfg (k1, 0)).run {}).1 = [k1, k2] := by decide +kernel

/-- vH1e: `(persistent! (assoc! (transient m) 1 :b))`: a new transient (token `tokT`) does not own `m`'s
nodes (made under `tokCreate`), so `do_add_mut` copies the collision node and reorders it. -/
theorem vH1e_new_transient : keysOf ((m0.addMut mapCfg tokT (k1, 1)).run {}).1 = [k1, k2] := by decide +kernel

/-- The transient chain without its last `assoc!`. -/
def tPrefix : Champ (Int × Nat) :=
  ((do let c ← (Champ.empty : Champ (Int × Nat)).addMut mapCfg tokT (k1, 0)
       c.addMut mapCfg tokT (k2, 0)) : M _).run {} |>.1

/-- vH1d control: inside the transient that made the collision node, `assoc!` keeps the order. -/
theorem vH1d_control : keysOf tPrefix = keysOf tChain := by decide +kernel

end Jank.R8.Champ.Programs
