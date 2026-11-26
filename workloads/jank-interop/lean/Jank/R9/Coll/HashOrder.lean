import Jank.R9.Coll.Order

/-!
# Round 9, area Coll: a hash collection's seq order, jank's CHAMP against Clojure's HAMT (M9-11)

Both index a key's 32-bit hash 5 bits at a time from the low end (immer `champ` with B = 5,
hamts/bits.hpp; Clojure PersistentHashMap `mask(hash, shift) = (hash >>> shift) & 0x01f`), and a
long hashes alike in both (Murmur3 `hashLong`; round 1's `integer_eq_hashLong`). They differ in where
a node keeps a sub-node:
- Clojure's `BitmapIndexedNode` keeps one array, entries and sub-nodes interleaved at their bit
  positions; `NodeSeq` walks it in position order (an `ArrayNode`, past 16 entries, makes every
  entry a one-entry sub-node at the same position). Its order: by the hash's 5-bit chunks read from
  the low end, lexicographically (`cljOrd`).
- immer's CHAMP node keeps its inline values (datamap) apart from its children (nodemap);
  `champ_iterator` (champ_iterator.hpp `step_down`/`step_right`) yields a node's values, then each
  child depth first (`champOrd`; round 3's replica `iterNode`, `Champ.toList`).
So a node holding a sub-node at position i and an inline entry at position j > i shows the entry
after the sub-node's keys in Clojure and before them in jank.

Keys here have distinct full hashes (no collision node); `depth` counts levels from the root.
-/

namespace Jank.R9.Coll.HashOrder

open Jank.R3.Immer.Champ Jank.R8.Champ.Programs Jank.R9.Coll.Order

/-- The 5-bit chunk of `h` at level `d`. -/
def idx (d h : Nat) : Nat := (h >>> (5 * d)) % 32

/-- The keys (with their hashes) at position `i` of level `d`. -/
def grp (d : Nat) (xs : List (Int × Nat)) (i : Nat) : List (Int × Nat) :=
  xs.filter (fun x => idx d x.2 == i)

/-- Clojure's HAMT order: positions in order, a crowded position recursed into in place. -/
def cljOrd : (fuel : Nat) → (d : Nat) → List (Int × Nat) → List Int
  | 0, _, xs => xs.map Prod.fst
  | f + 1, d, xs =>
    (List.range 32).flatMap fun i =>
      let g := grp d xs i
      if g.length ≥ 2 then cljOrd f (d + 1) g else g.map Prod.fst

/-- jank's CHAMP order: the inline keys (alone at their position) in order, then the crowded
positions, each recursed into. -/
def champOrd : (fuel : Nat) → (d : Nat) → List (Int × Nat) → List Int
  | 0, _, xs => xs.map Prod.fst
  | f + 1, d, xs =>
    ((List.range 32).flatMap fun i =>
      let g := grp d xs i
      if g.length ≥ 2 then [] else g.map Prod.fst) ++
    ((List.range 32).flatMap fun i =>
      let g := grp d xs i
      if g.length ≥ 2 then champOrd f (d + 1) g else [])

/-- With the hashes `hLong` of the keys. -/
def withHash (ks : List Int) : List (Int × Nat) := ks.map fun k => (k, hLong k)

theorem flatMap_ext' {α β : Type} {l : List α} {f g : α → List β} (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons]
    rw [h a (List.mem_cons_self ..), ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem flatMap_perm' {α β : Type} {l : List α} {f g : α → List β} (h : ∀ x ∈ l, (f x).Perm (g x)) :
    (l.flatMap f).Perm (l.flatMap g) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons a l ih =>
    simp only [List.flatMap_cons]
    exact List.Perm.append (h a (List.mem_cons_self ..)) (ih (fun x hx => h x (List.mem_cons_of_mem _ hx)))

theorem flatMap_append_perm {α β : Type} (l : List α) (f g : α → List β) :
    (l.flatMap (fun x => f x ++ g x)).Perm (l.flatMap f ++ l.flatMap g) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons a l ih =>
    simp only [List.flatMap_cons, List.append_assoc]
    refine List.Perm.append_left _ ?_
    refine (List.Perm.append_left _ ih).trans ?_
    rw [← List.append_assoc, ← List.append_assoc]
    exact List.Perm.append_right _ List.perm_append_comm

/-- ★ For every key list and level: if no position of the level holds two keys, jank's order is
Clojure's (both list the keys by their chunk at that level). -/
theorem champ_eq_clj_without_crowding (f d : Nat) (xs : List (Int × Nat))
    (h : ∀ i, (grp d xs i).length < 2) : champOrd (f + 1) d xs = cljOrd (f + 1) d xs := by
  simp only [champOrd, cljOrd]
  have h1 : ((List.range 32).flatMap fun i =>
      if (grp d xs i).length ≥ 2 then champOrd f (d + 1) (grp d xs i) else []) = [] := by
    rw [List.flatMap_eq_nil_iff]
    intro i _
    have := h i
    rw [if_neg (by omega)]
  rw [h1, List.append_nil]
  apply flatMap_ext'
  intro i _
  have := h i
  rw [if_neg (by omega), if_neg (by omega)]

/-- ★ The two orders hold the same keys (one is a permutation of the other), for every list,
level and fuel. -/
theorem champ_perm_clj (f d : Nat) (xs : List (Int × Nat)) :
    (champOrd f d xs).Perm (cljOrd f d xs) := by
  induction f generalizing d xs with
  | zero => exact List.Perm.refl _
  | succ f ih =>
    simp only [champOrd, cljOrd]
    have key : ∀ i ∈ List.range 32,
        ((if (grp d xs i).length ≥ 2 then [] else (grp d xs i).map Prod.fst) ++
         (if (grp d xs i).length ≥ 2 then champOrd f (d + 1) (grp d xs i) else [])).Perm
        (if (grp d xs i).length ≥ 2 then cljOrd f (d + 1) (grp d xs i)
          else (grp d xs i).map Prod.fst) := by
      intro i _
      by_cases hc : (grp d xs i).length ≥ 2
      · rw [if_pos hc, if_pos hc, if_pos hc, List.nil_append]; exact ih (d + 1) _
      · rw [if_neg hc, if_neg hc, if_neg hc, List.append_nil]
    exact (flatMap_append_perm _ _ _).symm.trans (flatMap_perm' key)

/-- `(vec (hash-set 5 9 8))`: 5 and 9 share position 23 at the root, 8 is alone at 31. Clojure
`[9 5 8]`, jank `[8 9 5]`; the replica's CHAMP (`build`, `Champ.toList`) agrees with `champOrd`. -/
theorem set_5_9_8 :
    cljOrd 7 0 (withHash [5, 9, 8]) = [9, 5, 8] ∧
    champOrd 7 0 (withHash [5, 9, 8]) = [8, 9, 5] ∧
    jankKeys [(5, 0), (9, 0), (8, 0)] = [8, 9, 5] := by
  decide +kernel

end Jank.R9.Coll.HashOrder
