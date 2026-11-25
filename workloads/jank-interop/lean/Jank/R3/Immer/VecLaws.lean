import Jank.R3.Immer.Objects
import Jank.R3.Immer.RbtsLaws

/-!
# jank's vector functions over the replica: `subvec` bounds and counts, `from_range`

- `fromList_size`: `from_range` (`vector(Iter, Sent)`: `push_back_mut` of each) has as many
  elements as it was given.
- `subvec_ok_iff`: core/seq.cpp `subvec` returns exactly when `start ≤ end`, `0 ≤ start` and
  `end ≤ count` (Clojure's `subvec` bounds), and then `subvec_count`: `end - start` elements.
-/

namespace Jank.R3.Immer.Objects

open Rbts

theorem foldl_pushBackMut_size {α : Type} [Inhabited α] (e : Nat) (xs : List α) :
    ∀ (acc : Tree α × Nat), (xs.foldl (fun (acc : Tree α × Nat) x => acc.1.pushBackMut e x acc.2) acc).1.size =
      acc.1.size + xs.length := by
  induction xs with
  | nil => intro acc; simp
  | cons x xs ih =>
    intro acc
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, pushBackMut_size]
    omega

theorem fromList_size {α : Type} [Inhabited α] (xs : List α) (n : Nat) :
    (Tree.fromList xs n).1.size = xs.length := by
  unfold Tree.fromList
  rw [foldl_pushBackMut_size]
  simp [Tree.empty]

theorem subvec_ok_iff (v : JVec) (s e : Int) (n : Nat) :
    (match (vecSubvec v s e n).1 with | .ok _ => true | .throws _ => false) = true ↔
      (s ≤ e ∧ 0 ≤ s ∧ e ≤ v.size) := by
  unfold vecSubvec
  by_cases h : e < s ∨ s < 0 ∨ e > v.size
  · have : (decide (e < s) || decide (s < 0) || decide (e > ↑v.size)) = true := by
      rcases h with h | h | h <;> simp [h]
    simp only [this, ite_true]
    constructor
    · intro h'; simp at h'
    · intro ⟨h1, h2, h3⟩; omega
  · have : (decide (e < s) || decide (s < 0) || decide (e > ↑v.size)) = false := by
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
    simp only [this, Bool.false_eq_true, ite_false]
    constructor
    · intro _; omega
    · intro _
      by_cases hse : s = e
      · simp [hse]
      · simp [hse]

theorem subvec_count (v : JVec) (s e : Int) (n : Nat) (h1 : s ≤ e) (h2 : 0 ≤ s) (h3 : e ≤ v.size) :
    (match (vecSubvec v s e n).1 with | .ok w => w.size | .throws _ => 0) = (e - s).toNat := by
  unfold vecSubvec
  have : (decide (e < s) || decide (s < 0) || decide (e > ↑v.size)) = false := by
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
  simp only [this, Bool.false_eq_true, ite_false]
  by_cases hse : s = e
  · subst hse; simp [Tree.empty]
  · rw [if_neg (by simpa using hse)]
    dsimp only
    simp only [fromList_size, List.length_map, List.length_take, List.length_drop, iter_length, Nat.min_def]
    split <;> first | rfl | omega

end Jank.R3.Immer.Objects
