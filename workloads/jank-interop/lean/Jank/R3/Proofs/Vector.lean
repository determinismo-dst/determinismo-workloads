import Jank.Vector

/-!
# Vectors: jank's index checks against Clojure's documented behavior, every input (round 3)

Round 1's `Jank.Vector` theorems (`get_in_range`, `get_out_of_range`, `contains_iff`,
`nth_some_iff_contains`, `assoc_count`, `assoc_get`, `pop_conj`, `subvec_length`) already hold for
every vector and index. They leave out the failing sides (when `assoc`, `pop`, `subvec`, `nth`
throw) and what `subvec` returns; round 2 checked transient `nth` after `persistent!` on one
example. These complete them, each for every input:

- `nth_iff`: `nth` returns the element exactly when the index is in range (APersistentVector /
  PersistentVector.nth: `IndexOutOfBoundsException` otherwise; a non-integer key throws);
- `assoc_none_iff`: `assoc` throws exactly when the index is negative or past the count
  ("index must be <= count"); `assoc_set` replaces in range;
- `pop_none_iff`: `pop` throws exactly on the empty vector ("Can't pop empty vector");
- `subvec_none_iff`, `subvec_spec`: `subvec` throws exactly when `end > count`, `start > end`
  or `start < 0` (APersistentVector.SubVector / core.clj), else returns the elements in
  `[start, end)`;
- `transient_nth_agrees`: jank 7135b7708's transient `nth` answers as Clojure's for every
  transient, active or not, and every index (the value, or an exception).
-/

namespace Jank.R3.Proofs.Vector

open Jank.Vector

variable {α : Type}

theorem nth_iff (v : List α) (i : Int) (x : α) :
    nth v (.int i) = some x ↔ 0 ≤ i ∧ ∃ h : i.toNat < v.length, v[i.toNat] = x := by
  unfold nth
  by_cases h1 : i < 0
  · simp [h1]; omega
  · by_cases h2 : v.length ≤ i.toNat
    · simp [h1, h2]; intro _ h; omega
    · have h3 : i.toNat < v.length := by omega
      simp [h1, h2, List.getElem?_eq_getElem h3]
      constructor
      · intro h; exact ⟨by omega, h3, h⟩
      · intro ⟨_, _, h⟩; exact h

theorem nth_other (v : List α) : nth v .other = none := rfl

theorem get_other (v : List α) (fb : α) : get v .other fb = fb := rfl

theorem contains_other (v : List α) : contains v .other = false := rfl

theorem assoc_none_iff (v : List α) (i : Int) (x : α) :
    assoc v (.int i) x = none ↔ (i < 0 ∨ (v.length : Int) < i) := by
  simp only [assoc]
  by_cases h : i > v.length ∨ 0 > i
  · rw [ite_cond_eq_true _ _ (eq_true h)]; constructor
    · intro _; omega
    · intro _; rfl
  · rw [ite_cond_eq_false _ _ (eq_false h)]; constructor
    · intro hc; split at hc <;> simp at hc
    · intro hc; omega

theorem assoc_other (v : List α) (x : α) : assoc v .other x = none := rfl

theorem assoc_set (v : List α) (i : Nat) (h : i < v.length) (x : α) :
    assoc v (.int i) x = some (v.set i x) := by
  have h' : ¬ ((i : Int) > v.length ∨ 0 > (i : Int)) := by omega
  have h'' : ((i : Int).toNat == v.length) = false := by simp; omega
  simp only [assoc, h', h'', ite_false, Bool.false_eq_true]
  simp

theorem pop_none_iff (v : List α) : pop v = none ↔ v = [] := by
  unfold pop
  cases v <;> simp

theorem subvec_none_iff (v : List α) (s e : Int) :
    subvec v s e = none ↔ (e < s ∨ s < 0 ∨ (v.length : Int) < e) := by
  unfold subvec
  by_cases h : e < s ∨ s < 0 ∨ e > v.length
  · rw [ite_cond_eq_true _ _ (eq_true h)]; constructor
    · intro _; omega
    · intro _; rfl
  · rw [ite_cond_eq_false _ _ (eq_false h)]; constructor
    · intro hc; split at hc <;> simp at hc
    · intro hc; omega

theorem subvec_spec (v : List α) (s e : Nat) (h1 : s ≤ e) (h2 : e ≤ v.length) :
    subvec v s e = some ((v.drop s).take (e - s)) := by
  unfold subvec
  have hn : ¬ ((e : Int) < s ∨ (s : Int) < 0 ∨ (e : Int) > v.length) := by omega
  simp only [hn, ite_false]
  by_cases hse : s = e
  · subst hse; simp
  · have : ((s : Int) == (e : Int)) = false := by simp; omega
    simp only [this, Bool.false_eq_true, ite_false]
    congr 2
    omega

/-- Transient `nth` (transient_vector.cpp:53, `assert_active()` first) answers as Clojure's
`TransientVector.nth` (`ensureEditable()` first): the same value, or both throw. -/
theorem transient_nth_agrees (t : Transient α) (i : Nat) :
    (tNth t i).toOption = (cTNth t i).toOption := by
  unfold tNth cTNth
  by_cases ha : t.active = true
  · simp only [ha, Bool.not_true, Bool.false_eq_true, ite_false]
    cases t.data[i]? <;> rfl
  · simp [ha, Except.toOption]

end Jank.R3.Proofs.Vector
