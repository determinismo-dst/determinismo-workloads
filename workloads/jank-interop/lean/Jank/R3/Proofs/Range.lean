import Jank.Seq.IntRange

/-!
# `range` over integers with an exact count: Clojure's sequence, every input (round 3, proofs)

Round 2 (`Jank.Seq.IntRange`) replicated integer_range.cpp: `count()` (186) computes
`end - start` in i64 and wraps (1,364 of 5,219 questions over 17 drawn i64 values differ from
Clojure). With the count computed exactly (`countExact`, the fix the round-2 search used), the
same object walks as Clojure's LongRange/Range: complete over the 5,219 questions, nothing found.
Here for every `start`, `end`, `step` in i64 and every number of elements walked:

- `fixed_walk_agrees`: `(range start end step)` with the exact count walks exactly Clojure's
  elements, with the same ending (`integer_range.cpp` `create` and `next` otherwise as written:
  `start + step` in i64, which never wraps while an element remains);
- `fixed_walk_agrees2`, `fixed_walk_agrees1`: the 2- and 1-argument forms.
-/

namespace Jank.R3.Proofs.Range

open Jank.Seq.IntRange

theorem ceil_le_one (d s : Int) (hs : 0 < s) : (d + s - 1) / s ≤ 1 ↔ d ≤ s := by
  rw [Int.ediv_le_iff_le_mul hs]
  constructor <;> intro h <;> omega

theorem go_stop (st : Int) (inside : Int → Bool) (f : Nat) (v : Int) (acc : List Int) (h : inside v = false) :
    cljWalk.go st inside f v acc = ⟨acc.reverse, .done⟩ := by
  cases f <;> simp [cljWalk.go, h]

theorem bounds (x : I64) : -2 ^ 63 ≤ x.toInt ∧ x.toInt < 2 ^ 63 :=
  ⟨by have := BitVec.le_toInt x; simpa using this, by have := @BitVec.toInt_lt 64 x; simpa using this⟩

theorem add_exact (x y : I64) (h1 : -2 ^ 63 ≤ x.toInt + y.toInt) (h2 : x.toInt + y.toInt < 2 ^ 63) :
    (x + y).toInt = x.toInt + y.toInt := by
  apply BitVec.toInt_add_of_not_saddOverflow
  simp only [BitVec.saddOverflow, Bool.or_eq_true, decide_eq_true_eq, not_or]
  constructor <;> simp <;> omega

/-- A positive step: the exact walk is Clojure's from any start below `end`. -/
theorem walk_pos (st e : I64) (hst : 0 < st.toInt) :
    ∀ (f : Nat) (r : IntRange) (acc : List Int), r.step = st → r.finish = e → r.start.toInt < e.toInt →
      walkExact f r acc = cljWalk.go st.toInt
        (fun v => if st.toInt > 0 then decide (v < e.toInt) else decide (v > e.toInt)) f r.start.toInt acc := by
  intro f
  induction f with
  | zero =>
    intro r acc _ _ hlt
    simp [walkExact, cljWalk.go, hst, hlt]
  | succ f ih =>
    intro r acc hs he hlt
    have hin : (if st.toInt > 0 then decide (r.start.toInt < e.toInt) else decide (r.start.toInt > e.toInt)) = true := by
      simp [hst, hlt]
    simp only [walkExact, cljWalk.go, hin, ite_true]
    have hc : countExact r = (e.toInt - r.start.toInt + st.toInt - 1) / st.toInt := by
      simp [countExact, hs, he, hst]
    by_cases hle : e.toInt - r.start.toInt ≤ st.toInt
    · have : countExact r ≤ 1 := by rw [hc]; exact (ceil_le_one _ _ hst).mpr hle
      simp only [this, decide_true, ite_true]
      rw [go_stop]
      simp [hst]; omega
    · have : ¬ countExact r ≤ 1 := by rw [hc]; intro h; exact hle ((ceil_le_one _ _ hst).mp h)
      simp only [this, decide_false, Bool.false_eq_true, ite_false]
      have hb1 := bounds r.start
      have hb2 := bounds e
      have hadd : (r.start + r.step).toInt = r.start.toInt + st.toInt := by
        rw [hs]; exact add_exact _ _ (by omega) (by omega)
      rw [ih { r with start := r.start + r.step } _ hs he (by simp only; omega)]
      simp only [hadd]

/-- A negative step: the same, from any start above `end`. -/
theorem walk_neg (st e : I64) (hst : st.toInt < 0) :
    ∀ (f : Nat) (r : IntRange) (acc : List Int), r.step = st → r.finish = e → e.toInt < r.start.toInt →
      walkExact f r acc = cljWalk.go st.toInt
        (fun v => if st.toInt > 0 then decide (v < e.toInt) else decide (v > e.toInt)) f r.start.toInt acc := by
  have hst' : ¬ st.toInt > 0 := by omega
  intro f
  induction f with
  | zero =>
    intro r acc _ _ hlt
    simp [walkExact, cljWalk.go, hst', hlt]
  | succ f ih =>
    intro r acc hs he hlt
    have hin : (if st.toInt > 0 then decide (r.start.toInt < e.toInt) else decide (r.start.toInt > e.toInt)) = true := by
      simp [hst', hlt]
    simp only [walkExact, cljWalk.go, hin, ite_true]
    have hc : countExact r = (-(e.toInt - r.start.toInt) + -st.toInt - 1) / -st.toInt := by
      simp [countExact, hs, he, hst']
    have hpos : 0 < -st.toInt := by omega
    by_cases hle : r.start.toInt - e.toInt ≤ -st.toInt
    · have : countExact r ≤ 1 := by
        rw [hc]; exact (ceil_le_one _ _ hpos).mpr (by omega)
      simp only [this, decide_true, ite_true]
      rw [go_stop]
      simp [hst']; omega
    · have : ¬ countExact r ≤ 1 := by
        rw [hc]; intro h; exact hle (by have := (ceil_le_one _ _ hpos).mp h; omega)
      simp only [this, decide_false, Bool.false_eq_true, ite_false]
      have hb1 := bounds r.start
      have hb2 := bounds e
      have hadd : (r.start + r.step).toInt = r.start.toInt + st.toInt := by
        rw [hs]; exact add_exact _ _ (by omega) (by omega)
      rw [ih { r with start := r.start + r.step } _ hs he (by simp only; omega)]
      simp only [hadd]

/-- `(range start end step)` (integer_range.cpp `create`, then `first`/`next` with the exact
count): Clojure's elements and ending, for every i64 `start`, `end`, `step` and every number of
elements walked. -/
theorem fixed_walk_agrees (s e st : I64) (f : Nat) :
    (match create3 s e st with
      | .emptyList => (⟨[], .done⟩ : Walk)
      | .repeatInf v => ⟨List.replicate f v.toInt, .more⟩
      | .range r => walkExact f r []) = cljWalk s.toInt e.toInt st.toInt f := by
  have hslt : ∀ a b : I64, a.slt b = decide (a.toInt < b.toInt) := by
    intro a b; simp [BitVec.slt]
  unfold create3 cljWalk
  have h0 : ((0 : I64).toInt) = 0 := by decide
  by_cases hz : st.toInt = 0
  · have hst : st = 0 := by
      apply BitVec.eq_of_toInt_eq; rw [hz]; decide
    subst hst
    by_cases hse : s = e
    · subst hse; simp
    · have : s.toInt ≠ e.toInt := fun h => hse (BitVec.eq_of_toInt_eq h)
      simp [hse, this, hslt, h0]
  · have hst0 : st ≠ 0 := by intro h; subst h; exact hz (by decide)
    by_cases hpos : 0 < st.toInt
    · by_cases hlt : s.toInt < e.toInt
      · have hne : s ≠ e := by intro h; subst h; omega
        simp only [hslt, h0, hpos, decide_true, Bool.true_and, hst0, hne, hz]
        simp [show ¬ e.toInt < s.toInt by omega, show ¬ st.toInt < 0 by omega, hpos]
        have key := walk_pos st e hpos f ⟨s, e, st, .positive⟩ [] rfl rfl hlt
        have hst0' : ¬ (st = 0#64) := hst0
        simpa [hpos, hne, hst0, hst0', hz] using key
      · by_cases hse : s = e
        · subst hse; simp [hz, hslt, h0]
          rw [go_stop]; · rfl
          simp [hpos]
        · have : e.toInt < s.toInt := by
            have : s.toInt ≠ e.toInt := fun h => hse (BitVec.eq_of_toInt_eq h)
            omega
          simp [hslt, h0, hpos, this, hz]
          rw [go_stop]; · rfl
          simp [hpos]; omega
    · have hneg : st.toInt < 0 := by omega
      by_cases hlt : e.toInt < s.toInt
      · have hne : s ≠ e := by intro h; subst h; omega
        simp only [hslt, h0, hneg, decide_true, hst0, hne, hz]
        simp [show ¬ (0 : Int) < st.toInt by omega, show ¬ s.toInt < e.toInt by omega, hneg]
        have key := walk_neg st e hneg f ⟨s, e, st, .negative⟩ [] rfl rfl hlt
        have hst0' : ¬ (st = 0#64) := hst0
        simpa [show ¬ (0 : Int) < st.toInt by omega, hneg, hne, hst0, hst0', hz] using key
      · by_cases hse : s = e
        · subst hse; simp [hz, hslt, h0]
          rw [go_stop]; · rfl
          simp [show ¬ (0 : Int) < st.toInt by omega]
        · have : s.toInt < e.toInt := by
            have : s.toInt ≠ e.toInt := fun h => hse (BitVec.eq_of_toInt_eq h)
            omega
          simp [hslt, h0, hneg, this, hz, show ¬ (0 : Int) < st.toInt by omega]
          rw [go_stop]; · rfl
          simp [show ¬ (0 : Int) < st.toInt by omega]; omega

/-- `(range start end)`: `create(start, end)` is `create(start, end, 1)` (integer_range.cpp:74). -/
theorem fixed_walk_agrees2 (s e : I64) (f : Nat) :
    (match create2 s e with
      | .emptyList => (⟨[], .done⟩ : Walk)
      | .repeatInf v => ⟨List.replicate f v.toInt, .more⟩
      | .range r => walkExact f r []) = cljWalk s.toInt e.toInt 1 f := by
  have := fixed_walk_agrees s e 1 f
  rw [show ((1 : I64).toInt) = 1 by decide] at this
  exact this

/-- `(range end)`: `create(end)` (integer_range.cpp:62) is the walk from 0 by 1. -/
theorem create1_eq (e : I64) : create1 e = create3 0 e 1 := by
  have hslt : ∀ a b : I64, a.slt b = decide (a.toInt < b.toInt) := by intro a b; simp [BitVec.slt]
  have h0 : (0 : I64).toInt = 0 := by decide
  have h1 : (1 : I64).toInt = 1 := by decide
  unfold create1 create3
  simp only [hslt, h0, h1]
  by_cases hz : e = 0
  · subst hz; simp [h0]
  · have hne : e.toInt ≠ 0 := fun h => hz (BitVec.eq_of_toInt_eq (by rw [h, h0]))
    have hne' : (0 : I64) ≠ e := fun h => hz h.symm
    by_cases hp : 0 < e.toInt
    · simp [hp, show ¬ e.toInt < 0 by omega]
      exact fun h => hz h.symm
    · simp [hp, show e.toInt < 0 by omega]

theorem fixed_walk_agrees1 (e : I64) (f : Nat) :
    (match create1 e with
      | .emptyList => (⟨[], .done⟩ : Walk)
      | .repeatInf v => ⟨List.replicate f v.toInt, .more⟩
      | .range r => walkExact f r []) = cljWalk 0 e.toInt 1 f := by
  rw [create1_eq]
  have := fixed_walk_agrees 0 e 1 f
  rw [show ((1 : I64).toInt) = 1 by decide, show ((0 : I64).toInt) = 0 by decide] at this
  exact this

end Jank.R3.Proofs.Range
