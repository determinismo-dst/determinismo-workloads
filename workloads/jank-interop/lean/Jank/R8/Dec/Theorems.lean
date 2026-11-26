import Jank.R8.Dec.Java

/-!
# Round 8, area D: proofs about the decimal arithmetic of fixes/R72.diff and fixes/X6.diff

For every input:
- ★ `roundQ_cases`, `roundQ_exact`, `roundQ_unnecessary`: `round_quotient` returns the truncated
  quotient `q` or `q + 1`, the exact quotient when the division is exact, and throws (UNNECESSARY)
  exactly when it is not.
- ★ `roundQ_half_ulp`: in the three HALF modes the result is within half a unit of `n / d`:
  `2 · |r·d − n| ≤ d`.
- ★ `roundQ_tie`: on a tie (`2 · (n % d) = d`) HALF_UP goes up, HALF_DOWN down, HALF_EVEN to the even
  neighbour.
- ★ `roundQ_down`, `roundQ_up`, `roundQ_ceiling`, `roundQ_floor`: the directed modes truncate the
  magnitude (DOWN), raise it (UP), and move toward +∞ / −∞ by the sign.
- ★ `lt_pow_digits`, `pow_digits_le`: `10^(digits n − 1) ≤ n < 10^(digits n)` (n > 0).
- ★ `round_digits_le`: `decimal::round` returns at most `p` digits.
- ★ `exact_scale_least`: exact division's digits at scale `preferred + k` (k > 0) end in no zero, so
  `preferred + k` is the least scale at or above the preferred one holding the quotient: Java's
  scale rule `max(preferred, least exact scale)`; with round 7's ★ `exact_sound` / `exact_complete`
  (Jank.R7.Coord.Decimal), the value and the throw are right too.
- ★ `add_scale`, `mul_scale`, `neg_scale`, `abs_scale`: the scale rules of add/subtract (max), multiply
  (sum), negate and abs (kept).
-/

namespace Jank.R8.Dec

open Jank.R3.Boost.Java

/-! ## round_quotient -/

theorem roundQ_exact (n d : Nat) (m : RM) (neg : Bool) (h : n % d = 0) :
    roundQ n d m neg = .ok (n / d) := by
  simp [roundQ, h]

/-- ★ The result is the truncated quotient or one more. -/
theorem roundQ_cases (n d : Nat) (m : RM) (neg : Bool) (r : Nat)
    (h : roundQ n d m neg = .ok r) : r = n / d ∨ r = n / d + 1 := by
  unfold roundQ at h
  by_cases h0 : n % d = 0
  · simp [h0] at h; omega
  · simp only [h0, ite_false] at h
    cases m <;> simp at h <;> (try split at h) <;> simp_all <;> omega

/-- ★ UNNECESSARY throws exactly when the division is not exact. -/
theorem roundQ_unnecessary (n d : Nat) (neg : Bool) :
    (∃ e, roundQ n d .unnecessary neg = .error e) ↔ n % d ≠ 0 := by
  unfold roundQ
  by_cases h0 : n % d = 0 <;> simp [h0]

/-- The HALF modes' choice: up exactly when the remainder is past half, or at half by the mode. -/
theorem roundQ_half_choice (n d : Nat) (m : RM) (neg : Bool) (r : Nat)
    (hm : m = .halfUp ∨ m = .halfDown ∨ m = .halfEven)
    (h : roundQ n d m neg = .ok r) :
    (r = n / d ∧ 2 * (n % d) ≤ d) ∨ (r = n / d + 1 ∧ d ≤ 2 * (n % d)) := by
  unfold roundQ at h
  by_cases h0 : n % d = 0
  · simp [h0] at h; omega
  · simp only [h0, ite_false] at h
    rcases hm with rfl | rfl | rfl <;> simp at h <;> split at h <;> simp_all <;> omega

/-- ★ In the HALF modes the result is within half a unit: `2 · |r·d − n| ≤ d`. -/
theorem roundQ_half_ulp (n d : Nat) (m : RM) (neg : Bool) (r : Nat) (hd : 0 < d)
    (hm : m = .halfUp ∨ m = .halfDown ∨ m = .halfEven)
    (h : roundQ n d m neg = .ok r) :
    2 * n ≤ 2 * (r * d) + d ∧ 2 * (r * d) ≤ 2 * n + d := by
  have hdm := Nat.div_add_mod n d
  have hlt := Nat.mod_lt n hd
  rcases roundQ_half_choice n d m neg r hm h with ⟨rfl, h2⟩ | ⟨rfl, h2⟩
  · rw [Nat.mul_comm (n / d) d]; omega
  · rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (n / d) d]; omega

/-- ★ Ties: HALF_UP rounds up, HALF_DOWN down, HALF_EVEN to the even neighbour. -/
theorem roundQ_tie (n d : Nat) (neg : Bool) (hd : 0 < d) (ht : 2 * (n % d) = d) :
    roundQ n d .halfUp neg = .ok (n / d + 1) ∧
    roundQ n d .halfDown neg = .ok (n / d) ∧
    (∀ r, roundQ n d .halfEven neg = .ok r → r % 2 = 0) := by
  have h0 : n % d ≠ 0 := by omega
  refine ⟨?_, ?_, ?_⟩
  · simp [roundQ, h0]; omega
  · simp [roundQ, h0]; omega
  · intro r h
    simp only [roundQ, h0, ite_false] at h
    split at h <;> simp at h <;> omega

/-- ★ DOWN truncates: `r·d ≤ n < (r + 1)·d`. -/
theorem roundQ_down (n d : Nat) (neg : Bool) (r : Nat) (hd : 0 < d)
    (h : roundQ n d .down neg = .ok r) : r * d ≤ n ∧ n < (r + 1) * d := by
  have hdm := Nat.div_add_mod n d
  have hlt := Nat.mod_lt n hd
  have : r = n / d := by
    unfold roundQ at h; by_cases h0 : n % d = 0 <;> simp [h0] at h <;> omega
  subst this
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (n / d) d]; omega

/-- ★ UP raises the magnitude: `n ≤ r·d < n + d`. -/
theorem roundQ_up (n d : Nat) (neg : Bool) (r : Nat) (hd : 0 < d)
    (h : roundQ n d .up neg = .ok r) : n ≤ r * d ∧ r * d < n + d := by
  have hdm := Nat.div_add_mod n d
  have hlt := Nat.mod_lt n hd
  unfold roundQ at h
  by_cases h0 : n % d = 0
  · simp [h0] at h; subst h; rw [Nat.mul_comm (n / d) d]; omega
  · simp [h0] at h; subst h; rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (n / d) d]; omega

/-- ★ CEILING moves toward +∞: a positive value's magnitude goes up, a negative one's down. -/
theorem roundQ_ceiling (n d : Nat) (neg : Bool) (r : Nat) (hd : 0 < d)
    (h : roundQ n d .ceiling neg = .ok r) :
    (neg = false → n ≤ r * d ∧ r * d < n + d) ∧ (neg = true → r * d ≤ n ∧ n < (r + 1) * d) := by
  have hdm := Nat.div_add_mod n d
  have hlt := Nat.mod_lt n hd
  unfold roundQ at h
  by_cases h0 : n % d = 0
  · simp [h0] at h; subst h
    refine ⟨fun _ => ?_, fun _ => ?_⟩
    · rw [Nat.mul_comm (n / d) d]; omega
    · rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (n / d) d]; omega
  · cases neg <;> simp [h0] at h <;> subst h <;> simp
    · rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (n / d) d]; omega
    · rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (n / d) d]; omega

/-- ★ FLOOR moves toward −∞. -/
theorem roundQ_floor (n d : Nat) (neg : Bool) (r : Nat) (hd : 0 < d)
    (h : roundQ n d .floor neg = .ok r) :
    (neg = false → r * d ≤ n ∧ n < (r + 1) * d) ∧ (neg = true → n ≤ r * d ∧ r * d < n + d) := by
  have hdm := Nat.div_add_mod n d
  have hlt := Nat.mod_lt n hd
  unfold roundQ at h
  by_cases h0 : n % d = 0
  · simp [h0] at h; subst h
    refine ⟨fun _ => ?_, fun _ => ?_⟩
    · rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (n / d) d]; omega
    · rw [Nat.mul_comm (n / d) d]; omega
  · cases neg <;> simp [h0] at h <;> subst h <;> simp
    · rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (n / d) d]; omega
    · rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (n / d) d]; omega

/-! ## digit counts -/

theorem digits_eq (n : Nat) : digits n = if n < 10 then 1 else digits (n / 10) + 1 := by
  rw [digits]; split <;> simp_all

theorem digits_pos (n : Nat) : 1 ≤ digits n := by
  rw [digits_eq]; split <;> omega

/-- ★ `n < 10^(digits n)`. -/
theorem lt_pow_digits (n : Nat) : n < 10 ^ digits n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [digits_eq]
    split
    · simpa using (by assumption : n < 10)
    · rename_i h
      have := ih (n / 10) (Nat.div_lt_self (by omega) (by decide))
      rw [Nat.pow_succ]
      omega

/-- ★ `10^(digits n − 1) ≤ n` for `n > 0`. -/
theorem pow_digits_le (n : Nat) (hn : 0 < n) : 10 ^ (digits n - 1) ≤ n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [digits_eq]
    split
    · simp; omega
    · rename_i h
      have := ih (n / 10) (Nat.div_lt_self (by omega) (by decide)) (by omega)
      simp only [Nat.add_sub_cancel]
      have hp := digits_pos (n / 10)
      obtain ⟨k, hk⟩ : ∃ k, digits (n / 10) = k + 1 := ⟨digits (n / 10) - 1, by omega⟩
      rw [hk] at this ⊢
      simp only [Nat.add_sub_cancel] at this
      rw [Nat.pow_succ]
      omega

/-- `n < 10^p` gives at most `p` digits (`p ≥ 1`). -/
theorem digits_le_of_lt (n p : Nat) (hp : 1 ≤ p) (h : n < 10 ^ p) : digits n ≤ p := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [digits_eq]; simp; omega
  · have := pow_digits_le n hn
    refine Nat.le_of_not_lt (fun hc => ?_)
    have : 10 ^ p ≤ 10 ^ (digits n - 1) := Nat.pow_le_pow_right (by decide) (by omega)
    omega

/-! ## rounding to a precision -/

/-- The sign wrapper of `decimal::round` keeps the magnitude. -/
theorem natAbs_signed (b : Bool) (r : Nat) : (if b then -(r : Int) else (r : Int)).natAbs = r := by
  cases b <;> simp

/-- ★ `decimal::round` keeps at most `p` digits (for `p ≥ 1`; `p = 0` is exact). -/
theorem round_digits_le (x y : BD) (mc : MC) (hp : 1 ≤ mc.p) (h : round x mc = .ok y) :
    digits y.u.natAbs ≤ mc.p := by
  unfold round at h
  have hp0 : mc.p ≠ 0 := by omega
  simp only [hp0, ite_false] at h
  by_cases hd : digits x.u.natAbs ≤ mc.p
  · simp only [hd, ite_true] at h; cases h; exact hd
  · simp only [hd, ite_false] at h
    generalize hrq : roundQ x.u.natAbs (10 ^ (digits x.u.natAbs - mc.p)) mc.m (decide (x.u < 0)) = rq at h
    cases rq with
    | error e => cases h
    | ok r =>
      have hlt := lt_pow_digits x.u.natAbs
      have hcases := roundQ_cases _ _ _ _ r hrq
      have hpow : 10 ^ digits x.u.natAbs = 10 ^ mc.p * 10 ^ (digits x.u.natAbs - mc.p) := by
        rw [← Nat.pow_add]; congr 1; omega
      have hpos : 0 < 10 ^ (digits x.u.natAbs - mc.p) := Nat.pow_pos (by decide)
      have hq : x.u.natAbs / 10 ^ (digits x.u.natAbs - mc.p) < 10 ^ mc.p := by
        rw [Nat.div_lt_iff_lt_mul hpos, ← hpow]; exact hlt
      have hr_le : r ≤ 10 ^ mc.p := by omega
      simp only at h
      by_cases hc : r = 10 ^ mc.p
      · simp only [hc, ite_true] at h
        cases h
        have e := natAbs_signed (decide (x.u < 0)) (10 ^ (mc.p - 1))
        simp only [decide_eq_true_eq] at e
        simp only [e]
        exact digits_le_of_lt _ _ hp (Nat.pow_lt_pow_right (by decide) (by omega))
      · simp only [hc, ite_false] at h
        cases h
        have e := natAbs_signed (decide (x.u < 0)) r
        simp only [decide_eq_true_eq] at e
        simp only [e]
        exact digits_le_of_lt _ _ hp (by omega)

theorem natAbs_ite (q : Prop) [Decidable q] (a : Nat) :
    (if q then -(a : Int) else (a : Int)).natAbs = a := by
  by_cases hq : q <;> simp [hq]

theorem ite_neg_iff (q : Prop) [Decidable q] (a : Nat) :
    (if q then -(a : Int) else (a : Int)) < 0 ↔ q ∧ a ≠ 0 := by
  by_cases hq : q <;> simp [hq] <;> omega

/-- ★ `decimal::round` in a HALF mode is within half a unit of the last kept place: the result's
magnitude, written at the scale `x.s − drop` (times 10 after a carry), is `r` with
`2 · |r · 10^drop − |u|| ≤ 10^drop`, and the sign is kept. -/
theorem round_half_ulp (x y : BD) (mc : MC) (hp : 1 ≤ mc.p)
    (hm : mc.m = .halfUp ∨ mc.m = .halfDown ∨ mc.m = .halfEven)
    (hd : mc.p < digits x.u.natAbs) (h : round x mc = .ok y) :
    ∃ r e : Nat, y.u.natAbs * 10 ^ e = r ∧ y.s + e = x.s - (digits x.u.natAbs - mc.p : Nat) ∧
      2 * x.u.natAbs ≤ 2 * (r * 10 ^ (digits x.u.natAbs - mc.p)) + 10 ^ (digits x.u.natAbs - mc.p) ∧
      2 * (r * 10 ^ (digits x.u.natAbs - mc.p)) ≤ 2 * x.u.natAbs + 10 ^ (digits x.u.natAbs - mc.p) ∧
      (y.u < 0 ↔ x.u < 0 ∧ r ≠ 0) := by
  unfold round at h
  have hp0 : mc.p ≠ 0 := by omega
  have hd' : ¬ digits x.u.natAbs ≤ mc.p := by omega
  simp only [hp0, hd', ite_false] at h
  generalize hrq : roundQ x.u.natAbs (10 ^ (digits x.u.natAbs - mc.p)) mc.m (decide (x.u < 0)) = rq at h
  cases rq with
  | error e => cases h
  | ok r =>
    have hpos : 0 < 10 ^ (digits x.u.natAbs - mc.p) := Nat.pow_pos (by decide)
    have hh := roundQ_half_ulp _ _ _ _ r hpos hm hrq
    refine ⟨r, ?_⟩
    simp only at h
    by_cases hc : r = 10 ^ mc.p
    · simp only [hc, ite_true] at h
      cases h
      have h1 : (10 : Nat) ^ (mc.p - 1) ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.pow_pos (by decide))
      have h2 : (10 : Nat) ^ mc.p ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.pow_pos (by decide))
      refine ⟨1, ?_, ?_, hh.1, hh.2, ?_⟩
      · rw [natAbs_ite, hc, Nat.pow_one, ← Nat.pow_succ]; congr 1; omega
      · show x.s - ((digits x.u.natAbs - mc.p : Nat) : Int) - 1 + ((1 : Nat) : Int) = _
        omega
      · rw [ite_neg_iff, hc]
        exact ⟨fun ⟨a, _⟩ => ⟨a, h2⟩, fun ⟨a, _⟩ => ⟨a, h1⟩⟩
    · simp only [hc, ite_false] at h
      cases h
      refine ⟨0, ?_, ?_, hh.1, hh.2, ?_⟩
      · rw [natAbs_ite, Nat.pow_zero, Nat.mul_one]
      · show x.s - ((digits x.u.natAbs - mc.p : Nat) : Int) + ((0 : Nat) : Int) = _
        omega
      · exact ite_neg_iff _ _

/-! ## exact division's scale -/

open Jank.R7.Coord.Decimal in
/-- ★ With `k = max twos fives > 0`, exact division's digits end in no zero: the scale
`preferred + k` is the least scale at or above the preferred one that holds the quotient. -/
theorem exact_scale_least (n d : Nat) (_hd : 0 < d) (hc : Nat.Coprime n d)
    (hk : 0 < max (steps d).twos (steps d).fives) : ¬ 10 ∣ resultDigits n d := by
  intro h10
  have hf := steps_factor d
  unfold resultDigits at h10
  simp only at h10
  have h2 : 2 ∣ resultDigits n d := by
    unfold resultDigits; exact Nat.dvd_trans ⟨5, rfl⟩ h10
  have h5 : 5 ∣ resultDigits n d := by
    unfold resultDigits; exact Nat.dvd_trans ⟨2, rfl⟩ h10
  unfold resultDigits at h2 h5
  simp only at h2 h5
  by_cases ht : (steps d).fives ≤ (steps d).twos
  · -- k = twos > 0: the digits are n · 5^(twos − fives); 2 divides d, so not n, so not them.
    have hk' : max (steps d).twos (steps d).fives = (steps d).twos := by omega
    rw [hk', Nat.sub_self, Nat.pow_zero, Nat.mul_one] at h2
    have hc25 : Nat.Coprime 2 (5 ^ ((steps d).twos - (steps d).fives)) :=
      Nat.Coprime.pow_right _ (by decide)
    have h2n : 2 ∣ n := (Nat.Coprime.dvd_of_dvd_mul_right hc25 h2)
    have h2d : 2 ∣ d := by
      have : 0 < (steps d).twos := by omega
      rw [hf]
      have h1 : 2 ∣ 2 ^ (steps d).twos := by
        have := Nat.pow_dvd_pow 2 (show 1 ≤ (steps d).twos by omega)
        simpa using this
      exact Nat.dvd_trans (Nat.dvd_trans h1 (Nat.dvd_mul_right _ _)) (Nat.dvd_mul_right _ _)
    have hg : Nat.gcd n d = 1 := hc
    have := Nat.dvd_gcd h2n h2d
    rw [hg] at this
    omega
  · -- k = fives > twos: the digits are n · 2^(fives − twos); 5 divides d, so not n.
    have hk' : max (steps d).twos (steps d).fives = (steps d).fives := by omega
    rw [hk', Nat.sub_self, Nat.pow_zero, Nat.mul_one] at h5
    have hc52 : Nat.Coprime 5 (2 ^ ((steps d).fives - (steps d).twos)) :=
      Nat.Coprime.pow_right _ (by decide)
    have h5n : 5 ∣ n := (Nat.Coprime.dvd_of_dvd_mul_right hc52 h5)
    have h5d : 5 ∣ d := by
      have : 0 < (steps d).fives := by omega
      rw [hf]
      have h1 : 5 ∣ 5 ^ (steps d).fives := by
        have := Nat.pow_dvd_pow 5 (show 1 ≤ (steps d).fives by omega)
        simpa using this
      exact Nat.dvd_trans (Nat.dvd_trans h1 (Nat.dvd_mul_left _ _)) (Nat.dvd_mul_right _ _)
    have hg : Nat.gcd n d = 1 := hc
    have := Nat.dvd_gcd h5n h5d
    rw [hg] at this
    omega

/-! ## scale rules of the exact operations -/

/-- ★ add/subtract: scale `max(s1, s2)`. -/
theorem add_scale (x y : BD) : (x.add y).s = max x.s y.s := by
  simp [BD.add, align]

/-- ★ multiply: scale `s1 + s2`. -/
theorem mul_scale (x y : BD) : (x.mul y).s = x.s + y.s := rfl

/-- ★ negate and abs keep the scale. -/
theorem neg_scale (x : BD) : x.neg.s = x.s := rfl
theorem abs_scale (x : BD) : x.abs.s = x.s := rfl

/-- In a context of precision 0 rounding is the identity (with-precision 0 is exact). -/
theorem round_exact (x : BD) (m : RM) : round x ⟨0, m⟩ = .ok x := by
  simp [round]

end Jank.R8.Dec
