/-!
# Round 7, coordinator: the arithmetic of S2's exact BigDecimal division

`fixes/S2.diff` adds `exact_divide` to jank's big_decimal.cpp: both operands are read exactly as
digits * 10^e; the quotient of the digit magnitudes is reduced by their gcd to `n / d`; the
factors 2 and 5 are stripped from `d`; if anything else is left the quotient does not terminate
("Non-terminating decimal expansion; no exact representable decimal result.", BigDecimal.divide's
error), else the result is `n * 2^(k-a) * 5^(k-b)` times 10^-k (with `k = max a b`), times the
operands' 10^(e1 - e2).

This file proves the arithmetic core for every input:
- ★ `strip_spec`: stripping is a factorization, `d = p^c * r`, and with enough fuel `p ∤ r`.
- ★ `exact_sound`: when the rest is 1, the result times `d` is `n * 10^k`.
- ★ `exact_complete`: when the rest is not 1 and `n`, `d` are coprime, no `m`, `k` give
  `n * 10^k = m * d`, so `n / d` is no finite decimal: the error is right.

The decimal reading (cpp_dec_float's scientific text) and the string back are not modeled; they
were checked against Clojure 1.12.3 on 418 operand pairs (REPORT-7 section 1.2).
-/

namespace Jank.R7.Coord.Decimal

/-- Strip the factor `p` from `d`: (how many, the rest). `fuel` bounds the steps. -/
def strip (p : Nat) : (fuel d : Nat) → Nat × Nat
  | 0, d => (0, d)
  | fuel + 1, d =>
    if d ≠ 0 ∧ d % p = 0 then
      let r := strip p fuel (d / p)
      (r.1 + 1, r.2)
    else (0, d)

theorem strip_factor (p fuel d : Nat) : d = p ^ (strip p fuel d).1 * (strip p fuel d).2 := by
  induction fuel generalizing d with
  | zero => simp [strip]
  | succ f ih =>
    unfold strip
    split
    · rename_i h
      have hd : d = p * (d / p) := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h.2)).symm
      have := ih (d / p)
      simp only
      rw [Nat.pow_succ]
      calc d = p * (d / p) := hd
        _ = p * (p ^ (strip p f (d / p)).1 * (strip p f (d / p)).2) := by rw [← this]
        _ = p ^ (strip p f (d / p)).1 * p * (strip p f (d / p)).2 := by
          rw [Nat.mul_comm p, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_comm p]
    · simp

theorem strip_rest_pos (p fuel d : Nat) (hd : 0 < d) : 0 < (strip p fuel d).2 := by
  have h := strip_factor p fuel d
  rcases Nat.eq_zero_or_pos (strip p fuel d).2 with h0 | h0
  · rw [h0, Nat.mul_zero] at h; omega
  · exact h0

theorem strip_done (p fuel d : Nat) (hp : 2 ≤ p) (hd : 0 < d) (hf : d ≤ fuel) :
    ¬ p ∣ (strip p fuel d).2 := by
  induction fuel generalizing d with
  | zero => omega
  | succ f ih =>
    unfold strip
    split
    · rename_i h
      simp only
      have hq : 0 < d / p := by
        have := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h.2)
        rcases Nat.eq_zero_or_pos (d / p) with h0 | h0
        · rw [h0] at this; omega
        · exact h0
      apply ih (d / p) hq
      have : d / p < d := Nat.div_lt_self hd (by omega)
      omega
    · rename_i h
      intro hdv
      apply h
      exact ⟨by omega, Nat.mod_eq_zero_of_dvd hdv⟩

/-- ★ Stripping is a factorization, and with fuel `d` it removes every factor `p`. -/
theorem strip_spec (p d : Nat) (hp : 2 ≤ p) (hd : 0 < d) :
    d = p ^ (strip p d d).1 * (strip p d d).2 ∧ ¬ p ∣ (strip p d d).2 :=
  ⟨strip_factor p d d, strip_done p d d hp hd (Nat.le_refl d)⟩

/-- The steps of exact_divide on a reduced quotient `n / d`. -/
structure Steps where
  twos : Nat
  fives : Nat
  rest : Nat

def steps (d : Nat) : Steps :=
  let s2 := strip 2 d d
  let s5 := strip 5 s2.2 s2.2
  ⟨s2.1, s5.1, s5.2⟩

/-- The digits exact_divide returns when the rest is 1, with `k = max twos fives`. -/
def resultDigits (n d : Nat) : Nat :=
  let s := steps d
  let k := max s.twos s.fives
  n * 2 ^ (k - s.twos) * 5 ^ (k - s.fives)

def resultScale (d : Nat) : Nat := max (steps d).twos (steps d).fives

theorem steps_factor (d : Nat) :
    d = 2 ^ (steps d).twos * 5 ^ (steps d).fives * (steps d).rest := by
  unfold steps
  simp only
  have h2 := strip_factor 2 d d
  have h5 := strip_factor 5 (strip 2 d d).2 (strip 2 d d).2
  rw [Nat.mul_assoc, ← h5]
  exact h2

/-- ★ When the rest is 1, the returned digits over 10^k are exactly `n / d`. -/
theorem exact_sound (n d : Nat) (h : (steps d).rest = 1) :
    resultDigits n d * d = n * 10 ^ resultScale d := by
  have hf := steps_factor d
  rw [h, Nat.mul_one] at hf
  unfold resultDigits resultScale
  simp only
  generalize ha : (steps d).twos = a at hf ⊢
  generalize hb : (steps d).fives = b at hf ⊢
  rw [hf]
  have h10 : (10 : Nat) ^ max a b = 2 ^ max a b * 5 ^ max a b := by
    rw [show (10 : Nat) = 2 * 5 from rfl, Nat.mul_pow]
  rw [h10]
  have e2 : 2 ^ (max a b - a) * 2 ^ a = 2 ^ max a b := by
    rw [← Nat.pow_add]; congr 1; omega
  have e5 : 5 ^ (max a b - b) * 5 ^ b = 5 ^ max a b := by
    rw [← Nat.pow_add]; congr 1; omega
  calc n * 2 ^ (max a b - a) * 5 ^ (max a b - b) * (2 ^ a * 5 ^ b)
      = n * ((2 ^ (max a b - a) * 2 ^ a) * (5 ^ (max a b - b) * 5 ^ b)) := by
        simp only [Nat.mul_assoc, Nat.mul_left_comm]
    _ = n * (2 ^ max a b * 5 ^ max a b) := by rw [e2, e5]

theorem coprime_of_not_dvd_prime (p r : Nat) (hp : p = 2 ∨ p = 5) (h : ¬ p ∣ r) :
    Nat.Coprime r p := by
  unfold Nat.Coprime
  have hg : Nat.gcd r p ∣ p := Nat.gcd_dvd_right r p
  have hpos : 0 < p := by omega
  have hle : Nat.gcd r p ≤ p := Nat.le_of_dvd hpos hg
  have hgr : Nat.gcd r p ∣ r := Nat.gcd_dvd_left r p
  rcases hp with rfl | rfl
  · have : Nat.gcd r 2 = 0 ∨ Nat.gcd r 2 = 1 ∨ Nat.gcd r 2 = 2 := by omega
    rcases this with h0 | h1 | h2
    · rw [h0] at hg; simp at hg
    · exact h1
    · rw [h2] at hgr; exact absurd hgr h
  · have : Nat.gcd r 5 = 0 ∨ Nat.gcd r 5 = 1 ∨ Nat.gcd r 5 = 2 ∨ Nat.gcd r 5 = 3 ∨
        Nat.gcd r 5 = 4 ∨ Nat.gcd r 5 = 5 := by omega
    rcases this with h0 | h1 | h2 | h3 | h4 | h5
    · rw [h0] at hg; simp at hg
    · exact h1
    · rw [h2] at hg; exact absurd hg (by decide)
    · rw [h3] at hg; exact absurd hg (by decide)
    · rw [h4] at hg; exact absurd hg (by decide)
    · rw [h5] at hgr; exact absurd hgr h

/-- ★ When the rest is not 1 (and `n`, `d` are coprime, as after the gcd reduction), no decimal
equals `n / d`: exact_divide's "Non-terminating" error is right. -/
theorem exact_complete (n d : Nat) (hd : 0 < d) (hc : Nat.Coprime n d)
    (h : (steps d).rest ≠ 1) : ∀ m k : Nat, n * 10 ^ k ≠ m * d := by
  intro m k heq
  -- d divides n * 10^k, and is coprime to n, so d divides 10^k
  have hd10 : d ∣ 10 ^ k := by
    have : d ∣ n * 10 ^ k := ⟨m, by rw [heq, Nat.mul_comm]⟩
    exact Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.symm hc) this
  -- the rest divides d
  have hf := steps_factor d
  have hrd : (steps d).rest ∣ d := ⟨2 ^ (steps d).twos * 5 ^ (steps d).fives, by
    rw [Nat.mul_comm]; exact hf⟩
  have hr10 : (steps d).rest ∣ 10 ^ k := Nat.dvd_trans hrd hd10
  -- the rest has no factor 2 or 5
  have hd2 : 0 < (strip 2 d d).2 := strip_rest_pos 2 d d hd
  have hn5 : ¬ 5 ∣ (steps d).rest := by
    unfold steps; exact strip_done 5 _ _ (by decide) hd2 (Nat.le_refl _)
  have hn2 : ¬ 2 ∣ (steps d).rest := by
    intro h2
    have h2' : ¬ 2 ∣ (strip 2 d d).2 := strip_done 2 d d (by decide) hd (Nat.le_refl d)
    apply h2'
    have : (steps d).rest ∣ (strip 2 d d).2 := by
      have := strip_factor 5 (strip 2 d d).2 (strip 2 d d).2
      unfold steps
      exact ⟨5 ^ (strip 5 (strip 2 d d).2 (strip 2 d d).2).1, by rw [Nat.mul_comm]; exact this⟩
    exact Nat.dvd_trans h2 this
  have hc2 := coprime_of_not_dvd_prime 2 _ (Or.inl rfl) hn2
  have hc5 := coprime_of_not_dvd_prime 5 _ (Or.inr rfl) hn5
  have hc10 : Nat.Coprime (steps d).rest (10 ^ k) := by
    rw [show (10 : Nat) = 2 * 5 from rfl, Nat.mul_pow]
    exact Nat.Coprime.mul_right (Nat.Coprime.pow_right k hc2) (Nat.Coprime.pow_right k hc5)
  exact h (Nat.Coprime.eq_one_of_dvd hc10 hr10)

/-- The gcd reduction gives coprime digits (Lean core's `Nat.coprime_div_gcd_div_gcd`), so
`exact_complete` applies to exact_divide's `n / d`. -/
theorem reduced_coprime (a b : Nat) (hb : 0 < b) :
    Nat.Coprime (a / Nat.gcd a b) (b / Nat.gcd a b) :=
  Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right a hb)

/-- The two operands of section 1.2: 6/3 gives digits 2, scale 0; 3/6 reduces to 1/2: digits 5,
scale 1; 1/3 has rest 3. -/
theorem examples :
    (steps 1).rest = 1 ∧ resultDigits 2 1 = 2 ∧ resultScale 1 = 0 ∧
    (steps 2).rest = 1 ∧ resultDigits 1 2 = 5 ∧ resultScale 2 = 1 ∧
    (steps 3).rest = 3 ∧ (steps 1024).rest = 1 ∧ resultDigits 1 1024 = 9765625 := by
  decide +kernel

end Jank.R7.Coord.Decimal
