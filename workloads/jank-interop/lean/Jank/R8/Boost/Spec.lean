/-!
# Round 8, area B: what a `cpp_dec_float<100>` keeps (S4), for every input

The 16 limbs of a nonzero finite value, read as one integer `A` (`data[0]` most significant), lie
in `[10^120, 10^128)`, and the value is `A · 10^(exp − 120)` with `exp` a multiple of 8. So a
value whose leading digit sits at `10^o` holds `(o mod 8) + 121` significant digits: 121 when
`o ≡ 0 (mod 8)` (`1 ≤ |x| < 10`, for instance), 128 when `o ≡ 7`.

The functions here state, at the level of those integers, what the limb code computes
(cpp_dec_float.hpp at jank's pin):
- `keepM`: `rd_string` 2083-2395 (a literal, `bigdec` of a string, S2's exact_divide's text): the
  first `(o mod 8) + 121` digits, truncated (the decimal part is cut at 120 digits, 2310-2316,
  after the point was moved so that at most 8 digits precede it, 2270-2284);
- `mulSpec`: `operator*=` 951-1012 with the school product (2643-2688, exact into 32 limbs)
  and the copy of 16 limbs (609-643): the exact product truncated;
- `addSpec`: `operator+=` 759-937 for equal signs: the smaller operand shifted down by whole
  limbs (its low limbs dropped), added, and one more limb dropped on a carry;
- `subSpec`: `operator+=` for opposite signs: the smaller magnitude shifted down (truncated),
  then subtracted, so the difference is rounded away from zero on the larger operand's grid.

The theorems are proved for every input. That the limb replica (round 3's `Jank.R3.Boost.Dec`)
and boost itself compute these functions is checked by search (`Jank.R8.Boost.Check`).
-/

namespace Jank.R8.Boost.Spec

theorem ten_pos (n : Nat) : 0 < 10 ^ n := Nat.pow_pos (by decide)

theorem pow_split (a b c : Nat) (h : a + b = c) : 10 ^ a * 10 ^ b = 10 ^ c := by
  rw [← Nat.pow_add, h]

/-- Truncation toward zero at the unit `q`: `X / q` units, and `X` lies in that unit. -/
theorem trunc_bounds (X q : Nat) (hq : 0 < q) : X / q * q ≤ X ∧ X < (X / q + 1) * q := by
  refine ⟨Nat.div_mul_le_self X q, ?_⟩
  rw [Nat.add_mul, Nat.one_mul]
  exact Nat.lt_div_mul_add hq

/-! ## Reading -/

/-- The 128-digit mantissa `rd_string` keeps for a positive integer `c` of `L` digits whose
leading digit sits at an order `o` with `o mod 8 = r` (the exponent is then `o − r`). -/
def keepM (c L r : Nat) : Nat :=
  if L ≤ 121 + r then c * 10 ^ (121 + r - L) else c / 10 ^ (L - (121 + r))

/-- ★ A value read from a decimal string keeps exactly `121 + r` digits (`r = o mod 8`):
the mantissa has `121 + r` digits. -/
theorem keepM_digits (c L r : Nat) (hL : 1 ≤ L) (lo : 10 ^ (L - 1) ≤ c) (hi : c < 10 ^ L) :
    10 ^ (120 + r) ≤ keepM c L r ∧ keepM c L r < 10 ^ (121 + r) := by
  unfold keepM
  split
  · rename_i h
    constructor
    · calc 10 ^ (120 + r) = 10 ^ (L - 1) * 10 ^ (121 + r - L) := (pow_split _ _ _ (by omega)).symm
        _ ≤ c * 10 ^ (121 + r - L) := Nat.mul_le_mul_right _ lo
    · calc c * 10 ^ (121 + r - L) < 10 ^ L * 10 ^ (121 + r - L) :=
            Nat.mul_lt_mul_of_pos_right hi (ten_pos _)
        _ = 10 ^ (121 + r) := pow_split _ _ _ (by omega)
  · rename_i h
    constructor
    · rw [Nat.le_div_iff_mul_le (ten_pos _)]
      calc 10 ^ (120 + r) * 10 ^ (L - (121 + r)) = 10 ^ (L - 1) := pow_split _ _ _ (by omega)
        _ ≤ c := lo
    · rw [Nat.div_lt_iff_lt_mul (ten_pos _)]
      calc c < 10 ^ L := hi
        _ = 10 ^ (121 + r) * 10 ^ (L - (121 + r)) := (pow_split _ _ _ (by omega)).symm

/-- ★ A read with more digits than it keeps is truncated toward zero: the kept mantissa is the
first `121 + r` digits of `c` (`c / 10^(L − 121 − r)`), and `c` lies in that last unit. -/
theorem keepM_trunc (c L r : Nat) (h : 121 + r < L) :
    keepM c L r = c / 10 ^ (L - (121 + r)) ∧
    keepM c L r * 10 ^ (L - (121 + r)) ≤ c ∧ c < (keepM c L r + 1) * 10 ^ (L - (121 + r)) := by
  have hk : keepM c L r = c / 10 ^ (L - (121 + r)) := by
    unfold keepM; split
    · omega
    · rfl
  rw [hk]
  exact ⟨rfl, trunc_bounds c _ (ten_pos _)⟩

/-- ★ A read with at most `121 + r` digits is exact (zeros are appended). -/
theorem keepM_exact (c L r : Nat) (h : L ≤ 121 + r) : keepM c L r = c * 10 ^ (121 + r - L) := by
  unfold keepM; split
  · rfl
  · omega

/-! ## Products -/

/-- `operator*=` on two full-precision mantissas (`prec_elem` 16 on both, as every value jank
holds): the 32-limb product; a nonzero top limb (`A·B ≥ 10^248`) moves the exponent by 8 and
the top 16 limbs are kept, else limbs 1..16. Returns the mantissa and the extra limb (0 or 1). -/
def mulSpec (A B : Nat) : Nat × Nat :=
  if 10 ^ 248 ≤ A * B then (A * B / 10 ^ 128, 1) else (A * B / 10 ^ 120, 0)

/-- ★ The product of two normalized mantissas is normalized: `121 + r` digits again, `r` the
product's order mod 8. -/
theorem mulSpec_norm (A B : Nat) (hA : 10 ^ 120 ≤ A ∧ A < 10 ^ 128) (hB : 10 ^ 120 ≤ B ∧ B < 10 ^ 128) :
    10 ^ 120 ≤ (mulSpec A B).1 ∧ (mulSpec A B).1 < 10 ^ 128 := by
  have lo : 10 ^ 240 ≤ A * B := by
    calc 10 ^ 240 = 10 ^ 120 * 10 ^ 120 := (pow_split 120 120 240 rfl).symm
      _ ≤ A * B := Nat.mul_le_mul hA.1 hB.1
  have hi : A * B < 10 ^ 256 := by
    calc A * B < 10 ^ 128 * 10 ^ 128 := Nat.mul_lt_mul'' hA.2 hB.2
      _ = 10 ^ 256 := pow_split 128 128 256 rfl
  unfold mulSpec
  split
  · rename_i h
    constructor
    · rw [Nat.le_div_iff_mul_le (ten_pos _), pow_split 120 128 248 rfl]; exact h
    · rw [Nat.div_lt_iff_lt_mul (ten_pos _), pow_split 128 128 256 rfl]; exact hi
  · rename_i h
    constructor
    · rw [Nat.le_div_iff_mul_le (ten_pos _), pow_split 120 120 240 rfl]; exact lo
    · rw [Nat.div_lt_iff_lt_mul (ten_pos _), pow_split 128 120 248 rfl]; exact Nat.lt_of_not_le h

/-- ★ A product is the exact product of the stored operands truncated toward zero at the unit
of its last kept limb (`10^(120 + 8d)` in mantissa units). -/
theorem mulSpec_trunc (A B : Nat) :
    (mulSpec A B).1 * 10 ^ (120 + 8 * (mulSpec A B).2) ≤ A * B ∧
    A * B < ((mulSpec A B).1 + 1) * 10 ^ (120 + 8 * (mulSpec A B).2) := by
  unfold mulSpec
  split
  · exact trunc_bounds (A * B) _ (ten_pos _)
  · exact trunc_bounds (A * B) _ (ten_pos _)

/-! ## Sums and differences -/

/-- `operator+=` with equal signs: `A` is the operand with the larger (or equal) exponent, `B`
the other, `δ` the exponent difference in limbs. `B` is shifted down by `δ` limbs (for `δ ≥ 16`
it vanishes: the `ofs_exp > max_delta_exp` branch returns `A`), added, and on a carry the
lowest limb is dropped. -/
def addSpec (A B δ : Nat) : Nat × Nat :=
  let S := A + B / 10 ^ (8 * δ)
  if 10 ^ 128 ≤ S then (S / 10 ^ 8, 1) else (S, 0)

/-- ★ A sum of equal signs is the exact sum truncated toward zero at the unit of the result's
last limb: `⌊(A·10^(8δ) + B) / 10^(8δ + 8c)⌋` with `c` the carry. -/
theorem addSpec_floor (A B δ : Nat) :
    (addSpec A B δ).1 = (A * 10 ^ (8 * δ) + B) / 10 ^ (8 * δ + 8 * (addSpec A B δ).2) := by
  have hS : A + B / 10 ^ (8 * δ) = (A * 10 ^ (8 * δ) + B) / 10 ^ (8 * δ) := by
    rw [Nat.add_comm (A * _), Nat.add_mul_div_right _ _ (ten_pos _), Nat.add_comm]
  unfold addSpec
  simp only
  split
  · simp only
    rw [hS, Nat.div_div_eq_div_mul, pow_split (8 * δ) 8 (8 * δ + 8 * 1) (by omega)]
  · simp only [Nat.mul_zero, Nat.add_zero]
    exact hS

/-- ★ The sum of a normalized `A` and any 16-limb `B` is normalized. -/
theorem addSpec_norm (A B δ : Nat) (hA : 10 ^ 120 ≤ A ∧ A < 10 ^ 128) (hB : B < 10 ^ 128) :
    10 ^ 120 ≤ (addSpec A B δ).1 ∧ (addSpec A B δ).1 < 10 ^ 128 := by
  have hle : B / 10 ^ (8 * δ) ≤ B := Nat.div_le_self _ _
  have h128 : 10 ^ 120 * 10 ^ 8 = 10 ^ 128 := pow_split 120 8 128 rfl
  have h136 : 10 ^ 128 * 10 ^ 8 = 10 ^ 136 := pow_split 128 8 136 rfl
  have h8 : 2 ≤ 10 ^ 8 := by decide
  have h2 : 2 * 10 ^ 128 ≤ 10 ^ 136 := by
    rw [← h136, Nat.mul_comm 2]; exact Nat.mul_le_mul_left _ h8
  unfold addSpec
  simp only
  split
  · rename_i h
    constructor
    · rw [Nat.le_div_iff_mul_le (ten_pos _), h128]; exact h
    · rw [Nat.div_lt_iff_lt_mul (ten_pos _), h136]; omega
  · rename_i h
    exact ⟨Nat.le_trans hA.1 (Nat.le_add_right _ _), Nat.lt_of_not_le h⟩

/-- `operator+=` with opposite signs: `A` is the larger magnitude (the larger exponent, or the
same exponent and larger limbs), `B` the smaller, shifted down by `δ` limbs before the
subtraction. The justification that follows shifts limbs, not the value. -/
def subSpec (A B δ : Nat) : Nat := A - B / 10 ^ (8 * δ)

/-- ★ A difference is the exact difference rounded away from zero (up in magnitude) at the
unit of the larger operand's last limb: `⌈(A·q − B) / q⌉` with `q = 10^(8δ)`. -/
theorem subSpec_ceil (A B δ : Nat) (h : B ≤ A * 10 ^ (8 * δ)) :
    A * 10 ^ (8 * δ) - B ≤ subSpec A B δ * 10 ^ (8 * δ) ∧
    subSpec A B δ * 10 ^ (8 * δ) < A * 10 ^ (8 * δ) - B + 10 ^ (8 * δ) := by
  unfold subSpec
  have hq := ten_pos (8 * δ)
  generalize 10 ^ (8 * δ) = q at *
  have hdm := Nat.div_add_mod B q
  have hmod := Nat.mod_lt B hq
  generalize B / q = b1 at *
  generalize B % q = b0 at *
  have hb1 : b1 ≤ A := by
    apply Nat.le_of_mul_le_mul_left _ hq
    calc q * b1 ≤ B := by omega
      _ ≤ A * q := h
      _ = q * A := Nat.mul_comm _ _
  rw [Nat.sub_mul]
  have hY : b1 * q ≤ A * q := Nat.mul_le_mul_right _ hb1
  have hc : q * b1 = b1 * q := Nat.mul_comm _ _
  generalize A * q = X at *
  generalize b1 * q = Y at *
  omega

/-- ★ With equal exponents (`δ = 0`) a difference is exact. -/
theorem subSpec_exact (A B : Nat) : subSpec A B 0 = A - B := by
  simp [subSpec]

end Jank.R8.Boost.Spec
