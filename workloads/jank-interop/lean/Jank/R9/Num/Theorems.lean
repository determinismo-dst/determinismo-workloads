import Jank.R9.Num.Model
import Std.Tactic.BVDecide
/-!
# Round 9, area N: theorems (for every input unless marked)
-/
namespace Jank.R9.Num

/-! ## DEC8-1 on doubles -/

/-- ★ The fix maps every boxable word (a real below `max_real`) to a boxable word: negating never
    makes D9's unboxable word. -/
theorem fixNeg_boxable (x : BitVec 64) (h : x < maxReal) : fixNegBits x < maxReal := by
  unfold fixNegBits isNaN64 maxReal expMask fracMask signBit at *
  split <;> bv_decide

/-- ★ Off NaN the fix is Java's negation, bit for bit (sign of zero included). -/
theorem fixNeg_eq_clj (x : BitVec 64) (h : isNaN64 x = false) : fixNegBits x = cljNegBits x := by
  simp [fixNegBits, cljNegBits, h]

/-- ★ On a NaN both results are NaNs (Clojure prints both as NaN; only raw bits could tell). -/
theorem fixNeg_nan (x : BitVec 64) (h : isNaN64 x = true) :
    isNaN64 (fixNegBits x) = true ∧ isNaN64 (cljNegBits x) = true := by
  refine ⟨by simp [fixNegBits, h], ?_⟩
  unfold isNaN64 cljNegBits expMask fracMask signBit at *
  bv_decide

/-- The sign of zero: `(- 0.0)` is -0.0 and `(- -0.0)` is 0.0 with the fix. -/
theorem fixNeg_pos_zero : fixNegBits 0#64 = signBit := by decide +kernel
theorem fixNeg_neg_zero : fixNegBits signBit = 0#64 := by decide +kernel

/-- Why the NaN branch: a plain negation of jank's `##NaN` is exactly `max_real`, which oref.hpp
    does not read as a real (D9). -/
theorem clj_neg_nan_unboxable : cljNegBits jankNaN = maxReal := by decide +kernel

/-! ## DEC8-1 on longs -/

/-- ★ On an `integer` box (an i64), the fix is LongOps.negate / negateP for every i64. -/
theorem fixNegInteger_eq (p : Bool) (x : Int) (h : i64min ≤ x) :
    fixNegInteger p x = cljNegLong p x := by
  unfold fixNegInteger cljNegLong
  by_cases hx : x = i64min
  · subst hx; simp [i64min]
  · have : x > i64min := by omega
    simp [hx, this]

/-- ★ On a `small_integer` box (an i32), the fix is LongOps.negate: no overflow is possible. -/
theorem fixNegSmall_eq (p : Bool) (x : Int) (h1 : i32min ≤ x) (_h2 : x ≤ i32max) :
    fixNegSmall x = cljNegLong p x := by
  unfold fixNegSmall cljNegLong
  have : x > i64min := by unfold i32min i64min at *; omega
  simp [this]

/-- ★ Stock `(- x)` of a `small_integer` (C++ `int` arithmetic) differs from Clojure exactly at
    -2^31 (round 1's D1 instance `(- -2147483648)`). -/
theorem stockNegSmall_differs_iff (x : Int) (h1 : i32min ≤ x) (h2 : x ≤ i32max) :
    stockNegSmall x ≠ cljNegLong false x ↔ x = i32min := by
  unfold stockNegSmall cljNegLong wrap
  unfold i32min i32max at *
  have hg : x > i64min := by unfold i64min; omega
  simp only [hg, ite_true, ne_eq, NegResult.long.injEq]
  constructor
  · intro hne; omega
  · intro hx; subst hx; decide

/-- ★ Stock `(- x)` of an `integer` (C++ `long`) differs exactly at Long/MIN_VALUE, where it
    returns Long/MIN_VALUE instead of throwing. -/
theorem stockNegInteger_differs_iff (x : Int) (h1 : i64min ≤ x) (h2 : x ≤ i64max) :
    stockNegInteger x ≠ cljNegLong false x ↔ x = i64min := by
  unfold stockNegInteger cljNegLong wrap
  unfold i64min i64max at *
  by_cases hx : x = -9223372036854775808
  · subst hx; decide
  · have hg : x > -9223372036854775808 := by omega
    simp only [hg, ite_true, ne_eq, NegResult.long.injEq, hx, iff_false, Decidable.not_not]
    omega

/-! ## DEC8-1 on BigDecimals (R72) -/

/-- ★ The fix keeps the scale (BigDecimal.negate). -/
theorem negDec_scale (x : Dec) : (negDec x).s = x.s := rfl

/-- ★ The stock definition `(0 - x)` on R72 takes the scale max(0, s). -/
theorem stockNegDec_scale (x : Dec) : (stockNegDec x).s = max 0 x.s := by
  simp [stockNegDec, exactSub, exactAdd, negDec]

/-- ★ The stock definition equals the fix exactly when the scale is not negative
    (`(- 1E+2M)`: scale -2, "-100" against "-1E+2"). -/
theorem stockNegDec_eq_iff (x : Dec) : stockNegDec x = negDec x ↔ 0 ≤ x.s := by
  constructor
  · intro h
    have := congrArg Dec.s h
    rw [stockNegDec_scale, negDec_scale] at this
    omega
  · intro h
    have hm : max 0 x.s = x.s := by omega
    simp [stockNegDec, exactSub, exactAdd, negDec, hm]

/-- ★ Both have the same value (cross-scaled): only the scale differs. -/
theorem stockNegDec_value (x : Dec) :
    cmpDec (stockNegDec x) (negDec x) = .eq := by
  have hm : max (max 0 x.s) x.s = max 0 x.s := by omega
  simp only [cmpDec, stockNegDec, exactSub, exactAdd, negDec, hm]
  have h1 : (max 0 x.s - 0 : Int).toNat = (max 0 x.s - 0).toNat := rfl
  have : (0 : Int) * 10 ^ (max 0 x.s - 0).toNat + -x.u * 10 ^ (max 0 x.s - x.s).toNat
      = -x.u * 10 ^ (max 0 x.s - x.s).toNat := by simp
  have hz : (max 0 x.s - max 0 x.s).toNat = 0 := by omega
  rw [this, hz]
  simp

/-! ## R72f: the fast path equals R72's general path -/

theorem mulPow10?_some {v : Int} {n : Nat} {x : Int} (h : mulPow10? v n = some x) : x = v * 10 ^ n := by
  unfold mulPow10? at h
  by_cases hv : v = 0
  · simp [hv] at h; subst h; simp [hv]
  · simp only [hv, ite_false] at h
    split at h
    · simp at h
    · split at h
      · simp at h; exact h.symm
      · simp at h

/-- ★ When the fast `+` answers, it is R72's exact `+` (unscaled value and scale). -/
theorem fastAdd_eq (l r z : Dec) (h : fastAdd l r = some z) : z = exactAdd l r := by
  unfold fastAdd at h
  split at h
  · dsimp only at h
    split at h
    · rename_i x y hx hy
      split at h
      · simp at h; subst h
        rw [mulPow10?_some hx, mulPow10?_some hy]; rfl
      · simp at h
    · simp at h
  · simp at h

/-- ★ When the fast `-` answers, it is R72's `-` (add(l, negate(r))). -/
theorem fastSub_eq (l r z : Dec) (h : fastSub l r = some z) : z = exactSub l r := by
  unfold fastSub at h
  split at h
  · dsimp only at h
    split at h
    · rename_i x y hx hy
      split at h
      · simp at h; subst h
        rw [mulPow10?_some hx, mulPow10?_some hy]
        simp only [exactSub, exactAdd, negDec]
        congr 1
        simp [Int.sub_eq_add_neg, Int.neg_mul]
      · simp at h
    · simp at h
  · simp at h

/-- ★ When the fast `*` answers, it is R72's exact `*`. -/
theorem fastMul_eq (l r z : Dec) (h : fastMul l r = some z) : z = exactMul l r := by
  unfold fastMul at h
  split at h
  · simp at h; subst h; rfl
  · simp at h

/-- ★ When the fast comparison answers, it is BigDecimal.compareTo's. -/
theorem fastCmp_eq (l r : Dec) (c : Ordering) (h : fastCmp l r = some c) : c = cmpDec l r := by
  unfold fastCmp at h
  split at h
  · dsimp only at h
    split at h
    · rename_i x y hx hy
      simp at h; subst h
      rw [mulPow10?_some hx, mulPow10?_some hy]; rfl
    · simp at h
  · simp at h

/-- ★ So the operators with the fast path in front are R72's operators, for every operand. -/
theorem withFast_add (l r : Dec) : withFast (fastAdd l r) (exactAdd l r) = exactAdd l r := by
  unfold withFast
  cases h : fastAdd l r with
  | none => rfl
  | some z => simp [fastAdd_eq l r z h]

theorem withFast_cmp (l r : Dec) : withFast (fastCmp l r) (cmpDec l r) = cmpDec l r := by
  unfold withFast
  cases h : fastCmp l r with
  | none => rfl
  | some c => simp [fastCmp_eq l r c h]

/-! ## V62: round-to-nearest-even -/

theorem rne_eq (n k : Nat) : rne n k =
    (if 2 * (n % 2 ^ k) > 2 ^ k ∨ (2 * (n % 2 ^ k) = 2 ^ k ∧ (n / 2 ^ k) % 2 = 1)
     then n / 2 ^ k + 1 else n / 2 ^ k) := rfl

theorem rne_cases (n k : Nat) : rne n k = n / 2 ^ k ∨ rne n k = n / 2 ^ k + 1 := by
  rw [rne_eq]; split <;> simp

/-- ★ `rne` is within half a unit of the last kept place: 2·|rne·2^k − n| ≤ 2^k. -/
theorem rne_half (n k : Nat) : 2 * dist (rne n k * 2 ^ k) n ≤ 2 ^ k := by
  have hd : 0 < 2 ^ k := Nat.two_pow_pos k
  have hdm := Nat.div_add_mod n (2 ^ k)
  have hr := Nat.mod_lt n hd
  rw [rne_eq]
  unfold dist
  generalize 2 ^ k = d at *
  generalize n / d = q at *
  generalize n % d = r at *
  have hA : q * d = d * q := Nat.mul_comm q d
  have hB : (q + 1) * d = d * q + d := by rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]
  split
  · rw [hB]; split <;> omega
  · rw [hA]; split <;> omega

/-- ★ On a tie (the dropped part is exactly half a unit) the result is even. -/
theorem rne_tie_even (n k : Nat) (h : 2 * (n % 2 ^ k) = 2 ^ k) : rne n k % 2 = 0 := by
  rw [rne_eq]
  split
  · rename_i hc
    rcases hc with hc | ⟨_, hq⟩
    · omega
    · omega
  · rename_i hc
    have : ¬ (n / 2 ^ k % 2 = 1) := fun hq => hc (Or.inr ⟨h, hq⟩)
    omega

/-- ★ `rne` is a nearest multiple: no multiple of 2^k is closer to n. -/
theorem rne_nearest (n k q' : Nat) : dist (rne n k * 2 ^ k) n ≤ dist (q' * 2 ^ k) n := by
  have hd : 0 < 2 ^ k := Nat.two_pow_pos k
  have hdm := Nat.div_add_mod n (2 ^ k)
  have hr := Nat.mod_lt n hd
  rw [rne_eq]
  unfold dist
  generalize 2 ^ k = d at *
  generalize n / d = q at *
  generalize n % d = r at *
  have hA : q * d = d * q := Nat.mul_comm q d
  have hB : (q + 1) * d = d * q + d := by rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]
  have hcmp : q' ≤ q ∨ q + 1 ≤ q' := by omega
  rcases hcmp with hle | hge
  · have hm : q' * d ≤ d * q := by rw [← hA]; exact Nat.mul_le_mul_right d hle
    split
    · rw [hB]; split <;> split <;> omega
    · rw [hA]; split <;> split <;> omega
  · have hm : d * q + d ≤ q' * d := by rw [← hB]; exact Nat.mul_le_mul_right d hge
    split
    · rw [hB]; split <;> split <;> omega
    · rw [hA]; split <;> split <;> omega

/-! ## Single inputs (the tests' values) -/

/-- `(float 0.1)`: 0x3DCCCCCD (Float 0.1); `(float 1e40)` and `(float ##Inf)` throw;
    `(float 16777217)` is 16777216. -/
theorem float_examples :
    floatCastBits 0x3FB999999999999A#64 = some 0x3DCCCCCD#32 ∧
    floatCastBits 0x483D6329F1C35CA5#64 = none ∧
    floatCastBits 0x7FF0000000000000#64 = none ∧
    floatCastBits 0x4170000010000000#64 = some 0x4B800000#32 := by decide +kernel

/-- `(long 2^63)` saturates; `(long 1e20)` throws; `(long ##NaN)` is 0; stock gives Long/MIN_VALUE
    for 2^63 on x86-64. -/
theorem long_examples :
    longCastBits 0x43E0000000000000#64 = some i64max ∧
    longCastBits 0x4415AF1D78B58C40#64 = none ∧
    longCastBits jankNaN = some 0 ∧
    stockLongBits 0x43E0000000000000#64 = i64min := by decide +kernel

end Jank.R9.Num
