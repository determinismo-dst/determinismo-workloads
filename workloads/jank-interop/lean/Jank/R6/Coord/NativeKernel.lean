import Jank.R6.Native.Theorems

/-! Kernel-only restatements of area P's LG1 theorems (`Jank.R6.Native.Thm`), which `bv_decide`
proves with its own per-proof axiom (its LRAT certificate checked by compiled code). These are the
same statements, proved by `omega` over `toNat`/`toInt`, so they rest only on `propext`,
`Classical.choice` and `Quot.sound`. -/

namespace Jank.R6.Coord

theorem msb_iff (b : BitVec 64) : b.msb = true ↔ 2 ^ 63 ≤ b.toNat := by
  rw [BitVec.msb_eq_decide]; simp

theorem toInt_eq (b : BitVec 64) :
    b.toInt = if b.toNat < 2 ^ 63 then (b.toNat : Int) else (b.toNat : Int) - 2 ^ 64 := by
  rw [BitVec.toInt_eq_toNat_cond]; simp only [Nat.reducePow]; split <;> split <;> omega

theorem lt_i64_usize_differs_iff (a b : BitVec 64) (ha : a.msb = false) :
    (b.ult a ≠ b.slt a) ↔ b.msb = true := by
  have hb := b.isLt; have ha' := a.isLt
  have h1 : ¬ 2 ^ 63 ≤ a.toNat := by rw [← msb_iff]; simp [ha]
  rw [msb_iff]
  simp only [BitVec.ult, BitVec.slt, toInt_eq, ne_eq, decide_eq_decide]
  split <;> split <;> omega

theorem lt_usize_i64_differs_iff (a b : BitVec 64) (ha : a.msb = false) :
    (a.ult b ≠ a.slt b) ↔ b.msb = true := by
  have hb := b.isLt; have ha' := a.isLt
  have h1 : ¬ 2 ^ 63 ≤ a.toNat := by rw [← msb_iff]; simp [ha]
  rw [msb_iff]
  simp only [BitVec.ult, BitVec.slt, toInt_eq, ne_eq, decide_eq_decide]
  split <;> split <;> omega

theorem le_differs_iff (a b : BitVec 64) (ha : a.msb = false) :
    ((b.ule a ≠ b.sle a) ↔ b.msb = true) ∧ ((a.ule b ≠ a.sle b) ↔ b.msb = true) := by
  have hb := b.isLt; have ha' := a.isLt
  have h1 : ¬ 2 ^ 63 ≤ a.toNat := by rw [← msb_iff]; simp [ha]
  rw [msb_iff]
  simp only [BitVec.ule, BitVec.sle, toInt_eq, ne_eq, decide_eq_decide]
  constructor <;> split <;> split <;> omega

theorem toNat_signExtend_32 (b : BitVec 32) :
    (b.signExtend 64).toNat = if b.toNat < 2 ^ 31 then b.toNat else b.toNat + (2 ^ 64 - 2 ^ 32) := by
  have hb := b.isLt
  rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth, BitVec.msb_eq_decide]
  simp only [Nat.reducePow, Nat.reduceSub] at *
  split <;> split <;> simp_all <;> omega

theorem msb32_iff (b : BitVec 32) : b.msb = true ↔ 2 ^ 31 ≤ b.toNat := by
  rw [BitVec.msb_eq_decide]; simp

theorem lt_int_usize_differs_iff (a : BitVec 64) (b : BitVec 32) (ha : a.msb = false) :
    ((b.signExtend 64).ult a ≠ (b.signExtend 64).slt a) ↔ b.msb = true := by
  have hs := toNat_signExtend_32 b
  have hb := b.isLt; have ha' := a.isLt
  have h1 : ¬ 2 ^ 63 ≤ a.toNat := by rw [← msb_iff]; simp [ha]
  rw [msb32_iff]
  simp only [BitVec.ult, BitVec.slt, toInt_eq, ne_eq, decide_eq_decide, hs]
  split <;> split <;> split <;> omega

theorem min_differs_iff (a b : BitVec 64) (ha : a.msb = false) :
    ((if b.ult a then b else a) ≠ (if b.slt a then b else a)) ↔ b.msb = true := by
  have hb := b.isLt; have ha' := a.isLt
  have h1 : ¬ 2 ^ 63 ≤ a.toNat := by rw [← msb_iff]; simp [ha]
  rw [msb_iff]
  simp only [BitVec.ult, BitVec.slt, toInt_eq, decide_eq_true_eq]
  have ha63 : a.toNat < 2 ^ 63 := by omega
  by_cases hb63 : b.toNat < 2 ^ 63 <;> simp only [hb63, ha63, ite_true, ite_false] <;>
    split <;> split <;> simp only [ne_eq, ← BitVec.toNat_inj, not_true_eq_false, false_iff] <;> omega

theorem max_differs_iff (a b : BitVec 64) (ha : a.msb = false) :
    ((if a.ult b then b else a) ≠ (if a.slt b then b else a)) ↔ b.msb = true := by
  have hb := b.isLt; have ha' := a.isLt
  have h1 : ¬ 2 ^ 63 ≤ a.toNat := by rw [← msb_iff]; simp [ha]
  rw [msb_iff]
  simp only [BitVec.ult, BitVec.slt, toInt_eq, decide_eq_true_eq]
  have ha63 : a.toNat < 2 ^ 63 := by omega
  by_cases hb63 : b.toNat < 2 ^ 63 <;> simp only [hb63, ha63, ite_true, ite_false] <;>
    split <;> split <;> simp only [ne_eq, ← BitVec.toNat_inj, not_true_eq_false, false_iff] <;> omega

theorem div_usize_by_i64_differs_iff (a b : BitVec 64) (ha : a.msb = false) (hb : b ≠ 0) :
    (a / b ≠ a.sdiv b) ↔ (b.msb = true ∧ (-b).ule a) := by
  have hbn : b.toNat ≠ 0 := fun h => hb (BitVec.eq_of_toNat_eq (by simp [h]))
  have hbl := b.isLt
  have ha63 : a.toNat < 2 ^ 63 := by
    have h := a.isLt; have h' : ¬ 2 ^ 63 ≤ a.toNat := by rw [← msb_iff]; simp [ha]
    omega
  unfold BitVec.sdiv; rw [ha]
  cases hbm : b.msb
  · simp
  · have hb63 : 2 ^ 63 ≤ b.toNat := (msb_iff b).mp hbm
    simp only [BitVec.udiv_eq, BitVec.neg_eq, true_and, BitVec.ule, decide_eq_true_eq, ne_eq,
      ← BitVec.toNat_inj, BitVec.toNat_udiv, BitVec.toNat_neg]
    have h0 : a.toNat / b.toNat = 0 := Nat.div_eq_of_lt (by omega)
    have hm : (2 ^ 64 - b.toNat) % 2 ^ 64 = 2 ^ 64 - b.toNat := Nat.mod_eq_of_lt (by omega)
    rw [h0, hm]
    have hq1 : a.toNat < 2 ^ 64 - b.toNat → a.toNat / (2 ^ 64 - b.toNat) = 0 := Nat.div_eq_of_lt
    have hq2 : 2 ^ 64 - b.toNat ≤ a.toNat → 0 < a.toNat / (2 ^ 64 - b.toNat) :=
      fun h => Nat.div_pos h (by omega)
    have hq3 : a.toNat / (2 ^ 64 - b.toNat) ≤ a.toNat := Nat.div_le_self _ _
    generalize a.toNat / (2 ^ 64 - b.toNat) = q at hq1 hq2 hq3 ⊢
    omega

theorem div_i64_by_usize_differs_iff (a b : BitVec 64) (ha : a.msb = false) (ha0 : a ≠ 0) :
    (b / a ≠ b.sdiv a) ↔ (b.msb = true ∧ 2#64 ≤ a) := by
  have han : a.toNat ≠ 0 := fun h => ha0 (BitVec.eq_of_toNat_eq (by simp [h]))
  have hbl := b.isLt
  have ha63 : a.toNat < 2 ^ 63 := by
    have h := a.isLt; have h' : ¬ 2 ^ 63 ≤ a.toNat := by rw [← msb_iff]; simp [ha]
    omega
  unfold BitVec.sdiv; rw [ha]
  cases hbm : b.msb
  · simp
  · have hb63 : 2 ^ 63 ≤ b.toNat := (msb_iff b).mp hbm
    simp only [BitVec.udiv_eq, BitVec.neg_eq, true_and, BitVec.le_def, ne_eq,
      ← BitVec.toNat_inj, BitVec.toNat_udiv, BitVec.toNat_neg, BitVec.toNat_ofNat]
    have hm : (2 ^ 64 - b.toNat) % 2 ^ 64 = 2 ^ 64 - b.toNat := Nat.mod_eq_of_lt (by omega)
    rw [hm]
    have hp1 : 0 < b.toNat / a.toNat := Nat.div_pos (by omega) (by omega)
    have hp2 : 2 ≤ a.toNat → b.toNat / a.toNat < 2 ^ 63 := fun h =>
      (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
    have hp3 : a.toNat = 1 → b.toNat / a.toNat = b.toNat := fun h => by rw [h, Nat.div_one]
    have hq1 : (2 ^ 64 - b.toNat) / a.toNat ≤ 2 ^ 64 - b.toNat := Nat.div_le_self _ _
    have hq3 : a.toNat = 1 → (2 ^ 64 - b.toNat) / a.toNat = 2 ^ 64 - b.toNat := fun h => by
      rw [h, Nat.div_one]
    generalize b.toNat / a.toNat = p at hp1 hp2 hp3 ⊢
    generalize (2 ^ 64 - b.toNat) / a.toNat = q at hq1 hq3 ⊢
    omega

/-! Each theorem above has exactly the type of area P's theorem of the same name (only P's
statement is used here, not its `bv_decide` proof). -/

theorem same_lt_i64_usize_differs_iff : type_of% Jank.R6.Native.Thm.lt_i64_usize_differs_iff := lt_i64_usize_differs_iff
theorem same_lt_usize_i64_differs_iff : type_of% Jank.R6.Native.Thm.lt_usize_i64_differs_iff := lt_usize_i64_differs_iff
theorem same_le_differs_iff : type_of% Jank.R6.Native.Thm.le_differs_iff := le_differs_iff
theorem same_lt_int_usize_differs_iff : type_of% Jank.R6.Native.Thm.lt_int_usize_differs_iff := lt_int_usize_differs_iff
theorem same_min_differs_iff : type_of% Jank.R6.Native.Thm.min_differs_iff := min_differs_iff
theorem same_max_differs_iff : type_of% Jank.R6.Native.Thm.max_differs_iff := max_differs_iff
theorem same_div_usize_by_i64_differs_iff : type_of% Jank.R6.Native.Thm.div_usize_by_i64_differs_iff := div_usize_by_i64_differs_iff
theorem same_div_i64_by_usize_differs_iff : type_of% Jank.R6.Native.Thm.div_i64_by_usize_differs_iff := div_i64_by_usize_differs_iff

end Jank.R6.Coord
