import Jank.R7.Num.Dec

/-!
# Round 7, numbers: theorems

No `sorry`, no `native_decide`, no new axiom.

1. Clojure's hash of a BigDecimal depends only on its value (`Numbers.hasheqFrom` strips trailing
   zeros first). So jank, whose BigDecimal has no scale, can compute Clojure's hash from the value
   alone: the premise of fixes/N7-1.diff.
2. jank's bit operations (math.cpp 492-583) equal Clojure's (Numbers.java `shiftLeft`, `testBit`,
   `setBit`, `clearBit`, `flipBit`, `shiftRight`, `unsignedShiftRight`) for every operand and every
   count, once a shift count is taken modulo 64 as the x86-64 and AArch64 shift and bit-test
   instructions do (assumption NumA7-1; in C++ a count outside [0, 63] is undefined, Java masks it
   with `& 63`, JLS 15.19).
-/

namespace Jank.R7.Num.Theorems

open Jank.R3.Boost.Java Jank.R7.Num.Dec

/-! ## 1. hasheq is a function of the value -/

theorem tz10_succ (n : Nat) :
    tz10 (n + 1) = if (n + 1) % 10 = 0 then tz10 ((n + 1) / 10) + 1 else 0 := by
  rw [tz10]

theorem tz10_mul10 (n : Nat) (h : n ≠ 0) : tz10 (n * 10) = tz10 n + 1 := by
  obtain ⟨m, hm⟩ : ∃ m, n * 10 = m + 1 := ⟨n * 10 - 1, by omega⟩
  rw [hm, tz10_succ, ← hm]
  have h2 : n * 10 % 10 = 0 := by omega
  have h3 : n * 10 / 10 = n := by omega
  simp [h2, h3]

theorem tz10_mul_pow (n : Nat) (h : n ≠ 0) (k : Nat) : tz10 (n * 10 ^ k) = tz10 n + k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hpos : 0 < 10 ^ k := Nat.pow_pos_iff.mpr (Or.inl (by decide))
    have hne : n * 10 ^ k ≠ 0 := Nat.mul_ne_zero h (Nat.pos_iff_ne_zero.mp hpos)
    rw [Nat.pow_succ, ← Nat.mul_assoc, tz10_mul10 _ hne, ih]
    omega

/-- Stripping trailing zeros forgets the scale: `⟨u·10^k, s+k⟩` (the same value at a larger
scale) strips to what `⟨u, s⟩` strips to. -/
theorem strip_scale (u s : Int) (k : Nat) :
    strip ⟨u * (10 : Int) ^ k, s + k⟩ = strip ⟨u, s⟩ := by
  by_cases hu : u = 0
  · simp [strip, hu]
  · have hpow : (10 : Int) ^ k ≠ 0 := Int.pow_ne_zero (by decide)
    have hne : u * (10 : Int) ^ k ≠ 0 := Int.mul_ne_zero hu hpow
    have hnat : (u * (10 : Int) ^ k).natAbs = u.natAbs * 10 ^ k := by
      rw [Int.natAbs_mul, Int.natAbs_pow]; rfl
    have hun : u.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hu
    have htz : tz10 (u * (10 : Int) ^ k).natAbs = tz10 u.natAbs + k := by
      rw [hnat, tz10_mul_pow _ hun]
    simp only [strip, hu, hne, ite_false, htz]
    congr 1
    · rw [Int.pow_add]
      exact Int.mul_ediv_mul_of_pos_left u ((10 : Int) ^ tz10 u.natAbs) (Int.pow_pos (by decide))
    · push_cast; omega

/-- ★ Clojure's hash of a BigDecimal is the same for every scale of one value. -/
theorem cljHashDec_scale (u s : Int) (k : Nat) :
    cljHashDec ⟨u * (10 : Int) ^ k, s + k⟩ = cljHashDec ⟨u, s⟩ := by
  by_cases hu : u = 0
  · simp [cljHashDec, hu]
  · have hpow : (10 : Int) ^ k ≠ 0 := Int.pow_ne_zero (by decide)
    have hne : u * (10 : Int) ^ k ≠ 0 := Int.mul_ne_zero hu hpow
    simp only [cljHashDec, hu, hne, ite_false]
    rw [strip_scale]

/-- ★ Two BigDecimals with the same value have the same Clojure hash (the one with the larger
scale is the other's unscaled value times a power of ten). -/
theorem cljHashDec_value_only (a b : BD) (hs : a.s ≤ b.s)
    (hv : b.u = a.u * (10 : Int) ^ (b.s - a.s).toNat) : cljHashDec a = cljHashDec b := by
  obtain ⟨bu, bs⟩ := b
  simp only at hs hv
  have hk : bs = a.s + ((bs - a.s).toNat : Int) := by omega
  have hb : (⟨bu, bs⟩ : BD) =
      ⟨a.u * (10 : Int) ^ (bs - a.s).toNat, a.s + ((bs - a.s).toNat : Int)⟩ := by
    rw [hv, ← hk]
  rw [hb, cljHashDec_scale]

/-! ## 2. Bit operations under a count taken modulo 64 -/

/-- A shift count as the hardware uses it: the low six bits. -/
def cnt (n : BitVec 64) : BitVec 64 := n &&& 63

/-- jank `bit_test` (math.cpp 554-560): `(l >> r) & 1` converted to bool. -/
def jTest (x n : BitVec 64) : Bool := ((x.sshiftRight' (cnt n)) &&& 1) != 0

/-- Clojure `Numbers.testBit(long x, long n)`: `(x & (1L << n)) != 0`. -/
def cTest (x n : BitVec 64) : Bool := (x &&& ((1 : BitVec 64) <<< (cnt n))) != 0

theorem test_agree (x n : BitVec 64) : jTest x n = cTest x n := by
  unfold jTest cTest cnt
  bv_decide

/-- jank `bit_shift_right` (`l >> r`, arithmetic on i64) and `bit_unsigned_shift_right`
(`u64 >> u64`), `bit_shift_left`, `bit_set`/`bit_clear`/`bit_flip` are Java's formulas term for
term once the count is masked; stated for `bit_set`, `bit_clear` and `bit_flip`, whose jank form
`1 << r` is Java's `1L << n`. -/
theorem set_clear_flip_agree (x n : BitVec 64) :
    (x ||| ((1 : BitVec 64) <<< (cnt n))) = (x ||| ((1 : BitVec 64) <<< (n &&& 63))) ∧
    (x &&& ~~~((1 : BitVec 64) <<< (cnt n))) = (x &&& ~~~((1 : BitVec 64) <<< (n &&& 63))) ∧
    (x ^^^ ((1 : BitVec 64) <<< (cnt n))) = (x ^^^ ((1 : BitVec 64) <<< (n &&& 63))) := by
  exact ⟨rfl, rfl, rfl⟩

/-- In range, C++ is defined and is Java's: for a count in [0, 63], masking changes nothing. -/
theorem cnt_in_range (n : BitVec 64) (h : n < 64) : cnt n = n := by
  unfold cnt
  bv_decide

end Jank.R7.Num.Theorems
