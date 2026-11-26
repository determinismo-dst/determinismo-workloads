import Std.Tactic.BVDecide
import Jank.R6.Native.Math

/-!
# For every input: where C++'s conversions make jank's `<`, `min`, `max`, `/` differ from Clojure

`a` is a `usize` from `count`/`alength` (below 2^63: no collection is that large), `b` the other
operand: an `int` literal sign-extended, or an `i64` (`(int x)`, a bit operation, a long object's
`data`). C++ converts `b` to `unsigned long long` (the usual arithmetic conversions,
`uac_unsigned_wins`), so `b < a` is the unsigned comparison `ult`; Clojure compares the numbers,
`slt` on the same bits. Each theorem gives the exact set of operands where the two differ.
-/

namespace Jank.R6.Native.Thm

/-- `(< b (count …))`: C++ compares unsigned; jank and Clojure differ exactly when `b < 0`. -/
theorem lt_i64_usize_differs_iff (a b : BitVec 64) (ha : a.msb = false) :
    (b.ult a ≠ b.slt a) ↔ b.msb = true := by
  bv_decide

/-- `(< (count …) b)`: differ exactly when `b < 0`. -/
theorem lt_usize_i64_differs_iff (a b : BitVec 64) (ha : a.msb = false) :
    (a.ult b ≠ a.slt b) ↔ b.msb = true := by
  bv_decide

/-- `(<= b (count …))` and `(<= (count …) b)`. -/
theorem le_differs_iff (a b : BitVec 64) (ha : a.msb = false) :
    ((b.ule a ≠ b.sle a) ↔ b.msb = true) ∧ ((a.ule b ≠ a.sle b) ↔ b.msb = true) := by
  bv_decide

/-- An `int` literal is sign-extended first: the same set (`(< -1 (count [1]))`). -/
theorem lt_int_usize_differs_iff (a : BitVec 64) (b : BitVec 32) (ha : a.msb = false) :
    ((b.signExtend 64).ult a ≠ (b.signExtend 64).slt a) ↔ b.msb = true := by
  bv_decide

/-- `std::min` over the common type `unsigned long long`, then boxed (`static_cast<i64>`, the same
bits), against Clojure's `min`: they differ exactly when `b < 0` (`(min (count [1 2 3]) -1)`). -/
theorem min_differs_iff (a b : BitVec 64) (ha : a.msb = false) :
    ((if b.ult a then b else a) ≠ (if b.slt a then b else a)) ↔ b.msb = true := by
  bv_decide

/-- `std::max(a, b)` is `a < b ? b : a`: differ exactly when `b < 0` (`(max (count [1]) -1)`). -/
theorem max_differs_iff (a b : BitVec 64) (ha : a.msb = false) :
    ((if a.ult b then b else a) ≠ (if a.slt b then b else a)) ↔ b.msb = true := by
  bv_decide

/-- `(/ (count …) b)`: unsigned division against D2's truncating division (jank's documented
integer `/`, round 1): they differ exactly when `b < 0` and `|b| ≤ a`. -/
theorem div_usize_by_i64_differs_iff (a b : BitVec 64) (ha : a.msb = false) (hb : b ≠ 0) :
    (a / b ≠ a.sdiv b) ↔ (b.msb = true ∧ (-b).ule a) := by
  bv_decide

/-- `(/ b (count …))`: differ exactly when `b < 0` and the count is at least 2. -/
theorem div_i64_by_usize_differs_iff (a b : BitVec 64) (ha : a.msb = false) (ha0 : a ≠ 0) :
    (b / a ≠ b.sdiv a) ↔ (b.msb = true ∧ 2#64 ≤ a) := by
  bv_decide

/-- `+ - *` produce the same bits signed or unsigned, and boxing reads them as `i64`: a `usize`
operand never changes a sum, difference or product that fits a long. -/
theorem add_usize_exact (a b : BitVec 64) (h : ¬ a.saddOverflow b = true) :
    (a + b).toInt = a.toInt + b.toInt :=
  BitVec.toInt_add_of_not_saddOverflow h

/-- A `uhash` boxed as `i64` keeps its unsigned value: it equals Clojure's signed `int` hash
exactly when the top bit is clear (`(hash 2)`: Clojure -971005196, jank 3323962100). -/
theorem hash_boxed_eq_iff (h : BitVec 32) : ((h.toNat : Int) = h.toInt) ↔ h.msb = false := by
  rw [BitVec.toInt_eq_msb_cond]
  cases hm : h.msb <;> simp
  have := BitVec.isLt h
  omega

/-- `uhash` arithmetic wraps at 32 bits: `(- (hash 0) 1)` is 4294967295 (Clojure -1). -/
theorem hash_sub_one_wraps : ((0 : BitVec 32) - 1).toNat = 4294967295 := by decide

end Jank.R6.Native.Thm
