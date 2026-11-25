import Jank.R3.Boost.DecFloat

/-!
# Round 3, Boost: theorems

No `sorry`, no `native_decide`, no new axioms. Statements about the replica's own predicates
(`fixedStyle`, `expPartRejected`) and about the positional arithmetic behind the octal reading.
-/

namespace Jank.R3.Boost.Theorems

open Jank.R3.Boost.Dec

/-! ## MP4: when jank's `str()` of a decimal is scientific

jank calls `str()` with no digits and no flags: `number_of_digits = 128`, the digit string has
`len ∈ [121, 128]` characters (`data[0]` plus 15 limbs of 8), and `format_float_string` takes
`digits = max(len, 16) = len`. -/

/-- With jank's flags, the text is fixed notation exactly when −4 ≤ order < len. -/
theorem jank_str_fixed_iff (myExp len : Int) :
    fixedStyle {} myExp len = true ↔ (-4 ≤ myExp ∧ myExp < len) := by
  simp [fixedStyle]

/-- Every nonzero value below 10^-4 (order ≤ −5) is printed in scientific form by jank, whatever
its digits; Java prints the plain form for adjusted exponents −6 and −5. -/
theorem jank_sci_below_1e_4 (myExp len : Int) (h : myExp ≤ -5) :
    fixedStyle {} myExp len = false := by
  simp [fixedStyle]; intro h1; omega

/-- From 10^128 up (order ≥ 128 ≥ len) jank prints scientific form. -/
theorem jank_sci_from_1e128 (myExp len : Int) (hlen : len ≤ 128) (h : 128 ≤ myExp) :
    fixedStyle {} myExp len = false := by
  simp [fixedStyle]; intro _; omega

/-! ## MP12: an AOT BigDecimal constant whose text is `<d>e±XX.0` cannot be read back

`gen_constant` writes `to_string()`, i.e. `str()` plus `.0` when it has no `.`: a single
significant digit in scientific form gives `d e ± x₁…xₖ . 0`. rd_string's standalone exponent
check (`expPartRejected`) rejects it for every sign and exponent digits. -/

theorem aot_sci_text_rejected (d sgn : Nat) (xs : List Nat) (hs : sgn = 43 ∨ sgn = 45) :
    expPartRejected ([d, 101, sgn] ++ xs ++ [46, 48]) 1 = true := by
  have hsgn : (sgn == 43 || sgn == 45) = true := by
    rcases hs with h | h <;> simp [h]
  unfold expPartRejected findFirstNotOf
  have hnx : ([d, 101, sgn] ++ xs ++ [46, 48]).getD (1 + 1) 0 = sgn := by simp
  rw [hnx]
  simp only [hsgn, if_true]
  rw [List.find?_isSome]
  refine ⟨xs.length + 3, ?_, ?_⟩
  · simp [List.mem_filter, List.mem_range]
  · have : ([d, 101, sgn] ++ xs ++ [46, 48]).getD (xs.length + 3) 0 = 46 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]
    rw [this]; decide

/-! ## MP15 (R7): a ratio part read as octal is smaller than its decimal reading

`posVal b ds` is the value of the digits `ds` in base `b` (boost's octal branch places each
digit's 3 bits: its value is `posVal 8`; Clojure's `BigInteger(s)` is `posVal 10`). -/

def posVal (b : Nat) : List Nat → Nat
  | [] => 0
  | d :: ds => d * b ^ ds.length + posVal b ds

theorem octal_le_decimal (ds : List Nat) : posVal 8 ds ≤ posVal 10 ds := by
  induction ds with
  | nil => simp [posVal]
  | cons d ds ih =>
    simp only [posVal]
    have hp : 8 ^ ds.length ≤ 10 ^ ds.length := Nat.pow_le_pow_left (by omega) _
    have := Nat.mul_le_mul_left d hp
    omega

/-- Any digit string of two or more digits with a nonzero leading digit reads strictly smaller
in octal: `0010/3` is `8/3`, `1/0100000000000000000000` is `1/8^20`. -/
theorem octal_lt_decimal (d : Nat) (ds : List Nat) (hd : 1 ≤ d) (hn : ds ≠ []) :
    posVal 8 (d :: ds) < posVal 10 (d :: ds) := by
  simp only [posVal]
  have hlen : ds.length ≠ 0 := by
    intro h; exact hn (List.eq_nil_of_length_eq_zero h)
  have hp : 8 ^ ds.length < 10 ^ ds.length := Nat.pow_lt_pow_left (by omega) hlen
  have h1 : d * 8 ^ ds.length < d * 10 ^ ds.length := Nat.mul_lt_mul_of_pos_left hp (by omega)
  have := octal_le_decimal ds
  omega

/-! ## MP1: no decimal is a third

cpp_dec_float divides by multiplying with an inverse held in 128 decimal digits, and its
multiplication truncates (never rounds up). No terminating decimal `m / 10^k` is 1/3, so
`6 × inverse(3)` is 2 only if the inverse lies above 1/3; the replica's Newton iteration (from
the double estimate, with truncating products) stays below, giving 1.999…9. -/

theorem no_decimal_third (m k : Nat) : 3 * m ≠ 10 ^ k := by
  intro h
  have h1 : (10 ^ k) % 3 = 1 := by
    rw [Nat.pow_mod]; simp
  omega

theorem six_times_decimal_ne_two (m k : Nat) : 6 * m ≠ 2 * 10 ^ k := by
  intro h
  exact no_decimal_third m k (by omega)

end Jank.R3.Boost.Theorems
