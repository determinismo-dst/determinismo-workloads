import Jank.R7.Coord.Decimal

/-!
# Round 8, coordinator: S3c's exact ratio-to-decimal conversion

`fixes/S3c.diff` (ratio.cpp `to_exact_native_big_decimal`) turns a ratio `n/d` (reduced, `d > 0`,
ratio.cpp 47-64) into a decimal wherever a ratio meets a BigDecimal outside division, as Clojure's
Numbers.toBigDecimal does: it strips the factors 2 and 5 from `d` (two `while` loops), throws
"Non-terminating decimal expansion" when anything else is left, and otherwise returns the digits
`n * 2^(k-a) * 5^(k-b)` with scale `k = max a b` (as the text "<digits>e-<k>"). The loops are round
7's `steps` (Jank.R7.Coord.Decimal), with a signed numerator. ★ for every input:
- `conv_sound`: a result is exactly `n / d`;
- `conv_complete`: no result (the throw) means no decimal equals `n / d`.
-/

namespace Jank.R8.Coord.RatioDec

open Jank.R7.Coord.Decimal

/-- S3c's conversion: `some (digits, scale)` or `none` (the throw). -/
def conv (n : Int) (d : Nat) : Option (Int × Nat) :=
  if (steps d).rest = 1 then
    let k := resultScale d
    some (n * (2 ^ (k - (steps d).twos) * 5 ^ (k - (steps d).fives) : Nat), k)
  else none

/-- ★ A result is exactly `n / d`: digits * d = n * 10^scale. -/
theorem conv_sound (n : Int) (d : Nat) (m : Int) (k : Nat) (h : conv n d = some (m, k)) :
    m * d = n * (10 ^ k : Nat) := by
  unfold conv at h
  split at h
  · rename_i hr
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hs := exact_sound 1 d hr
    unfold resultDigits at hs
    simp only [Nat.one_mul] at hs
    rw [Int.mul_assoc, ← Int.natCast_mul]
    unfold resultScale at hs ⊢
    rw [hs]
  · simp at h

/-- ★ No result means no decimal equals `n / d` (for the reduced ratio: `n`, `d` coprime). -/
theorem conv_complete (n : Int) (d : Nat) (hd : 0 < d) (hc : Nat.Coprime n.natAbs d)
    (h : conv n d = none) : ∀ (m : Int) (k : Nat), n * (10 ^ k : Nat) ≠ m * d := by
  intro m k heq
  unfold conv at h
  split at h
  · simp at h
  · rename_i hr
    have hn := exact_complete n.natAbs d hd hc hr m.natAbs k
    apply hn
    have := congrArg Int.natAbs heq
    simpa [Int.natAbs_mul] using this

/-- (+ 1/3 1M) throws; 7/4 is 175 at scale 2; -1/8 is -125 at scale 3. -/
theorem examples :
    conv 1 3 = none ∧ conv 7 4 = some (175, 2) ∧ conv (-1) 8 = some (-125, 3) ∧
    conv 7 3 = none := by
  decide +kernel

end Jank.R8.Coord.RatioDec
