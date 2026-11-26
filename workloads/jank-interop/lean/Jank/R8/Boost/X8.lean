import Jank.R8.Boost.Spec

/-!
# Round 8, area B: x8 and (/ 6.0M 3.0M), single inputs, by the kernel

The operands' mantissas are what the replica and boost store (results/r8-boost-brief.txt):
`P = 2^200` read as `P · 10^64` at exponent 56 (61 digits at order 60, `60 mod 8 = 4`); boost's
Newton inverse of P, `qStock`, 124 digits at exponent −64; S2's quotient, the exact `5^200 · 10^-200`
read back (140 digits at order −61, `−61 mod 8 = 3`, so 124 kept); 6.0 as `6 · 10^120` at exponent 0
and boost's inverse of 3, the 128-digit `0.333…3` at exponent −8.
-/

namespace Jank.R8.Boost.X8

open Jank.R8.Boost.Spec

def P : Nat := 2 ^ 200

/-- boost's `calculate_inv` of 2^200 (cpp_dec_float.hpp 1222-1270), the 16 limbs as one integer. -/
def qStock : Nat :=
  6223015277861141707144064053780124240590252168721167133101116614789698834035383441183944823125713616956966589555122482125175

/-- P is read exactly. -/
theorem p_read : keepM P 61 4 = P * 10 ^ 64 := by decide +kernel

/-- S2's quotient keeps the first 124 of the exact quotient's 140 digits. -/
theorem s2_quotient : keepM (5 ^ 200) 140 3 = 5 ^ 200 / 10 ^ 16 := by decide +kernel

/-- The stock Newton inverse is ABOVE 1/P (`qStock · 10^-184 > 1/P`): round 3's "the inverse is
below 1/v" does not hold here. -/
theorem stock_inverse_above : 10 ^ 184 < P * qStock := by decide +kernel

/-- S2's truncated quotient is below 1/P. -/
theorem s2_quotient_below : P * (5 ^ 200 / 10 ^ 16) < 10 ^ 184 := by decide +kernel

/-- Stock x8: `P · qStock` (exponent 56 − 64 + 8 = 0) is exactly 1: the excess is past the 121
digits a value of order 0 keeps. -/
theorem x8_stock : mulSpec (P * 10 ^ 64) qStock = (10 ^ 120, 1) := by decide +kernel

/-- Patched x8: `P · (5^200 / 10^16)` (exponent 56 − 64 = −8) is `1 − 699 · 10^-128`, printed by
jank as 0.99…99301 (128 digits; boost's scientific text pads a 0: "…993010"). -/
theorem x8_patched : mulSpec (P * 10 ^ 64) (5 ^ 200 / 10 ^ 16) = (10 ^ 128 - 699, 0) := by
  decide +kernel

/-- Stock `(/ 6.0M 3.0M)`: 6 times the 128-digit inverse of 3 (exponent 0 − 8 + 8 = 0) is
`2 − 10^-120`: 1.999…9 with 120 nines. -/
theorem six_over_three_stock : mulSpec (6 * 10 ^ 120) ((10 ^ 128 - 1) / 3) = (2 * 10 ^ 120 - 1, 1) := by
  decide +kernel

end Jank.R8.Boost.X8
