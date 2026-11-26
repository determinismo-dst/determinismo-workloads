import Jank.R6.Champ.Laws

/-!
# Round 6, CHAMP: what each lost premise does (jank's doubles on the replica)

`Laws.lean` proves the laws under `Lawful`. jank's `=` and `hash` drop two of its premises:

- `compat` (equal keys hash alike): `0.0` and `-0.0` are `=` (`real::equal` is C++ `==`,
  number.cpp 267-282 and oref.hpp 414-419 for tagged reals) but `hash::real` (hash.cpp 116-127,
  `v ^ (v >> 32)` of the bits) gives 0 and 2^31 (round 1's D12). Their hashes share the low 30
  bits, so the first 6 levels of `get` agree and the 7th does not.
- `refl`: `##NaN` (`jank_nan`, a tagged `small_real`, number.cpp 512) is not `=` to itself, and
  immer compares with `std::equal_to<object_ref>` = `runtime::equal` (core/equal.cpp 19-22), which
  has no identity check; Clojure's maps and sets use `Util.equiv`, whose first test is `k1 == k2`.

`dbl` is jank's hash and `=` on doubles as IEEE bit patterns (kernel-evaluable; NaN never `=`).
Each fact is kernel-checked on the replica:

- law 1 (`get` of another key) breaks both ways under D12: `-0.0` is found in `#{0.0}`, lost
  after adding `2.0`, found again after removing `2.0` (`negzero_*`); with `1.0` instead of `2.0`
  it stays found (the values split at level 4, where `-0.0` still agrees with `0.0`);
- the count law never breaks: `count` = the iteration's length for every equality
  (`count_eq_seq_add`/`_sub` in `Laws.lean`), here with `NaN` stored twice (`nan_*`);
- uniqueness breaks under a lost `refl`: two `NaN`s in one collision node, never found, never
  removed.
-/

namespace Jank.R6.Champ.Breaks

open Jank.R3.Immer.Champ Jank.R6.Champ

/-- IEEE `==` on double bit patterns: NaN unequal to everything, `0.0 == -0.0`. -/
def isNaN (b : Nat) : Bool := (b >>> 52) % 2048 == 2047 && b % 2 ^ 52 != 0
def ieeeEq (a b : Nat) : Bool := !isNaN a && !isNaN b && (a == b || (a % 2 ^ 63 == 0 && b % 2 ^ 63 == 0))
/-- `hash::real`: `v ^ (v >> 32)` returned as `u32`. -/
def jhash (b : Nat) : Nat := (b ^^^ (b >>> 32)) % 2 ^ 32

/-- jank's hash sets of doubles (`std::hash<object_ref>`, `std::equal_to<object_ref>`). -/
def dbl : Cfg Nat Nat where
  hashT := jhash
  hashK := jhash
  eqTT := ieeeEq
  eqTK := ieeeEq

def pz : Nat := 0                      -- 0.0
def nz : Nat := 0x8000000000000000     -- -0.0
def two : Nat := 0x4000000000000000    -- 2.0
def one : Nat := 0x3FF0000000000000    -- 1.0
def nan : Nat := 0x7FF8000000000000    -- ##NaN (`NAN`)

def addS (c : Champ Nat) (v : Nat) : Champ Nat := ((c.add dbl v).run {}).1
def subS (c : Champ Nat) (k : Nat) : Champ Nat := ((c.sub dbl k).run {}).1

/-- The premise jank's doubles lose: `0.0 = -0.0`, hashes 0 and 2^31. -/
theorem negzero_compat_fails : ieeeEq pz nz = true ∧ jhash pz = 0 ∧ jhash nz = 2 ^ 31 := by decide +kernel

/-- `(contains? #{0.0} -0.0)`: found (Clojure: true). -/
theorem negzero_found_alone : Champ.get dbl (addS Champ.empty pz) nz = some pz := by decide +kernel

/-- `(contains? (conj #{0.0} 2.0) -0.0)`: lost after adding a value not `=` to `-0.0` (Clojure: true). -/
theorem negzero_lost_after_add : Champ.get dbl (addS (addS Champ.empty pz) two) nz = none ∧
    ieeeEq two nz = false := by decide +kernel

/-- `(contains? (disj (conj #{0.0} 2.0) 2.0) -0.0)`: found again after removing `2.0`. -/
theorem negzero_found_after_sub : Champ.get dbl (subS (addS (addS Champ.empty pz) two) two) nz = some pz := by
  decide +kernel

/-- With `1.0` instead of `2.0`, `-0.0` is still found. -/
theorem negzero_found_with_one : Champ.get dbl (addS (addS Champ.empty pz) one) nz = some pz := by decide +kernel

/-- `(disj (conj #{0.0} 2.0) -0.0)` removes nothing: the count stays 2; `(disj #{0.0} -0.0)` is
empty. -/
theorem negzero_disj : (subS (addS (addS Champ.empty pz) two) nz).size = 2 ∧
    (subS (addS Champ.empty pz) nz).size = 0 := by decide +kernel

/-- `##NaN` twice: stored twice, in one collision node, never found, never removed; the count and
the iteration agree (2). -/
theorem nan_stored_twice : (addS (addS Champ.empty nan) nan).size = 2 ∧
    (addS (addS Champ.empty nan) nan).toList = [nan, nan] := by decide +kernel

theorem nan_never_found : Champ.get dbl (addS Champ.empty nan) nan = none ∧
    (subS (addS (addS Champ.empty nan) one) nan).size = 2 := by decide +kernel

end Jank.R6.Champ.Breaks
