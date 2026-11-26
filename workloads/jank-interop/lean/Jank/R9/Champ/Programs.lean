import Jank.R9.Champ.Order
import Jank.R8.Champ.Programs

/-!
# Round 9, CHAMP: the programs, on the replica (`decide +kernel`)

**H8-1 with the fix.** Round 8's programs (`Jank.R8.Champ.Programs`: the longs 1 and 7676047846, one
full jank hash) run through the fixed steps give Clojure's orders: `fix_y22*`.

**H9-1: a transient chain and its persistent twin differ in CONTENTS (stock jank).** Three stored
values `a`, `q`, `b` of one full hash with `a = q`, `q = b` and `a ≠ b` (jank's BigDecimal `=` is
`|x - y| < 2^-52`, D8: not transitive). The chain `conj a, conj b, conj a, disj q`:
- transient (`conj!`/`disj!`): the collision node `[b, a]` is the transient's own, so `conj! a` writes
  `a` in place; `disj! q` finds `b` first and removes it: `#{a}`;
- persistent (`conj`/`disj`): `conj a` moves `a` to the front (`[a, b]`, H8-1); `disj q` finds `a`
  first: `#{b}`.
Clojure (exact `=`): `#{a b}` both ways. With the fix (either half) both chains give `#{a}`.
Here the equality is an abstract non-transitive one over `Nat` (`h91Cfg`: 1 = 2, 2 = 3, 1 ≠ 3, one
hash); the driver (`jank9-champ h91`) runs the same chain with round 3's replicas of jank's
BigDecimal hash and `=` on the three BigDecimals found by search, and `.r9-scratch/champ/dec/h91.cpp`
runs it on immer itself.
-/

namespace Jank.R9.Champ.Programs

open Jank.R3.Immer.Champ Jank.R6.Champ Jank.R7.Champ Jank.R8.Champ Jank.R8.Champ.Programs Jank.R9.Champ

/-! ## H8-1 with the fix -/

/-- `(assoc m k :b)` with the fix. -/
def assocF (m : Champ (Int × Nat)) (k : Int) (val : Nat) : Champ (Int × Nat) := ((addRootF mapCfg m (k, val)).run {}).1

/-- y22: `(assoc m 1 :b)` keeps `(7676047846 1)`. -/
theorem fix_y22 : keysOf m0 = [k2, k1] ∧ keysOf (assocF m0 k1 1) = [k2, k1] := by decide +kernel

/-- y22b: `(assoc m 1 :a)` keeps the order. -/
theorem fix_y22b : keysOf (assocF m0 k1 0) = [k2, k1] := by decide +kernel

/-- y22c: `(conj s 1)` keeps the order (immer half; the jank half returns `s` itself). -/
theorem fix_y22c : ((addRootF setCfg s0 k1).run {}).1.toList = [k2, k1] := by decide +kernel

def tChainF : Champ (Int × Nat) :=
  ((do let c ← addMutRootF mapCfg tokT (Champ.empty : Champ (Int × Nat)) (k1, 0)
       let c ← addMutRootF mapCfg tokT c (k2, 0)
       addMutRootF mapCfg tokT c (k1, 1)) : M _).run {} |>.1

def pChainF : Champ (Int × Nat) :=
  ((do let c ← addRootF mapCfg (Champ.empty : Champ (Int × Nat)) (k1, 0)
       let c ← addRootF mapCfg c (k2, 0)
       addRootF mapCfg c (k1, 1)) : M _).run {} |>.1

/-- y22d: the transient chain and the persistent chain hold the same entries in the same order. -/
theorem fix_y22d : tChainF.toList = pChainF.toList ∧ keysOf pChainF = [k2, k1] := by decide +kernel

/-- y22e: `assoc!` on a new transient of `m` keeps the order. -/
theorem fix_y22e : keysOf ((addMutRootF mapCfg tokT m0 (k1, 1)).run {}).1 = [k2, k1] := by decide +kernel

/-! ## H9-1 on an abstract non-transitive equality -/

/-- One full hash for every value; `=` relates 1 and 2, 2 and 3 (both ways) and each value to itself,
but not 1 and 3 (`a = 1`, `q = 2`, `b = 3`: jank's D8 on three BigDecimals). -/
def h91Cfg : Cfg Nat Nat where
  hashT _ := 3969516785
  hashK _ := 3969516785
  eqTT x y := x == y || (x + y == 3 && x * y == 2) || (x + y == 5 && x * y == 6)
  eqTK x y := x == y || (x + y == 3 && x * y == 2) || (x + y == 5 && x * y == 6)

def tok9 : Nat := 1001

/-- `(persistent! (-> (transient #{}) (conj! a) (conj! b) (conj! a) (disj! q)))`, stock. -/
def h91T : Champ Nat :=
  ((do let c ← (Champ.empty : Champ Nat).addMut h91Cfg tok9 1
       let c ← c.addMut h91Cfg tok9 3
       let c ← c.addMut h91Cfg tok9 1
       c.subMut h91Cfg tok9 2) : M _).run {} |>.1

/-- `(-> #{} (conj a) (conj b) (conj a) (disj q))`, stock. -/
def h91P : Champ Nat :=
  ((do let c ← (Champ.empty : Champ Nat).add h91Cfg 1
       let c ← c.add h91Cfg 3
       let c ← c.add h91Cfg 1
       c.sub h91Cfg 2) : M _).run {} |>.1

/-- The same two chains with the fix. -/
def h91TF : Champ Nat :=
  ((do let c ← addMutRootF h91Cfg tok9 (Champ.empty : Champ Nat) 1
       let c ← addMutRootF h91Cfg tok9 c 3
       let c ← addMutRootF h91Cfg tok9 c 1
       c.subMut h91Cfg tok9 2) : M _).run {} |>.1

def h91PF : Champ Nat :=
  ((do let c ← addRootF h91Cfg (Champ.empty : Champ Nat) 1
       let c ← addRootF h91Cfg c 3
       let c ← addRootF h91Cfg c 1
       c.sub h91Cfg 2) : M _).run {} |>.1

/-- H9-1 on the replica: stock, the transient chain keeps `a` and the persistent twin keeps `b`;
with the fix both keep `a`. -/
theorem h91_stock_contents_differ : h91T.toList = [1] ∧ h91P.toList = [3] := by decide +kernel

theorem h91_fixed_agree : h91TF.toList = [1] ∧ h91PF.toList = [1] := by decide +kernel

/-- The control: without the repeated `conj a` (no in-place write) both chains agree on stock. -/
def h91Tc : Champ Nat :=
  ((do let c ← (Champ.empty : Champ Nat).addMut h91Cfg tok9 1
       let c ← c.addMut h91Cfg tok9 3
       c.subMut h91Cfg tok9 2) : M _).run {} |>.1

def h91Pc : Champ Nat :=
  ((do let c ← (Champ.empty : Champ Nat).add h91Cfg 1
       let c ← c.add h91Cfg 3
       c.sub h91Cfg 2) : M _).run {} |>.1

theorem h91_control : h91Tc.toList = [1] ∧ h91Pc.toList = [1] := by decide +kernel

/-- The equality is not lawful (not transitive): round 8's sequence theorem does not apply, and its
conclusion fails (`h91_stock_contents_differ`); the fixed one (`buildTF_agree_empty`) holds. -/
theorem h91_not_transitive : h91Cfg.eqTT 1 2 = true ∧ h91Cfg.eqTT 2 3 = true ∧ h91Cfg.eqTT 1 3 = false := by
  decide

end Jank.R9.Champ.Programs
