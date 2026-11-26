/-!
# Round 8, coordinator: `min` and `max` on objects (V56, V57), stock and with fixes/V56.diff

Clojure 1.12's `Numbers.min(Object, Object)` and `max(Object, Object)` (Numbers.java 4124-4233):
a NaN operand is the result (the first one first); otherwise `min` is `lt(x, y) ? x : y` and `max`
is `gt(x, y) ? x : y`, so on a tie both give the SECOND operand.

jank 94d32623's object `min`/`max` (core/math.hpp 741-866 and 868-990, the object branches):
`min` is `l < r ? l : r` and `max` is `l < r ? r : l`; C++'s `<` is false whenever a NaN takes
part. `fixes/V56.diff` puts the two NaN checks first and writes `max` as `r < l ? l : r`.

A number is modeled by its value (an integer stands for any ordered value) and a kind tag (long,
double, BigInt, ...), because a tie between a long and a double is visible: `(max 1 1.0)` is 1.0.
The tag never takes part in a comparison. ★ theorems hold for every pair.
-/

namespace Jank.R8.Coord.MinMax

/-- A number as `min`/`max` see it: NaN, or a value with its kind. -/
inductive Num where
  | nan
  | val (v : Int) (kind : Nat)
  deriving DecidableEq, Repr

def isNaN : Num → Bool
  | .nan => true
  | .val _ _ => false

/-- C++'s `<` and Clojure's `lt`: false when a NaN takes part, else the values' order. -/
def lt : Num → Num → Bool
  | .val a _, .val b _ => decide (a < b)
  | _, _ => false

def cljMin (x y : Num) : Num := if isNaN x then x else if isNaN y then y else if lt x y then x else y
def cljMax (x y : Num) : Num := if isNaN x then x else if isNaN y then y else if lt y x then x else y

def stockMin (x y : Num) : Num := if lt x y then x else y
def stockMax (x y : Num) : Num := if lt x y then y else x

/-- fixes/V56.diff, as written in math.hpp's object branches. -/
def fixedMin (x y : Num) : Num :=
  if isNaN x then x else if isNaN y then y else if lt x y then x else y
def fixedMax (x y : Num) : Num :=
  if isNaN x then x else if isNaN y then y else if lt y x then x else y

/-- ★ With V56, jank's object min and max are Clojure's for every pair. -/
theorem fixed_eq_clj (x y : Num) : fixedMin x y = cljMin x y ∧ fixedMax x y = cljMax x y :=
  ⟨rfl, rfl⟩

/-- ★ Stock `min` differs from Clojure's exactly when the first operand is NaN and the second
is not: `(min ##NaN 1)` through a fn is 1 (V56). -/
theorem stock_min_differs_iff (x y : Num) :
    stockMin x y ≠ cljMin x y ↔ (x = .nan ∧ y ≠ .nan) := by
  cases x <;> cases y <;> simp [stockMin, cljMin, isNaN, lt]
  all_goals (split <;> simp_all)

/-- ★ Stock `max` differs from Clojure's exactly when the second operand is NaN and the first is
not (V56), or on a tie of two different numbers (V57: `(max 1 1.0)` through a fn is 1, Clojure's
1.0; `(max 0.0 -0.0)` gives 0.0, Clojure's -0.0). -/
theorem stock_max_differs_iff (x y : Num) :
    stockMax x y ≠ cljMax x y ↔
      ((y = .nan ∧ x ≠ .nan) ∨
       (∃ a k j, x = .val a k ∧ y = .val a j ∧ k ≠ j)) := by
  cases x with
  | nan => cases y <;> simp [stockMax, cljMax, isNaN, lt]
  | val a k =>
    cases y with
    | nan => simp [stockMax, cljMax, isNaN, lt]
    | val b j =>
      simp only [stockMax, cljMax, isNaN, lt]
      by_cases hab : a < b
      · have : ¬ b < a := by omega
        simp [hab, this]
        intro h; omega
      · by_cases hba : b < a
        · simp [hab, hba]
          intro h; omega
        · have he : a = b := by omega
          subst he
          simp [hab]
          constructor
          · intro h; exact ⟨a, k, ⟨rfl, rfl⟩, j, ⟨rfl, rfl⟩, h⟩
          · rintro ⟨a', k', ⟨_, rfl⟩, j', ⟨_, rfl⟩, h⟩; exact h

/-- The cases of section 1.4: (min ##NaN 1), (max 1 ##NaN) and the tie (max 1 1.0), with kind 0
a long and 1 a double. -/
theorem examples :
    stockMin .nan (.val 1 0) = .val 1 0 ∧ cljMin .nan (.val 1 0) = .nan ∧
    stockMax (.val 1 0) .nan = .val 1 0 ∧ cljMax (.val 1 0) .nan = .nan ∧
    stockMax (.val 1 0) (.val 1 1) = .val 1 0 ∧ cljMax (.val 1 0) (.val 1 1) = .val 1 1 := by
  decide

end Jank.R8.Coord.MinMax
