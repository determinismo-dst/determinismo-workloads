import Jank.R3.Codegen.Native

/-!
# For every input: what the emitted code does with native values

- the C++ type of an integer literal's text against the analyzer's `literal_type`;
- R24's loop `(loop [x c] (if (< x n) (recur (+ x 0.5)) x))`: jank's `int` local never reaches
  `n > 0` from any start below it, Clojure's double local always does;
- every JIT and AOT command line makes jank's `while(true){…}` loops and its functions
  `mustprogress`.
-/

namespace Jank.R3.Codegen

open Jank.Analyzer

/-- The analyzer types a literal `int` exactly in `[-2^31, 2^31)`; the C++ text is an `int` exactly
in `(-2^31, 2^31)`: they differ only at `-2147483648`, whose text is a `long`. -/
theorem decimal_text_type_int_iff (v : Int) : cppDecimalType v = .int ↔ -2147483648 < v ∧ v < 2147483648 := by
  unfold cppDecimalType
  by_cases h : v.natAbs ≤ 2147483647
  · simp only [h, if_true, true_iff]; omega
  · simp only [h, if_false]
    constructor
    · intro hc; cases hc
    · intro ⟨h1, h2⟩; omega

theorem int_min_literal_types :
    literalType (.integer (BitVec.ofInt 64 (-2147483648))) false = .int
    ∧ cppDecimalType (-2147483648) = .long := by decide

/-- C++'s `(int)(x + 0.5)` for an `int` `x` (the sum is exact in double): truncation toward zero
of `(2x + 1) / 2`. -/
def halfStep (x : Int) : Int := if 0 ≤ 2 * x + 1 then (2 * x + 1) / 2 else -((-(2 * x + 1)) / 2)

theorem halfStep_nonneg (x : Int) (h : 0 ≤ x) : halfStep x = x := by
  unfold halfStep; split <;> omega

theorem halfStep_neg (x : Int) (h : x < 0) : halfStep x = x + 1 := by
  unfold halfStep; split <;> omega

/-- jank's loop state after `k` iterations (the `recur` taken while `x < n`). -/
def jankLoop (n c : Int) : Nat → Int
  | 0 => c
  | k + 1 => let x := jankLoop n c k; if x < n then halfStep x else x

/-- For every start `c < n` with `n > 0`, jank's loop local stays below `n` forever: the loop
never ends (and has no side effect: `lt`, `add` and the cast are inline arithmetic). -/
theorem r24_never_exits (n c : Int) (hn : 0 < n) (hc : c < n) (k : Nat) : jankLoop n c k < n ∧ jankLoop n c k ≤ max c 0 := by
  induction k with
  | zero => simp [jankLoop]; omega
  | succ k ih =>
    simp only [jankLoop]
    obtain ⟨h1, h2⟩ := ih
    simp only [h1, if_true]
    by_cases hx : 0 ≤ jankLoop n c k
    · rw [halfStep_nonneg _ hx]; exact ⟨h1, h2⟩
    · rw [halfStep_neg _ (by omega)]; omega

/-- Clojure's loop local is a double: `c + k/2` reaches `n` after `2(n - c)` steps. -/
theorem r24_clojure_exits (n c : Int) (hc : c < n) : ∃ k : Nat, 2 * n ≤ 2 * c + k :=
  ⟨(2 * (n - c)).toNat, by omega⟩

/-! ## Every command line makes loops `mustprogress` -/

def stdOf (f : Flag) : Option String := match f with | .std s => some s | _ => none
def finiteOf (f : Flag) : Option Bool := match f with | .finiteLoops b => some b | _ => none

theorem filterMap_filter_debug {β : Type} (h : Flag → Option β) (hd : h .debugInfo = none) (l : List Flag) :
    (l.filter (· != .debugInfo)).filterMap h = l.filterMap h := by
  induction l with
  | nil => rfl
  | cons x rest ih =>
    rw [List.filter_cons]
    by_cases hx : x = .debugInfo
    · subst hx
      have e : (Flag.debugInfo != Flag.debugInfo) = false := by decide
      rw [e]
      simp only [Bool.false_eq_true, ite_false]
      rw [ih, List.filterMap_cons, hd]
    · have e : (x != Flag.debugInfo) = true := bne_iff_ne.mpr hx
      rw [e]
      simp only [ite_true, List.filterMap_cons]
      rw [ih]

theorem filterMap_map_none {α β : Type} (l : List α) (g : α → Flag) (h : Flag → Option β)
    (hg : ∀ a, h (g a) = none) : (l.map g).filterMap h = [] := by
  induction l with
  | nil => rfl
  | cons a rest ih => simp [List.filterMap_cons, hg a, ih]

theorem jit_std (bt : BuildType) (c : Cli) : (jitArgs bt c).filterMap stdOf = ["gnu++20"] := by
  have hopt : stdOf (optFlag c.levels.runtime 0) = none := by unfold optFlag; split <;> rfl
  simp only [stdOf] at hopt
  have hi := filterMap_map_none c.includes Flag.include stdOf (fun _ => rfl)
  have hl := filterMap_map_none c.libDirs Flag.libDir stdOf (fun _ => rfl)
  have hdf := filterMap_map_none c.defines Flag.define stdOf (fun _ => rfl)
  unfold jitArgs jitArgsPrefix
  split
  · cases bt <;> simp [List.filterMap_append, List.filterMap_cons, hi, hl, hdf, hopt, jankJitFlags,
      commonFlags, jitCompilerFlags, stdOf]
  · rw [List.filterMap_append, filterMap_filter_debug stdOf rfl]
    cases bt <;> simp [List.filterMap_append, List.filterMap_cons, hi, hl, hdf, hopt, jankJitFlags,
      commonFlags, jitCompilerFlags, stdOf]

theorem jit_finite (bt : BuildType) (c : Cli) : (jitArgs bt c).filterMap finiteOf = [] := by
  have hopt : finiteOf (optFlag c.levels.runtime 0) = none := by unfold optFlag; split <;> rfl
  simp only [finiteOf] at hopt
  have hi := filterMap_map_none c.includes Flag.include finiteOf (fun _ => rfl)
  have hl := filterMap_map_none c.libDirs Flag.libDir finiteOf (fun _ => rfl)
  have hdf := filterMap_map_none c.defines Flag.define finiteOf (fun _ => rfl)
  unfold jitArgs jitArgsPrefix
  split
  · cases bt <;> simp [List.filterMap_append, List.filterMap_cons, hi, hl, hdf, hopt, jankJitFlags,
      commonFlags, jitCompilerFlags, finiteOf]
  · rw [List.filterMap_append, filterMap_filter_debug finiteOf rfl]
    cases bt <;> simp [List.filterMap_append, List.filterMap_cons, hi, hl, hdf, hopt, jankJitFlags,
      commonFlags, jitCompilerFlags, finiteOf]

/-- Every JIT command line (every build type, every `-O`, `-I`, `-L`, `-D`): a non-empty
`while(true){…}` loop is `mustprogress`, and so is every function. -/
theorem jit_loops_must_progress (bt : BuildType) (c : Cli) :
    loopMustProgress (jitArgs bt c) false = true ∧ functionMustProgress (jitArgs bt c) = true := by
  have h1 : finiteLoopsKind (jitArgs bt c) = none := by
    have := jit_finite bt c
    unfold finiteLoopsKind
    show ((jitArgs bt c).filterMap finiteOf).getLast? = none
    rw [this]; rfl
  have h2 : effectiveStd (jitArgs bt c) = "gnu++20" := by
    have := jit_std bt c
    unfold effectiveStd
    show ((jitArgs bt c).filterMap stdOf).getLast?.getD "gnu++17" = "gnu++20"
    rw [this]; rfl
  simp [loopMustProgress, functionMustProgress, h1, h2, isCxx11OrLater]

end Jank.R3.Codegen
