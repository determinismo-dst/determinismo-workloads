import Jank.Analyzer.Eval

/-!
# Theorems about the analyzer replica

Proved with `decide`/`simp` (no `sorry`, no `native_decide`).
-/

namespace Jank.Analyzer

def arithTypes : List CT := [.bool, .int, .long, .double]

/-- The type an `if` or a `case` pair gets (`find_branch_common_type`, cpp_util.cpp:1908), or
`object_ref` when the branches are rejected (not reached for the types below). -/
def branchType (t : CT) (e : Option CT) : CT :=
  match findBranchCommonType t e false with
  | .ok b => b.type
  | .error _ => .objectRef

def branchConverts (t : CT) (e : Option CT) : Bool × Bool :=
  match findBranchCommonType t e false with
  | .ok b => (b.thenNeedsConversion, b.elseNeedsConversion)
  | .error _ => (false, false)

/-- `if` with branches of two different arithmetic types is accepted without boxing either
branch, and gets one native type that differs from at least one branch's: that branch's value is
converted (7135b7708, `find_branch_common_type`). -/
theorem if_merges_distinct_natives :
    ∀ a ∈ arithTypes, ∀ b ∈ arithTypes, a ≠ b →
      branchConverts a (some b) = (false, false) ∧
      isAnyObject (branchType a (some b)) = false ∧
      (branchType a (some b) ≠ a ∨ branchType a (some b) ≠ b) := by
  decide

/-- `(if c 1 2.5)` is a `double`; `(if c true 1)` and `(if c 0 false)` are `int`s. -/
theorem if_int_double : branchType .int (some .double) = .double := by decide
theorem if_bool_int : branchType .bool (some .int) = .int := by decide
theorem if_int_bool : branchType .int (some .bool) = .int := by decide

/-- When the other branch is an object, the native branch is boxed (no native merge). -/
theorem if_object_branch :
    ∀ a ∈ arithTypes, (branchConverts .objectRef (some a)).2 = true ∧
      (branchConverts a (some .objectRef)).1 = true ∧ branchType a (some .objectRef) = .objectRef := by
  decide

/-- `analyze_case`'s type loop (processor.cpp:1484-1522): each branch against the default, the
last pair's common type wins, conversion if any pair needed one. -/
def caseChosenType (dflt : CT) (branches : List CT) : CT × Bool :=
  branches.foldl (fun (acc : CT × Bool) b =>
    match findBranchCommonType b (some dflt) false with
    | .ok r => (r.type, acc.2 || r.thenNeedsConversion || r.elseNeedsConversion)
    | .error _ => acc) (dflt, false)

/-- A `double` branch then an `int` branch with an `int` default: the case is an `int`, with no
conversion, so the `double` branch's value is truncated by the case's local. -/
theorem case_last_branch_wins : caseChosenType .int [.double, .int] = (.int, false) := by decide

/-- The same branches in the other order: the case is a `double`. -/
theorem case_order_matters : caseChosenType .int [.int, .double] = (.double, false) := by decide

/-- An object branch, then a `double` branch: everything is converted to `double`, including the
object branch (`from_object`, which throws for a keyword or nil). -/
theorem case_object_then_double : caseChosenType .int [.objectRef, .double] = (.double, true) := by decide

/-- A literal that fits i32 is a C++ `int` (32 bits); Clojure's literal is a 64-bit long. -/
theorem small_literal_is_int (v : BitVec 32) : literalType (.smallInteger v) false = .int := rfl

/-- Loop locals keep native types (`mutable_type` erases only typed objects, C strings, void). -/
theorem loop_local_native : ∀ t ∈ arithTypes, mutableType t = t := by decide

/-- A `recur` argument for an `int` loop local: a `double` is cast, an object is converted with
`convert<int>::from_object`, a `long` is cast. -/
theorem recur_conversions :
    determineImplicitConversion .double .int = .cast ∧
    determineImplicitConversion .long .int = .cast ∧
    determineImplicitConversion .objectRef .int = .fromObject ∧
    determineImplicitConversion (.typed "nil") .bool = .fromObject ∧
    determineImplicitConversion .int .double = .cast := by
  decide

/-- What the macro gets (context.cpp:634): for `(m a₁ … aₙ)`, the arguments are
`((a₁ … aₙ))`, then `m`, then `a₁ … aₙ`: `&form` is a one-element list holding the arguments, and
`&env` is the macro's own symbol. -/
theorem macro_arguments (md : Option Obj) (m : Obj) (args : List Obj) :
    (consObj (consObj (Obj.persistentList md (m :: args)).rest .nil) (.persistentList md (m :: args))).elems
      = some (.persistentList none [.persistentList none args] :: m :: args) := by
  simp [Obj.rest, Obj.elems, consObj]

/-- So `&form` is never the form: for every macro call, `&form` ≠ the call. -/
theorem macro_form_is_not_the_form (md : Option Obj) (m : Obj) (args : List Obj) :
    (Obj.persistentList none [.persistentList none args]) ≠ .persistentList md (m :: args) ∨
      (m = .persistentList none args ∧ args = [] ∧ md = none) := by
  by_cases h : md = none
  · subst h
    by_cases h2 : args = []
    · subst h2
      by_cases h3 : m = .persistentList none []
      · exact Or.inr ⟨h3, rfl, rfl⟩
      · left; intro h4; injection h4 with _ h5; injection h5 with h6; exact h3 h6.symm
    · left; intro h4; injection h4 with _ h5; injection h5 with _ h6; exact h2 h6.symm
  · left; intro h4; injection h4 with h5; exact h (h5.symm)

/-- A frame chain `fn f [n]` (no locals) whose parent `let` frame binds `f`: the local lookup
(`find_local_or_capture`, which `analyze_symbol` consults first, processor.cpp:1599) finds the
outer `f` across the fn, so the fn's name never wins (Clojure: the name is the innermost local). -/
def shadowArena : Arena :=
  { frames := #[{ type := .root },
                { type := .let, parent := some 0, locals := [(Obj.s "f", [0])] },
                { type := .fn, parent := some 1, locals := [(Obj.s "n", [1])], fnCtx := some 0 }],
    bindings := #[{ name := Obj.s "f" }, { name := Obj.s "n" }],
    fnCtxs := #[{ name := "f" }] }

theorem outer_local_wins_over_fn_name :
    findLocalOrCapture shadowArena 2 (Obj.s "f") = some ⟨0, [2]⟩ ∧
    findNamedRecursion shadowArena 2 (Obj.s "f") = some ⟨2, []⟩ := by
  decide

/-- A `long` value assigned to an `int` loop local (`recur (inc x)` from 2147483647) wraps. -/
theorem int_local_wraps :
    (match convNative .int (.i 2147483648) with | .ok (.i v) => some v | _ => none) = some (-2147483648) := by
  decide

/-- A boolean literal stays a C++ `bool` (a `cpp_literal`), which C++ arithmetic accepts. -/
theorem bool_literal_is_native : literalIsPrimitive (.boolean true) = false ∧ literalType (.boolean true) false = .bool := by
  decide

end Jank.Analyzer
