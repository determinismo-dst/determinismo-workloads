import Jank.R4.Interop.Worlds

/-!
# Round 4 interop theorems (no sorry, no native_decide, no new axiom)

★ marks a statement for every input.
-/

namespace Jank.R4.Interop.Theorems

open Jank.Interop
open Jank.R3.Interop
open Jank.R4.Interop

/-- ★ Two primitive operands (builtins, pointers, arrays or **enums**) never reach `GetOperator`:
jank's analysis gives the built-in operator's type or an error, never a user operator function
(processor.cpp 395-410). -/
theorem jank_primitive_operands_builtin_only (p : Platform) (o : Operators.OWorld) (op : Cxx.Op)
    (a b : CType) (ha : Paths.isPrimitive (Clang.nonRef a) = true)
    (hb : Paths.isPrimitive (Clang.nonRef b) = true) (f : Operators.OpFn) :
    Operators.jankOperator p o op [a, b] ≠ .fn f := by
  unfold Operators.jankOperator
  simp only [List.headD_cons, List.getD_cons_succ, List.getD_cons_zero, ha, hb, Bool.and_true,
    Bool.or_true, if_true]
  split <;> simp

/-- ★ A unary operator on a primitive operand never reaches `GetOperator` either. -/
theorem jank_primitive_operand_unary_builtin_only (p : Platform) (o : Operators.OWorld) (op : Cxx.Op)
    (a : CType) (ha : Paths.isPrimitive (Clang.nonRef a) = true) (f : Operators.OpFn) :
    Operators.jankOperator p o op [a] ≠ .fn f := by
  unfold Operators.jankOperator
  simp only [List.headD_cons, List.length_cons, List.length_nil, ha, Bool.true_and,
    beq_self_eq_true, Bool.true_or, if_true]
  split <;> simp

/-- ★ `(cpp/X. args…)` on a class template: the specialization jank constructs never depends on
the arguments — it is the template's defaults (build_cpp_value 3740-3752). -/
theorem jank_ctor_specialization_is_defaults (p : Platform) (t : Templates.ClassTmpl)
    (args : List CType) (targs ps : List CType)
    (h : Templates.jankCtor p t args = .ok (targs, ps)) : targs = t.defaults.filterMap id := by
  unfold Templates.jankCtor at h
  split at h
  · exact absurd h (by simp)
  · dsimp only at h
    split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      exact h.1.symm
    · exact absurd h (by simp)

/-- ★ A call through a var whose root is a deferred fn returns that fn's value (realizing it). -/
theorem deferred_call_returns_body (s : Deferred.St) (v : String) (d r : Nat)
    (h : s.root v = .deferred d r) : (Deferred.stepJank s (.call v)).2 = some r :=
  Deferred.realize_own_root_same_result s v d r h

/-- ★ With `--eager`, every step equals Clojure's. -/
theorem eager_agrees_clojure (s : Deferred.St) (op : Deferred.Op) :
    Deferred.stepEager s op = Deferred.stepClj s op := rfl


/-- `GetOperator` returns a base's member `operator*` that `D`'s own `operator*` hides in C++. -/
theorem getOperator_includes_hidden_base_member :
    ((Operators.getOperator Operators.world .star [.lref Operators.tD, .b .int]).map (·.id)).contains
      "int B::operator*(int) const" = true := by decide +kernel

/-- C++'s member lookup in `D` finds only `D::operator*`. -/
theorem cpp_member_lookup_hides_base :
    ((Operators.memberLookup Operators.world .star "D").toOption.map (·.map (·.id))) = some ["int D::operator*(double) const"] := by
  decide +kernel

/-- `GetOperator` follows `pn`'s using-directive to `px::operator|`; ADL would not. -/
theorem getOperator_follows_using_directive :
    ((Operators.getOperator Operators.world .pipe [.lref Operators.tP, .lref Operators.tP]).map (·.id)).contains
      "int px::operator|(pn::P const&, pn::P const&)" = true := by decide +kernel


def names : List String :=
  ["★ jank_primitive_operands_builtin_only", "★ jank_primitive_operand_unary_builtin_only",
   "★ jank_ctor_specialization_is_defaults", "★ deferred_call_returns_body", "★ eager_agrees_clojure",
   "Deferred.old_object_rebinds_var", "Deferred.clojure_keeps_new_root", "Deferred.realize_own_root_same_result", "getOperator_includes_hidden_base_member",
   "cpp_member_lookup_hides_base", "getOperator_follows_using_directive", "Worlds4.delete_cxx_new_crashes"]

end Jank.R4.Interop.Theorems
