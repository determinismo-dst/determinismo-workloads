import Jank.R5.Interop.World5

/-!
# Round 5 interop theorems (no sorry, no native_decide; ★ = for every input)
-/

namespace Jank.R5.Interop.Theorems5

open Jank.Interop
open Jank.R3.Interop
open Jank.R3.Interop.Clang
open Jank.R5.Interop.Ops5

/-! ## V-F1/F2: a class temporary is an lvalue to jank's overload resolution -/

/-- ★ For every class and every constructor-call operand of it, jank gives `BestOverloadMatch` an
lvalue (processor.cpp 565-572 makes the argument type `T&`), where C++ has a prvalue. -/
theorem class_temporary_is_lvalue (o : Ops5.Operand) (n : String) (ht : o.type = .record n)
    (hk : o.kind = .temp) : jankArgVK {} o = .lvalue ∧ o.cxxVK = .prvalue := by
  simp [jankArgVK, Ops5.Operand.jankType, Ops5.Operand.cxxVK, hk, ht, isLValueReferenceType, isPointerType,
    isBuiltinType, view]

/-- ★ For every type `A` (class or builtin) and template parameter, the type deduced for a
forwarding reference `T&&` is `A&` from an lvalue and `A` otherwise ([temp.deduct.call]/3). -/
theorem forwarding_deduction_record (n : String) (vk : VK) (i : Nat) :
    deduceOne (.record n) vk (.fwd i) =
      some (i, if vk == .lvalue then .lref (.record n) else .record n) := rfl

theorem forwarding_deduction_builtin (k : Builtin) (vk : VK) (i : Nat) :
    deduceOne (.b k) vk (.fwd i) = some (i, if vk == .lvalue then .lref (.b k) else .b k) := rfl

/-- ★ So for every class temporary, jank deduces `T = A&` where C++ deduces `T = A` (V-F2). -/
theorem temporary_forwarding_deduces_lref (o : Ops5.Operand) (n : String) (i : Nat)
    (ht : o.type = .record n) (hk : o.kind = .temp) :
    deduceOne o.type (jankArgVK {} o) (.fwd i) = some (i, .lref (.record n)) ∧
    deduceOne o.type o.cxxVK (.fwd i) = some (i, .record n) := by
  obtain ⟨h1, h2⟩ := class_temporary_is_lvalue o n ht hk
  rw [h1, h2, ht]
  exact ⟨rfl, rfl⟩

/-! ## V-F3/F4: member calls pass every argument as an lvalue -/

/-- ★ For every parameter type, `cpp_member_call`'s emitted argument is an lvalue
(cpp_processor.cpp 1730-1775), while `cpp_call` moves into an rvalue-reference parameter. -/
theorem member_call_args_lvalue (prm : CType) : emittedVK {} true prm = .lvalue := by
  simp [emittedVK]

theorem nonmember_call_moves (u : CType) : emittedVK {} false (.rref u) = .xvalue := by
  simp [emittedVK, isRValueReferenceType, view]

/-! ## V-F5: a named builtin local is a prvalue to jank's overload resolution -/

/-- ★ For every builtin type, a `let`-bound local of it is a prvalue to `BestOverloadMatch` (its
binding type is the init's type, processor.cpp analyze_let 2414-2421; CppInterOp.cpp 2022-2026), where C++ has an
lvalue (a named variable). -/
theorem named_builtin_local_is_prvalue (o : Ops5.Operand) (k : Builtin) (ht : o.type = .b k)
    (hk : o.kind = .named) : jankArgVK {} o = .prvalue ∧ o.cxxVK = .lvalue := by
  simp [jankArgVK, Ops5.Operand.jankType, Ops5.Operand.cxxVK, hk, ht, isLValueReferenceType, isPointerType,
    isBuiltinType, view]

/-! ## V-F7: GetOperator drops namespace-scope using-declarations -/

theorem usingTargets_append (w : W5) (extra : List (String × String))
    (h : ∀ e ∈ extra, e.1 ≠ "") :
    usingTargets { w with usingNs := w.usingNs ++ extra } "" = usingTargets w "" := by
  have hf : extra.filter (fun e => e.1 == "") = [] := by
    rw [List.filter_eq_nil_iff]
    intro e he
    simpa using h e he
  simp only [usingTargets, List.filter_append, hf, List.append_nil]
  rfl

/-- ★ For every world, operator and argument list: adding using-declarations to namespaces other
than the global one never changes what jank's `GetOperator` finds (CppInterOp.cpp 7022-7031 keep
only `FunctionTemplateDecl`/`FunctionDecl`; the TU lookup, 6999-7006, is the only place a using
declaration is resolved). C++'s argument-dependent lookup finds them ([basic.lookup.argdep]/4). -/
theorem jank_getOperator_ignores_namespace_using (w : W5) (op : Cxx.Op) (args : List CType)
    (extra : List (String × String)) (h : ∀ e ∈ extra, e.1 ≠ "") :
    jankGetOperator { w with usingNs := w.usingNs ++ extra } {} op args = jankGetOperator w {} op args := by
  simp only [jankGetOperator, usingTargets_append w extra h]
  rfl

/-! ## V-F8: a member re-exported by a using-declaration -/

/-- ★ For every derived class `d` and base `b ≠ d`: the object conversion of a member whose acting
context is `b` (what jank gives a base member it finds through the base, `AddMethodCandidate`
SemaOverload.cpp 7914-7917 with the base method as the found decl) is never an exact match. -/
theorem norm_record (d : String) : (nonRef (CType.record d)).canonical.unqual = .record d := rfl

theorem base_acting_context_not_exact (w : W5) (d b : String) (hne : d ≠ b) (s : SCS)
    (h : objICS w (.record d) b = .std s) : s.rank ≠ .exact := by
  unfold objICS at h
  rw [norm_record] at h
  dsimp only at h
  have hb : (d == b) = false := by simpa using hne
  rw [hb] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  split at h
  · injection h with h
    rw [← h]
    decide
  · cases h

/-- ★ … while the acting context C++ gives a using-declared member is the derived class itself
([over.match.funcs]/4): an exact (identity) object conversion. -/
theorem using_member_acting_context_exact (w : W5) (d : String) :
    objICS w (.record d) d = .std { rank := .exact, identity := true } := by
  unfold objICS
  rw [norm_record]
  simp

/-! ## Templates and the arity filter -/

/-- ★ `GetOperatorArity` of a template is `~0` (CppInterOp.cpp 6973): every operator template
passes the arity filter at every call arity. -/
theorem templates_pass_arity (f : Fn) (n : Nat) (h : f.tparams > 0) : arityOk f n = true := by
  simp [arityOk, h]

def names : List String :=
  ["★ class_temporary_is_lvalue", "★ forwarding_deduction_record", "★ forwarding_deduction_builtin",
   "★ temporary_forwarding_deduces_lref", "★ member_call_args_lvalue", "nonmember_call_moves",
   "★ named_builtin_local_is_prvalue", "usingTargets_append", "norm_record",
   "★ jank_getOperator_ignores_namespace_using", "★ base_acting_context_not_exact",
   "★ using_member_acting_context_exact", "★ templates_pass_arity"]

end Jank.R5.Interop.Theorems5
