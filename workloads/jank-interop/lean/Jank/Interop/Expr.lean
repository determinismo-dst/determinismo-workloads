import Jank.Interop.CppInterop

/-!
# The interop expressions (`include/cpp/jank/analyze/expr/cpp_*.hpp`, `src/.../expr/cpp_*.cpp`)

The analyzer agent's `Jank/Analyzer/Expr.lean` replicates the whole expression tree with an arena
and opaque `CppType` spellings; it is imported here for its enums (`ExprPosition`, `ExprKind`,
`CppValueKind`, `ConversionPolicy`, `LoopKind`) and for `Obj`. The interop analysis needs the
structure of C++ types (`CType`), so this file keeps its own value tree of the expressions the
interop code builds and inspects, with the same fields as the C++ structs. `IExpr.mk` carries the
base `expression` fields (position, needs_box, form); `IData` the struct's own.

Mutation: where the C++ mutates an expression in place (`propagate_position`, `value->type = ...`
in build_cpp_call, `val->val_kind = ...` in analyze_cpp_member_access), the replica returns the
updated value.
-/

namespace Jank.Interop

open Jank.Analyzer (Obj ExprPosition ExprKind CppValueKind ConversionPolicy LoopKind)
open CppInterop (Scope)

/-- `analyze::local_binding` as the interop code reads it. -/
structure Binding where
  name : String
  type : CType
  isLoopVariable : Bool := false
  needsBox : Bool := true
  deriving Repr, BEq, Inhabited

mutual
  /-- `analyze::expression` with its struct's fields. -/
  inductive IExpr where
    | mk (position : ExprPosition) (needsBox : Bool) (form : Obj) (data : IData)
  inductive IData where
    | primitiveLiteral (data : Obj)
    | cppLiteral (data : Obj)
    /-- `expr::local_reference`: the binding and (for `resolved_expression`) its value. -/
    | localReference (b : Binding) (value : Option IExpr)
    | varDeref (name : String)
    /-- `expr::call` of a jank function (a dynamic call, `object_ref` result). -/
    | call (fnName : String) (args : List IExpr)
    | if_ (type : CType) (cond then_ : IExpr) (else_ : Option IExpr)
    | let_ (pairs : List (Binding × IExpr)) (body : List IExpr) (loopKind : LoopKind)
    | recur (args : List IExpr)
    | cppRaw (code : String)
    | cppType (sym : String) (type : CType)
    | cppValue (sym : String) (type : CType) (scope : Scope) (kind : CppValueKind)
    | cppConversion (type convType : CType) (value : IExpr) (policy : ConversionPolicy)
    | cppUnsafeCast (type : CType) (value : IExpr)
    | cppCall (type : CType) (source : IExpr) (args : List IExpr) (functionCode : String)
    | cppConstructorCall (type : CType) (fn : Option FnDecl) (args : List IExpr) (isAggregate : Bool)
    | cppMemberCall (parentType : CType) (fn : FnDecl) (args : List IExpr)
    | cppMemberAccess (type : CType) (scope : FieldDecl) (name : String) (obj : IExpr)
    | cppBuiltinOperatorCall (op : Cxx.Op) (args : List IExpr) (type : CType)
    | cppBox (value : IExpr)
    | cppUnbox (type : CType) (value : IExpr)
    | cppNew (type : CType) (value : IExpr)
    | cppDelete (value : IExpr)
end

instance : Inhabited IExpr := ⟨.mk .value true .nil (.cppRaw "")⟩

namespace IExpr

def position : IExpr → ExprPosition | .mk p _ _ _ => p
def needsBox : IExpr → Bool | .mk _ n _ _ => n
def form : IExpr → Obj | .mk _ _ f _ => f
def data : IExpr → IData | .mk _ _ _ d => d
def withData (e : IExpr) (d : IData) : IExpr := .mk e.position e.needsBox e.form d

/-- `expression::kind`. -/
def kind (e : IExpr) : ExprKind :=
  match e.data with
  | .primitiveLiteral _ => .primitiveLiteral
  | .cppLiteral _ => .cppLiteral
  | .localReference .. => .localReference
  | .varDeref _ => .varDeref
  | .call .. => .call
  | .if_ .. => .if_
  | .let_ .. => .let
  | .recur _ => .recur
  | .cppRaw _ => .cppRaw
  | .cppType .. => .cppType
  | .cppValue .. => .cppValue
  | .cppConversion .. => .cppConversion
  | .cppUnsafeCast .. => .cppUnsafeCast
  | .cppCall .. => .cppCall
  | .cppConstructorCall .. => .cppConstructorCall
  | .cppMemberCall .. => .cppMemberCall
  | .cppMemberAccess .. => .cppMemberAccess
  | .cppBuiltinOperatorCall .. => .cppBuiltinOperatorCall
  | .cppBox _ => .cppBox
  | .cppUnbox .. => .cppUnbox
  | .cppNew .. => .cppNew
  | .cppDelete _ => .cppDelete

/-- `expression::propagate_position` (expression.cpp:40), overridden identically by every cpp_*
struct that has one (cpp_box.cpp:19, cpp_call.cpp:36, ...). -/
def propagatePosition (e : IExpr) (pos : ExprPosition) : IExpr := .mk pos e.needsBox e.form e.data

end IExpr

/-! ## The structs' constructors (expr/cpp_*.cpp) -/

/-- cpp_raw.cpp:cpp_raw:6. -/
def mkCppRaw (pos : ExprPosition) (needsBox : Bool) (form : Obj) (code : String) : IExpr :=
  .mk pos needsBox form (.cppRaw code)
/-- cpp_type.cpp:cpp_type:6: the base `form` is the symbol. -/
def mkCppType (pos : ExprPosition) (needsBox : Bool) (sym : String) (type : CType) : IExpr :=
  .mk pos needsBox (Obj.s sym) (.cppType sym type)
/-- cpp_value.cpp:cpp_value:6 (the symbol is the form) and :21 (an explicit form; the struct's own
`form` member is still set to the symbol). -/
def mkCppValue (pos : ExprPosition) (needsBox : Bool) (form : Obj) (sym : String) (type : CType)
    (scope : Scope) (kind : CppValueKind) : IExpr :=
  .mk pos needsBox form (.cppValue sym type scope kind)
/-- cpp_literal.cpp:cpp_literal:6. -/
def mkCppLiteral (pos : ExprPosition) (needsBox : Bool) (form data : Obj) : IExpr :=
  .mk pos needsBox form (.cppLiteral data)
/-- cpp_conversion.cpp:cpp_conversion:6. -/
def mkCppConversion (pos : ExprPosition) (needsBox : Bool) (form : Obj) (type convType : CType)
    (policy : ConversionPolicy) (value : IExpr) : IExpr :=
  .mk pos needsBox form (.cppConversion type convType value policy)
/-- cpp_unsafe_cast.cpp:cpp_unsafe_cast:6. -/
def mkCppUnsafeCast (pos : ExprPosition) (needsBox : Bool) (form : Obj) (type : CType) (value : IExpr) : IExpr :=
  .mk pos needsBox form (.cppUnsafeCast type value)
/-- cpp_call.cpp:cpp_call:6 and :21 (with `function_code`). -/
def mkCppCall (pos : ExprPosition) (needsBox : Bool) (form : Obj) (type : CType) (source : IExpr)
    (args : List IExpr) (functionCode : String := "") : IExpr :=
  .mk pos needsBox form (.cppCall type source args functionCode)
/-- cpp_constructor_call.cpp:cpp_constructor_call:10. -/
def mkCppConstructorCall (pos : ExprPosition) (needsBox : Bool) (form : Obj) (type : CType)
    (fn : Option FnDecl) (isAggregate : Bool) (args : List IExpr) : IExpr :=
  .mk pos needsBox form (.cppConstructorCall type fn args isAggregate)
/-- cpp_member_call.cpp:cpp_member_call:6: the constructor's `type` parameter is stored in
`parent_type`. -/
def mkCppMemberCall (pos : ExprPosition) (needsBox : Bool) (form : Obj) (type : CType) (fn : FnDecl)
    (args : List IExpr) : IExpr :=
  .mk pos needsBox form (.cppMemberCall type fn args)
/-- cpp_member_access.cpp:cpp_member_access:6. -/
def mkCppMemberAccess (pos : ExprPosition) (needsBox : Bool) (form : Obj) (type : CType)
    (scope : FieldDecl) (name : String) (obj : IExpr) : IExpr :=
  .mk pos needsBox form (.cppMemberAccess type scope name obj)
/-- cpp_builtin_operator_call.cpp:cpp_builtin_operator_call:6. -/
def mkCppBuiltinOperatorCall (pos : ExprPosition) (needsBox : Bool) (form : Obj) (op : Cxx.Op)
    (args : List IExpr) (type : CType) : IExpr :=
  .mk pos needsBox form (.cppBuiltinOperatorCall op args type)
/-- cpp_box.cpp:cpp_box:6. -/
def mkCppBox (pos : ExprPosition) (needsBox : Bool) (form : Obj) (value : IExpr) : IExpr :=
  .mk pos needsBox form (.cppBox value)
/-- cpp_unbox.cpp:cpp_unbox:6. -/
def mkCppUnbox (pos : ExprPosition) (needsBox : Bool) (form : Obj) (type : CType) (value : IExpr) : IExpr :=
  .mk pos needsBox form (.cppUnbox type value)
/-- cpp_new.cpp:cpp_new:6. -/
def mkCppNew (pos : ExprPosition) (needsBox : Bool) (form : Obj) (type : CType) (value : IExpr) : IExpr :=
  .mk pos needsBox form (.cppNew type value)
/-- cpp_delete.cpp:cpp_delete:6. -/
def mkCppDelete (pos : ExprPosition) (needsBox : Bool) (form : Obj) (value : IExpr) : IExpr :=
  .mk pos needsBox form (.cppDelete value)

/-- `walk` (cpp_box.cpp:30, cpp_call.cpp:57, ...): the children each struct visits, in order. -/
def IExpr.children (e : IExpr) : List IExpr :=
  match e.data with
  | .cppBox v | .cppUnbox _ v | .cppNew _ v | .cppDelete v | .cppUnsafeCast _ v
  | .cppConversion _ _ v _ => [v]
  | .cppCall _ _ args _ | .cppConstructorCall _ _ args _ | .cppMemberCall _ _ args
  | .cppBuiltinOperatorCall _ args _ => args
  | .cppMemberAccess _ _ _ o => [o]
  | _ => []

/-- `to_runtime_data` (cpp_*.cpp): the base map merged with the struct's entries. Most interop
structs add nothing ("TODO: Fill in."); cpp_literal adds `data`, cpp_call `source`/`arg_exprs`,
cpp_builtin_operator_call `op`/`arg_exprs`. Modeled as the keys added. -/
def IExpr.runtimeDataKeys (e : IExpr) : List String :=
  ["kind", "position", "needs_box"] ++
  match e.data with
  | .cppLiteral _ => ["data"]
  | .cppCall .. => ["source", "arg_exprs"]
  | .cppBuiltinOperatorCall .. => ["op", "arg_exprs"]
  | _ => []

end Jank.Interop
