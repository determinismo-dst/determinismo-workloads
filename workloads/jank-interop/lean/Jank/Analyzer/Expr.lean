/-!
# The analyzer's expression tree, replicated

Lean replica of `include/cpp/jank/analyze/expression.hpp`, `local_frame.hpp` and every
`include/cpp/jank/analyze/expr/*.hpp` (paths under `upstream/compiler+runtime/`), plus `Obj`, the
runtime objects the analyzer consumes (forms) and embeds (literals).

Layout. The C++ tree is a graph of `jtl::ref`/`jtl::ptr` pointers to heap objects that are mutated
after construction (`propagate_position`, `force_boxed`, a binding's usage flags, a loop's
`loop_kind`, a function context's flags). The replica keeps that pointer semantics: every heap
object lives in an `Arena` and is named by its index.

- `ExprId`    = `expression_ref` / `expression_ptr` (`jtl::ref<expression>`), index into `Arena.exprs`
- `FrameId`   = `local_frame_ptr`, index into `Arena.frames`
- `BindingId` = `local_binding_ref` / `local_binding_ptr`, index into `Arena.bindings` (a binding
  stored in a frame's `locals` deque, in a `local_capture`, or a stack temporary)
- `FnCtxId`   = `function_context_ref`, index into `Arena.fnCtxs`

`std::unordered_map`s are association lists in insertion order (their iteration order is
unspecified in C++; see the analyzer report's assumptions).
-/

namespace Jank.Analyzer

/-- `runtime::object_type` (`include/cpp/jank/runtime/object.hpp:16`), all values in order. -/
inductive ObjectType where
  | nil | boolean | integer | smallInteger | bigInteger | bigDecimal | real | smallReal | ratio
  | persistentString | persistentStringSequence
  | keyword | symbol | character
  | persistentList
  | persistentVector | transientVector | persistentVectorSequence
  | persistentArrayMap | transientArrayMap | persistentArrayMapSequence
  | persistentHashMap | transientHashMap | persistentHashMapSequence
  | persistentSortedMap | transientSortedMap | persistentSortedMapSequence
  | persistentHashSet | transientHashSet | persistentHashSetSequence
  | persistentSortedSet | transientSortedSet | persistentSortedSetSequence
  | cons | lazySequence | range | integerRange | repeat | iterator | nativeArraySequence
  | nativeVectorSequence
  | chunkBuffer | arrayChunk | chunkedCons
  | nativeFunctionWrapper | jitFunction | jitVariadicFunction | jitClosure | jitVariadicClosure
  | deferredCppFunction | multiFunction
  | nativePointerWrapper
  | atom | volatile_ | reduced | delay | future | promise | ns
  | var | varThreadBinding | varUnboundRoot
  | taggedLiteral
  | rePattern | reMatcher | uuid | inst
  | opaqueBox
  | array
  | readerConditional
  | exceptionInfo
  deriving Repr, BEq, DecidableEq, Inhabited, Hashable

/-- A runtime object (`runtime::object_ref`) as the analyzer sees it: forms coming from the reader
or from macros, and the data of literals. Metadata is `jtl::option<object_ref>` / `lazy_meta`
(`none` = no meta). Numbers keep jank's representations: `smallInteger` is the tagged `i32`
(`make_box` of an integral in `[INT32_MIN, INT32_MAX]`, make_box.hpp:95), `integer` the boxed
`i64`; `smallReal` the tagged `f64` (`make_box` of a floating value), `real` the boxed `f64`;
doubles are kept as their IEEE bits. -/
inductive Obj where
  | nil
  | boolean (b : Bool)
  /-- `obj::integer`: a boxed i64. -/
  | integer (v : BitVec 64)
  /-- `obj::small_integer`: a tagged i32. -/
  | smallInteger (v : BitVec 32)
  /-- `obj::big_integer` (boost cpp_int). -/
  | bigInteger (v : Int)
  /-- `obj::big_decimal`: `unscaled * 10^-scale`. -/
  | bigDecimal (unscaled : Int) (scale : Int)
  /-- `obj::real`: a boxed f64, by its bits. -/
  | real (bits : UInt64)
  /-- `obj::small_real`: a tagged f64, by its bits. -/
  | smallReal (bits : UInt64)
  /-- `obj::ratio`: numerator / denominator (`native_big_integer`s). -/
  | ratio (num den : Int)
  | persistentString (s : String)
  | keyword (ns name : String)
  | symbol (metadata : Option Obj) (ns name : String)
  /-- `obj::character`: its data is a string (UTF-8 of the character). -/
  | character (data : String)
  | persistentList (metadata : Option Obj) (xs : List Obj)
  | persistentVector (metadata : Option Obj) (xs : List Obj)
  | persistentArrayMap (metadata : Option Obj) (kvs : List (Obj × Obj))
  | persistentHashMap (metadata : Option Obj) (kvs : List (Obj × Obj))
  | persistentSortedMap (metadata : Option Obj) (kvs : List (Obj × Obj))
  | persistentHashSet (metadata : Option Obj) (xs : List Obj)
  | persistentSortedSet (metadata : Option Obj) (xs : List Obj)
  /-- `obj::cons` (syntax-quote and macros build these). -/
  | cons (metadata : Option Obj) (first rest : Obj)
  /-- A realized `obj::lazy_sequence` over `xs` (meta allowed). -/
  | lazySequence (metadata : Option Obj) (xs : List Obj)
  /-- Any other sequence type (`range`, vector sequences, chunked conses, ...): its type and
  elements. -/
  | seqOf (type : ObjectType) (xs : List Obj)
  /-- A `runtime::var`, by its namespace and name. -/
  | var (ns name : String)
  /-- Any other object with identity (functions, atoms, regexes, namespaces, ...). -/
  | opaque (type : ObjectType) (id : Nat)
  deriving Repr, BEq, Inhabited

/-- `object_ref::get_type()` / `object::type`. -/
def Obj.type : Obj → ObjectType
  | .nil => .nil
  | .boolean _ => .boolean
  | .integer _ => .integer
  | .smallInteger _ => .smallInteger
  | .bigInteger _ => .bigInteger
  | .bigDecimal _ _ => .bigDecimal
  | .real _ => .real
  | .smallReal _ => .smallReal
  | .ratio _ _ => .ratio
  | .persistentString _ => .persistentString
  | .keyword _ _ => .keyword
  | .symbol _ _ _ => .symbol
  | .character _ => .character
  | .persistentList _ _ => .persistentList
  | .persistentVector _ _ => .persistentVector
  | .persistentArrayMap _ _ => .persistentArrayMap
  | .persistentHashMap _ _ => .persistentHashMap
  | .persistentSortedMap _ _ => .persistentSortedMap
  | .persistentHashSet _ _ => .persistentHashSet
  | .persistentSortedSet _ _ => .persistentSortedSet
  | .cons _ _ _ => .cons
  | .lazySequence _ _ => .lazySequence
  | .seqOf t _ => t
  | .var _ _ => .var
  | .opaque t _ => t

/-- A symbol with no meta. -/
def Obj.sym (ns name : String) : Obj := .symbol none ns name
/-- An unqualified symbol with no meta. -/
def Obj.s (name : String) : Obj := .symbol none "" name
/-- A list with no meta. -/
def Obj.l (xs : List Obj) : Obj := .persistentList none xs
/-- A vector with no meta. -/
def Obj.v (xs : List Obj) : Obj := .persistentVector none xs
/-- `make_box(i64)` (make_box.hpp:91): tagged `small_integer` when it fits i32, else `integer`. -/
def Obj.ofInt (i : Int) : Obj :=
  if -2147483648 ≤ i ∧ i ≤ 2147483647 then .smallInteger (BitVec.ofInt 32 i)
  else .integer (BitVec.ofInt 64 i)

/-- `jtl::ptr<void>` handles from Clang/CppInterOp: a type (`QualType` pointer), a scope or a
function declaration. Opaque to the analyzer except for identity; `named` carries the spelling
(e.g. `"jank::runtime::object_ref"`). -/
inductive CppType where
  | null
  | named (spelling : String)
  deriving Repr, BEq, DecidableEq, Inhabited, Hashable

/-- `cpp_util::untyped_object_ref_type()`: the type `jank::runtime::object_ref`. -/
def CppType.untypedObjectRef : CppType := .named "jank::runtime::object_ref"

/-- `read::source_position` (read/source.hpp:10). -/
structure SourcePosition where
  offset : Nat := 0
  line : Nat := 1
  col : Nat := 1
  deriving Repr, BEq, Inhabited

/-- `read::source` (read/source.hpp:24). -/
structure ReadSource where
  file : String := "NO_SOURCE_PATH"
  module : String := ""
  start : SourcePosition := {}
  «end» : SourcePosition := {}
  macroExpansion : Obj := .nil
  deriving Repr, BEq, Inhabited

/-- A var as an expression refers to it (`runtime::var_ref`): interned in a namespace by name. -/
structure VarRef where
  ns : String
  name : String
  deriving Repr, BEq, DecidableEq, Inhabited, Hashable

abbrev ExprId := Nat
abbrev FrameId := Nat
abbrev BindingId := Nat
abbrev FnCtxId := Nat

/-- `expression_position` (expression.hpp:13). -/
inductive ExprPosition where
  | value | call | statement | tail | type
  deriving Repr, BEq, DecidableEq, Inhabited

/-- `expression_kind` (expression.hpp:46). `cpp_value_min = cpp_raw`, `cpp_value_max = cpp_delete`. -/
inductive ExprKind where
  | uninitialized | def | varDeref | varRef | call | primitiveLiteral | list | vector | map | set
  | function | recur | recursionReference | namedRecursion | localReference | let | letfn | do_
  | if_ | throw_ | try_ | case_
  | cppRaw | cppType | cppValue | cppLiteral | cppConversion | cppUnsafeCast | cppCall
  | cppConstructorCall | cppMemberCall | cppMemberAccess | cppBuiltinOperatorCall | cppBox
  | cppUnbox | cppNew | cppDelete
  deriving Repr, BEq, DecidableEq, Inhabited

/-- `cpp_value_min <= kind <= cpp_value_max`: the interop kinds. -/
def ExprKind.isCpp : ExprKind → Bool
  | .cppRaw | .cppType | .cppValue | .cppLiteral | .cppConversion | .cppUnsafeCast | .cppCall
  | .cppConstructorCall | .cppMemberCall | .cppMemberAccess | .cppBuiltinOperatorCall | .cppBox
  | .cppUnbox | .cppNew | .cppDelete => true
  | _ => false

/-- `expr::let::loop_kind` (let.hpp). -/
inductive LoopKind where
  | normal | loopWithRecur | loopWithoutRecur
  deriving Repr, BEq, DecidableEq, Inhabited

/-- `analyze::conversion_policy` (cpp_conversion.hpp). -/
inductive ConversionPolicy where
  | intoObject | fromObject
  deriving Repr, BEq, DecidableEq, Inhabited

/-- `expr::cpp_value::value_kind` (cpp_value.hpp). -/
inductive CppValueKind where
  | null | boolTrue | boolFalse | constructor | variable | enumConstant | function
  | memberAccess | memberCall | operatorCall
  deriving Repr, BEq, DecidableEq, Inhabited

/-- `expr::parameter` (function.hpp). -/
structure Parameter where
  name : Obj
  type : CppType
  deriving Repr, BEq, Inhabited

/-- `expr::function_arity` (function.hpp). `body` is a `do_ref`. -/
structure FunctionArity where
  params : List Parameter
  body : ExprId
  frame : Option FrameId
  fnCtx : FnCtxId
  deriving Repr, BEq, Inhabited

/-- `expr::arity_key` (function.hpp). -/
structure ArityKey where
  paramCount : UInt64
  isVariadic : Bool
  deriving Repr, BEq, Inhabited

/-- `expr::function_context` (function.hpp). `fn` is a `jtl::ptr<function>` (null until set). -/
structure FunctionContext where
  fn : Option ExprId := none
  name : String := ""
  uniqueName : String := ""
  paramCount : UInt64 := 0
  isVariadic : Bool := false
  isRecurRecursive : Bool := false
  isNamedRecursive : Bool := false
  deriving Repr, BEq, Inhabited

/-- `expr::catch_` (try.hpp). `body` is a `do_ref`; `type` is the void type for a catch-all. -/
structure Catch where
  sym : Obj
  type : CppType
  body : ExprId
  deriving Repr, BEq, Inhabited

/-- The fields each expression struct adds to `expression`, one constructor per struct. A field
that the C++ struct redeclares (`call::form`, `cpp_value::form`) is kept beside the base `form`. -/
inductive ExprData where
  | uninitialized
  /-- `expr::def`: `name` (a symbol), `value` (`jtl::option<expression_ref>`). -/
  | def (name : Obj) (value : Option ExprId)
  /-- `expr::var_deref`. -/
  | varDeref (qualifiedName : Obj) (var : VarRef)
  /-- `expr::var_ref`. -/
  | varRef (qualifiedName : Obj) (var : VarRef)
  /-- `expr::call`: `source_expr`, `arg_exprs`, and its own `form` (a persistent list). -/
  | call (sourceExpr : ExprId) (argExprs : List ExprId) (form : Obj)
  /-- `expr::primitive_literal`. -/
  | primitiveLiteral (data : Obj)
  | list (dataExprs : List ExprId) (metadata : Option ExprId)
  | vector (dataExprs : List ExprId) (metadata : Option ExprId)
  | map (dataExprs : List (ExprId × ExprId)) (metadata : Option ExprId)
  | set (dataExprs : List ExprId) (metadata : Option ExprId)
  /-- `expr::function`: `meta` is a `persistent_hash_map_ref` (an `Obj`). -/
  | function (name uniqueName : String) (arities : List FunctionArity) (metadata : Obj)
      (isVariadic : Bool)
  /-- `expr::recur`: `args` (a persistent list), `loop_target` (`jtl::option<let_ref>`). -/
  | recur (args : Obj) (argExprs : List ExprId) (opEqualExprs : List ExprId)
      (loopTarget : Option ExprId)
  /-- `expr::recursion_reference`. -/
  | recursionReference (fnCtx : FnCtxId)
  /-- `expr::named_recursion`: `recursion_ref` is held by value in C++; here it is an arena
  entry (a `recursionReference`) that nothing else points to. -/
  | namedRecursion (recursionRef : ExprId) (args : Obj) (argExprs : List ExprId)
  /-- `expr::local_reference`: `binding` is a `local_binding_ptr`. -/
  | localReference (name : Obj) (binding : BindingId)
  /-- `expr::let`: `pairs` of `(local_binding_ref, expression_ref)`, `body` a `do_ref`. -/
  | «let» (pairs : List (BindingId × ExprId)) (body : ExprId) (loopKind : LoopKind)
  /-- `expr::letfn`: `pairs` of `(local_binding_ref, function_ref)`. -/
  | letfn (pairs : List (BindingId × ExprId)) (body : ExprId)
  /-- `expr::do_`: `values`. -/
  | do_ (values : List ExprId)
  /-- `expr::if_`. -/
  | if_ (type : CppType) (condition then_ : ExprId) (else_ : Option ExprId)
  /-- `expr::throw_`: `value` absent = rethrow. -/
  | throw_ (value : Option ExprId)
  /-- `expr::try_`: `body`, `catch_bodies`, `finally_body` (all `do_ref`). -/
  | try_ (body : ExprId) (catchBodies : List Catch) (finallyBody : Option ExprId)
  /-- `expr::case_`: `shift`, `mask`, `keys` are `i64`. -/
  | case_ (valueExpr : ExprId) (shift mask : BitVec 64) (defaultExpr : ExprId)
      (keys : List (BitVec 64)) (exprs : List ExprId)
  /-- `expr::cpp_raw`. -/
  | cppRaw (code : String)
  /-- `expr::cpp_type`. -/
  | cppType (sym : Obj) (type : CppType)
  /-- `expr::cpp_value`: its own `form`, `sym`, `type`, `scope`, `val_kind`. -/
  | cppValue (form : Obj) (sym : Obj) (type scope : CppType) (valKind : CppValueKind)
  /-- `expr::cpp_literal`. -/
  | cppLiteral (data : Obj)
  /-- `expr::cpp_conversion`. -/
  | cppConversion (type conversionType : CppType) (valueExpr : ExprId) (policy : ConversionPolicy)
  /-- `expr::cpp_unsafe_cast`. -/
  | cppUnsafeCast (type : CppType) (valueExpr : ExprId)
  /-- `expr::cpp_call`. -/
  | cppCall (type : CppType) (sourceExpr : ExprId) (argExprs : List ExprId) (functionCode : String)
  /-- `expr::cpp_constructor_call`: `fn` null for builtins and aggregates. -/
  | cppConstructorCall (type fn : CppType) (argExprs : List ExprId) (isAggregate : Bool)
  /-- `expr::cpp_member_call`. -/
  | cppMemberCall (parentType fn : CppType) (argExprs : List ExprId)
  /-- `expr::cpp_member_access`. -/
  | cppMemberAccess (type scope : CppType) (name : String) (objExpr : ExprId)
  /-- `expr::cpp_builtin_operator_call`: `op` is a `Cpp::Operator` (`int`). -/
  | cppBuiltinOperatorCall (op : BitVec 32) (argExprs : List ExprId) (type : CppType)
  /-- `expr::cpp_box`. -/
  | cppBox (valueExpr : ExprId) (source : ReadSource)
  /-- `expr::cpp_unbox`. -/
  | cppUnbox (type : CppType) (valueExpr : ExprId) (source : ReadSource)
  /-- `expr::cpp_new`. -/
  | cppNew (type : CppType) (valueExpr : ExprId)
  /-- `expr::cpp_delete`. -/
  | cppDelete (valueExpr : ExprId)
  deriving Repr, BEq, Inhabited

/-- The kind each struct passes to `expression{ expr_kind, ... }`. -/
def ExprData.kind : ExprData → ExprKind
  | .uninitialized => .uninitialized
  | .def .. => .def
  | .varDeref .. => .varDeref
  | .varRef .. => .varRef
  | .call .. => .call
  | .primitiveLiteral .. => .primitiveLiteral
  | .list .. => .list
  | .vector .. => .vector
  | .map .. => .map
  | .set .. => .set
  | .function .. => .function
  | .recur .. => .recur
  | .recursionReference .. => .recursionReference
  | .namedRecursion .. => .namedRecursion
  | .localReference .. => .localReference
  | .let .. => .let
  | .letfn .. => .letfn
  | .do_ .. => .do_
  | .if_ .. => .if_
  | .throw_ .. => .throw_
  | .try_ .. => .try_
  | .case_ .. => .case_
  | .cppRaw .. => .cppRaw
  | .cppType .. => .cppType
  | .cppValue .. => .cppValue
  | .cppLiteral .. => .cppLiteral
  | .cppConversion .. => .cppConversion
  | .cppUnsafeCast .. => .cppUnsafeCast
  | .cppCall .. => .cppCall
  | .cppConstructorCall .. => .cppConstructorCall
  | .cppMemberCall .. => .cppMemberCall
  | .cppMemberAccess .. => .cppMemberAccess
  | .cppBuiltinOperatorCall .. => .cppBuiltinOperatorCall
  | .cppBox .. => .cppBox
  | .cppUnbox .. => .cppUnbox
  | .cppNew .. => .cppNew
  | .cppDelete .. => .cppDelete

/-- `analyze::expression` (expression.hpp:180): the common base, with the struct's own fields in
`data`. `frame` is a `local_frame_ptr` (nullable); `needs_box` defaults to true; `form` defaults
to nil. -/
structure Expr where
  kind : ExprKind
  position : ExprPosition := .value
  frame : Option FrameId := none
  needsBox : Bool := true
  form : Obj := .nil
  data : ExprData
  /-- `expr::case_::type` (case.hpp, added in jank 7135b7708; `case_::get_type()` returns it). Kept
  on the base so that `ExprData.case_` keeps its arity; `.null` for every other kind. -/
  caseType : CppType := .null
  deriving Repr, BEq, Inhabited

/-- `local_frame::frame_type` (local_frame.hpp). -/
inductive FrameType where
  | root | fn | «let» | letfn | try_ | catch_ | finally
  deriving Repr, BEq, DecidableEq, Inhabited

/-- `analyze::local_binding` (local_frame.hpp). `alive` is the replica's own flag: false once the
C++ object's storage has ended (a stack temporary whose address escaped), so a later use is a
dangling-pointer read. -/
structure LocalBinding where
  name : Obj
  nativeName : String := ""
  valueExpr : Option ExprId := none
  originatingFrame : Option FrameId := none
  needsBox : Bool := true
  hasBoxedUsage : Bool := false
  hasUnboxedUsage : Bool := false
  isCapture : Bool := false
  isLoopVariable : Bool := false
  type : CppType := CppType.untypedObjectRef
  alive : Bool := true
  deriving Repr, BEq, Inhabited

/-- `analyze::local_capture`: a copy of the binding (owned) and a pointer to the original. -/
structure LocalCapture where
  binding : BindingId
  originatingBinding : BindingId
  deriving Repr, BEq, Inhabited

/-- `analyze::local_frame`. `locals : unordered_map<symbol_ref, deque<local_binding>>` (latest at
the back of each list), `captures : unordered_map<symbol_ref, local_capture>`. Keys compare with
`std::equal_to<symbol_ref>` (ns and name, not meta). -/
structure LocalFrame where
  type : FrameType
  parent : Option FrameId := none
  locals : List (Obj × List BindingId) := []
  captures : List (Obj × LocalCapture) := []
  fnCtx : Option FnCtxId := none
  deriving Repr, BEq, Inhabited

/-- The heap: every object the analyzer allocates. -/
structure Arena where
  exprs : Array Expr := #[]
  frames : Array LocalFrame := #[]
  bindings : Array LocalBinding := #[]
  fnCtxs : Array FunctionContext := #[]
  deriving Repr, Inhabited

/-- A diagnostic (`jank::error_ref`): its `error::kind` name and message. -/
structure AnalyzeError where
  kind : String
  message : String
  form : Obj := .nil
  deriving Repr, BEq, Inhabited

end Jank.Analyzer
-- READY
