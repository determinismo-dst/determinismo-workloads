import Jank.Interop.AnalyzeForms

/-!
# The interop IR and code generation, replicated

- `src/cpp/jank/ir/builder.cpp:530-747`: the `cpp_*` instruction builders (each appends an
  instruction and, in tail position, a `ret`);
- `src/cpp/jank/ir/processor.cpp:857-974`: the lowering of each interop expression;
- `src/cpp/jank/codegen/cpp_processor.cpp`: `lift_constant` (131), `gen_constant` (253), and the
  `gen` of every `cpp_*` instruction (1180-1918), producing the C++ text.

The text is what the JIT compiles; `Eval.lean` gives that text its C++ meaning.
-/

namespace Jank.Interop.Codegen

open Jank.Analyzer (Obj ExprPosition ExprKind CppValueKind ConversionPolicy LoopKind)
open CppUtil

/-! ## Literals -/

/-- `std::to_chars` shortest round-trip text of a finite double, then `.0` appended when it has
neither a `.` nor an `e` (string_builder.cpp:83). Lean's `toString` is not shortest; the
digits here only matter for the literal's C++ type (always `double`). -/
def doubleText (x : Float) : String :=
  if x.isInf then (if x < 0 then "-INFINITY" else "INFINITY")
  else if x.isNaN then "NAN"
  else
    let s := toString x
    if s.contains '.' || s.contains 'e' then s else s ++ ".0"

/-- cpp_processor.cpp:lift_constant:131, the eval target, unboxed: a real's text by
`string_builder` (`INFINITY`, `-INFINITY`, `NAN` for non-finite values), else
`o.to_code_string()` (decimal integers, `true`/`false`, a quoted escaped string). -/
def liftConstantUnboxed (o : Obj) : String :=
  match o with
  | .real b | .smallReal b => doubleText (Float.ofBits b)
  | .smallInteger v => toString v.toInt
  | .integer v => toString v.toInt
  | .boolean b => if b then "true" else "false"
  | .persistentString s => "\"" ++ s ++ "\""
  | _ => "<object>"

/-- cpp_processor.cpp:lift_constant:131, boxed (eval target): a typed `oref` built around the
object's pointer, or `small_integer_ref{ i }` (with `static_cast<jtl::i32>` for `INT32_MIN`, whose
literal "is treated as a long"), or `small_real_ref{ d }`. -/
def liftConstantBoxed (w : World) (o : Obj) : String :=
  let t := getQualifiedTypeName w (literalType o true)
  match o with
  | .nil => "jank::runtime::jank_nil"
  | .smallInteger v =>
    if v.toInt == -2147483648 then s!"{t}\{ static_cast<jtl::i32>({v.toInt}) }" else s!"{t}\{ {v.toInt} }"
  | .smallReal b => s!"{t}\{ {doubleText (Float.ofBits b)} }"
  | _ => s!"{t}\{ _jank_codegen\{ }, (void*)0x... }"

/-- cpp_processor.cpp:gen_constant:253 (module target), the numeric and string cases. -/
def genConstant (o : Obj) (isBoxed : Bool) : String :=
  match o with
  | .boolean b => if !isBoxed then (if b then "true" else "false")
                  else if b then "jank::runtime::jank_true" else "jank::runtime::jank_false"
  | .smallInteger v => if !isBoxed then toString v.toInt else s!"_jank_small_int({v.toInt})"
  | .integer v =>
    let i := v.toInt
    if !isBoxed then toString i
    else if (BitVec.ofInt 32 i).toInt == i then s!"_jank_small_int({i})" else s!"_jank_int({i})"
  | .real b | .smallReal b =>
    if !isBoxed then doubleText (Float.ofBits b) else s!"_jank_small_real({doubleText (Float.ofBits b)})"
  | .persistentString s => if !isBoxed then "\"" ++ s ++ "\"" else if s.isEmpty then "_jank_string()" else s!"_jank_string(\"{s}\")"
  | .nil => "jank::runtime::jank_nil"
  | _ => "<constant>"

/-! ## IR instructions (ir/instruction.hpp, the interop ones) -/

inductive Inst where
  | cppScopeOpen (name : String)
  | cppScopeClose (name scope : String)
  | cppRaw (name : String) (code : String)
  | cppValue (name : String) (e : IExpr)
  | cppLiteral (name : String) (type : CType) (value : Obj) (lifted : String)
  | cppIntoObject (name value : String) (e : IExpr)
  | cppFromObject (name value : String) (e : IExpr)
  | cppUnsafeCast (name value : String) (e : IExpr)
  | cppCall (name : String) (value : Option String) (args : List String) (e : IExpr)
  | cppConstructorCall (name : String) (args : List String) (e : IExpr)
  | cppMemberCall (name : String) (args : List String) (e : IExpr)
  | cppMemberAccess (name value : String) (e : IExpr)
  | cppBuiltinOperatorCall (name : String) (args : List String) (e : IExpr)
  | cppBox (name value : String) (e : IExpr)
  | cppUnbox (name value metaName : String) (e : IExpr)
  | cppNew (name : String) (args : List String) (e : IExpr)
  | cppDelete (name value : String) (e : IExpr)
  | ret (name value : String) (type : CType)
  | literal (name : String) (o : Obj)

/-- The IR builder's state: the instructions so far and the next identifier. -/
structure Builder where
  insts : Array Inst := #[]
  next : Nat := 0
  lifted : List (Obj × String) := []

abbrev BM := StateM Builder

def nextIdent (pfx : String := "v") : BM String := do
  let b ← get
  set { b with next := b.next + 1 }
  return s!"{pfx}{b.next}"

def emit (i : Inst) : BM Unit := modify fun b => { b with insts := b.insts.push i }

/-- builder.cpp:ret:522. -/
def ret (value : String) (type : CType) : BM String := do
  let n ← nextIdent; emit (.ret n value type); return n

def retIfTail (e : IExpr) (name : String) : BM String :=
  if e.position == .tail then ret name (expressionType e) else pure name

/-- builder.cpp:cpp_scope_open:530. -/
def cppScopeOpen : BM String := do let n ← nextIdent "s"; emit (.cppScopeOpen n); return n
/-- builder.cpp:cpp_scope_close:538. -/
def cppScopeClose (scope : String) : BM String := do let n ← nextIdent; emit (.cppScopeClose n scope); return n
/-- builder.cpp:cpp_raw:546. -/
def cppRaw (e : IExpr) (code : String) : BM String := do
  let n ← nextIdent; emit (.cppRaw n code); retIfTail e n
/-- builder.cpp:cpp_value:558. -/
def cppValue (e : IExpr) : BM String := do let n ← nextIdent; emit (.cppValue n e); retIfTail e n
/-- builder.cpp:cpp_literal:571: typed by `literal_codegen_type(value, false)`; one lifted name
per distinct value. -/
def cppLiteral (pos : ExprPosition) (value : Obj) : BM String := do
  let type := literalCodegenType value false
  let b ← get
  let lifted ← match b.lifted.lookup value with
    | some l => pure l
    | none => do
      let l := s!"const_{b.lifted.length}"
      modify fun b => { b with lifted := (value, l) :: b.lifted }
      pure l
  let n ← nextIdent
  emit (.cppLiteral n type value lifted)
  if pos == .tail then ret n type else return n
/-- builder.cpp:literal (a boxed literal; the analyzer agent's, used for `nil`). -/
def literal (o : Obj) : BM String := do let n ← nextIdent; emit (.literal n o); return n
/-- builder.cpp:cpp_conversion:597: into_object of void is the nil literal. -/
def cppConversion (value : String) (e : IExpr) : BM String := do
  let .cppConversion t _ _ policy := e.data | return value
  let mut n ← nextIdent
  if policy == .intoObject then
    if CppInterop.isVoid t then n ← literal .nil
    else emit (.cppIntoObject n value e)
  else emit (.cppFromObject n value e)
  retIfTail e n
/-- builder.cpp:cpp_unsafe_cast:625. -/
def cppUnsafeCast (value : String) (e : IExpr) : BM String := do
  let n ← nextIdent; emit (.cppUnsafeCast n value e); retIfTail e n
/-- builder.cpp:cpp_call:637. -/
def cppCall (value : Option String) (args : List String) (e : IExpr) : BM String := do
  let n ← nextIdent; emit (.cppCall n value args e); retIfTail e n
/-- builder.cpp:cpp_constructor_call:651. -/
def cppConstructorCall (args : List String) (e : IExpr) : BM String := do
  let n ← nextIdent; emit (.cppConstructorCall n args e); retIfTail e n
/-- builder.cpp:cpp_member_call:664. -/
def cppMemberCall (args : List String) (e : IExpr) : BM String := do
  let n ← nextIdent; emit (.cppMemberCall n args e); retIfTail e n
/-- builder.cpp:cpp_member_access:677. -/
def cppMemberAccess (value : String) (e : IExpr) : BM String := do
  let n ← nextIdent; emit (.cppMemberAccess n value e); retIfTail e n
/-- builder.cpp:cpp_builtin_operator_call:691. -/
def cppBuiltinOperatorCall (args : List String) (e : IExpr) : BM String := do
  let n ← nextIdent; emit (.cppBuiltinOperatorCall n args e); retIfTail e n
/-- builder.cpp:cpp_box:704. -/
def cppBox (value : String) (e : IExpr) : BM String := do
  let n ← nextIdent; emit (.cppBox n value e); retIfTail e n
/-- builder.cpp:cpp_unbox:716. -/
def cppUnbox (value metaName : String) (e : IExpr) : BM String := do
  let n ← nextIdent; emit (.cppUnbox n value metaName e); retIfTail e n
/-- builder.cpp:cpp_new:731. -/
def cppNew (args : List String) (e : IExpr) : BM String := do
  let n ← nextIdent; emit (.cppNew n args e); retIfTail e n
/-- builder.cpp:cpp_delete:743. -/
def cppDelete (value : String) (e : IExpr) : BM String := do
  let n ← nextIdent; emit (.cppDelete n value e); retIfTail e n

/-- ir/processor.cpp:gen for the interop expressions (856-973); other expressions are lowered to
an opaque name (the analyzer/codegen agents' part). -/
partial def gen (e : IExpr) : BM String := do
  match e.data with
  -- 857
  | .cppRaw code => cppRaw e code
  -- 862: "A cpp_type expression was found during codegen, but that should not be possible."
  | .cppType .. => pure "<codegen_internal_failure>"
  -- 868
  | .cppValue .. => cppValue e
  -- 873
  | .cppLiteral d => cppLiteral e.position d
  -- 878
  | .cppConversion _ _ v _ => do cppConversion (← gen v) e
  -- 883
  | .cppUnsafeCast _ v => do cppUnsafeCast (← gen v) e
  -- 888: a cpp_value source that is not a member pointer is not generated
  | .cppCall _ source args _ => do
    let as ← args.mapM gen
    let st := expressionType source
    if source.kind == .cppValue && (st.isNull || !CppInterop.isPointerToMemberType st) then cppCall none as e
    else cppCall (some (← gen source)) as e
  -- 906
  | .cppConstructorCall _ _ args _ => do cppConstructorCall (← args.mapM gen) e
  -- 917
  | .cppMemberCall _ _ args => do cppMemberCall (← args.mapM gen) e
  -- 928
  | .cppMemberAccess _ _ _ o => do cppMemberAccess (← gen o) e
  -- 933
  | .cppBuiltinOperatorCall _ args _ => do cppBuiltinOperatorCall (← args.mapM gen) e
  -- 944
  | .cppBox v => do cppBox (← gen v) e
  -- 949: the source's meta as a boxed literal
  | .cppUnbox _ v => do let m ← literal .nil; cppUnbox (← gen v) m e
  -- 957: the constructor call's arguments, not the call
  | .cppNew _ v => do
    match v.data with
    | .cppConstructorCall _ _ args _ => cppNew (← args.mapM gen) e
    | _ => cppNew [] e
  -- 971
  | .cppDelete v => do cppDelete (← gen v) e
  -- Non-interop expressions: their interop children are lowered in order.
  | .let_ pairs body _ => do
    for (_, v) in pairs do let _ ← gen v
    let mut last := ""
    for b in body do last ← gen b
    return last
  | .if_ _ c t e => do
    -- ir/processor.cpp:gen(if_): the branches are lowered in value position (if.cpp:24)
    let _ ← gen c; let _ ← gen (t.propagatePosition .value)
    if let some x := e then let _ ← gen (x.propagatePosition .value)
    nextIdent "if"
  | .recur args => do for a in args do let _ ← gen a
                      nextIdent "recur"
  | .call _ args => do for a in args do let _ ← gen a
                       nextIdent "call"
  | _ => nextIdent "obj"

/-! ## C++ text (cpp_processor.cpp gen of each instruction) -/

/-- cpp_processor.cpp:gen(cpp_value_ref):1216. -/
def genCppValue (w : World) (name : String) (e : IExpr) : String :=
  match e.data with
  | .cppValue _ t scope k =>
    if k == .null then s!"auto &&{name}(nullptr);"
    else if k == .boolTrue || k == .boolFalse then s!"auto &&{name}({k == .boolTrue});"
    else if CppInterop.isStaticVariable scope && CppInterop.isConstType (CppInterop.getNonReferenceType t) &&
            isPrimitive (CppInterop.getNonReferenceType t) then
      s!"auto {name}({CppInterop.getQualifiedCompleteNameWithTemplateArgs scope});"
    else if CppInterop.isFunction scope || CppInterop.isTemplatedFunction scope then
      s!"auto &&{name}(static_cast<{getQualifiedTypeName w t}>(&{CppInterop.getQualifiedCompleteNameWithTemplateArgs scope}));"
    else if CppInterop.isArrayType (CppInterop.getNonReferenceType t) then
      s!"{getQualifiedTypeName w (CppInterop.getPointerType (CppInterop.getArrayElementType (CppInterop.getNonReferenceType t)))} {name}({CppInterop.getQualifiedCompleteNameWithTemplateArgs scope});"
    else s!"auto &&{name}({if CppInterop.isPointerToMemberType t then "&" else ""}{CppInterop.getQualifiedCompleteNameWithTemplateArgs scope});"
  | _ => ""

/-- cpp_processor.cpp:gen(cpp_literal_ref):1278: a mutable copy of the lifted constant. -/
def genCppLiteral (name : String) (value : Obj) : String := s!"auto {name}({liftConstantUnboxed value});"

/-- cpp_processor.cpp:gen(cpp_into_object_ref):1287 (also used for from_object, 1334). -/
def genCppIntoObject (w : World) (name value : String) (e : IExpr) : String :=
  match e.data with
  | .cppConversion t ct _ policy =>
    if CppInterop.isVoid ct then s!"auto const {name}(jank::runtime::jank_nil);"
    else if isUntypedObject t && isAnyObject w ct then s!"auto &&{name}({value});"
    else if integerRefType.canonical == t.canonical then
      s!"auto const {name}(jank::runtime::make_box<jank::runtime::obj::integer>({value}));"
    else
      -- 7135b7708 (cpp_processor.cpp:1321): `auto &&` (it was `auto const`)
      s!"auto &&{name}(jank::runtime::convert<{getQualifiedTypeName w (CppInterop.getTypeWithoutCv (CppInterop.getNonReferenceType ct)).canonical}>::{if policy == .intoObject then "into_object" else "from_object"}({value}));"
  | _ => ""

/-- cpp_processor.cpp:gen(cpp_unsafe_cast_ref):1340: a C-style cast. -/
def genCppUnsafeCast (w : World) (name value : String) (t : CType) : String :=
  s!"auto const {name}(({getQualifiedTypeName w t})({value}));"

/-- cpp_processor.cpp:gen(cpp_constructor_call_ref):1563, the argument list: a trait conversion
when exactly one side is an object, else a `static_cast` to the parameter type when the types
differ (pointer inequality of the `QualType`s), and parentheses unless aggregate. -/
def genCppConstructorCall (w : World) (name : String) (args : List String) (e : IExpr) : String :=
  match e.data with
  | .cppConstructorCall t fn argExprs isAgg =>
    if args.isEmpty then s!"{getQualifiedTypeName w t} {name}\{ };"
    else
      let paramTypes : List CType :=
        match fn with
        | some f => (List.range (CppInterop.getFunctionNumArgs f)).map (CppInterop.getFunctionArgType f)
        | none => if isPrimitive (CppInterop.getNonReferenceType t) then [t]
                  else aggregateInitializationTypes w (CppInterop.getScopeFromType w t)
      let parts := (args.zip argExprs).zipIdx.map fun ((a, ae), i) =>
        let aty := expressionType ae
        let pt := paramTypes.getD i .null
        if isAnyObject w pt && !isAnyObject w aty then
          s!"jank::runtime::convert<{getQualifiedTypeName w aty}>::into_object({a})"
        else if !isAnyObject w pt && isAnyObject w aty then
          s!"jank::runtime::convert<{getQualifiedTypeName w pt}>::from_object({a})"
        else if pt != aty then s!"static_cast<{getQualifiedTypeName w pt}>({a})"
        else a
      let (o, c) := if isAgg then ("{", "}") else ("(", ")")
      s!"{getQualifiedTypeName w t} {name} {o}{", ".intercalate parts}{c};"
  | _ => ""

/-- cpp_processor.cpp:gen(cpp_call_ref):1352, the direct case: the function called by its
qualified name (C++ resolves the overload again). -/
def genCppCall (w : World) (name : String) (args : List String) (e : IExpr) : String :=
  match e.data with
  | .cppCall t source _ _ =>
    let callee := match source.data with
      | .cppValue _ _ scope _ => CppInterop.getQualifiedCompleteName scope
      | _ => "<fn>"
    if CppInterop.isVoid t then s!"jank::runtime::obj::nil_ref {name};{callee}({", ".intercalate args});"
    else s!"auto &&{name}({callee}({", ".intercalate args}));"
  | _ => ""

/-- cpp_processor.cpp:gen(cpp_member_call_ref):1730. -/
def genCppMemberCall (name : String) (args : List String) (fn : FnDecl) (isPtr : Bool) : String :=
  s!"auto &&{name}({args.headD ""}{if isPtr then "->" else "."}{fn.name}({", ".intercalate (args.drop 1)}));"

/-- cpp_processor.cpp:gen(cpp_member_access_ref):1777. -/
def genCppMemberAccess (name value member : String) (isPtr : Bool) : String :=
  s!"auto &&{name}({value}{if isPtr then "->" else "."}{member});"

/-- cpp_processor.cpp:gen(cpp_builtin_operator_call_ref):1794. -/
def genCppBuiltinOperatorCall (name : String) (op : Cxx.Op) (args : List String) : String :=
  let opName := (operatorName op).getD "?"
  match args with
  | [a] => s!"auto &&{name}( {opName}{a} );"
  | [a, b] => if opName == "aget" then s!"auto &&{name}( {a}[{b}] );" else s!"auto &&{name}( {a} {opName} {b} );"
  | _ => ""

/-- cpp_processor.cpp:gen(cpp_box_ref):1824: the box records the canonical value type's name. -/
def genCppBox (w : World) (name value : String) (valueType : CType) : String :=
  s!"auto {name}\{ jank::runtime::make_box<jank::runtime::obj::opaque_box>({value}, \"{getQualifiedTypeName w (CppInterop.getNonReferenceType valueType).canonical}\") };"

/-- cpp_processor.cpp:gen(cpp_unbox_ref):1848. -/
def genCppUnbox (w : World) (name value metaName : String) (t : CType) : String :=
  let tn := getQualifiedTypeName w t.canonical
  s!"auto {name}\{ static_cast<{tn}>(jank_unbox_with_source(\"{tn}\", {value}.erase().raw(), {metaName}.erase().raw())) };"

/-- cpp_processor.cpp:gen(cpp_new_ref):1866: brace initialization in GC memory. -/
def genCppNew (w : World) (name : String) (args : List String) (t : CType) : String :=
  s!"auto {name}\{ new (UseGC) {getQualifiedTypeName w t}\{ {String.join (args.map (· ++ ","))} } };"

/-- cpp_processor.cpp:gen(cpp_delete_ref):1894. -/
def genCppDelete (w : World) (name value : String) (pointee : CType) (needsFinalizer : Bool) : String :=
  (if needsFinalizer then s!"\{ using T = {getQualifiedTypeName w pointee};\n{value}->~T(); }\n" else "") ++
  s!"GC_free({value});\njank::runtime::obj::nil_ref {name};"

/-- The text of one instruction. -/
def instText (w : World) : Inst → String
  | .cppScopeOpen n => if n == "s0" then "" else "{"
  | .cppScopeClose _ s => if s == "s0" then "" else "}"
  | .cppRaw _ _ => "<cpp/raw code in the raw buffer>"
  | .cppValue n e => genCppValue w n e
  | .cppLiteral n _ v _ => genCppLiteral n v
  | .cppIntoObject n v e | .cppFromObject n v e => genCppIntoObject w n v e
  | .cppUnsafeCast n v e => genCppUnsafeCast w n v (expressionType e)
  | .cppCall n _ args e => genCppCall w n args e
  | .cppConstructorCall n args e => genCppConstructorCall w n args e
  | .cppMemberCall n args e =>
    match e.data with
    | .cppMemberCall _ f as => genCppMemberCall n args f
        (CppInterop.isPointerType (CppInterop.getNonReferenceType (expressionType (as.headD default))))
    | _ => ""
  | .cppMemberAccess n v e =>
    match e.data with
    | .cppMemberAccess _ _ m o => genCppMemberAccess n v m (CppInterop.isPointerType (CppInterop.getNonReferenceType (expressionType o)))
    | _ => ""
  | .cppBuiltinOperatorCall n args e =>
    match e.data with
    | .cppBuiltinOperatorCall op _ _ => genCppBuiltinOperatorCall n op args
    | _ => ""
  | .cppBox n v e => match e.data with | .cppBox x => genCppBox w n v (expressionType x) | _ => ""
  | .cppUnbox n v m e => genCppUnbox w n v m (expressionType e)
  | .cppNew n args e => match e.data with | .cppNew t _ => genCppNew w n args t | _ => ""
  | .cppDelete n v e =>
    match e.data with
    | .cppDelete x =>
      let pt := CppInterop.getPointeeType (expressionType x)
      genCppDelete w n v pt (!CppInterop.isTriviallyDestructible w pt)
    | _ => ""
  | .ret _ v _ => s!"return {v};"
  | .literal n o => s!"auto const {n}({liftConstantBoxed w o});"

/-- The C++ lines the interop part of an expression compiles to. -/
def cppText (w : World) (e : IExpr) : List String :=
  let (_, b) := (gen e).run {}
  b.insts.toList.map (instText w) |>.filter (!·.isEmpty)

end Jank.Interop.Codegen
