import Jank.R3.Interop.Clang

/-!
# CppInterOp 28b0830d, replicated (round 3)

Each definition is one function of `deps/cppinterop/lib/CppInterOp/CppInterOp.cpp` (line cited)
that jank's analyzer or code generator calls through `src/cpp/jank/analyze/cppinterop.cpp` (each
jank wrapper locks the interpreter mutex and makes exactly that call). The code is transcribed:
what CppInterOp computes itself (type kinds, pointees, which scope, which synthesized operand,
which Sema entry point and with which flags) is replicated line by line; Sema's answer comes from
`Clang.lean`.

`Platform` decides the Clang kind of plain `char` (`Char_S` on x86-64 Linux and macOS, `Char_U`
on AArch64 Linux) and of `wchar_t` (`WChar_S` / `WChar_U`; CXA9: AArch64 Linux's `wchar_t` is
`unsigned int`, the AAPCS64 choice Clang's AArch64 Linux target makes).
-/

namespace Jank.R3.Interop.CppInterOp

open Jank.Interop
open Jank.R3.Interop.Clang

abbrev Scope := Option Decl

/-! ## Type predicates -/

/-- CppInterOp.cpp:499 `IsBuiltin`: `Ty->isBuiltinType()` (enums, pointers, classes are not). -/
def isBuiltin (t : CType) : Bool := isBuiltinType t
/-- CppInterOp.cpp:504 `IsIntegral`: `Ty->isIntegralType(Ctx)`; in C++ never an enum. -/
def isIntegral (t : CType) : Bool := isIntegralType t
/-- CppInterOp.cpp:514 `IsVoid`. -/
def isVoid (t : CType) : Bool := isVoidType t
/-- CppInterOp.cpp:755 `IsEnumType`. -/
def isEnumType (t : CType) : Bool := isEnumeralType t
/-- CppInterOp.cpp:2857 `IsPointerType` (function pointers included). -/
def isPointerType (t : CType) : Bool := Clang.isPointerType t
/-- CppInterOp.cpp:2862. -/
def isPointerToMemberType (t : CType) : Bool := isMemberPointerType t
/-- CppInterOp.cpp:2872. -/
def isPointerToMemberFunctionType (t : CType) : Bool :=
  match view t with | .memPtr _ u => Clang.isFunctionType u | _ => false
/-- CppInterOp.cpp:2930. -/
def isArrayType (t : CType) : Bool := Clang.isArrayType t
/-- CppInterOp.cpp:3062. -/
def isReferenceType (t : CType) : Bool := Clang.isReferenceType t
/-- CppInterOp.cpp:3067. -/
def isRvalueReferenceType (t : CType) : Bool := isRValueReferenceType t
/-- CppInterOp.cpp:2829 `IsConstType`: `QT.isConstQualified()`. -/
def isConstType (t : CType) : Bool := isConstQualified t
/-- CppInterOp.cpp:429. -/
def isFunctionPointerType (t : CType) : Bool := Clang.isFunctionPointerType t

/-! ## Type transformers -/

/-- CppInterOp.cpp:3088 `GetNonReferenceType`. -/
def getNonReferenceType (t : CType) : CType := if isReferenceType t then nonRef t else t
/-- CppInterOp.cpp:3390 `GetCanonicalType` (null stays null). -/
def getCanonicalType (t : CType) : CType := if t.isNull then .null else t.canonical
/-- CppInterOp.cpp:3113 `GetTypeWithoutCv`: `getUnqualifiedDesugaredType`. -/
def getTypeWithoutCv (t : CType) : CType := view t
/-- CppInterOp.cpp:3119 `GetTypeWithConst`. -/
def getTypeWithConst (t : CType) : CType := .cv true false t
/-- CppInterOp.cpp:3050 `GetLValueReferenceType` (`getLValueReferenceType` collapses `T&` and
`T&&` to `T&`). -/
def getLvalueReferenceType (t : CType) : CType :=
  match view t with | .lref u | .rref u => .lref u | _ => .lref t
/-- CppInterOp.cpp:3023. -/
def getPointerType (t : CType) : CType := .ptr t
/-- CppInterOp.cpp:2949 `GetArrayElementType` (null for a non-array). -/
def getArrayElementType (t : CType) : CType := arrayElem t
/-- CppInterOp.cpp:3014 `GetPointeeType`: an array's element type, a pointer's pointee, else
null. Round 2 (IA11) answered null for arrays. -/
def getPointeeType (t : CType) : CType :=
  if isArrayType t then getArrayElementType t
  else if !isPointerType t then .null
  else pointeeOf t

/-- `while (QT->isArrayType()) QT = QT->getArrayElementTypeNoTypeQual()`. -/
def stripArrays : Nat → CType → CType
  | 0, t => t
  | n + 1, t => match view t with | .array e _ => stripArrays n e | _ => t

/-- `for (PT = QT->getPointeeType(); !PT.isNull(); ...) QT = PT` (pointers, references, member
pointers; `Type::getPointeeType`). -/
def stripPointees : Nat → CType → CType
  | 0, t => t
  | n + 1, t => match view t with
    | .ptr u | .lref u | .rref u | .memPtr _ u => stripPointees n u
    | _ => t

/-- CppInterOp.cpp:3095 `GetUnderlyingType`: canonical, unqualified; every array dimension, then
every pointer, reference and member-pointer level; canonical unqualified again. A pointer to an
array stops at the array. -/
def getUnderlyingType (t : CType) : CType :=
  (stripPointees 16 (stripArrays 16 t.canonical.unqual)).canonical.unqual

/-! ## Signedness and width modifiers (CppInterOp.cpp:3131-3367) -/

/-- The Clang `BuiltinType::Kind` of a builtin on a platform: plain `char` is `Char_S` or
`Char_U`, `wchar_t` is `WChar_S` or `WChar_U`. -/
inductive Kind where
  | Bool | Char_S | Char_U | SChar | UChar | WChar_S | WChar_U | Char8 | Char16 | Char32
  | Short | UShort | Int | UInt | Long | ULong | LongLong | ULongLong
  | Float | Double | LongDouble | Void | NullPtr
  deriving Repr, BEq, DecidableEq, Inhabited

def kindOf (p : Platform) : Builtin → Kind
  | .bool => .Bool | .char => if p.charSigned then .Char_S else .Char_U | .schar => .SChar
  | .uchar => .UChar | .wchar => if p.charSigned then .WChar_S else .WChar_U | .char8 => .Char8
  | .char16 => .Char16 | .char32 => .Char32 | .short => .Short | .ushort => .UShort | .int => .Int
  | .uint => .UInt | .long => .Long | .ulong => .ULong | .llong => .LongLong | .ullong => .ULongLong
  | .float => .Float | .double => .Double | .ldouble => .LongDouble | .void => .Void
  | .nullptr => .NullPtr

/-- `C.getQualifiedType(T, QT.getQualifiers())`: the local qualifiers of the operand kept. -/
def localQuals : CType → Bool × Bool
  | .cv c v _ => (c, v)
  | _ => (false, false)

def requal (t : CType) (k : Builtin) : CType :=
  let (c, v) := localQuals t
  CType.mkCv c v (.b k)

/-- CppInterOp.cpp:3131 `GetSignedType`: `Char_S` (plain `char` where it is signed) and every
kind without a signed partner come back unchanged. -/
def getSignedType (p : Platform) (t : CType) : CType :=
  match builtin? t with
  | none => t
  | some k => match kindOf p k with
    | .UChar | .Char_U => requal t .schar
    | .UShort => requal t .short
    | .UInt => requal t .int
    | .ULong => requal t .long
    | .ULongLong => requal t .llong
    | _ => t

/-- CppInterOp.cpp:3188 `GetUnsignedType`: `Char_U` (plain `char` where it is unsigned) comes back
unchanged. -/
def getUnsignedType (p : Platform) (t : CType) : CType :=
  match builtin? t with
  | none => t
  | some k => match kindOf p k with
    | .SChar | .Char_S => requal t .uchar
    | .Short => requal t .ushort
    | .Int => requal t .uint
    | .Long => requal t .ulong
    | .LongLong => requal t .ullong
    | _ => t

/-- CppInterOp.cpp:3241 `GetShortType`: `bool`, `char8_t`, `char16_t`, `char32_t` and the floating
types come back unchanged. -/
def getShortType (p : Platform) (t : CType) : CType :=
  match builtin? t with
  | none => t
  | some k => match kindOf p k with
    | .Int | .Long | .LongLong | .SChar | .Char_S | .WChar_S => requal t .short
    | .UInt | .ULong | .ULongLong | .UChar | .Char_U | .WChar_U => requal t .ushort
    | _ => t

/-- CppInterOp.cpp:3290 `GetLongType`: `long` and `unsigned long` come back unchanged, so a second
`:long` never makes `long long`; `long long` itself becomes `long`; `bool` and the `charN_t`
types come back unchanged. -/
def getLongType (p : Platform) (t : CType) : CType :=
  match builtin? t with
  | none => t
  | some k => match kindOf p k with
    | .SChar | .Short | .Int | .LongLong | .Char_S | .WChar_S => requal t .long
    | .UChar | .Char_U | .UShort | .UInt | .ULongLong | .WChar_U => requal t .ulong
    | .Double => requal t .ldouble
    | _ => t

/-- CppInterOp.cpp:3337 `IsShortType`. -/
def isShortType (t : CType) : Bool :=
  match builtin? t with | some .short | some .ushort => true | _ => false

/-! ## Scopes -/

/-- CppInterOp.cpp:1111 `GetScopeFromType`: canonical type, one pointer level or every array
dimension stripped (`getPointeeOrArrayElementType`), desugared; an enum's or a class's
declaration, else null (a reference, a function type, a function pointer: null). -/
def getScopeFromType (x : XWorld) (t : CType) : Scope :=
  let c := t.canonical
  let c := match view c with
    | .ptr u => u
    | .array .. => stripArrays 16 c
    | _ => c
  match view c with
  | .record n => (x.findClass n).map Decl.class_
  | .enum n => (x.findEnum n).map Decl.enum_
  | _ => none

/-- CppInterOp.cpp:3537 `GetTypeFromScope`: a function (or function template) gives a *pointer*
to its function type; a value its type; a class its type. -/
def getTypeFromScope : Scope → CType
  | some (.class_ c) => .record c.name
  | some (.enum_ e) => .enum e.name
  | some (.enumConstant e _ _) => .enum e
  | some (.function f) => .ptr (.fn f.ret f.params)
  | some (.variable _ t _ _) => t
  | some (.typedef_ n t) => .alias n t
  | some (.field _ f) => f.type
  | _ => .null

/-- CppInterOp.cpp:897 `IsVariable`: a `VarDecl` only (a non-static data member is a
`FieldDecl`). -/
def isVariable : Scope → Bool | some (.variable ..) => true | _ => false
/-- CppInterOp.cpp:2810 `IsNonStaticVariable`: a `FieldDecl`. -/
def isNonStaticVariable : Scope → Bool | some (.field ..) => true | _ => false
/-- CppInterOp.cpp:2801 `IsStaticVariable`: any `VarDecl`. -/
def isStaticVariable : Scope → Bool | some (.variable ..) => true | _ => false
/-- CppInterOp.cpp:2797 `IsPrivateVariable`: the declaration's own access. -/
def isPrivateVariable : Scope → Bool | some (.field _ f) => f.isPrivate | _ => false
def isProtectedVariable : Scope → Bool | some (.field _ f) => f.isProtected | _ => false

/-- Class member lookup for a name (`LookupQualifiedName` on a class, [class.member.lookup]): the
declarations in the most derived class that declares the name; several base subobjects declaring
it is an ambiguity (more than one result). Fields, static members (`VarDecl`s) and methods. -/
partial def memberLookup (x : XWorld) (cls : String) (name : String) : List Decl :=
  match x.findClass cls with
  | none => []
  | some c =>
    let fields := (c.fields.filter (·.name == name)).map (Decl.field c.name)
    let statics := (x.staticFields.filter fun (o, n, _) => o == cls && n == name).map
      fun (o, n, t) => Decl.variable (o ++ "::" ++ n) t true false
    let methods := (c.methods.filter (·.name == name)).map fun f => Decl.function { f with owner := c.name }
    let here := fields ++ statics ++ methods
    if !here.isEmpty then here
    else
      let fromBases := c.bases.map fun b => memberLookup x b name
      match fromBases.filter (!·.isEmpty) with
      | [] => []
      | [r] => r
      | rs => rs.flatten

/-- CppInterOp.cpp:2502 `LookupDatamember`: `Lookup::Named` (qualified lookup, bases included); a
single `FieldDecl` result, else null (a static member is a `VarDecl`: null). -/
def lookupDatamember (x : XWorld) (name : String) : Scope → Scope
  | some (.class_ c) =>
    match memberLookup x c.name name with
    | [d@(.field ..)] => some d
    | _ => none
  | _ => none

/-- CppInterOp.cpp:2480 `GetStaticDatamembers`: the class's own `VarDecl`s (`decls()`; bases not
visited). -/
def getStaticDatamembers (x : XWorld) : Scope → List Decl
  | some (.class_ c) => (x.staticFields.filter (·.1 == c.name)).map
      fun (o, n, t) => Decl.variable (o ++ "::" ++ n) t true false
  | _ => []

/-- CppInterOp.cpp:1181 `GetNamed` in a class: a single result (an overload set or an ambiguity
is `(NamedDecl*)-1`, which `GetNamed` turns into null). -/
def getNamedInClass (x : XWorld) (cls : String) (name : String) : Scope :=
  match memberLookup x cls name with
  | [d] => some d
  | _ => none

/-! ## Sema-backed queries -/

/-- CppInterOp.cpp:578 `GetCommonType`: two arithmetic types (unscoped enums included; a
reference type is not arithmetic) → `UsualArithmeticConversions` (both promoted: `bool`/`bool` is
`int`); pointer-like on both sides (pointers, arrays, member pointers, `nullptr_t`) → the
composite pointer type after decay; anything else (classes, references, `bool` with a pointer) →
null. -/
def getCommonType (p : Platform) (x : XWorld) (a b : CType) : CType :=
  if isArithmeticType x a && isArithmeticType x b then (usualArithmetic p x a b).getD .null
  else
    let pl (t : CType) := Clang.isPointerType t || Clang.isArrayType t || isMemberPointerType t || isNullPtrType t
    if pl a && pl b then (compositePointer x a b).getD .null else .null

/-- CppInterOp.cpp:639 `IsImplicitlyConvertible`. -/
def isImplicitlyConvertible (p : Platform) (x : XWorld) (src dst : CType) : Bool :=
  tryImplicitConversion p x src dst

/-- CppInterOp.cpp:690 `IsConstructible`. -/
def isConstructible (p : Platform) (x : XWorld) (dst src : CType) : Bool :=
  isConstructibleTrait p x dst src

/-- CppInterOp.cpp:718 `IsAssignable`. -/
def isAssignable (p : Platform) (x : XWorld) (dst src : CType) : Bool :=
  isAssignableTrait p x dst src

/-- CppInterOp.cpp:653 `IsCStyleConvertible`: the operand is synthesized from the source type
alone. A pointer or member pointer: a null pointer (`CK_NullToPointer` over the literal `0`,
which Clang still sees as a null pointer constant); an integral or enumeration type: the literal
`0` of that type (a null pointer constant when integral); every other source (floating, class,
array, `std::nullptr_t`, function): false without asking Sema. -/
def isCStyleConvertible (p : Platform) (x : XWorld) (src dst : CType) : Bool :=
  let s := nonRef src
  if Clang.isPointerType s || isMemberPointerType s then
    cStyleCastOk p x { type := s, npc := true } dst
  else if isIntegralOrEnumerationType s then
    cStyleCastOk p x { type := s, npc := !isEnumeralType s } dst
  else false

/-- CppInterOp.cpp:7067 `GetBuiltinOperatorType`: every operand is an lvalue of its non-reference
type (qualifiers kept), except a non-reference `std::nullptr_t` (a prvalue). -/
def getBuiltinOperatorType (p : Platform) (x : XWorld) (op : Cxx.Op) (args : List CType) : CType :=
  if args.any (·.isNull) then .null
  else builtinOp p x op (args.map fun t =>
    { type := nonRef t, lvalue := !(isNullPtrType (nonRef t) && !isLValueReferenceType t) })

/-- CppInterOp.cpp:2889 `GetFunctionTypeFromPointerToMember(member_type, obj_type)`: the object
parameter is `C&` (or `C*` when the object type is a pointer), `const` only when the object type
*itself* is const-qualified (for `const C *` it is the pointee that is const: the parameter is
`C *`). -/
def getFunctionTypeFromPointerToMember (memberType objType : CType) : CType :=
  match view memberType with
  | .memPtr cls pointee =>
    let ot := nonRef objType
    let classT : CType := if isConstQualified ot then .cv true false (.record cls) else .record cls
    let objParam := if Clang.isPointerType ot then .ptr classT else .lref classT
    match view pointee with
    | .fn r ps => .fn r (objParam :: ps)
    | _ => .fn pointee [objParam]
  | _ => .null

/-- CppInterOp.cpp:1702 `GetFunctionArgTypeFromType` / 1682 `GetFunctionNumArgsFromType`. -/
def getFunctionArgTypeFromType (t : CType) (i : Nat) : CType :=
  match view t with
  | .fn _ ps => ps.getD i .null
  | .ptr u => match view u with | .fn _ ps => ps.getD i .null | _ => .null
  | _ => .null

def getFunctionNumArgsFromType (t : CType) : Nat :=
  match view t with
  | .fn _ ps => ps.length
  | .ptr u => match view u with | .fn _ ps => ps.length | _ => 0
  | _ => 0

/-! ## Overload resolution (CppInterOp.cpp:1996 `AddOverloadCandidates`, 2203
`BestOverloadMatch`) -/

/-- The argument expressions CppInterOp synthesizes: a prvalue for a non-reference type, an
lvalue for `T&`, an xvalue for `T&&`; the expression's type is the non-reference type. -/
def argKind (t : CType) : VK :=
  if isLValueReferenceType t then .lvalue else if isRValueReferenceType t then .xvalue else .prvalue

/-- One candidate: `AddOverloadCandidate` (free functions, static members — which get the
non-member argument list, implicit object argument included — and constructors) or
`AddMethodCandidate` (non-static members: the first argument is the object, matched against the
class, the rest against the parameters). A deleted method is not added at all. -/
def candidate (p : Platform) (x : XWorld) (f : FnDecl) (args : List CType) : Option Clang.Cand :=
  let member := f.isMethod && !f.isStatic && !f.isCtor
  if f.isMethod && f.isDeleted && !f.isCtor then none
  else
    let (objIcs, rest) : List ICS × List CType :=
      if member then
        match args with
        | [] => ([], [])
        | o :: r =>
          let ot := nonRef o
          let okObj := (view ot).canonical.unqual == .record f.owner || derivedFrom x (view ot) (.record f.owner)
          let constOk := !isConstQualified ot || f.isConst
          ([if okObj && constOk then .std { rank := .exact, identity := true } else .bad], r)
      else ([], args)
    let n := rest.length
    let arity := n ≥ f.required && (n ≤ f.params.length || f.isVariadic)
    let ics := rest.zipIdx.map fun (a, i) =>
      match f.params[i]? with
      | some prm => paramConv p x false (nonRef a) (argKind a) prm
      | none => .std { rank := .exact, identity := true }
    let all := objIcs ++ ics
    some { fn := f, ics := all, viable := arity && all.all ICS.ok && !(member && args.isEmpty) }

/-- CppInterOp.cpp:2203 `BestOverloadMatch`: the best viable function (a deleted best included),
else the candidates `BestViableFunction` marked `Best` (an ambiguity), else nothing. -/
def bestOverloadMatch (p : Platform) (x : XWorld) (fns : List FnDecl) (args : List CType) : List FnDecl :=
  let cands := fns.filterMap fun f => candidate p x f args
  match Clang.bestViable cands with
  | (some b, _) => [b.fn]
  | (none, gathered) => gathered.map (·.fn)

end Jank.R3.Interop.CppInterOp
