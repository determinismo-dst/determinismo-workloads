/-!
# C++ types and the facts Clang/CppInterOp answer about them

jank's interop code (`src/cpp/jank/analyze/cppinterop.cpp`) never computes a C++ fact itself: it
asks CppInterOp (`Cpp::IsImplicitlyConvertible`, `Cpp::BestOverloadMatch`, ...), which asks Clang's
Sema. Those libraries are not read here. This file models the facts they answer, following the
C++ standard (C++20, the standard jank compiles with), as plain functions over a small universe of
types. Each function names the CppInterOp call it stands for. Every modeling choice is an
assumption listed in the report (IA1...).

Platform: LP64 (Linux/macOS, x86-64 and AArch64): `int` 32 bits, `long` and `long long` 64 bits,
`wchar_t` 32 bits signed. Plain `char` is signed on x86-64 (and Apple AArch64) and unsigned on
Linux AArch64: `Platform.charSigned`.
-/

namespace Jank.Interop

/-- Clang `BuiltinType` kinds that jank's code paths name. -/
inductive Builtin where
  | void | bool | char | schar | uchar | wchar | char8 | char16 | char32
  | short | ushort | int | uint | long | ulong | llong | ullong
  | float | double | ldouble | nullptr
  deriving Repr, BEq, DecidableEq, Inhabited, Hashable

structure Platform where
  charSigned : Bool := true
  deriving Repr, BEq, Inhabited

def x86_64 : Platform := { charSigned := true }
def linuxAArch64 : Platform := { charSigned := false }

namespace Builtin

def isIntegerKind : Builtin → Bool
  | .bool | .char | .schar | .uchar | .wchar | .char8 | .char16 | .char32
  | .short | .ushort | .int | .uint | .long | .ulong | .llong | .ullong => true
  | _ => false

def isFloating : Builtin → Bool
  | .float | .double | .ldouble => true
  | _ => false

def isArithmetic (k : Builtin) : Bool := k.isIntegerKind || k.isFloating

/-- Bits of the value representation (LP64). -/
def width : Builtin → Nat
  | .bool => 1
  | .char | .schar | .uchar | .char8 => 8
  | .short | .ushort | .char16 => 16
  | .int | .uint | .wchar | .char32 | .float => 32
  | .long | .ulong | .llong | .ullong | .double => 64
  | .ldouble => 80
  | _ => 0

def isSigned (p : Platform) : Builtin → Bool
  | .char => p.charSigned
  | .schar | .short | .int | .long | .llong | .wchar => true
  | _ => false

/-- Integer conversion rank ([conv.rank]). -/
def rank : Builtin → Nat
  | .bool => 0
  | .char | .schar | .uchar | .char8 => 1
  | .short | .ushort | .char16 => 2
  | .int | .uint | .wchar | .char32 => 3
  | .long | .ulong => 4
  | .llong | .ullong => 5
  | _ => 0

def minVal (p : Platform) (k : Builtin) : Int :=
  if k == .bool then 0 else if k.isSigned p then -(2 ^ (k.width - 1)) else 0

def maxVal (p : Platform) (k : Builtin) : Int :=
  if k == .bool then 1 else if k.isSigned p then 2 ^ (k.width - 1) - 1 else 2 ^ k.width - 1

def fits (p : Platform) (k : Builtin) (v : Int) : Bool := k.minVal p ≤ v && v ≤ k.maxVal p

/-- The unsigned type of the same rank ([conv.arith] 4th bullet). -/
def toUnsigned : Builtin → Builtin
  | .int => .uint | .long => .ulong | .llong => .ullong | .short => .ushort
  | .schar | .char => .uchar | k => k

/-- Clang's spelling (`QualType::getAsString`). -/
def spelling : Builtin → String
  | .void => "void" | .bool => "bool" | .char => "char" | .schar => "signed char"
  | .uchar => "unsigned char" | .wchar => "wchar_t" | .char8 => "char8_t"
  | .char16 => "char16_t" | .char32 => "char32_t" | .short => "short"
  | .ushort => "unsigned short" | .int => "int" | .uint => "unsigned int" | .long => "long"
  | .ulong => "unsigned long" | .llong => "long long" | .ullong => "unsigned long long"
  | .float => "float" | .double => "double" | .ldouble => "long double"
  | .nullptr => "std::nullptr_t"

end Builtin

/-- A C++ type (a `clang::QualType` as an opaque pointer, `jtl::ptr<void>`). `alias` is sugar
(a typedef or alias template) that canonicalization strips; `null` is the null `jtl::ptr<void>`
CppInterOp returns when it has no answer. -/
inductive CType where
  | b (k : Builtin)
  | cv (isConst isVolatile : Bool) (t : CType)
  | ptr (t : CType)
  | lref (t : CType)
  | rref (t : CType)
  | array (elem : CType) (size : Option Nat)
  | fn (ret : CType) (params : List CType)
  | enum (name : String)
  | record (name : String)
  | alias (name : String) (target : CType)
  | memPtr (cls : String) (t : CType)
  | null
  deriving Repr, BEq, Inhabited

namespace CType

def int : CType := .b .int
def long : CType := .b .long
def double : CType := .b .double
def bool : CType := .b .bool
def char : CType := .b .char
def void : CType := .b .void
def nullptrT : CType := .b .nullptr
def const (t : CType) : CType := .cv true false t
def isNull : CType → Bool | .null => true | _ => false

end CType

/-! ## Declarations: the world the program's C++ lives in

`cpp/raw` and headers declare these; CppInterOp looks them up. A scope (`clang_decl`) is one of
them. -/

structure FieldDecl where
  name : String
  type : CType
  isPrivate : Bool := false
  isProtected : Bool := false
  isStatic : Bool := false
  deriving Repr, BEq, Inhabited

/-- How a function template computes its parameter types and return type from the argument types
(template argument deduction plus the `requires` clause; `none`: not viable). -/
inductive TemplateKind where
  | none
  /-- `jank::runtime::{add, sub, mul, div}` and `lt`/`lte` (core/math.hpp): four templates on
  `L`, `R` chosen by `primitive_number`. -/
  | mathBinary (op : String)
  /-- `jank::runtime::inc`/`dec` (core/math.hpp:1186). -/
  | mathUnary (op : String)
  deriving Repr, BEq, Inhabited

structure FnDecl where
  name : String
  params : List CType := []
  /-- Parameters without a default argument. -/
  required : Nat := 0
  ret : CType := .b .void
  isMethod : Bool := false
  isStatic : Bool := false
  isConst : Bool := false
  isCtor : Bool := false
  isExplicit : Bool := false
  isDeleted : Bool := false
  isPrivate : Bool := false
  isProtected : Bool := false
  isVariadic : Bool := false
  template : TemplateKind := .none
  /-- A constructor `T(std::initializer_list<elem>)`. -/
  initListElem : Option CType := none
  /-- The class a member function belongs to. -/
  owner : String := ""
  deriving Repr, BEq, Inhabited

structure ClassDecl where
  name : String
  bases : List String := []
  fields : List FieldDecl := []
  ctors : List FnDecl := []
  methods : List FnDecl := []
  isAggregate : Bool := false
  complete : Bool := true
  /-- Non-explicit conversion functions (`operator T()`). -/
  convertsTo : List CType := []
  /-- An `oref<value_type>` specialization (jank's typed object references). -/
  orefOf : Option String := none
  deriving Repr, BEq, Inhabited

structure EnumDecl where
  name : String
  isScoped : Bool := false
  underlying : Builtin := .int
  constants : List (String × Int) := []
  deriving Repr, BEq, Inhabited

/-- A Clang declaration (`clang_decl`, a scope). -/
inductive Decl where
  | namespace_ (name : String)
  | class_ (c : ClassDecl)
  | enum_ (e : EnumDecl)
  | enumConstant (enumName : String) (name : String) (value : Int)
  | function (f : FnDecl)
  | variable (name : String) (type : CType) (isStatic : Bool) (isConstExprPrimitive : Bool)
  | typedef_ (name : String) (target : CType)
  | field (owner : String) (f : FieldDecl)
  deriving Repr, BEq, Inhabited

/-! ## The default world: jank's runtime types, a few std types, the program's own declarations -/

def objectRefName : String := "jank::runtime::object_ref"
def orefName (v : String) : String := s!"jank::runtime::oref<jank::runtime::obj::{v}>"

/-- jank's typed object references (`obj::X_ref = oref<obj::X>`), oref.hpp. -/
def typedRefs : List String :=
  ["nil", "boolean", "integer", "small_integer", "real", "small_real", "big_integer", "ratio",
   "persistent_string", "character", "keyword", "symbol", "persistent_list", "persistent_vector",
   "persistent_array_map", "persistent_hash_map", "persistent_hash_set", "opaque_box", "var",
   "jit_function", "jit_closure", "re_pattern"]

def typedRef (v : String) : CType := .alias s!"jank::runtime::obj::{v}_ref" (.record (orefName v))

def objectRef : CType := .record objectRefName
def objectT : CType := .record "jank::runtime::object"
def stdString : CType := .alias "std::string" (.record "std::basic_string<char>")
def vectorInt : CType := .record "std::vector<int>"
def sizeT : CType := .alias "size_t" (.b .ulong)

structure World where
  classes : List ClassDecl
  enums : List EnumDecl
  functions : List FnDecl
  deriving Repr, Inhabited

def jankClasses : List ClassDecl :=
  [{ name := "jank::runtime::object" },
   { name := objectRefName },
   { name := "std::basic_string<char>",
     ctors := [{ name := "basic_string", isCtor := true, params := [], required := 0, ret := .null },
               { name := "basic_string", isCtor := true,
                 params := [.ptr (.const (.b .char))], required := 1, ret := .null },
               { name := "basic_string", isCtor := true,
                 params := [.lref (.const stdString)], required := 1, ret := .null }],
     methods := [{ name := "size", isMethod := true, isConst := true, ret := sizeT },
                 { name := "empty", isMethod := true, isConst := true, ret := .b .bool }] },
   { name := "std::vector<int>",
     ctors := [{ name := "vector", isCtor := true, params := [], required := 0, ret := .null },
               { name := "vector", isCtor := true, isExplicit := true, params := [sizeT],
                 required := 1, ret := .null },
               { name := "vector", isCtor := true, params := [sizeT, .lref (.const (.b .int))],
                 required := 2, ret := .null },
               { name := "vector", isCtor := true,
                 params := [.record "std::initializer_list<int>"], required := 1, ret := .null,
                 initListElem := some (.b .int) }],
     methods := [{ name := "size", isMethod := true, isConst := true, ret := sizeT }] },
   { name := "std::initializer_list<int>" },
   -- The program's own types (declared with cpp/raw).
   { name := "person", fields := [{ name := "name", type := stdString }], isAggregate := true },
   { name := "point", fields := [{ name := "x", type := .b .int }, { name := "y", type := .b .int }],
     isAggregate := true },
   { name := "base" },
   { name := "derived", bases := ["base"] },
   { name := "wide", ctors := [{ name := "wide", isCtor := true, params := [.b .long],
                                 required := 1, ret := .null }] }]
  ++ typedRefs.map fun v => { name := orefName v, orefOf := some v }

def jankEnums : List EnumDecl :=
  [{ name := "color", isScoped := false, underlying := .uint, constants := [("red", 0), ("green", 1)] },
   { name := "mode", isScoped := true, underlying := .int, constants := [("off", 0), ("on", 1)] }]

/-- `jank::runtime::{add, sub, mul, div, lt, lte, inc, dec}`, the targets of clojure.core's
`:inline` expansions (core.jank 1371-1697), as the template families they are. -/
def jankMathFns : List FnDecl :=
  ["add", "sub", "mul", "div", "lt", "lte"].map (fun op =>
    { name := s!"jank::runtime::{op}", params := [.null, .null], required := 2, ret := .null,
      template := .mathBinary op }) ++
  ["inc", "dec"].map (fun op =>
    { name := s!"jank::runtime::{op}", params := [.null], required := 1, ret := .null,
      template := .mathUnary op })

/-- Free functions the searched programs declare with `cpp/raw`, one per parameter type. -/
def paramFns : List FnDecl :=
  [("take_bool", CType.b .bool), ("take_char", .b .char), ("take_uchar", .b .uchar),
   ("take_short", .b .short), ("take_int", .b .int), ("take_uint", .b .uint),
   ("take_long", .b .long), ("take_ulong", .b .ulong), ("take_float", .b .float),
   ("take_double", .b .double), ("take_cstr", .ptr (.const (.b .char))),
   ("take_mut_cstr", .ptr (.b .char)), ("take_string", .lref (.const stdString)),
   ("take_color", .enum "color")].map fun (n, t) =>
    { name := n, params := [t], required := 1, ret := t }

def world0 : World := { classes := jankClasses, enums := jankEnums,
                         functions := jankMathFns ++ paramFns }

namespace World

def findClass (w : World) (n : String) : Option ClassDecl := w.classes.find? (·.name == n)
def findEnum (w : World) (n : String) : Option EnumDecl := w.enums.find? (·.name == n)

end World

/-! ## Canonical types and the simple queries -/

namespace CType

def mkCv (c v : Bool) (u : CType) : CType := if c || v then .cv c v u else u

/-- Canonicalization with a depth bound (types here are far shallower than 32). -/
def canonicalN : Nat → CType → CType
  | 0, t => t
  | n + 1, t =>
    match t with
    | .alias _ u => canonicalN n u
    | .cv c v u =>
      match canonicalN n u with
      | .cv c' v' x => mkCv (c || c') (v || v') x
      | .lref x => .lref x
      | .rref x => .rref x
      | .array e m => .array (canonicalN n (.cv c v e)) m
      | x => mkCv c v x
    | .ptr u => .ptr (canonicalN n u)
    | .lref u => .lref (canonicalN n u)
    | .rref u => .rref (canonicalN n u)
    | .array e m => .array (canonicalN n e) m
    | .fn r ps => .fn (canonicalN n r) (ps.map (canonicalN n))
    | .memPtr c u => .memPtr c (canonicalN n u)
    | u => u

/-- Clang `QualType::getCanonicalType`: sugar stripped, cv merged and pushed to where C++ puts
it (a cv array is an array of cv elements; cv on a reference is dropped). -/
def canonical (t : CType) : CType := canonicalN 32 t

/-- Top-level cv of a canonical type removed. -/
def unqual : CType → CType
  | .cv _ _ t => t
  | t => t

def topConst : CType → Bool
  | .cv c _ _ => c
  | _ => false

def topVolatile : CType → Bool
  | .cv _ v _ => v
  | _ => false

end CType

/-- Type identity, as `QualType` pointer equality after canonicalization. -/
def sameType (a b : CType) : Bool := a.canonical == b.canonical

/-! ## C++ facts (CppInterOp's answers) -/

namespace Cxx



/-- `Cpp::GetNonReferenceType`. -/
def nonRef : CType → CType
  | .lref t | .rref t => t
  | .alias n t => match t.canonical with
    | .lref _ | .rref _ => nonRef t
    | _ => .alias n t
  | t => t

def isReference (t : CType) : Bool :=
  match t.canonical with | .lref _ | .rref _ => true | _ => false

def isRvalueReference (t : CType) : Bool :=
  match t.canonical with | .rref _ => true | _ => false

/-- `Cpp::GetTypeWithoutCv` (top level, on the canonical type). -/
def withoutCv (t : CType) : CType := t.canonical.unqual

def withConst (t : CType) : CType := (CType.cv true false t).canonical
def withVolatile (t : CType) : CType := (CType.cv false true t).canonical

def builtinKind? (t : CType) : Option Builtin :=
  match t.canonical.unqual with | .b k => some k | _ => none

/-- `Cpp::IsBuiltin`: a Clang `BuiltinType` (enums, pointers, arrays and classes are not;
IA2). -/
def isBuiltin (t : CType) : Bool := (builtinKind? t).isSome

def isVoid (t : CType) : Bool := builtinKind? t == some .void
def isNullptrT (t : CType) : Bool := builtinKind? t == some .nullptr

def isPointer (t : CType) : Bool :=
  match t.canonical.unqual with | .ptr _ => true | _ => false

def isArray (t : CType) : Bool :=
  match t.canonical.unqual with | .array .. => true | _ => false

def isSizedArray (t : CType) : Bool :=
  match t.canonical.unqual with | .array _ (some _) => true | _ => false

def isEnum (t : CType) : Bool :=
  match t.canonical.unqual with | .enum _ => true | _ => false

def isRecord (t : CType) : Bool :=
  match t.canonical.unqual with | .record _ => true | _ => false

def isFunctionPointer (t : CType) : Bool :=
  match t.canonical.unqual with | .ptr (.fn ..) => true | _ => false

def isMemberPointer (t : CType) : Bool :=
  match t.canonical.unqual with | .memPtr .. => true | _ => false

def isConst (t : CType) : Bool := t.canonical.topConst

/-- `Cpp::IsIntegral` (IA3: integer types, `bool`, the character types and enums). -/
def isIntegral (t : CType) : Bool :=
  match t.canonical.unqual with
  | .b k => k.isIntegerKind
  | .enum _ => true
  | _ => false

def isArithmetic (t : CType) : Bool :=
  match builtinKind? t with | some k => k.isArithmetic | none => false

def pointee (t : CType) : CType :=
  match t.canonical.unqual with | .ptr u => u | _ => .null

def arrayElem (t : CType) : CType :=
  match t.canonical.unqual with | .array e _ => e | _ => .null

def isObjectType (t : CType) : Bool :=
  match t.canonical.unqual with
  | .fn .. | .lref _ | .rref _ | .null => false
  | .b .void => false
  | _ => true

def isFunctionType (t : CType) : Bool :=
  match t.canonical.unqual with | .fn .. => true | _ => false

/-- Unscoped enum. -/
def isUnscopedEnum (w : World) (t : CType) : Bool :=
  match t.canonical.unqual with
  | .enum n => match w.findEnum n with | some e => !e.isScoped | none => false
  | _ => false

def enumUnderlying (w : World) (t : CType) : Builtin :=
  match t.canonical.unqual with
  | .enum n => (w.findEnum n).map (·.underlying) |>.getD .int
  | _ => .int

/-- `Cpp::IsTypeDerivedFrom`: a proper (transitive) base class. -/
partial def isDerivedFrom (w : World) (d b : CType) : Bool :=
  match d.canonical.unqual, b.canonical.unqual with
  | .record dn, .record bn =>
    if dn == bn then false
    else match w.findClass dn with
      | some c => c.bases.any fun x => x == bn || isDerivedFrom w (.record x) (.record bn)
      | none => false
  | _, _ => false

/-- `Cpp::GetUnderlyingType`: pointers, references and arrays stripped down to the element. -/
partial def underlyingType (t : CType) : CType :=
  match t.canonical.unqual with
  | .ptr u | .lref u | .rref u | .array u _ => underlyingType u
  | u => u

/-! ### Promotions and the usual arithmetic conversions ([conv.prom], [expr.arith.conv]) -/

/-- The promoted type of an arithmetic or unscoped-enum operand. -/
def promote (p : Platform) (w : World) (t : CType) : Option Builtin :=
  match t.canonical.unqual with
  | .b k =>
    if k.isFloating then some k
    else if !k.isIntegerKind then none
    else if k.rank < Builtin.rank .int || k == .bool then
      -- every value of a type narrower than int fits int (char16_t / char32_t / wchar_t aside)
      if Builtin.int.fits p (k.minVal p) && Builtin.int.fits p (k.maxVal p) then some .int else some .uint
    else if k == .wchar then some .int
    else if k == .char32 then some .uint
    else some k
  | .enum _ =>
    if isUnscopedEnum w t then
      let u := enumUnderlying w t
      if u.rank < Builtin.rank .int then some .int else some u
    else none
  | _ => none

/-- The common type of two promoted arithmetic types. -/
def usualArith (p : Platform) (a b : Builtin) : Builtin :=
  if a == .ldouble || b == .ldouble then .ldouble
  else if a == .double || b == .double then .double
  else if a == .float || b == .float then .float
  else if a == b then a
  else if a.isSigned p == b.isSigned p then (if a.rank ≥ b.rank then a else b)
  else
    let (s, u) := if a.isSigned p then (a, b) else (b, a)
    if u.rank ≥ s.rank then u
    else if s.fits p (u.minVal p) && s.fits p (u.maxVal p) then s
    else s.toUnsigned

end Cxx

end Jank.Interop
