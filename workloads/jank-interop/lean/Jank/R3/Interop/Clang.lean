import Jank.Interop.Search

/-!
# What Clang answers when CppInterOp asks (round 3)

CppInterOp 28b0830d (`deps/cppinterop/lib/CppInterOp/CppInterOp.cpp`) wraps Clang. Where a
CppInterOp function reads the AST (type kinds, pointees, scopes) its answer is replicated from its
own code in `CppInterOp.lean`. Where it hands a synthesized expression to Sema
(`TryImplicitConversion`, `BuildTypeTrait`, `BuildCStyleCastExpr`, `UsualArithmeticConversions`,
`FindCompositePointerType`, `CreateBuiltin{Unary,Bin}Op`, `AddOverloadCandidate`,
`BestViableFunction`), this file answers as Sema does, read from Clang at `llvmorg-23.1.0` (the
LLVM that jank's flake pins through nixpkgs 02f5696b, `llvmPackages_23` = 23.1.0) where the
deciding lines were fetched into `deps/llvm-23.1.0/` (`Type.cpp`, `SemaExpr.cpp`,
`SemaOverload.cpp`, `SemaCast.cpp`, `SemaTemplate.cpp`, `TemplateBase.cpp`, `APSInt.cpp`), and
by the C++20 standard elsewhere (`-std=gnu++20`, util/clang.cpp:347). Each standard-modeled answer
carries an assumption id (CXA...).

The type universe is round 2's `CType`/`World` (`Jank/Interop/Cxx.lean`), so every answer can be
compared one-for-one with round 2's (`Census.lean`). `XWorld` adds the facts round 2's world does
not carry (Library gap: inheritance access, explicit conversion functions, static members, function
templates, fixed enums).
-/

namespace Jank.R3.Interop

open Jank.Interop

/-- Clang `ExprValueKind` of a synthesized operand. -/
inductive VK where
  | prvalue | lvalue | xvalue
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A function template, as far as deduction from call arguments and explicit arguments goes:
parameter `i` is the template parameter itself by value (`.param`), a fixed type (`.fixed t`), and
the return type is the parameter or fixed. `tparams` template type parameters, `T0`, `T1`, ... -/
inductive TPat where
  | param (i : Nat)
  | fixed (t : CType)
  deriving Repr, BEq, Inhabited

structure FnTemplate where
  name : String
  tparams : Nat
  params : List TPat
  ret : TPat
  deriving Repr, BEq, Inhabited

/-- Round 2's world plus the declarations round 3's worlds need. -/
structure XWorld where
  w : World := world0
  /-- (derived, base) pairs inherited non-publicly. -/
  privateBases : List (String × String) := []
  /-- (class, target): `explicit operator target()`. -/
  explicitConvertsTo : List (String × CType) := []
  /-- Static data members: (class, name, type). -/
  staticFields : List (String × String × CType) := []
  /-- Unscoped enums whose underlying type is fixed (`enum e : T`). -/
  fixedEnums : List String := []
  /-- Function templates (global namespace), in declaration order. -/
  templates : List FnTemplate := []
  deriving Inhabited

def XWorld.findClass (x : XWorld) (n : String) : Option ClassDecl := x.w.findClass n
def XWorld.findEnum (x : XWorld) (n : String) : Option EnumDecl := x.w.findEnum n

namespace Clang

/-! ## Type views (clang/lib/AST/Type.cpp) -/

/-- Top-level sugar and qualifiers removed: what `QT->isX()` and `getAs<X>()` look at. -/
def view : CType → CType
  | .alias _ t => view t
  | .cv _ _ t => view t
  | t => t

def builtin? (t : CType) : Option Builtin := match view t with | .b k => some k | _ => none
/-- `Type::isBuiltinType`: `isa<BuiltinType>(CanonicalType)`. -/
def isBuiltinType (t : CType) : Bool := match view t with | .b _ => true | _ => false
/-- `Type::isIntegralType` in C++ (Type.cpp:2160): a builtin integer (`bool`, the character types
and the integers); never an enumeration. -/
def isIntegralType (t : CType) : Bool := match view t with | .b k => k.isIntegerKind | _ => false
def isIntegralOrEnumerationType (t : CType) : Bool :=
  match view t with | .b k => k.isIntegerKind | .enum _ => true | _ => false
def isFloatingType (t : CType) : Bool := match view t with | .b k => k.isFloating | _ => false
def isEnumeralType (t : CType) : Bool := match view t with | .enum _ => true | _ => false
def isPointerType (t : CType) : Bool := match view t with | .ptr _ => true | _ => false
def isMemberPointerType (t : CType) : Bool := match view t with | .memPtr .. => true | _ => false
def isArrayType (t : CType) : Bool := match view t with | .array .. => true | _ => false
def isReferenceType (t : CType) : Bool := match view t with | .lref _ | .rref _ => true | _ => false
def isLValueReferenceType (t : CType) : Bool := match view t with | .lref _ => true | _ => false
def isRValueReferenceType (t : CType) : Bool := match view t with | .rref _ => true | _ => false
def isNullPtrType (t : CType) : Bool := match view t with | .b .nullptr => true | _ => false
def isVoidType (t : CType) : Bool := match view t with | .b .void => true | _ => false
def isRecordType (t : CType) : Bool := match view t with | .record _ => true | _ => false
def isFunctionType (t : CType) : Bool := match view t with | .fn .. => true | _ => false
def isFunctionPointerType (t : CType) : Bool :=
  match view t with | .ptr u => isFunctionType u | _ => false

/-- `QualType::isConstQualified`: local qualifiers or those reached through typedef sugar. -/
def isConstQualified : CType → Bool
  | .cv c _ t => c || isConstQualified t
  | .alias _ t => isConstQualified t
  | _ => false

def isVolatileQualified : CType → Bool
  | .cv _ v t => v || isVolatileQualified t
  | .alias _ t => isVolatileQualified t
  | _ => false

/-- `QualType::getNonReferenceType`. -/
def nonRef (t : CType) : CType := match view t with | .lref u | .rref u => u | _ => t

/-- `Type::getPointeeType` (Type.cpp:789): pointers, references and member pointers. -/
def pointeeOf (t : CType) : CType :=
  match view t with
  | .ptr u | .lref u | .rref u | .memPtr _ u => u
  | _ => .null

/-- `ASTContext::getAsConstantArrayType(QT)->getElementType()`: the array's qualifiers pushed to
the element. -/
def arrayElemQ (c v : Bool) : CType → Option CType
  | .alias _ t => arrayElemQ c v t
  | .cv c' v' t => arrayElemQ (c || c') (v || v') t
  | .array e _ => some (CType.mkCv c v e)
  | _ => none

def arrayElem (t : CType) : CType := (arrayElemQ false false t).getD .null

/-- Unscoped enum `n`. -/
def isUnscoped (x : XWorld) (n : String) : Bool :=
  match x.findEnum n with | some e => !e.isScoped | none => false

/-- `Type::isArithmeticType` (Type.cpp:2426): arithmetic builtins and complete unscoped enums. -/
def isArithmeticType (x : XWorld) (t : CType) : Bool :=
  match view t with
  | .b k => k.isArithmetic
  | .enum n => isUnscoped x n
  | _ => false

/-- `isIntegralOrUnscopedEnumerationType`. -/
def isIntegralOrUnscopedEnum (x : XWorld) (t : CType) : Bool :=
  match view t with
  | .b k => k.isIntegerKind
  | .enum n => isUnscoped x n
  | _ => false

/-! ## Promotions and the usual arithmetic conversions -/

/-- The promotion type of an unscoped enum (Sema::ActOnEnumBody's `BestPromotionType`): a fixed
underlying type promotes like that type; otherwise `int` when every enumerator fits `int`
(C++ [conv.prom]/3), else the underlying type. CXA2: round 2's `promote` gave `color` (underlying
`unsigned int`, values 0 and 1) the promotion `unsigned int`; Clang gives `int`. -/
def enumPromotion (p : Platform) (x : XWorld) (n : String) : Option Builtin :=
  match x.findEnum n with
  | none => none
  | some e =>
    if e.isScoped then none
    else if x.fixedEnums.contains n then
      (Cxx.promote p x.w (.b e.underlying))
    else if e.constants.all (fun (_, v) => Builtin.int.fits p v) then some .int
    else some e.underlying

/-- Integral and floating promotions ([conv.prom], [conv.fpprom]) of an operand's type; floating
types stay (C++ has no float → double promotion here). -/
def promote (p : Platform) (x : XWorld) (t : CType) : Option Builtin :=
  match view t with
  | .b k => Cxx.promote p x.w (.b k)
  | .enum n => enumPromotion p x n
  | _ => none

/-- `Sema::UsualArithmeticConversions` (SemaExpr.cpp:1707) on two arithmetic operands: both
promoted, then the common type. -/
def usualArithmetic (p : Platform) (x : XWorld) (a b : CType) : Option CType :=
  match promote p x a, promote p x b with
  | some i, some j => some (.b (Cxx.usualArith p i j))
  | _, _ => none

/-! ## Standard conversion sequences (SemaOverload.cpp:2340 `IsStandardConversion`) -/

/-- What overload ranking needs of a standard conversion sequence. -/
structure SCS where
  rank : Cxx.Rank
  /-- Second and Third are both identity (`isIdentityConversion`). -/
  identity : Bool
  ptrToBool : Bool := false
  /-- A derived-to-base pointer or class conversion. -/
  derivedToBase : Bool := false
  refBinding : Bool := false
  bindsToRvalue : Bool := false
  isLvalueRef : Bool := false
  /-- For a reference binding: the referenced type is the source type exactly (cv included). -/
  sameRefType : Bool := false
  /-- cv-qualifier count of the referenced type ([over.ics.rank] 3.2.6). -/
  refCv : Nat := 0
  deriving Repr, BEq, Inhabited

inductive ICS where
  | std (s : SCS)
  | user (after : SCS)
  | bad
  deriving Repr, BEq, Inhabited

def ICS.ok : ICS → Bool | .bad => false | _ => true

def cvCount (t : CType) : Nat := (if isConstQualified t then 1 else 0) + (if isVolatileQualified t then 1 else 0)

/-- cv of `a` covers cv of `b`. -/
def cvCovers (a b : CType) : Bool :=
  (isConstQualified a || !isConstQualified b) && (isVolatileQualified a || !isVolatileQualified b)

/-- Class inheritance (`CXXRecordDecl::isDerivedFrom`, any access, proper base). -/
def derivedFrom (x : XWorld) (d b : CType) : Bool := Cxx.isDerivedFrom x.w (view d) (view b)

/-- An expression's type after the lvalue transformations (array/function decay). -/
def decayed (t : CType) : CType :=
  match view t with
  | .array .. => .ptr (arrayElem t)
  | .fn r ps => .ptr (.fn r ps)
  | u => u

/-- `IsStandardConversion` from an expression of non-reference type `src` and kind `vk` to the
non-reference, non-class type `dst`. CXA3: the conversion kinds follow round 2's `stdConv`
([conv]), with the enum promotion of `enumPromotion` and the null pointer constant rule (an
expression of type `std::nullptr_t` is a null pointer constant; a synthesized operand of any other
type is not). -/
def standardConv (p : Platform) (x : XWorld) (src : CType) (_vk : VK) (dst : CType) : Option SCS :=
  let s := (decayed src).canonical.unqual
  let d := dst.canonical.unqual
  let mk (r : Cxx.Rank) (ident : Bool) : Option SCS := some { rank := r, identity := ident }
  if isRecordType s || isRecordType d then none
  else if s == d then mk .exact true
  else match s, d with
  | .b sk, .b dk =>
    if sk == .void || dk == .void || dk == .nullptr then none
    else if sk == .nullptr then none
    else if dk == .bool then
      (if sk.isArithmetic then some { rank := .conversion, identity := false } else none)
    else if sk.isArithmetic && dk.isArithmetic then
      if (Cxx.promote p x.w s == some dk) || (sk == .float && dk == .double) then mk .promotion false
      else mk .conversion false
    else none
  | .enum n, .b dk =>
    if !isUnscoped x n || !dk.isArithmetic then none
    else if dk == .bool then some { rank := .conversion, identity := false }
    else if enumPromotion p x n == some dk then mk .promotion false
    else mk .conversion false
  | .b .nullptr, .ptr _ => mk .conversion false
  | .b .nullptr, .memPtr .. => mk .conversion false
  | .ptr _, .b .bool => some { rank := .conversion, identity := false, ptrToBool := true }
  | .memPtr .., .b .bool => some { rank := .conversion, identity := false, ptrToBool := true }
  | .ptr a, .ptr b =>
    let a' := a.canonical
    let b' := b.canonical
    if a'.unqual == b'.unqual && cvCovers b' a' then mk .exact false
    else if b'.unqual == .b .void && cvCovers b' a' && Cxx.isObjectType a' then mk .conversion false
    else if derivedFrom x a'.unqual b'.unqual && cvCovers b' a' then
      some { rank := .conversion, identity := false, derivedToBase := true }
    else none
  | _, _ => none

/-! ## Reference binding and user-defined conversions -/

/-- Reference-compatible: `cv1 T1` vs `cv2 T2` ([dcl.init.ref]/4). -/
def refCompatible (x : XWorld) (t1 t2 : CType) : Bool :=
  let a := t1.canonical
  let b := t2.canonical
  (a.unqual == b.unqual || derivedFrom x b.unqual a.unqual) && cvCovers a b

/-- Reference-related ([dcl.init.ref]/4): the same class or a base, ignoring cv. -/
def refRelated (x : XWorld) (t1 t2 : CType) : Bool :=
  let a := t1.canonical.unqual
  let b := t2.canonical.unqual
  a == b || derivedFrom x b a

mutual

/-- A user-defined conversion from an expression (`src`, `vk`) to `dst` ([over.ics.user],
`IsUserDefinedConversion`): a converting constructor of `dst` (explicit ones only when
`allowExplicit`), or a conversion function of `src` (explicit ones only when `allowExplicit`).
The first standard conversion inside it must not itself be user-defined. -/
partial def userConv (p : Platform) (x : XWorld) (allowExplicit : Bool) (src : CType) (vk : VK)
    (dst : CType) : Option SCS :=
  let d := (nonRef dst).canonical.unqual
  let s := src.canonical.unqual
  let byCtor : Bool := match d with
    | .record n =>
      match x.findClass n with
      | some c => c.ctors.any fun f =>
          (allowExplicit || !f.isExplicit) && !f.isDeleted && f.initListElem.isNone &&
          f.params.length ≥ 1 && f.required ≤ 1 &&
          (match f.params with
           | ptype :: _ => (paramConv p x true src vk ptype).ok
           | [] => false)
      | none => false
    | _ => false
  let fns : List CType := match s with
    | .record n =>
      ((x.findClass n).map (·.convertsTo) |>.getD []) ++
        (if allowExplicit then (x.explicitConvertsTo.filter (·.1 == n)).map (·.2) else [])
    | _ => []
  let byFn := fns.findSome? fun u => if isRecordType dst then
      (if (nonRef u).canonical.unqual == d then some { rank := .exact, identity := true : SCS } else none)
    else standardConv p x u .prvalue (nonRef dst)
  if byCtor then some { rank := .exact, identity := true } else byFn

/-- `TryCopyInitialization` of a parameter of type `param` from an argument expression
(`src` non-reference, value kind `vk`): reference binding ([dcl.init.ref], [over.ics.ref]) or
copy-initialization ([over.best.ics]); `suppressUser` forbids user-defined conversions. -/
partial def paramConv (p : Platform) (x : XWorld) (suppressUser : Bool) (src : CType) (vk : VK)
    (param : CType) : ICS :=
  let viaValue (target : CType) (bindRv : Bool) (isRefB : Bool) (lref : Bool) : ICS :=
    if isRecordType target then
      if (view src).canonical.unqual == (view target).canonical.unqual then
        .std { rank := .exact, identity := true, refBinding := isRefB, bindsToRvalue := bindRv,
               isLvalueRef := lref }
      else if derivedFrom x (view src) (view target) then
        .std { rank := .conversion, identity := false, derivedToBase := true,
               refBinding := isRefB, bindsToRvalue := bindRv, isLvalueRef := lref }
      else if suppressUser then .bad
      else match userConv p x false src vk target with
        | some s => .user { s with refBinding := isRefB, bindsToRvalue := bindRv, isLvalueRef := lref }
        | none => .bad
    else match standardConv p x src vk target with
      | some s => .std { s with refBinding := isRefB, bindsToRvalue := bindRv, isLvalueRef := lref }
      | none =>
        if suppressUser then .bad
        else match userConv p x false src vk target with
          | some s => .user { s with refBinding := isRefB, bindsToRvalue := bindRv, isLvalueRef := lref }
          | none => .bad
  match view param with
  | .lref u =>
    let direct := vk == .lvalue && refCompatible x u src
    if direct then
      let same := (u.canonical) == src.canonical
      .std { rank := (if (u.canonical.unqual == src.canonical.unqual) then .exact else .conversion),
             identity := u.canonical.unqual == src.canonical.unqual,
             derivedToBase := u.canonical.unqual != src.canonical.unqual,
             refBinding := true, isLvalueRef := true, sameRefType := same, refCv := cvCount u }
    else if isConstQualified u && !isVolatileQualified u then
      if refRelated x u src && !refCompatible x u src then .bad
      else if vk != .lvalue && refCompatible x u src then
        .std { rank := (if u.canonical.unqual == src.canonical.unqual then .exact else .conversion),
               identity := u.canonical.unqual == src.canonical.unqual,
               refBinding := true, bindsToRvalue := true, isLvalueRef := true,
               sameRefType := u.canonical == src.canonical, refCv := cvCount u }
      else match viaValue u true true true with
        | .std s => .std { s with refCv := cvCount u }
        | .user s => .user { s with refCv := cvCount u }
        | .bad => .bad
    else .bad
  | .rref u =>
    if refRelated x u src && (vk == .lvalue || !refCompatible x u src) then .bad
    else if vk != .lvalue && refCompatible x u src then
      .std { rank := (if u.canonical.unqual == src.canonical.unqual then .exact else .conversion),
             identity := u.canonical.unqual == src.canonical.unqual,
             refBinding := true, bindsToRvalue := true, sameRefType := u.canonical == src.canonical,
             refCv := cvCount u }
    else match viaValue u true true false with
      | .std s => .std { s with refCv := cvCount u }
      | .user s => .user { s with refCv := cvCount u }
      | .bad => .bad
  | _ => viaValue param false false false

end

/-- `Sema::TryImplicitConversion` as `Cpp::IsImplicitlyConvertible` calls it (CppInterOp.cpp:639):
the source is a prvalue `OpaqueValueExpr` of the non-reference source type, `AllowedExplicit::All`
(explicit constructors and conversion functions count), and the target is taken as given: a
reference target type has no standard conversion (SemaOverload.cpp:2663 `CanonFrom == CanonTo`
never holds for it) and only a class source with a conversion function to it could reach it. -/
def tryImplicitConversion (p : Platform) (x : XWorld) (src dst : CType) : Bool :=
  let s := nonRef src
  if isReferenceType dst then
    -- user-defined: only conversion functions of a class source (`operator T&`); the model's
    -- classes declare none returning references.
    false
  else if isRecordType dst then
    (view s).canonical.unqual == (view dst).canonical.unqual || derivedFrom x (view s) (view dst) ||
      (userConv p x true s .prvalue dst).isSome
  else if isRecordType s then (userConv p x true s .prvalue dst).isSome
  else (standardConv p x s .prvalue dst).isSome

/-- `std::is_constructible<To, From>` (`BuildTypeTrait(TT_IsConstructible)`, CppInterOp.cpp:690):
`To t(declval<From>())`, where `declval<From>()` is an lvalue for `From = U&`, else an xvalue.
Direct-initialization: explicit constructors and conversion functions count; a non-class target
from a non-class source takes any standard conversion; `bool` from `std::nullptr_t` is allowed
([dcl.init.general]/16.9). CXA4: C++20 parenthesized aggregate initialization is not modeled
(no searched program constructs an aggregate from one argument). -/
def isConstructibleTrait (p : Platform) (x : XWorld) (to src : CType) : Bool :=
  let vk : VK := if isLValueReferenceType src then .lvalue else .xvalue
  let s := nonRef src
  if isReferenceType to then (paramConv p x false s vk to).ok
  else if isRecordType to then
    (view s).canonical.unqual == (view to).canonical.unqual || derivedFrom x (view s) (view to) ||
      (userConv p x true s vk to).isSome
  else if isRecordType s then (userConv p x true s vk to).isSome
  else if isVoidType to then false
  else (standardConv p x s vk to).isSome || (isNullPtrType s && builtin? to == some .bool)

/-- `std::is_assignable<To&, From&&>` (CppInterOp.cpp:718). For a non-class `To`: a non-const
lvalue, assigned an implicit conversion of the source; for a class: its implicit copy/move
assignment from a source converted to it (CXA5: the model's classes declare no other
`operator=`). -/
def isAssignableTrait (p : Platform) (x : XWorld) (to src : CType) : Bool :=
  let t := nonRef to
  if isConstQualified t then false
  else if isRecordType t then (paramConv p x false (nonRef src) .xvalue (.rref (view t).canonical.unqual)).ok
  else (paramConv p x false (nonRef src) .xvalue (view t).canonical.unqual).ok

/-! ## The composite pointer type (`Sema::FindCompositePointerType`, [expr.type]/4) -/

def isPointerLike (t : CType) : Bool := isPointerType t || isMemberPointerType t || isNullPtrType t

/-- On decayed operand types. A `std::nullptr_t` operand is a null pointer constant. -/
def compositePointer (x : XWorld) (a b : CType) : Option CType :=
  let a := (decayed a).canonical.unqual
  let b := (decayed b).canonical.unqual
  if !isPointerLike a && !isPointerLike b then none
  else if isPointerLike a && isNullPtrType b then some a
  else if isPointerLike b && isNullPtrType a then some b
  else if !isPointerLike a || !isPointerLike b then none
  else match a, b with
  | .ptr u, .ptr v =>
    let u' := u.canonical
    let v' := v.canonical
    let c := isConstQualified u' || isConstQualified v'
    let vo := isVolatileQualified u' || isVolatileQualified v'
    if u'.unqual == v'.unqual then some (.ptr (CType.mkCv c vo u'.unqual))
    else if u'.unqual == .b .void && Cxx.isObjectType v' then some (.ptr (CType.mkCv c vo (.b .void)))
    else if v'.unqual == .b .void && Cxx.isObjectType u' then some (.ptr (CType.mkCv c vo (.b .void)))
    else if derivedFrom x u'.unqual v'.unqual then some (.ptr (CType.mkCv c vo v'.unqual))
    else if derivedFrom x v'.unqual u'.unqual then some (.ptr (CType.mkCv c vo u'.unqual))
    else none
  | .memPtr c1 t1, .memPtr c2 t2 =>
    if c1 == c2 && t1.canonical == t2.canonical then some a else none
  | _, _ => none

/-! ## C-style casts (`Sema::BuildCStyleCastExpr`, [expr.cast]) on a given operand -/

/-- An operand of a cast: its type, and whether it is a null pointer constant (an integer literal
`0`, or anything of type `std::nullptr_t`). -/
structure Operand where
  type : CType
  npc : Bool
  deriving Inhabited

/-- `static_cast<dst>(e)` ([expr.static.cast]). CXA6: modeled from the standard. -/
def staticCastOk (p : Platform) (x : XWorld) (e : Operand) (dst : CType) : Bool :=
  let s := (decayed e.type).canonical.unqual
  let d := dst.canonical.unqual
  if isConstructibleTrait p x dst e.type then true
  else if d == .b .void then true
  else if e.npc && (isPointerType d || isMemberPointerType d || isNullPtrType d) then true
  else match s, d with
  | .ptr a, .ptr b =>
    let a' := a.canonical
    let b' := b.canonical
    if a'.unqual == .b .void then Cxx.isObjectType b' && cvCovers b' a'
    else derivedFrom x b'.unqual a'.unqual && cvCovers b' a'
  | .b sk, .b dk => sk.isArithmetic && dk.isArithmetic
  | .enum _, .b dk => dk.isArithmetic
  | .b sk, .enum _ => sk.isArithmetic
  | .enum _, .enum _ => true
  | _, _ => false

/-- `reinterpret_cast<dst>(e)` ([expr.reinterpret.cast]) on prvalues. -/
def reinterpretOk (e : Operand) (dst : CType) : Bool :=
  let s := (decayed e.type).canonical.unqual
  let d := dst.canonical.unqual
  match s, d with
  | .ptr _, .ptr _ => true
  | .ptr _, .b dk => dk.isIntegerKind && dk.width ≥ 64
  | .b sk, .ptr _ => sk.isIntegerKind
  | .enum _, .ptr _ => true
  | .b .nullptr, .b dk => dk.isIntegerKind && dk.width ≥ 64
  | .memPtr _ a, .memPtr _ b => isFunctionType a == isFunctionType b
  | _, _ => s == d && (isPointerType s || isMemberPointerType s || isIntegralOrEnumerationType s)

/-- A C-style cast `(dst)e` ([expr.cast]/4): a `const_cast`, a `static_cast`, a
`reinterpret_cast`, each possibly followed by a `const_cast` (pointer constness stripped). -/
def cStyleCastOk (p : Platform) (x : XWorld) (e : Operand) (dst : CType) : Bool :=
  let stripPtr (t : CType) : CType := match (view t).canonical.unqual with
    | .ptr u => .ptr u.canonical.unqual
    | u => u
  staticCastOk p x e dst || staticCastOk p x { e with type := stripPtr (decayed e.type) } (stripPtr dst) ||
    reinterpretOk e dst

/-! ## Built-in operators on synthesized operands (`CreateBuiltin{Unary,Bin}Op`) -/

/-- An operand: its non-reference type and whether it is an lvalue. -/
structure Opnd where
  type : CType
  lvalue : Bool
  deriving Inhabited

/-- The result type of a built-in operator ([expr.*]), or null. Class operands: only `=` between
the same class has built-in meaning (`CheckAssignmentOperands` treats C++ classes like C structs
after `CheckSingleAssignmentConstraints`, SemaExpr.cpp:10226; same canonical unqualified type is
`Compatible`, SemaExpr.cpp:9693). CXA7: the other operators follow [expr]. -/
def builtinOp (p : Platform) (x : XWorld) (op : Cxx.Op) (args : List Opnd) : CType :=
  let arithT (t : CType) := isArithmeticType x t
  match args with
  | [a] =>
    let t := a.type
    match op with
    | .amp => if a.lvalue then .ptr t else .null
    | .star => match decayed t with | .ptr u => (if isVoidType u then .null else .lref u) | _ => .null
    | .exclaim => if arithT t || isPointerType (decayed t) || isMemberPointerType t then .b .bool else .null
    | .minus | .plus =>
      match promote p x t with
      | some k => .b k
      | none => if op == .plus && isPointerType (decayed t) then decayed t else .null
    | .tilde => match promote p x t with
      | some k => if k.isIntegerKind then .b k else .null
      | none => .null
    | .plusPlus | .minusMinus =>
      if a.lvalue && !isConstQualified t && ((arithT t && !isEnumeralType t && builtin? t != some .bool) || isPointerType t)
      then .lref t.canonical else .null
    | _ => .null
  | [a, b] =>
    let ta := a.type
    let tb := b.type
    let arith := if arithT ta && arithT tb then usualArithmetic p x ta tb else none
    let integralK (k : Builtin) := k.isIntegerKind
    match op with
    | .plus | .minus | .star | .slash =>
      match arith with
      | some k => k
      | none =>
        if (op == .plus || op == .minus) && isPointerType (decayed ta) && isIntegralOrUnscopedEnum x tb then decayed ta
        else if op == .plus && isIntegralOrUnscopedEnum x ta && isPointerType (decayed tb) then decayed tb
        else if op == .minus && isPointerType (decayed ta) && isPointerType (decayed tb) then .b .long
        else .null
    | .percent | .amp | .pipe | .caret =>
      match arith with | some (.b k) => if integralK k then .b k else .null | _ => .null
    | .lessLess | .greaterGreater =>
      match promote p x ta, promote p x tb with
      | some i, some j => if integralK i && integralK j then .b i else .null
      | _, _ => .null
    | .equalEqual | .exclaimEqual | .greater | .less | .greaterEqual | .lessEqual =>
      if arith.isSome || (compositePointer x ta tb).isSome then .b .bool else .null
    | .ampAmp | .pipePipe =>
      let ok (t : CType) := arithT t || isPointerType (decayed t) || isMemberPointerType t
      if ok ta && ok tb then .b .bool else .null
    | .equal =>
      if !a.lvalue || isConstQualified ta || isArrayType ta || isVoidType ta || isFunctionType ta then .null
      else if isRecordType ta then
        (if (view ta).canonical.unqual == (view tb).canonical.unqual then ta else .null)
      else if (paramConv p x false tb (if b.lvalue then .lvalue else .prvalue) (view ta).canonical.unqual).ok
        || (isPointerType ta && isNullPtrType tb) then ta
      else .null
    | .plusEqual | .minusEqual | .starEqual | .slashEqual | .percentEqual | .ampEqual
    | .pipeEqual | .caretEqual | .lessLessEqual | .greaterGreaterEqual =>
      if a.lvalue && !isConstQualified ta && arithT ta && !isEnumeralType ta && arith.isSome then ta
      else if a.lvalue && (op == .plusEqual || op == .minusEqual) && isPointerType ta && isIntegralOrUnscopedEnum x tb then ta
      else .null
    | .subscript =>
      match decayed ta with
      | .ptr u => if isIntegralOrUnscopedEnum x tb then .lref u else .null
      | _ => .null
    | _ => .null
  | _ => .null

/-! ## Overload resolution (`AddOverloadCandidate`, `BestViableFunction`, [over.match]) -/

/-- [over.ics.rank]/3.2: is standard sequence `a` better than `b`. -/
def betterSCS (a b : SCS) : Bool :=
  if a.rank.ord < b.rank.ord then true
  else if b.rank.ord < a.rank.ord then false
  -- 3.2.1: a proper subsequence (identity beats a qualification adjustment)
  else if a.identity && !b.identity && a.rank == .exact then true
  -- 4.1: not converting a pointer to bool beats converting one
  else if !a.ptrToBool && b.ptrToBool then true
  -- 3.2.3: rvalue reference binding to an rvalue beats an lvalue reference binding
  else if a.refBinding && b.refBinding && a.bindsToRvalue && b.bindsToRvalue && !a.isLvalueRef && b.isLvalueRef then true
  -- 3.2.6: both reference bindings to the same type, `a` less cv-qualified
  else if a.refBinding && b.refBinding && a.bindsToRvalue == b.bindsToRvalue && a.refCv < b.refCv then true
  else false

def betterICS (a b : ICS) : Bool :=
  match a, b with
  | .std s, .std t => betterSCS s t
  | .std _, .user _ => true
  | .user s, .user t => betterSCS s t
  | _, _ => false

/-- A candidate: the function (template instantiations carry `fromTemplate`), and its implicit
conversion sequences, one per argument (the implicit object first for a member). -/
structure Cand where
  fn : FnDecl
  fromTemplate : Bool := false
  ics : List ICS
  viable : Bool
  deriving Inhabited

/-- [over.match.best]/2: `a` is better than `b`. -/
def betterCand (a b : Cand) : Bool :=
  let pairs := a.ics.zip b.ics
  let noWorse := pairs.all fun (i, j) => !betterICS j i
  let someBetter := pairs.any fun (i, j) => betterICS i j
  noWorse && (someBetter || (!a.fromTemplate && b.fromTemplate))

/-- `OverloadCandidateSet::BestViableFunction` (SemaOverload.cpp): the first viable candidate
improved by every later one that is better, then every viable candidate the best is not better
than is gathered transitively (`Cand->Best`); more than one gathered is `OR_Ambiguous`. CXA8:
Clang 21+'s deferred template deduction (a perfect non-template match skips the templates) gives
the same answer as the full comparison for the model's candidates. Returns the best (or none) and
the gathered set. -/
def bestViable (cands : List Cand) : Option Cand × List Cand := Id.run do
  let viable := cands.filter (·.viable)
  match viable with
  | [] => return (none, [])
  | c0 :: rest =>
    let best := rest.foldl (fun b c => if betterCand c b then c else b) c0
    -- the transitive closure of "best is not better than"
    let mut gathered : List Cand := [best]
    let mut pending : List Cand := [best]
    let mut fuel := viable.length * viable.length + 1
    while !pending.isEmpty && fuel > 0 do
      fuel := fuel - 1
      let cur := pending.head!
      pending := pending.tail
      for c in viable do
        if !(gathered.any fun g => g.fn == c.fn) && !betterCand cur c then
          gathered := gathered ++ [c]
          pending := pending ++ [c]
    if gathered.length == 1 then return (some best, gathered) else return (none, gathered)

end Clang

end Jank.R3.Interop
