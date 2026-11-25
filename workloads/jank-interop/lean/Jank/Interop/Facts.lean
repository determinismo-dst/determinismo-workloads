import Jank.Interop.Cxx

/-!
# Conversions, overload resolution and builtin operators, as Clang's Sema decides them

The answers CppInterOp's `IsImplicitlyConvertible`, `IsConstructible`, `IsCStyleConvertible`,
`GetCommonType`, `GetBuiltinOperatorType` and `BestOverloadMatch` give, modeled from the C++20
standard on the types of `Cxx.lean`. Also the spec-side predicates the standard defines and jank
never asks for: `static_cast` validity ([expr.static.cast]) and list-initialization narrowing
([dcl.init.list]).
-/

namespace Jank.Interop.Cxx



/-- An implicit conversion sequence's rank ([over.ics.rank]). -/
inductive Rank where
  | exact | promotion | conversion | userDefined
  deriving Repr, BEq, DecidableEq, Inhabited

def Rank.ord : Rank → Nat
  | .exact => 0 | .promotion => 1 | .conversion => 2 | .userDefined => 3

variable (p : Platform) (w : World)

/-- Array-to-pointer and function-to-pointer decay of an expression's type. -/
def decay (t : CType) : CType :=
  match t.canonical.unqual with
  | .array e _ => .ptr e
  | .fn r ps => .ptr (.fn r ps)
  | u => u

/-- cv of `a` is at least cv of `b`. -/
def cvCovers (a b : CType) : Bool :=
  (a.topConst || !b.topConst) && (a.topVolatile || !b.topVolatile)

/-- A standard conversion sequence from an expression of (non-reference) type `src` to the
non-reference type `dst` ([conv]); `none` when there is none. -/
def stdConv (src dst : CType) : Option Rank :=
  let s := decay src
  let d := dst.canonical.unqual
  if s == d then some .exact
  else match s, d with
  | .b sk, .b dk =>
    if sk == .void || dk == .void then none
    else if sk == .nullptr then (if dk == .nullptr then some .exact else none)
    else if dk == .nullptr then none
    else if dk == .bool then (if sk.isArithmetic then some .conversion else none)
    else if sk.isArithmetic && dk.isArithmetic then
      if (promote p w s == some dk && sk != dk) || (sk == .float && dk == .double) then some .promotion
      else some .conversion
    else none
  | .enum _, .b dk =>
    if isUnscopedEnum w s && dk.isArithmetic then
      if promote p w s == some dk then some .promotion else some .conversion
    else none
  | .b .nullptr, .ptr _ => some .conversion
  | .b .nullptr, .memPtr .. => some .conversion
  | .ptr _, .b .bool => some .conversion
  | .ptr a, .ptr b =>
    let a' := a.canonical
    let b' := b.canonical
    if a'.unqual == b'.unqual && cvCovers b' a' then some .exact
    else if (b'.unqual == .b .void) && cvCovers b' a' && isObjectType a' then some .conversion
    else if isDerivedFrom w a'.unqual b'.unqual && cvCovers b' a' then some .conversion
    else none
  | .record a, .record b =>
    if a == b then some .exact
    else if isDerivedFrom w (.record a) (.record b) then some .conversion
    else none
  | _, _ => none

/-- A user-defined conversion ([over.ics.user]) to `dst` from `src`: a non-explicit converting
constructor of `dst` (`explicitOk`: any constructor, direct-initialization), or a conversion
function of `src`. -/
def userConv (explicitOk : Bool) (src dst : CType) : Bool :=
  let d := dst.canonical.unqual
  let s := (decay src)
  let byCtor := match d with
    | .record n =>
      match w.findClass n with
      | some c => c.ctors.any fun f =>
          (explicitOk || !f.isExplicit) && !f.isDeleted && f.initListElem.isNone &&
          f.params.length ≥ 1 && f.required ≤ 1 &&
          (match f.params with
           | ptype :: _ =>
             let pt := nonRef ptype
             -- the copy/move constructors of the class itself are not converting here
             !(pt.canonical.unqual == d) && (stdConv p w s pt).isSome
           | [] => false)
      | none => false
    | _ => false
  let byFn := match s with
    | .record n =>
      match w.findClass n with
      | some c => c.convertsTo.any fun u => (stdConv p w u dst).isSome
      | none => false
    | _ => false
  byCtor || byFn

/-- The implicit conversion sequence initializing a parameter of type `param` from an argument
whose type is `arg` (a reference type means an lvalue of the referred type, else a prvalue). -/
def implicitConv (arg param : CType) : Option Rank :=
  let argIsLvalue := match arg.canonical with | .lref _ => true | _ => false
  let src := (nonRef arg).canonical
  match param.canonical with
  | .lref u =>
    let u' := u.canonical
    let direct := argIsLvalue && (src.unqual == u'.unqual || isDerivedFrom w src.unqual u'.unqual)
                  && cvCovers u' src
    if direct then some (if src.unqual == u'.unqual then .exact else .conversion)
    else if u'.topConst && !u'.topVolatile then
      match stdConv p w src u' with
      | some r => some r
      | none => if userConv p w false src u' then some .userDefined else none
    else none
  | .rref u =>
    if argIsLvalue then none
    else match stdConv p w src u.canonical with
      | some r => some r
      | none => if userConv p w false src u then some .userDefined else none
  | d =>
    match stdConv p w src d with
    | some r => some r
    | none => if userConv p w false src d then some .userDefined else none

/-- `Cpp::IsImplicitlyConvertible(from, to)`: copy-initialization of a `to` from a `from`. -/
def isImplicitlyConvertible (src dst : CType) : Bool := (implicitConv p w src dst).isSome

/-- `Cpp::IsConstructible(to, from)` (`std::is_constructible<to, from>`: `to t(declval<from>())`,
where `declval<from>()` is an xvalue unless `from` is an lvalue reference). -/
def isConstructible (dst src : CType) : Bool :=
  let s := (nonRef src).canonical
  match dst.canonical with
  | .lref _ | .rref _ => (implicitConv p w src dst).isSome
  | d =>
    if (implicitConv p w src d).isSome then true
    else match d.unqual with
      | .record _ => userConv p w true s d
      -- direct-initialization of bool from std::nullptr_t ([dcl.init.general] 16.9)
      | .b .bool => s.unqual == .b .nullptr
      | _ => false

/-- [expr.static.cast]: is `static_cast<dst>(e)` well-formed for an `e` of type `src`. -/
def staticCastValid (src dst : CType) : Bool :=
  let s := (decay (nonRef src)).canonical
  let d := dst.canonical
  if isConstructible p w d src then true
  else if d.unqual == .b .void then true
  else match s.unqual, d.unqual with
  -- p7 inverse standard conversions: Base* -> Derived*, arithmetic both ways, void* -> T*
  | .ptr a, .ptr b =>
    let a' := a.canonical
    let b' := b.canonical
    if a'.unqual == .b .void then isObjectType b' && cvCovers b' a'
    else isDerivedFrom w b'.unqual a'.unqual && cvCovers b' a'
  | .b sk, .b dk => sk.isArithmetic && dk.isArithmetic
  | .enum _, .b dk => dk.isArithmetic
  | .b sk, .enum _ => sk.isArithmetic
  | .enum _, .enum _ => true
  | _, _ => false

/-- `Cpp::IsCStyleConvertible`: a C-style cast `(dst)e` ([expr.cast]: a `const_cast`, a
`static_cast`, a `reinterpret_cast`, each possibly followed by a `const_cast`). -/
def isCStyleConvertible (src dst : CType) : Bool :=
  let s := (decay (nonRef src)).canonical
  let d := dst.canonical
  let stripPtr (t : CType) : CType := match t.unqual with
    | .ptr u => .ptr u.canonical.unqual
    | u => u
  if staticCastValid p w src dst then true
  else if staticCastValid p w (stripPtr s) (stripPtr d) then true
  else match s.unqual, d.unqual with
  | .ptr _, .ptr _ => true
  | .ptr _, .b dk => dk.isIntegerKind && dk.width ≥ 64
  | .b sk, .ptr _ => sk.isIntegerKind
  | .enum _, .ptr _ => true
  | .b .nullptr, .b dk => dk.isIntegerKind && dk.width ≥ 64
  | _, _ => false

/-- `Cpp::GetCommonType` (IA4): the type of `c ? a : b` for arithmetic operands (the usual
arithmetic conversions), the composite pointer type for pointers, the type itself when equal;
null otherwise. -/
def commonType (a b : CType) : CType :=
  let a' := (nonRef a).canonical.unqual
  let b' := (nonRef b).canonical.unqual
  if a' == b' then a'
  else match promote p w a', promote p w b' with
    | some x, some y => .b (usualArith p x y)
    | _, _ =>
      if isPointer a' && isNullptrT b' then a'
      else if isPointer b' && isNullptrT a' then b'
      else .null

/-! ### Builtin operators ([over.built], [expr]) -/

/-- `Cpp::Operator`, the operators jank's `match_operator` table names. -/
inductive Op where
  | plus | minus | star | slash | percent | plusPlus | minusMinus | equalEqual | exclaimEqual
  | greater | less | greaterEqual | lessEqual | spaceship | exclaim | ampAmp | pipePipe | tilde
  | amp | pipe | caret | lessLess | greaterGreater | equal | plusEqual | minusEqual | starEqual
  | slashEqual | percentEqual | ampEqual | pipeEqual | caretEqual | lessLessEqual
  | greaterGreaterEqual | subscript | call
  deriving Repr, BEq, DecidableEq, Inhabited

def Op.isComparison : Op → Bool
  | .equalEqual | .exclaimEqual | .greater | .less | .greaterEqual | .lessEqual => true
  | _ => false

/-- `Cpp::GetBuiltinOperatorType(op, args)` (IA5): the type of the expression `a op b` (or
`op a`) when the operands have builtin meaning, else null. Class operands have no builtin meaning
(jank's `oref` types have no conversion functions). -/
def builtinOperatorType (op : Op) (args : List CType) : CType :=
  let isLvalue (t : CType) : Bool := match t.canonical with | .lref _ => true | _ => false
  match args with
  | [a] =>
    let t := (nonRef a).canonical
    match op with
    | .amp => .ptr (nonRef a)
    | .star => match (decay t) with | .ptr u => .lref u | _ => .null
    | .exclaim => if isArithmetic t || isPointer t || isUnscopedEnum w t then .b .bool else .null
    | .minus | .plus => match promote p w t with | some k => .b k | none => .null
    | .tilde => match promote p w t with
      | some k => if k.isIntegerKind then .b k else .null
      | none => .null
    | .plusPlus | .minusMinus =>
      if isLvalue a && !t.topConst && (isArithmetic t || isPointer t) && t.unqual != .b .bool
      then .lref t else .null
    | _ => .null
  | [a, b] =>
    let ta := (nonRef a).canonical
    let tb := (nonRef b).canonical
    let arith : Option Builtin := match promote p w ta, promote p w tb with
      | some x, some y => some (usualArith p x y)
      | _, _ => none
    let integral (k : Builtin) : Bool := k.isIntegerKind
    match op with
    | .plus | .minus | .star | .slash =>
      match arith with
      | some k => .b k
      | none =>
        if (op == .plus || op == .minus) && isPointer (decay ta) && isIntegral tb then decay ta
        else if op == .plus && isIntegral ta && isPointer (decay tb) then decay tb
        else if op == .minus && isPointer (decay ta) && isPointer (decay tb) then .b .long
        else .null
    | .percent | .amp | .pipe | .caret =>
      match arith with | some k => if integral k then .b k else .null | none => .null
    | .lessLess | .greaterGreater =>
      match promote p w ta, promote p w tb with
      | some x, some y => if integral x && integral y then .b x else .null
      | _, _ => .null
    | .equalEqual | .exclaimEqual | .greater | .less | .greaterEqual | .lessEqual =>
      if arith.isSome || (isPointer (decay ta) && isPointer (decay tb)) ||
         (isPointer (decay ta) && isNullptrT tb) || (isNullptrT ta && isPointer (decay tb)) then .b .bool
      else .null
    | .ampAmp | .pipePipe =>
      let ok (t : CType) := isArithmetic t || isPointer (decay t) || isUnscopedEnum w t
      if ok ta && ok tb then .b .bool else .null
    | .equal | .plusEqual | .minusEqual | .starEqual | .slashEqual | .percentEqual | .ampEqual
    | .pipeEqual | .caretEqual | .lessLessEqual | .greaterGreaterEqual =>
      if isLvalue a && !ta.topConst && (isArithmetic ta || isPointer ta) &&
         (arith.isSome || (isPointer ta && (stdConv p w tb ta).isSome)) then .lref ta else .null
    | .subscript =>
      match decay ta with
      | .ptr u => if isIntegral tb then .lref u else .null
      | _ => .null
    | _ => .null
  | _ => .null

/-! ### List-initialization narrowing ([dcl.init.list] 9.4.5 p7), for non-constant sources -/

def isNarrowing (src dst : CType) : Bool :=
  match builtinKind? src, builtinKind? dst with
  | some s, some d =>
    if s.isFloating && d.isIntegerKind && d != .bool then true
    else if s.isFloating && d.isFloating then
      (s == .ldouble && d != .ldouble) || (s == .double && d == .float)
    else if s.isIntegerKind && s != .bool && d.isFloating then true
    else if s.isIntegerKind && d.isIntegerKind && d != .bool then
      !(d.fits p (s.minVal p) && d.fits p (s.maxVal p))
    else false
  | _, _ =>
    (isUnscopedEnum w src && (builtinKind? dst).any (·.isFloating)) ||
    (isPointer src && builtinKind? dst == some .bool)

end Jank.Interop.Cxx
