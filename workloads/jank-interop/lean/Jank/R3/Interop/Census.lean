import Jank.R3.Interop.Worlds

/-!
# Round 2's CppInterOp answers against the round-3 replica

Round 2 (`Jank/Interop/CppInterop.lean`, `Cxx.lean`, `Facts.lean`) answered each CppInterOp query
by the C++ standard. Round 3 replicates CppInterOp's own code. This census asks both every query
jank makes, over a type universe that covers every kind of type round 2's worlds draw (builtins,
cv, typedefs, enums, classes with bases, jank's object references, pointers, references, arrays,
function and member-pointer types), and lists where they disagree. Each disagreement is a
replaced round-2 assumption (AN, IA*, I).
-/

namespace Jank.R3.Interop.Census

open Jank.Interop
open Jank.R3.Interop.Worlds (x3 tshow)


def typeUniverse : List CType :=
  let bs : List CType := [.void, .bool, .char, .schar, .uchar, .wchar, .char8, .char16, .char32, .short, .ushort,
                          .int, .uint, .long, .ulong, .llong, .ullong, .float, .double, .ldouble, .nullptr].map CType.b
  bs ++
  [.cv true false (.b .int), .cv true false (.b .char), .cv true false (.b .double), sizeT, stdString,
   typedRef "integer", objectRef, .enum "color", .enum "mode", .record "base", .record "derived",
   .record "Foo", .record "meters", .ptr (.b .int), .ptr (.cv true false (.b .int)), .ptr (.b .void),
   .ptr (.cv true false (.b .void)), .ptr (.b .char), .ptr (.cv true false (.b .char)),
   .ptr (.record "base"), .ptr (.record "derived"), .ptr (.ptr (.b .int)), .ptr (.fn (.b .int) [.b .int]),
   .ptr (.array (.b .int) (some 3)), .lref (.b .int), .lref (.cv true false (.b .int)), .rref (.b .int),
   .lref (.record "base"), .lref (.cv true false stdString), .array (.b .int) (some 3),
   .array (.cv true false (.b .char)) (some 4), .array (.array (.b .int) (some 3)) (some 2),
   .fn (.b .int) [.b .int], .memPtr "Foo" (.b .int)]

def builtinsAndCv : List CType :=
  typeUniverse.filter fun t => (Clang.builtin? t).isSome

def showOpt (s : Option Decl) : String := match s with | some d => CppInterop.declName d | none => "null"

structure Row where
  name : String
  total : Nat
  diffs : List String

def compare1 (name : String) (ts : List CType) (f : CType → String) (g : CType → String) : Row :=
  { name, total := ts.length,
    diffs := ts.filterMap fun t => let a := f t; let b := g t; if a == b then none else some s!"{tshow t}: round 2 {a}; CppInterOp {b}" }

def compare2 (name : String) (ts : List CType) (f g : CType → CType → String) : Row :=
  let pairs := ts.flatMap fun a => ts.map fun b => (a, b)
  { name, total := pairs.length,
    diffs := pairs.filterMap fun (a, b) => let u := f a b; let v := g a b
      if u == v then none else some s!"({tshow a}, {tshow b}): round 2 {u}; CppInterOp {v}" }

def ct (t : CType) : String := if t.isNull then "null" else tshow t.canonical

def rows : List Row :=
  let p := x86_64
  let w := x3.w
  [compare1 "IsIntegral" typeUniverse (fun t => toString (CppInterop.isIntegral t)) (fun t => toString (CppInterOp.isIntegral t)),
   compare1 "IsBuiltin" typeUniverse (fun t => toString (CppInterop.isBuiltin t)) (fun t => toString (CppInterOp.isBuiltin t)),
   compare1 "GetPointeeType" typeUniverse (fun t => ct (CppInterop.getPointeeType t)) (fun t => ct (CppInterOp.getPointeeType t)),
   compare1 "GetUnderlyingType" typeUniverse (fun t => ct (CppInterop.getUnderlyingType t)) (fun t => ct (CppInterOp.getUnderlyingType t)),
   compare1 "GetScopeFromType" typeUniverse (fun t => showOpt (CppInterop.getScopeFromType w t)) (fun t => showOpt (CppInterOp.getScopeFromType x3 t)),
   compare1 "GetSignedType (x86-64)" builtinsAndCv (fun t => ct (CppInterop.getSignedType p t)) (fun t => ct (CppInterOp.getSignedType p t)),
   compare1 "GetUnsignedType (x86-64)" builtinsAndCv (fun t => ct (CppInterop.getUnsignedType p t)) (fun t => ct (CppInterOp.getUnsignedType p t)),
   compare1 "GetShortType (x86-64)" builtinsAndCv (fun t => ct (CppInterop.getShortType p t)) (fun t => ct (CppInterOp.getShortType p t)),
   compare1 "GetLongType (x86-64)" builtinsAndCv (fun t => ct (CppInterop.getLongType p t)) (fun t => ct (CppInterOp.getLongType p t)),
   compare1 "GetSignedType (AArch64)" builtinsAndCv (fun t => ct (CppInterop.getSignedType linuxAArch64 t)) (fun t => ct (CppInterOp.getSignedType linuxAArch64 t)),
   compare1 "GetUnsignedType (AArch64)" builtinsAndCv (fun t => ct (CppInterop.getUnsignedType linuxAArch64 t)) (fun t => ct (CppInterOp.getUnsignedType linuxAArch64 t)),
   compare2 "GetCommonType" typeUniverse (fun a b => ct (CppInterop.getCommonType p w a b)) (fun a b => ct (CppInterOp.getCommonType p x3 a b)),
   compare2 "IsImplicitlyConvertible" typeUniverse (fun a b => toString (CppInterop.isImplicitlyConvertible p w a b)) (fun a b => toString (CppInterOp.isImplicitlyConvertible p x3 a b)),
   compare2 "IsConstructible(to, from)" typeUniverse (fun a b => toString (CppInterop.isConstructible p w a b)) (fun a b => toString (CppInterOp.isConstructible p x3 a b)),
   compare2 "IsCStyleConvertible" typeUniverse (fun a b => toString (CppInterop.isCStyleConvertible p w a b)) (fun a b => toString (CppInterOp.isCStyleConvertible p x3 a b)),
   compare2 "GetBuiltinOperatorType(=)" typeUniverse (fun a b => ct (CppInterop.getBuiltinOperatorType p w .equal [a, b])) (fun a b => ct (CppInterOp.getBuiltinOperatorType p x3 .equal [a, b])),
   compare2 "GetBuiltinOperatorType(+)" typeUniverse (fun a b => ct (CppInterop.getBuiltinOperatorType p w .plus [a, b])) (fun a b => ct (CppInterOp.getBuiltinOperatorType p x3 .plus [a, b])),
   compare2 "GetBuiltinOperatorType(<)" typeUniverse (fun a b => ct (CppInterop.getBuiltinOperatorType p w .less [a, b])) (fun a b => ct (CppInterOp.getBuiltinOperatorType p x3 .less [a, b])),
   { name := "GetTypeFromScope(function) / IsVariable(field)", total := 2,
     diffs := (let f : FnDecl := { name := "take_int", params := [.b .int], required := 1, ret := .b .int }
               let fd : Decl := .field "point" { name := "x", type := .b .int }
               (if ct (CppInterop.getTypeFromScope (some (.function f))) != ct (CppInterOp.getTypeFromScope (some (.function f)))
                then [s!"take_int: round 2 {ct (CppInterop.getTypeFromScope (some (.function f)))}; CppInterOp {ct (CppInterOp.getTypeFromScope (some (.function f)))}"] else []) ++
               (if CppInterop.isVariable (some fd) != CppInterOp.isVariable (some fd)
                then [s!"point::x (a FieldDecl): round 2 IsVariable {CppInterop.isVariable (some fd)}; CppInterOp {CppInterOp.isVariable (some fd)}"] else [])) }]

end Jank.R3.Interop.Census
