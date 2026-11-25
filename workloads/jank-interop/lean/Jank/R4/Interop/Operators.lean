import Jank.R3.Interop.Worlds
import Jank.R4.Interop.TopLevel

/-!
# Round 4: C++ operator calls with CppInterOp's real `GetOperator`

Round 3 assumed (CXA10) that `GetOperator` finds no operator function for the program's classes.
This file replicates what it finds, and the two jank paths an operator call takes, against C++20's
[over.match.oper] (without the rewritten comparison candidates, which jank's book documents as
unsupported: book/src/cpp-interop/native-functions.md "Operators").

jank (analyze/processor.cpp `build_cpp_call` 367-511, then 526-760):
- A first operand of a *primitive* type (`cpp_util::is_primitive`, cpp_util.cpp 1025: a builtin,
  pointer, array **or enum**) with a primitive second operand (or none) goes to
  `build_builtin_operator_call` (196-249): its type is `GetBuiltinOperatorType`
  (CppInterOp.cpp 7066: `Sema::CreateBuiltin{Unary,Bin}Op`, built-in meaning only), and codegen
  emits the C++ operator syntax `a op b` (cpp_processor.cpp 1794-1821), which the JIT resolves
  with overload resolution, user operators included. The result is then boxed by the analysed
  type (`convert<T>::into_object`, cpp_processor.cpp 1287-1331).
- Otherwise `cppinterop::get_operator` (analyze/cppinterop.cpp 752-767 → CppInterOp.cpp 6977
  `GetOperator`): (1) `LookupOverloadedOperatorName` from the current scope (the translation
  unit), (2) `FindAssociatedClassesAndNamespaces`, then `LookupQualifiedName` in each associated
  namespace (which follows using-directives), (3) each associated class's own `operator@`
  members (`DeclContext::lookup`, no base lookup, no hiding) and its hidden friends. Then
  `find_best_overload` (cpp_util.cpp 1584) → `BestOverloadMatch` (CppInterOp.cpp 2203): members
  get the first operand as the object (`AddMethodCandidate`), no built-in candidate is added. An
  ambiguity is an error; no viable candidate is an error.

C++ ([over.match.oper]/3): member candidates from qualified lookup in the first operand's class
(hiding: a class's own `operator@` hides its bases'), non-member candidates from unqualified lookup
(the global namespace here) and argument-dependent lookup (associated namespaces *without*
using-directives, [basic.lookup.argdep]/4, plus hidden friends of associated classes), and the
built-in candidates of [over.built] (minus those with the parameter-type-list of a non-template
non-member candidate).
-/

namespace Jank.R4.Interop.Operators

open Jank.Interop
open Jank.R3.Interop
open Jank.R3.Interop.Clang
open Jank.R3.Interop.CppInterOp

abbrev TopLevelVal := Jank.R4.Interop.TopLevel.Val

def tyText (t : CType) : String := Jank.Interop.CppInterop.getTypeAsString t

/-! ## The declarations -/

/-- An operator function. Members take the object implicitly (`params` exclude it). -/
structure OpFn where
  id : String
  op : Cxx.Op
  /-- Enclosing namespace of a non-member ("" is the global namespace). -/
  ns : String := ""
  params : List CType
  ret : CType
  /-- The class of a member operator. -/
  member : Option String := none
  /-- The class a hidden friend is declared in (visible to argument-dependent lookup only). -/
  friendOf : Option String := none
  /-- What it returns, for the jank-visible value. -/
  result : TopLevelVal := .int 0
  deriving Inhabited

/-- A class: qualified name, namespace, bases, one conversion function and one converting
constructor at most (so user conversions through it name one function). -/
structure OClass where
  name : String
  ns : String := ""
  bases : List String := []
  convertsTo : List CType := []
  ctorFrom : List CType := []
  deriving Inhabited

structure OEnum where
  name : String
  ns : String := ""
  isScoped : Bool := false
  underlying : Builtin := .int
  constants : List (String × Int) := []
  deriving Inhabited

structure OWorld where
  classes : List OClass
  enums : List OEnum
  ops : List OpFn
  /-- (namespace, nominated namespace): `namespace N { using namespace M; }`. -/
  usingDirs : List (String × String) := []
  deriving Inhabited

def OWorld.findClass (o : OWorld) (n : String) : Option OClass := o.classes.find? (·.name == n)
def OWorld.findEnum (o : OWorld) (n : String) : Option OEnum := o.enums.find? (·.name == n)

/-- The XWorld round 3's conversion and built-in replicas query. -/
def OWorld.xworld (o : OWorld) : XWorld :=
  { w := { world0 with
      classes := world0.classes ++ o.classes.map fun c =>
        { name := c.name, bases := c.bases, convertsTo := c.convertsTo,
          ctors := c.ctorFrom.map fun t => { name := c.name, isCtor := true, params := [t], required := 1, ret := .null } },
      enums := world0.enums ++ o.enums.map fun e =>
        { name := e.name, isScoped := e.isScoped, underlying := e.underlying, constants := e.constants } },
    fixedEnums := [] }

/-! ## Associated classes and namespaces ([basic.lookup.argdep]/3; Sema
`FindAssociatedClassesAndNamespaces`) -/

/-- The class and its bases (transitively, at most 8 levels). -/
def classAndBasesF (o : OWorld) : Nat → String → List String
  | 0, n => [n]
  | k + 1, n => match o.findClass n with
    | some c => n :: c.bases.flatMap (classAndBasesF o k)
    | none => [n]

def classAndBases (o : OWorld) (n : String) : List String := classAndBasesF o 8 n

def assocClasses (o : OWorld) (t : CType) : List String :=
  match (nonRef t).canonical.unqual with
  | .record n => (classAndBases o n).eraseDups
  | _ => []

def nsOf (o : OWorld) (t : CType) : List String :=
  match (nonRef t).canonical.unqual with
  | .record n => (classAndBases o n).filterMap (fun c => (o.findClass c).map (·.ns)) |>.eraseDups
  | .enum n => match o.findEnum n with | some e => [e.ns] | none => []
  | _ => []

/-- `LookupQualifiedName` in a namespace: its own members, else (transitively) the namespaces its
using-directives nominate ([namespace.qual]/2). -/
def qualifiedNs (o : OWorld) (fuel : Nat) (n : String) : List String :=
  match fuel with
  | 0 => [n]
  | k + 1 => n :: (o.usingDirs.filter (·.1 == n)).flatMap fun (_, m) => qualifiedNs o k m

/-! ## jank: CppInterOp.cpp 6977 `GetOperator` -/

def getOperator (o : OWorld) (op : Cxx.Op) (args : List CType) : List OpFn :=
  let named := o.ops.filter (·.op == op)
  -- (1) unqualified lookup from the translation unit scope: global non-members
  let tu := named.filter fun f => f.member.isNone && f.friendOf.isNone && f.ns == ""
  -- (2) associated namespaces, qualified lookup (following using-directives)
  let nss := (args.flatMap (nsOf o)).eraseDups
  let viaNs := nss.flatMap fun n =>
    let reach := qualifiedNs o 4 n
    named.filter fun f => f.member.isNone && f.friendOf.isNone && reach.contains f.ns
  -- (3) associated classes: own members (no hiding), hidden friends
  let acs := (args.flatMap (assocClasses o)).eraseDups
  let viaCls := acs.flatMap fun c => named.filter fun f => f.member == some c || f.friendOf == some c
  (tu ++ viaNs ++ viaCls).foldl (fun acc f => if acc.any (·.id == f.id) then acc else acc ++ [f]) []

/-! ## Implicit conversion sequences with the converting function named -/

inductive OICS where
  | std (s : SCS)
  | user (via : String) (after : SCS)
  | bad
  deriving Inhabited

def OICS.ok : OICS → Bool | .bad => false | _ => true

/-- Which user-defined conversion a sequence from `src` to `param` goes through. -/
def viaOf (o : OWorld) (src param : CType) : String :=
  let s := (nonRef src).canonical.unqual
  let d := (nonRef param).canonical.unqual
  match s, d with
  | .record n, _ => if (o.findClass n).any (!·.convertsTo.isEmpty) then s!"{n}::operator conversion" else s!"ctor {tyText d}"
  | _, .record m => s!"{m}::{m}(ctor)"
  | _, _ => "?"

def argVK (t : CType) : VK := if isLValueReferenceType t then .lvalue else .prvalue

/-- `TryCopyInitialization` of `param` from an operand of type `arg` (round 3's `paramConv`),
with the user-defined conversion named. -/
def conv (p : Platform) (o : OWorld) (arg param : CType) : OICS :=
  match paramConv p o.xworld false (nonRef arg) (argVK arg) param with
  | .std s => .std s
  | .user s => .user (viaOf o arg param) s
  | .bad => .bad

/-- `TryObjectArgumentInitialization` (SemaOverload.cpp 6109-6220): the same class is identity,
a derived class is a derived-to-base conversion (`ICK_Derived_To_Base`, conversion rank), else
bad. (Round 3's `candidate` gave a derived object an exact match.) -/
def objConv (o : OWorld) (arg : CType) (cls : String) : OICS :=
  match (nonRef arg).canonical.unqual with
  | .record n =>
    if n == cls then .std { rank := .exact, identity := true }
    else if (classAndBases o n).contains cls then .std { rank := .conversion, identity := false, derivedToBase := true }
    else .bad
  | _ => .bad

/-- [over.ics.rank]/3: user-defined sequences compare only through the same conversion. -/
def betterICS (a b : OICS) : Bool :=
  match a, b with
  | .std s, .std t => betterSCS s t
  | .std _, .user .. => true
  | .user f s, .user g t => f == g && betterSCS s t
  | _, _ => false

structure Cand where
  id : String
  builtin : Bool := false
  ret : CType
  ics : List OICS
  viable : Bool
  fn? : Option OpFn := none
  deriving Inhabited

def betterCand (a b : Cand) : Bool :=
  let pairs := a.ics.zip b.ics
  (pairs.all fun (i, j) => !betterICS j i) && (pairs.any fun (i, j) => betterICS i j)

/-- `BestViableFunction`, as round 3's `Clang.bestViable`. -/
def bestViable (cands : List Cand) : Option Cand × List Cand := Id.run do
  let viable := cands.filter (·.viable)
  match viable with
  | [] => return (none, [])
  | c0 :: rest =>
    let best := rest.foldl (fun b c => if betterCand c b then c else b) c0
    let mut gathered : List Cand := [best]
    let mut pending : List Cand := [best]
    let mut fuel := viable.length * viable.length + 1
    while !pending.isEmpty && fuel > 0 do
      fuel := fuel - 1
      let cur := pending.head!
      pending := pending.tail
      for c in viable do
        if !(gathered.any fun g => g.id == c.id) && !betterCand cur c then
          gathered := gathered ++ [c]
          pending := pending ++ [c]
    if gathered.length == 1 then return (some best, gathered) else return (none, gathered)

/-- A function candidate: members take the first operand as the object. -/
def fnCand (p : Platform) (o : OWorld) (f : OpFn) (args : List CType) : Cand :=
  match f.member with
  | some cls =>
    match args with
    | a0 :: rest =>
      let oi := objConv o a0 cls
      let is := (rest.zip f.params).map fun (a, prm) => conv p o a prm
      { id := f.id, ret := f.ret, ics := oi :: is, fn? := some f,
        viable := rest.length == f.params.length && oi.ok && is.all OICS.ok }
    | [] => { id := f.id, ret := f.ret, ics := [], viable := false, fn? := some f }
  | none =>
    let is := (args.zip f.params).map fun (a, prm) => conv p o a prm
    { id := f.id, ret := f.ret, ics := is, fn? := some f,
      viable := args.length == f.params.length && is.all OICS.ok }

/-! ## C++ [over.match.oper] -/

/-- Qualified member lookup of `operator@` in a class ([class.member.lookup]): the class's own
declarations hide its bases'; declarations reached through two different bases are ambiguous. -/
def memberLookupF (o : OWorld) (op : Cxx.Op) : Nat → String → Except String (List OpFn)
  | 0, _ => .ok []
  | k + 1, cls =>
    let own := o.ops.filter fun f => f.op == op && f.member == some cls
    if !own.isEmpty then .ok own
    else match o.findClass cls with
      | none => .ok []
      | some c => do
        let found ← c.bases.mapM (memberLookupF o op k)
        let nonEmpty := found.filter (!·.isEmpty)
        match nonEmpty with
        | [] => .ok []
        | [one] => .ok one
        | _ => .error s!"lookup of `operator` in `{cls}` is ambiguous"

def memberLookup (o : OWorld) (op : Cxx.Op) (cls : String) : Except String (List OpFn) :=
  memberLookupF o op 8 cls

def promotedArith : List Builtin := [.int, .uint, .long, .ulong, .llong, .ullong, .float, .double, .ldouble]
def promotedIntegral : List Builtin := [.int, .uint, .long, .ulong, .llong, .ullong]

/-- The built-in candidates of [over.built] for the operators searched. -/
def builtinCands (p : Platform) (o : OWorld) (op : Cxx.Op) (args : List CType) (nonMembers : List OpFn) :
    List Cand :=
  let x := o.xworld
  let sameAsNonMember (ps : List CType) := nonMembers.any fun f =>
    f.params.length == ps.length && (f.params.zip ps).all fun (a, b) => (nonRef a).canonical.unqual == b.canonical.unqual
  let mk (ps : List Builtin) (ret : CType) : Option Cand :=
    let pts := ps.map CType.b
    if sameAsNonMember pts then none else
    let is := (args.zip pts).map fun (a, prm) => conv p o a prm
    some { id := s!"built-in {tyText ret} operator({", ".intercalate (ps.map Builtin.spelling)})",
           builtin := true, ret, ics := is, viable := args.length == ps.length && is.all OICS.ok }
  match args.length, op with
  | 1, .minus => promotedArith.filterMap fun l => mk [l] (.b l)
  | 2, .plus | 2, .minus | 2, .star =>
    promotedArith.flatMap fun l => promotedArith.filterMap fun r =>
      mk [l, r] ((usualArithmetic p x (.b l) (.b r)).getD .null)
  | 2, .pipe | 2, .amp | 2, .caret =>
    promotedIntegral.flatMap fun l => promotedIntegral.filterMap fun r =>
      mk [l, r] ((usualArithmetic p x (.b l) (.b r)).getD .null)
  | _, _ => []

def isClassOrEnum (t : CType) : Bool :=
  match (nonRef t).canonical.unqual with | .record _ | .enum _ => true | _ => false

/-- C++: the operator function or built-in `a @ b` uses, or why it is ill-formed. -/
def cppOperator (p : Platform) (o : OWorld) (op : Cxx.Op) (args : List CType) : Except String Cand := do
  if !(args.any isClassOrEnum) then
    let t := getBuiltinOperatorType p o.xworld op args
    if t.isNull then throw "no built-in operator" else return { id := "built-in", builtin := true, ret := t, ics := [], viable := true }
  let named := o.ops.filter (·.op == op)
  let members ← match args with
    | a0 :: _ => match (nonRef a0).canonical.unqual with
      | .record n => memberLookup o op n
      | _ => pure []
    | [] => pure []
  let unqual := named.filter fun f => f.member.isNone && f.friendOf.isNone && f.ns == ""
  let nss := (args.flatMap (nsOf o)).eraseDups
  let adlNs := named.filter fun f => f.member.isNone && f.friendOf.isNone && nss.contains f.ns
  let acs := (args.flatMap (assocClasses o)).eraseDups
  let friends := named.filter fun f => f.friendOf.any acs.contains
  let nonMembers := (unqual ++ adlNs ++ friends).foldl (fun acc f => if acc.any (·.id == f.id) then acc else acc ++ [f]) []
  let cands := (members ++ nonMembers).map (fnCand p o · args) ++ builtinCands p o op args nonMembers
  match bestViable cands with
  | (some c, _) => return c
  | (none, []) => throw "no viable operator"
  | (none, g) => throw s!"ambiguous between {g.map (·.id)}"

/-! ## jank's paths -/

/-- What jank does with `(cpp/<op> a b)`: `.ok (chosen, jankType)` or the analysis error. For the
built-in path the "chosen" id is `built-in`, and the value is what the emitted `a op b` computes,
boxed by the analysed type. -/
inductive JankOut where
  /-- Built-in path: the analysed type. -/
  | builtin (type : CType)
  /-- An operator function chosen by `BestOverloadMatch`. -/
  | fn (f : OpFn)
  | error (msg : String)
  deriving Inhabited

def jankOperator (p : Platform) (o : OWorld) (op : Cxx.Op) (args : List CType) : JankOut :=
  let x := o.xworld
  let objType := nonRef (args.headD .null)
  let builtinPath :=
    let t := getBuiltinOperatorType p x op args
    if t.isNull then JankOut.error "The operator is not supported for these types." else .builtin t
  if Paths.isPrimitive objType && (args.length == 1 || Paths.isPrimitive (nonRef (args.getD 1 .null))) then builtinPath
  else
    let fns := getOperator o op args
    if fns.isEmpty then .error "The operator is not supported for the type."
    else
      -- build_cpp_call 565-572: class (and enum) operands become lvalues; builtins stay prvalues
      let callArgs := args.map fun a =>
        if Clang.isPointerType a || Clang.isReferenceType a || isBuiltinType a then a else .lref a
      let cands := fns.map (fnCand p o · callArgs)
      match bestViable cands with
      | (some c, _) => match c.fn? with | some f => .fn f | none => .error "?"
      | (none, []) => .error "No matching overload."
      | (none, g) => .error s!"This call is ambiguous between {g.length} different overloads."

/-! ## The world searched (world XVIII) -/

def tV : CType := .record "V"
def tW : CType := .record "ops::W"
def tB : CType := .record "B"
def tD : CType := .record "D"
def tM : CType := .record "M"
def tQ : CType := .record "Q"
def tU : CType := .record "lib::U"
def tP : CType := .record "pn::P"
def tUE : CType := .enum "ue"
def tSE : CType := .enum "se"
def cref (t : CType) : CType := .lref (.const t)

def world : OWorld :=
  { classes :=
      [{ name := "V" },
       { name := "ops::W", ns := "ops" },
       { name := "B" },
       { name := "D", bases := ["B"] },
       { name := "M", convertsTo := [.b .double] },
       { name := "Q", convertsTo := [.b .int], ctorFrom := [.b .int] },
       { name := "lib::U", ns := "lib" },
       { name := "pn::P", ns := "pn" }],
    enums :=
      [{ name := "ue", constants := [("ua", 1), ("ub", 2)] },
       { name := "se", isScoped := true, constants := [("a", 1), ("b", 2)] }],
    ops :=
      [{ id := "int V::operator+(int) const", op := .plus, params := [.b .int], ret := .b .int, member := some "V", result := .int 1 },
       { id := "int ops::operator+(ops::W const&, ops::W const&)", op := .plus, ns := "ops", params := [cref tW, cref tW], ret := .b .int, result := .int 2 },
       { id := "int B::operator*(int) const", op := .star, params := [.b .int], ret := .b .int, member := some "B", result := .int 3 },
       { id := "int D::operator*(double) const", op := .star, params := [.b .double], ret := .b .int, member := some "D", result := .int 4 },
       { id := "Q operator+(Q, Q)", op := .plus, params := [tQ, tQ], ret := tQ, result := .int 5 },
       { id := "int lib::U::operator-(lib::U const&, lib::U const&) (hidden friend)", op := .minus, params := [cref tU, cref tU], ret := .b .int, friendOf := some "lib::U", result := .int 6 },
       { id := "int px::operator|(pn::P const&, pn::P const&)", op := .pipe, ns := "px", params := [cref tP, cref tP], ret := .b .int, result := .int 7 },
       { id := "double operator*(ue, ue)", op := .star, params := [tUE, tUE], ret := .b .double, result := .dbl 0.5 },
       { id := "se operator|(se, se)", op := .pipe, params := [tSE, tSE], ret := tSE, result := .int 3 },
       { id := "int operator-(se)", op := .minus, params := [tSE], ret := .b .int, result := .int 8 }],
    usingDirs := [("pn", "px")] }

/-- The operand forms: an lvalue global of each class (`cpp/gv`…), an enumerator (a prvalue),
and builtin literals. -/
def operands : List (String × CType) :=
  [("cpp/gv", .lref tV), ("cpp/gw", .lref tW), ("cpp/gb", .lref tB), ("cpp/gd", .lref tD),
   ("cpp/gm", .lref tM), ("cpp/gq", .lref tQ), ("cpp/gu", .lref tU), ("cpp/gp", .lref tP),
   ("cpp/ua", tUE), ("cpp/se.a", tSE), ("1", .b .int), ("2.5", .b .double)]

def opsSearched : List (Cxx.Op × String) := [(.plus, "+"), (.minus, "-"), (.star, "*"), (.pipe, "|")]

structure OpCase where
  op : Cxx.Op
  opText : String
  args : List (String × CType)
  deriving Inhabited

def OpCase.text (c : OpCase) : String := s!"(cpp/{c.opText} {" ".intercalate (c.args.map (·.1))})"

def allCases : List OpCase :=
  (opsSearched.flatMap fun (op, t) => operands.flatMap fun a => operands.map fun b => { op, opText := t, args := [a, b] }) ++
  (operands.map fun a => { op := .minus, opText := "-", args := [a] })

/-- The value jank boxes on the built-in path: the JIT's `a op b` calls the operator C++ chooses,
then `convert<analysed type>::into_object` converts its result. -/
def builtinPathValue (p : Platform) (o : OWorld) (cppChoice : Cand) (jankType : CType) : String :=
  match cppChoice.fn? with
  | none => "the built-in result (same as C++)"
  | some f =>
    match (nonRef jankType).canonical.unqual, (nonRef f.ret).canonical.unqual with
    | .b k, .b _ | .b k, .enum _ =>
      match Jank.R4.Interop.TopLevel.convertTo p k f.result with
      | some v => s!"{v.show} (the JIT calls `{f.id}`, which returns {f.result.show}, then boxes it as `{tyText jankType}`)"
      | none => "undefined (out-of-range conversion)"
    | _, _ => s!"a JIT compile error (`{f.id}` returns `{tyText f.ret}`, boxed as `{tyText jankType}`)"

/-- Judge one case: `none` when jank does what C++ does. -/
def judge (p : Platform) (c : OpCase) : Option (String × String) :=
  let args := c.args.map (·.2)
  let cpp := cppOperator p world c.op args
  let jank := jankOperator p world c.op args
  match cpp, jank with
  | .error _, .error _ => none
  | .ok cc, .builtin t =>
    if cc.builtin then
      (if (nonRef t).canonical.unqual == (nonRef cc.ret).canonical.unqual then none
       else some ("builtin-type", s!"{c.text}: C++ built-in `{tyText cc.ret}`; jank `{tyText t}`"))
    else
      let v := builtinPathValue p world cc t
      let jankVal : Option TopLevelVal := match cc.fn?, (nonRef t).canonical.unqual with
        | some f, .b k => Jank.R4.Interop.TopLevel.convertTo p k f.result
        | _, _ => none
      let sameValue := match cc.fn?, jankVal with
        | some f, some jv => jv.same f.result
        | _, _ => false
      if sameValue then
        some ("enum-user-operator-type", s!"{c.text}: C++ calls `{cc.id}` (`{tyText cc.ret}`); jank analyses the built-in `{tyText t}`, same value")
      else some ("enum-user-operator-bypassed", s!"{c.text}: C++ calls `{cc.id}` → {cc.fn?.map (·.result.show) |>.getD "?"}; jank analyses the built-in operator as `{tyText t}`; value {v}")
  | .ok cc, .error e =>
    let cls :=
      if args.length ≥ 1 && Paths.isPrimitive (nonRef args.head!) && (args.length == 1 || Paths.isPrimitive (nonRef (args.getD 1 .null))) then "enum-user-operator-unreachable"
      else if cc.builtin then "no-builtin-candidates"
      else if e.startsWith "This call is ambiguous" then "hidden-member-candidates"
      else "rejects"
    some (cls, s!"{c.text}: C++ calls `{cc.id}`; jank: {e}")
  | .error ce, .fn f =>
    let cls := if f.ns != "" && f.member.isNone && f.friendOf.isNone && !(nsOfArgs args).contains f.ns then "using-directive-operator"
      else "accepts-ill-formed"
    some (cls, s!"{c.text}: C++ ill-formed ({ce}); jank calls `{f.id}`")
  | .error ce, .builtin t => some ("accepts-ill-formed", s!"{c.text}: C++ ill-formed ({ce}); jank built-in `{tyText t}`")
  | .ok cc, .fn f =>
    if cc.id == f.id then none
    else some ("different-operator", s!"{c.text}: C++ calls `{cc.id}`; jank calls `{f.id}`")
where
  nsOfArgs (args : List CType) : List String := (args.flatMap (nsOf world)).eraseDups

end Jank.R4.Interop.Operators
