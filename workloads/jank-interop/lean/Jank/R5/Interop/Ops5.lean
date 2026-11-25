import Jank.R4.Interop.Operators

/-!
# Round 5: operator templates, `=`, compound assignment, `aget` (`[]`), the call operator, and
the value categories jank gives operands

jank 94d32623 (compiler+runtime identical to 7135b7708), CppInterOp 28b0830d, Clang 23.1.0.
Round 4 (`Jank/R4/Interop/Operators.lean`) replicated `GetOperator`'s lookup and `BestOverloadMatch`
for `+ - * |` on non-template operators. This file adds what it left out, read from the same code:

jank's analysis (analyze/processor.cpp `build_cpp_call` 266-760, `build_indirect_cpp_call`
874-1010; analyze/cpp_util.cpp `match_operator` 1749-1797, `find_best_overload`):
- operator names: `=`, `+=` … `>>=` and `aget` (`[]`) are `cpp/` operators; `()` is used
  internally for calls of class objects (`build_indirect_cpp_call` 930-965);
- a primitive first operand with a primitive (or no) second operand takes the built-in path
  (`build_builtin_operator_call` 196-249), unary `&` always does (395-397);
  `GetBuiltinOperatorType` (CppInterOp.cpp 7066-7210) makes every operand except a non-reference
  `nullptr_t` an **lvalue** (7080-7087);
- otherwise `GetOperator` (CppInterOp.cpp 6977-7064): unqualified lookup from the TU scope (using
  declarations resolved, 7000-7006), `LookupQualifiedName` in every associated namespace (7022-7031),
  whose results are kept only when they are a `FunctionTemplateDecl` or `FunctionDecl` (7026-7029):
  a `UsingShadowDecl` (a namespace-scope `using N::operator@;`) is **dropped**; every associated
  class's own `operator@` (`DeclContext::lookup`, shadows dropped likewise, 7044-7050) and hidden
  friends (7053-7062), implicit special members declared first (`ForceDeclarationOfImplicitMembers`,
  7040); the arity filter `kind & GetOperatorArity(ND)` (6991) passes every template (`~0`, 6973);
- `BestOverloadMatch` (CppInterOp.cpp 2203-2238, `AddOverloadCandidates` 1996-2124): argument value
  kinds from the types jank passes — a class argument becomes `T&` (processor.cpp 565-572: every
  type that is not a pointer, reference or builtin), so a class **temporary is an lvalue**; a builtin
  stays a **prvalue**, also when it is a named local (`let` binding type = init type, analyze_let 2414-2421; local
  reference type, local_reference.cpp 29-32); member candidates get the acting context of the class
  that declares them (`AddMethodCandidate` SemaOverload.cpp 7914-7917), so a base member is a
  derived-to-base object conversion even when the derived class re-exports it with a using-declaration;
  no built-in candidates and no surrogate call functions;
- `find_best_overload` (cpp_util.cpp 1584-1640): an ambiguity, a deleted best, a private best are
  errors.

Codegen (codegen/cpp_processor.cpp): every operand is a named variable (`auto t(lit)` for a C++
literal, 1278-1285; `T t(args)` for a constructor call, 1655-1726); `cpp_call` (1352-1560) names the
function qualified (`GetQualifiedCompleteName`, CppInterOp.cpp 991-1013: no template arguments) and
wraps an argument in `std::move` when the chosen function's parameter is an rvalue reference
(1410-1417); `cpp_member_call` (1730-1775) emits `obj.operator@(args)` with the arguments as they
are, never moved; `cpp_builtin_operator_call` (1794-1821) emits `a op b`, `op a` or `a[b]`.
Clang then compiles that text: what it calls is resolved again from the emitted names and the
emitted (lvalue/xvalue) arguments.

C++ ([over.match.oper], [over.call.object], [over.built], [over.match.funcs]/4, [temp.deduct.call],
[namespace.udecl], [basic.lookup.argdep], C++20 as `-std=gnu++20`, util/clang.cpp 347).
-/

namespace Jank.R5.Interop.Ops5

open Jank.Interop
open Jank.R3.Interop
open Jank.R3.Interop.Clang

def tyText (t : CType) : String := Jank.Interop.CppInterop.getTypeAsString t

/-! ## Declarations -/

/-- A function parameter, possibly in terms of template parameter `i`. -/
inductive PPat where
  | fixed (t : CType)
  /-- `T` by value. -/
  | byVal (i : Nat)
  /-- `T const &`. -/
  | cref (i : Nat)
  /-- `T &&`, a forwarding reference. -/
  | fwd (i : Nat)
  deriving Repr, BEq, Inhabited

inductive RPat where
  | fixed (t : CType)
  | param (i : Nat)
  deriving Repr, BEq, Inhabited

/-- A requires-clause on the deduced arguments. -/
inductive Constraint where
  | none
  /-- `std::is_integral_v<std::remove_cvref_t<T_i>>`. -/
  | integralDecayed (i : Nat)
  deriving Repr, BEq, Inhabited

/-- What a call returns (the observable value). -/
inductive Body where
  | const (v : Int)
  /-- `std::is_lvalue_reference_v<T_i> ? a : b`. -/
  | lrefT (i : Nat) (a b : Int)
  /-- An assignment operator: the object takes the right operand's value. -/
  | assign
  deriving Repr, BEq, Inhabited

structure Fn where
  id : String
  op : Cxx.Op
  /-- Namespace of a non-member ("" is the global namespace). -/
  ns : String := ""
  member : Option String := none
  friendOf : Option String := none
  /-- Parameters (a member's exclude the object). -/
  params : List PPat
  ret : RPat := .fixed (.b .int)
  /-- Number of template type parameters (0: not a template). -/
  tparams : Nat := 0
  defaults : List (Option CType) := []
  constraint : Constraint := .none
  deleted : Bool := false
  body : Body := .const 0
  deriving Repr, BEq, Inhabited

structure Cls where
  name : String
  ns : String := ""
  bases : List String := []
  convertsTo : List CType := []
  ctorFrom : List CType := []
  /-- `using Base::operator@;` in the class: (base, operator). -/
  usingOps : List (String × Cxx.Op) := []
  /-- The implicitly declared copy assignment is deleted (a user-declared move assignment). -/
  copyDeleted : Bool := false
  deriving Repr, BEq, Inhabited

structure W5 where
  classes : List Cls
  fns : List Fn
  /-- `namespace N { using M::operator@; }`: (N, the function's id). -/
  usingNs : List (String × String) := []
  /-- `namespace N { using namespace M; }`: (N, M). -/
  usingDirs : List (String × String) := []
  deriving Inhabited

def W5.cls (w : W5) (n : String) : Option Cls := w.classes.find? (·.name == n)

/-- The implicitly declared copy and move assignment operators ([class.copy.assign]/2, /4); Clang
declares them in `ForceDeclarationOfImplicitMembers` (CppInterOp.cpp 7040) and in lookup
(`LookupDirect`, SemaLookup.cpp 1133-1136). -/
def implicitAssign (c : Cls) : List Fn :=
  [{ id := s!"{c.name}::operator=({c.name} const&){if c.copyDeleted then " = delete" else ""}", op := .equal,
     member := some c.name, params := [.fixed (.lref (.const (.record c.name)))],
     ret := .fixed (.lref (.record c.name)), deleted := c.copyDeleted, body := .assign },
   { id := s!"{c.name}::operator=({c.name}&&)", op := .equal, member := some c.name,
     params := [.fixed (.rref (.record c.name))], ret := .fixed (.lref (.record c.name)), body := .assign }]

def W5.allFns (w : W5) : List Fn := w.fns ++ w.classes.flatMap implicitAssign

def W5.fnById (w : W5) (id : String) : Option Fn := w.allFns.find? (·.id == id)

/-- Round 3's world for `paramConv`, with these classes (as round 4's `OWorld.xworld`). -/
def W5.xworld (w : W5) : XWorld :=
  { w := { world0 with
      classes := world0.classes ++ w.classes.map fun c =>
        { name := c.name, bases := c.bases, convertsTo := c.convertsTo,
          ctors := c.ctorFrom.map fun t =>
            { name := c.name, isCtor := true, params := [t], required := 1, ret := .null } } },
    fixedEnums := [] }

def classAndBasesF (w : W5) : Nat → String → List String
  | 0, n => [n]
  | k + 1, n => match w.cls n with
    | some c => n :: c.bases.flatMap (classAndBasesF w k)
    | none => [n]

def classAndBases (w : W5) (n : String) : List String := classAndBasesF w 6 n

def assocClasses (w : W5) (t : CType) : List String :=
  match (nonRef t).canonical.unqual with
  | .record n => (classAndBases w n).eraseDups
  | _ => []

def assocNs (w : W5) (t : CType) : List String :=
  match (nonRef t).canonical.unqual with
  | .record n => (classAndBases w n).filterMap (fun c => (w.cls c).map (·.ns)) |>.eraseDups
  | _ => []

/-- `LookupQualifiedName` in a namespace: its own declarations and, transitively, those of the
namespaces its using-directives nominate ([namespace.qual]/2). -/
def qualifiedNs (w : W5) : Nat → String → List String
  | 0, n => [n]
  | k + 1, n => n :: (w.usingDirs.filter (·.1 == n)).flatMap fun (_, m) => qualifiedNs w k m

def dedupFns (fs : List (Fn × String)) : List (Fn × String) :=
  fs.foldl (fun acc f => if acc.any (·.1.id == f.1.id) then acc else acc ++ [f]) []

/-! ## Template argument deduction ([temp.deduct.call]) -/

/-- One parameter/argument pair: the template parameter it deduces and the deduced type, from the
argument's non-reference type `a` and value category. `T` by value: the decayed, cv-unqualified
type (/2); `T const &`: the referenced type without cv (/3); `T &&` with an lvalue: `A&` (/3). -/
def deduceOne (a : CType) (vk : VK) : PPat → Option (Nat × CType)
  | .fixed _ => none
  | .byVal i => some (i, (decayed a).canonical.unqual)
  | .cref i => some (i, a.canonical.unqual)
  | .fwd i => some (i, if vk == .lvalue then .lref a.canonical else a.canonical)

/-- Merge the deduced pairs; `none` on a conflict. -/
def mergeDeduced : List (Nat × CType) → List (Nat × CType) → Option (List (Nat × CType))
  | acc, [] => some acc
  | acc, (i, t) :: rest =>
    match acc.lookup i with
    | some t' => if t' == t then mergeDeduced acc rest else none
    | none => mergeDeduced (acc ++ [(i, t)]) rest

def fillArgs (fn : Fn) (ded : List (Nat × CType)) : Option (List CType) :=
  (List.range fn.tparams).mapM fun i =>
    match ded.lookup i with
    | some t => some t
    | none => fn.defaults.getD i none

def satisfies (fn : Fn) (targs : List CType) : Bool :=
  match fn.constraint with
  | .none => true
  | .integralDecayed i => isIntegralType (nonRef (targs.getD i .null))

/-- The deduced template arguments of `fn` for arguments `(non-reference type, value category)`. -/
def deduce (fn : Fn) (args : List (CType × VK)) : Option (List CType) := do
  let pairs := (fn.params.zip args).filterMap fun (p, (a, vk)) => deduceOne (nonRef a) vk p
  let ded ← mergeDeduced [] pairs
  let targs ← fillArgs fn ded
  if satisfies fn targs then some targs else none

def substP (targs : List CType) : PPat → CType
  | .fixed t => t
  | .byVal i => targs.getD i .null
  | .cref i => .lref (.const (targs.getD i .null))
  | .fwd i => match targs.getD i .null with | .lref u => .lref u | u => .rref u

def retOf (fn : Fn) (targs : List CType) : CType :=
  match fn.ret with | .fixed t => t | .param i => targs.getD i .null

/-! ## Conversions and candidates -/

inductive ICS5 where
  | std (s : SCS)
  | user (via : String) (s : SCS)
  | bad
  deriving Inhabited

def ICS5.ok : ICS5 → Bool | .bad => false | _ => true

/-- The conversion function or constructor a user-defined sequence goes through. -/
def viaOf (w : W5) (src param : CType) : String :=
  match (nonRef src).canonical.unqual, (nonRef param).canonical.unqual with
  | .record n, d => if (w.cls n).any (!·.convertsTo.isEmpty) then s!"{n}::conversion" else s!"ctor {tyText d}"
  | _, .record m => s!"{m}::{m}"
  | _, _ => "?"

/-- `TryCopyInitialization` of `param` from an argument of non-reference type `arg` and kind `vk`
(round 3's `paramConv`, with the user conversion named). -/
def conv (p : Platform) (w : W5) (arg : CType) (vk : VK) (param : CType) : ICS5 :=
  match paramConv p w.xworld false (nonRef arg) vk param with
  | .std s => .std s
  | .user s => .user (viaOf w arg param) s
  | .bad => .bad

/-- The implicit object parameter of a member of class `ctx` ([over.match.funcs]/4-5,
`TryObjectArgumentInitialization`): identity for the same class, derived-to-base for a base. -/
def objICS (w : W5) (obj : CType) (ctx : String) : ICS5 :=
  match (nonRef obj).canonical.unqual with
  | .record n =>
    if n == ctx then .std { rank := .exact, identity := true }
    else if (classAndBases w n).contains ctx then .std { rank := .conversion, identity := false, derivedToBase := true }
    else .bad
  | _ => .bad

def betterICS (a b : ICS5) : Bool :=
  match a, b with
  | .std s, .std t => betterSCS s t
  | .std _, .user .. => true
  | .user f s, .user g t => f == g && betterSCS s t
  | _, _ => false

structure Cand where
  key : String
  fn? : Option Fn := none
  targs : List CType := []
  builtin : Bool := false
  surrogate : Bool := false
  ret : CType
  params : List CType := []
  ics : List ICS5
  viable : Bool
  fromTemplate : Bool := false
  deriving Inhabited

def betterCand (a b : Cand) : Bool :=
  let pairs := a.ics.zip b.ics
  (pairs.all fun (i, j) => !betterICS j i) &&
    ((pairs.any fun (i, j) => betterICS i j) || (!a.fromTemplate && b.fromTemplate))

/-- `BestViableFunction` (as round 3/4's `bestViable`). -/
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
        if !(gathered.any fun g => g.key == c.key) && !betterCand cur c then
          gathered := gathered ++ [c]
          pending := pending ++ [c]
    if gathered.length == 1 then return (some best, gathered) else return (none, gathered)

def targsText (ts : List CType) : String :=
  if ts.isEmpty then "" else s!"<{", ".intercalate (ts.map tyText)}>"

/-- A function candidate. `obj`: the object argument (members only); `args`: the others. -/
def fnCand (p : Platform) (w : W5) (f : Fn) (ctx : String) (obj : Option (CType × VK))
    (args : List (CType × VK)) : Cand :=
  let inst : Option (List CType) := if f.tparams > 0 then deduce f args else some []
  match inst with
  | none => { key := f.id, fn? := some f, ret := .null, ics := [], viable := false, fromTemplate := f.tparams > 0 }
  | some ta =>
    let ps := f.params.map (substP ta)
    let is := (args.zip ps).map fun ((a, vk), prm) => conv p w a vk prm
    let oi : List ICS5 := match f.member, obj with
      | some _, some (o, _) => [objICS w o ctx]
      | some _, none => [.bad]
      | none, _ => []
    { key := s!"{f.id}{targsText ta}", fn? := some f, targs := ta, ret := retOf f ta, params := ps,
      ics := oi ++ is, viable := args.length == ps.length && (oi ++ is).all ICS5.ok,
      fromTemplate := f.tparams > 0 }

/-! ## C++: [over.match.oper], [over.call.object], [over.built] -/

/-- Class member lookup of `operator@` ([class.member.lookup]) with the acting context of each
result: the class's own declarations and the members its using-declarations name (members of the
class for the implicit object parameter, [over.match.funcs]/4) hide the bases'; two bases that both
declare it are ambiguous. -/
def memberLookupF (w : W5) (op : Cxx.Op) : Nat → String → Except String (List (Fn × String))
  | 0, _ => .ok []
  | k + 1, cls =>
    let own := (w.allFns.filter fun f => f.op == op && f.member == some cls).map (·, cls)
    let viaUsing : List (Fn × String) := match w.cls cls with
      | some c => (c.usingOps.filter (·.2 == op)).flatMap fun (b, _) =>
          ((memberLookupF w op k b).toOption.getD []).map fun (f, _) => (f, cls)
      | none => []
    if !(own ++ viaUsing).isEmpty then .ok (own ++ viaUsing)
    else match w.cls cls with
      | none => .ok []
      | some c => do
        let found ← c.bases.mapM (memberLookupF w op k)
        match found.filter (!·.isEmpty) with
        | [] => .ok []
        | [one] => .ok one
        | _ => .error s!"lookup of `operator` in `{cls}` is ambiguous"

def memberLookup (w : W5) (op : Cxx.Op) (cls : String) : Except String (List (Fn × String)) :=
  memberLookupF w op 6 cls

def classOf (t : CType) : Option String :=
  match (nonRef t).canonical.unqual with | .record n => some n | _ => none

def usingTargets (w : W5) (n : String) : List Fn :=
  (w.usingNs.filter (·.1 == n)).filterMap fun (_, id) => w.fnById id

/-- Non-member candidates of an operator expression: unqualified lookup (the global namespace,
using-declarations included) and argument-dependent lookup (associated namespaces with their
using-declarations, not their using-directives, [basic.lookup.argdep]/4; hidden friends of
associated classes). -/
def nonMemberCands (w : W5) (op : Cxx.Op) (argTypes : List CType) : List (Fn × String) :=
  let named := w.allFns.filter (·.op == op)
  let unqual := (named.filter fun f => f.member.isNone && f.friendOf.isNone && f.ns == "") ++
    (usingTargets w "").filter (·.op == op)
  let nss := (argTypes.flatMap (assocNs w)).eraseDups
  let adl := nss.flatMap fun n =>
    (named.filter fun f => f.member.isNone && f.friendOf.isNone && f.ns == n) ++ (usingTargets w n).filter (·.op == op)
  let acs := (argTypes.flatMap (assocClasses w)).eraseDups
  let friends := named.filter fun f => f.friendOf.any acs.contains
  dedupFns ((unqual ++ adl ++ friends).map (·, ""))

def promotedArith : List Builtin := [.int, .uint, .long, .ulong, .llong, .ullong, .float, .double, .ldouble]
def promotedIntegral : List Builtin := [.int, .uint, .long, .ulong, .llong, .ullong]

/-- A pointer to an object type (the built-in pointer arithmetic and subscript candidates of
[over.built]/13-14 are for "cv-qualified or cv-unqualified completely-defined object type" `T`). -/
def isObjPtr : CType → Bool
  | .ptr (.fn ..) => false
  | .ptr _ => true
  | _ => false

/-- The object pointer types an operand reaches: its own, or a conversion function's. -/
def pointerTargets (w : W5) (t : CType) : List CType :=
  match (nonRef t).canonical.unqual with
  | .ptr u => [.ptr u].filter isObjPtr
  | .record n => ((w.cls n).map (·.convertsTo) |>.getD []).filter isObjPtr
  | _ => []

/-- The built-in candidates of [over.built] for the operators searched (CXA4-4 as round 4). `=`,
`+=`, `++` take the left operand's own type `L` (no user conversion and no temporary on the left,
[over.match.oper]/4; only `L&` can bind it). -/
def builtinCands (p : Platform) (w : W5) (op : Cxx.Op) (args : List (CType × VK))
    (nonMembers : List Fn) : List Cand :=
  let x := w.xworld
  let sameAsNonMember (ps : List CType) := nonMembers.any fun f => f.tparams == 0 &&
    f.params.length == ps.length && (f.params.zip ps).all fun (a, b) =>
      (nonRef (substP [] a)).canonical.unqual == b.canonical.unqual
  let mk (ps : List CType) (ret : CType) : Option Cand :=
    if sameAsNonMember (ps.map nonRef) then none else
    let is := (args.zip ps).map fun ((a, vk), prm) => conv p w a vk prm
    some { key := s!"built-in {tyText ret} operator({", ".intercalate (ps.map tyText)})", builtin := true,
           ret, params := ps, ics := is, viable := args.length == ps.length && is.all ICS5.ok }
  let arithPairs (ks : List Builtin) : List Cand := ks.flatMap fun l => ks.filterMap fun r =>
    mk [.b l, .b r] ((usualArithmetic p x (.b l) (.b r)).getD .null)
  let leftL : Option CType := match args.head? with
    | some (a, _) => if isArithmeticType x (nonRef a) && !isRecordType (nonRef a) then some (nonRef a).canonical.unqual else none
    | none => none
  let ptrs := (args.flatMap fun (a, _) => pointerTargets w a).eraseDups
  match args.length, op with
  | 2, .plus => arithPairs promotedArith ++
      ptrs.flatMap (fun pt => [mk [pt, .b .long] pt, mk [.b .long, pt] pt].filterMap id)
  | 2, .minus => arithPairs promotedArith ++ ptrs.filterMap (fun pt => mk [pt, .b .long] pt)
  | 2, .star | 2, .slash => arithPairs promotedArith
  | 2, .pipe | 2, .amp | 2, .caret | 2, .percent => arithPairs promotedIntegral
  | 2, .subscript => ptrs.flatMap fun pt => match pt with
      | .ptr u => [mk [pt, .b .long] (.lref u), mk [.b .long, pt] (.lref u)].filterMap id
      | _ => []
  | 2, .equal | 2, .plusEqual => match leftL with
      | some l => promotedArith.filterMap fun r => mk [.lref l, .b r] (.lref l)
      | none => []
  | 1, .plusPlus => match leftL with
      | some l => if l == .b .bool then [] else [mk [.lref l] (.lref l)].filterMap id
      | none => []
  | _, _ => []

/-- Surrogate call functions ([over.call.object]/2): for each conversion function of the class to
a pointer to function `R(*)(P…)`, a candidate taking the object through that conversion, then P…. -/
def surrogates (p : Platform) (w : W5) (obj : CType) (args : List (CType × VK)) : List Cand :=
  match (nonRef obj).canonical.unqual with
  | .record n => ((w.cls n).map (·.convertsTo) |>.getD []).filterMap fun t =>
      match t with
      | .ptr (.fn r ps) =>
        let is := (args.zip ps).map fun ((a, vk), prm) => conv p w a vk prm
        let oi : ICS5 := .user s!"{n}::conversion" { rank := .exact, identity := true }
        some { key := s!"surrogate {tyText r}({", ".intercalate (ps.map tyText)}) via {n}::operator {tyText t}",
               surrogate := true, ret := r, params := ps, ics := oi :: is,
               viable := args.length == ps.length && is.all ICS5.ok }
      | _ => none
  | _ => []

def isClassOrEnum (t : CType) : Bool :=
  match (nonRef t).canonical.unqual with | .record _ | .enum _ => true | _ => false

def opnd (a : CType × VK) : Opnd := { type := nonRef a.1, lvalue := a.2 == .lvalue }

/-- [over.match.oper]/11: a selected built-in candidate converts the class operands to its
parameter types and is then the built-in operator, the other operands unchanged. -/
def builtinAfterSelect (p : Platform) (w : W5) (op : Cxx.Op) (args : List (CType × VK)) (c : Cand) : CType :=
  let ops := (args.zip c.params).map fun ((a, vk), prm) =>
    if isRecordType (nonRef a) then ({ type := nonRef prm, lvalue := isLValueReferenceType prm } : Opnd)
    else opnd (a, vk)
  builtinOp p w.xworld op ops

/-- C++: what `a @ b`, `@a`, `a[b]` or `f(a)` (`op = .call`, the object first) calls. -/
def cppResolve (p : Platform) (w : W5) (op : Cxx.Op) (args : List (CType × VK)) : Except String Cand := do
  if op == .call then
    let (o, ovk) := args.headD (.null, .prvalue)
    let some cls := classOf o | throw "not callable"
    let members ← memberLookup w .call cls
    let cands := members.map (fun (f, ctx) => fnCand p w f ctx (some (o, ovk)) args.tail) ++ surrogates p w o args.tail
    match bestViable cands with
    | (some c, _) => if c.fn?.any (·.deleted) then throw "deleted" else return c
    | (none, []) => throw "no viable call"
    | (none, g) => throw s!"ambiguous between {g.map (·.key)}"
  if !(args.any fun (a, _) => isClassOrEnum a) then
    let t := builtinOp p w.xworld op (args.map opnd)
    if t.isNull then throw "no built-in operator" else return { key := "built-in", builtin := true, ret := t, ics := [], viable := true }
  let members ← match args.head? with
    | some (a0, _) => match classOf a0 with
      | some n => memberLookup w op n
      | none => pure []
    | none => pure []
  let memberOnly := op == .equal || op == .subscript
  let nonMembers := if memberOnly then [] else nonMemberCands w op (args.map (·.1))
  let obj := args.head?
  let fnCands := members.map (fun (f, ctx) => fnCand p w f ctx obj args.tail) ++
    nonMembers.map (fun (f, _) => fnCand p w f "" none args)
  let cands := fnCands ++ builtinCands p w op args (nonMembers.map (·.1))
  match bestViable cands with
  | (some c, _) =>
    if c.fn?.any (·.deleted) then throw "deleted"
    else if c.builtin then
      let t := builtinAfterSelect p w op args c
      if t.isNull then throw "the selected built-in operator is ill-formed on these operands" else return { c with ret := t }
    else return c
  | (none, []) =>
    -- unary `&` with no viable user operator is the built-in address-of ([over.match.oper]/9)
    if op == .amp && args.length == 1 then
      let t := builtinOp p w.xworld op (args.map opnd)
      if t.isNull then throw "no viable operator" else return { key := "built-in", builtin := true, ret := t, ics := [], viable := true }
    else throw "no viable operator"
  | (none, g) => throw s!"ambiguous between {g.map (·.key)}"

/-! ## jank -/

/-- How a jank operand form reaches C++. -/
inductive Kind where
  /-- `cpp/g`: a global variable, an lvalue of its type; jank types it `T&`. -/
  | global
  /-- `(cpp/T. args)`: a constructor call, a prvalue; jank types it `T`. -/
  | temp
  /-- `1`, `2.5`: a C++ literal (`cpp_literal`), a prvalue; jank types it `int`/`double`. -/
  | literal
  /-- `x` bound by `(let [x (cpp/int. 1)] …)`: a named variable, an lvalue; its binding type is
  the init's type `int`. -/
  | named
  deriving Repr, BEq, Inhabited

structure Operand where
  text : String
  type : CType
  kind : Kind
  deriving Repr, BEq, Inhabited

def Operand.cxxVK (o : Operand) : VK :=
  match o.kind with | .global | .named => .lvalue | .temp | .literal => .prvalue

/-- `cpp_util::expression_type`. -/
def Operand.jankType (o : Operand) : CType :=
  match o.kind with | .global => .lref o.type | _ => o.type

/-- The mechanisms, each with a switch that sets it to C++'s rule (the replica runs with none). -/
structure Fix where
  /-- A class temporary keeps its prvalue category (instead of processor.cpp 565-572's `T&`). -/
  tempPrvalue : Bool := false
  /-- `cpp_member_call` moves an argument whose parameter is an rvalue reference, as `cpp_call` does. -/
  memberMove : Bool := false
  /-- A named builtin local is an lvalue to overload resolution. -/
  localLvalue : Bool := false
  /-- `GetBuiltinOperatorType` gives operands their own value categories. -/
  builtinVK : Bool := false
  /-- `GetOperator` resolves using-declarations found in associated namespaces. -/
  usingNs : Bool := false
  /-- A base member re-exported by `using` gets the derived class as acting context. -/
  usingCtx : Bool := false
  /-- Surrogate call functions are candidates. -/
  surrogates : Bool := false
  /-- Built-in candidates are candidates. -/
  builtinCands : Bool := false
  /-- Member lookup hides base members (only the first operand's class, C++'s lookup). -/
  hide : Bool := false
  deriving Repr, BEq, Inhabited

def fixNames : List (String × Fix) :=
  [("class-temporary-is-lvalue", { tempPrvalue := true }),
   ("member-call-args-not-moved", { memberMove := true }),
   ("named-builtin-local-is-rvalue", { localLvalue := true }),
   ("builtin-operand-always-lvalue", { builtinVK := true }),
   ("using-declaration-in-namespace-dropped", { usingNs := true }),
   ("using-member-base-object", { usingCtx := true }),
   ("no-surrogate-call-functions", { surrogates := true }),
   ("no-builtin-candidates", { builtinCands := true }),
   ("no-member-hiding", { hide := true })]

def Fix.union (a b : Fix) : Fix :=
  { tempPrvalue := a.tempPrvalue || b.tempPrvalue, memberMove := a.memberMove || b.memberMove,
    localLvalue := a.localLvalue || b.localLvalue, builtinVK := a.builtinVK || b.builtinVK,
    usingNs := a.usingNs || b.usingNs, usingCtx := a.usingCtx || b.usingCtx,
    surrogates := a.surrogates || b.surrogates, builtinCands := a.builtinCands || b.builtinCands,
    hide := a.hide || b.hide }

/-- The value category an argument has in `BestOverloadMatch` (CppInterOp.cpp 2022-2026 from the
type jank passes: `T&` lvalue, `T&&` xvalue, otherwise prvalue; processor.cpp 565-572 turns every
type that is not a pointer, reference or builtin into `T&`). -/
def jankArgVK (fx : Fix) (o : Operand) : VK :=
  let t := o.jankType
  if isLValueReferenceType t then .lvalue
  else if isPointerType t || isBuiltinType t then
    (if fx.localLvalue && o.kind == .named then .lvalue else .prvalue)
  else if fx.tempPrvalue then .prvalue else .lvalue

/-- `GetOperatorArity` (CppInterOp.cpp 6954-6975, OperatorKinds.def): 1 unary, 2 binary, 3 both;
a template is `~0`. -/
def opArity : Cxx.Op → Nat
  | .plus | .minus | .star | .amp | .plusPlus | .minusMinus | .call => 3
  | .tilde | .exclaim => 1
  | _ => 2

def arityOk (f : Fn) (callArgs : Nat) : Bool :=
  f.tparams > 0 || (opArity f.op &&& (if callArgs == 1 then 1 else 2)) != 0

/-- CppInterOp.cpp 6977-7064 `GetOperator`, with each candidate's acting context (the class that
declares a member). -/
def jankGetOperator (w : W5) (fx : Fix) (op : Cxx.Op) (argTypes : List CType) : List (Fn × String) :=
  let named := w.allFns.filter fun f => f.op == op && arityOk f argTypes.length
  -- (1) unqualified lookup from the TU scope; using-declarations resolved (6999-7006)
  let tu := (named.filter fun f => f.member.isNone && f.friendOf.isNone && f.ns == "") ++
    (usingTargets w "").filter fun f => f.op == op && arityOk f argTypes.length
  -- (2, 3) LookupQualifiedName in each associated namespace; a UsingShadowDecl is neither a
  -- FunctionTemplateDecl nor a FunctionDecl (7026-7029)
  let nss := (argTypes.flatMap (assocNs w)).eraseDups
  let viaNs := nss.flatMap fun n =>
    let reach := qualifiedNs w 4 n
    (named.filter fun f => f.member.isNone && f.friendOf.isNone && reach.contains f.ns) ++
      (if fx.usingNs then reach.flatMap fun m => (usingTargets w m).filter fun f => f.op == op && arityOk f argTypes.length else [])
  -- (4) each associated class: its own members (shadows dropped) and hidden friends
  let acs := (argTypes.flatMap (assocClasses w)).eraseDups
  let first := (argTypes.head?.bind classOf)
  let ctxOf (f : Fn) (c : String) : String :=
    if fx.usingCtx then
      match first.bind w.cls with
      | some fc => if fc.usingOps.any (fun (b, o) => o == op && (classAndBases w b).contains c) then fc.name else c
      | none => c
    else c
  let members : List (Fn × String) :=
    if fx.hide then
      match first with
      | some n => ((memberLookup w op n).toOption.getD []).filter fun (f, _) => arityOk f argTypes.length
      | none => []
    else acs.flatMap fun c => (named.filter fun f => f.member == some c).map fun f => (f, ctxOf f c)
  let viaCls := members ++ (acs.flatMap fun c => (named.filter fun f => f.friendOf == some c).map (·, ""))
  dedupFns ((tu ++ viaNs).map (·, "") ++ viaCls)

/-- What jank's analysis decides. -/
inductive JA where
  | builtin (t : CType)
  | chosen (c : Cand)
  | error (msg : String)
  deriving Inhabited

/-- analyze/processor.cpp: the built-in path (`build_builtin_operator_call`) or `GetOperator` and
`find_best_overload`; for `.call`, `build_indirect_cpp_call` (a class object only). -/
def jankAnalyze (p : Platform) (w : W5) (fx : Fix) (op : Cxx.Op) (ops : List Operand) : JA :=
  let x := w.xworld
  let jt := ops.map (·.jankType)
  let t0 := nonRef (jt.headD .null)
  let builtinPath := op != .call &&
    ((op == .amp && ops.length == 1) ||
     (Paths.isPrimitive t0 && (ops.length == 1 || Paths.isPrimitive (nonRef (jt.getD 1 .null)))))
  if op == .call && classOf t0 == none then .error "There is no call operator."
  else if builtinPath then
    let t := if fx.builtinVK then builtinOp p x op (ops.map fun o => opnd (o.type, o.cxxVK))
      else CppInterOp.getBuiltinOperatorType p x op jt
    if t.isNull then .error "The operator is not supported for these types." else .builtin t
  else
    let fns := jankGetOperator w fx op jt
    let args := ops.map fun o => (o.type, jankArgVK fx o)
    let obj := args.head?
    let fnCands := fns.map fun (f, ctx) =>
      if f.member.isSome then fnCand p w f ctx obj args.tail else fnCand p w f "" none args
    let extra := (if fx.builtinCands && op != .call then builtinCands p w op args ((nonMemberCands w op (args.map (·.1))).map (·.1)) else []) ++
      (if fx.surrogates && op == .call then surrogates p w (obj.map (·.1) |>.getD .null) args.tail else [])
    if fns.isEmpty && extra.isEmpty then .error "The operator is not supported for the type."
    else match bestViable (fnCands ++ extra) with
      | (some c, _) =>
        if c.fn?.any (·.deleted) then .error "The function cannot be called, since it's deleted."
        else if c.builtin then
          let t := builtinAfterSelect p w op args c
          if t.isNull then .error "built-in" else .chosen { c with ret := t }
        else .chosen c
      | (none, []) => .error "No matching overload."
      | (none, g) => .error s!"This call is ambiguous between {g.length} different overloads."

/-- The value categories of the emitted arguments: every operand is a named variable (an lvalue);
`cpp_call` wraps one in `std::move` when the chosen function's parameter is an rvalue reference
(cpp_processor.cpp 1410-1417), `cpp_member_call` never (1755-1764). -/
def emittedVK (fx : Fix) (member : Bool) (param : CType) : VK :=
  if isRValueReferenceType param && (!member || fx.memberMove) then .xvalue else .lvalue

/-- The outcome of a case. -/
inductive Out where
  | val (key : String) (v : Int)
  | builtinT (t : CType)
  | err (stage : String) (msg : String)
  deriving Inhabited

def Out.show : Out → String
  | .val k v => s!"{v} (calls {k})"
  | .builtinT t => s!"the built-in operator ({tyText t})"
  | .err s m => s!"{s} error: {m}"

def bodyValue (c : Cand) : Int :=
  match c.fn? with
  | some f => match f.body with
    | .const v => v
    | .lrefT i a b => if isLValueReferenceType (c.targs.getD i .null) then a else b
    | .assign => 1000
  | none => if c.surrogate then 7 else 0

def candOut (c : Cand) : Out :=
  if c.builtin then .builtinT (nonRef c.ret).canonical.unqual else .val c.key (bodyValue c)

/-- Clang compiling the emitted text: `obj.operator@(args)` (member lookup in the object's class),
`N::operator@(args)` (qualified lookup in N: its declarations, its using-declarations, its
using-directives; no ADL), or an unqualified `operator@(args)` for a global or hidden friend
(unqualified lookup and ADL). -/
def jit (p : Platform) (w : W5) (fx : Fix) (op : Cxx.Op) (ops : List Operand) (c : Cand) : Out :=
  if c.builtin || c.surrogate then candOut c
  else match c.fn? with
  | none => candOut c
  | some f =>
    let member := f.member.isSome
    let rest := if member then ops.tail else ops
    let args := (rest.zip (c.params ++ List.replicate rest.length .null)).map fun (o, prm) =>
      (o.type, emittedVK fx member prm)
    let cands : Except String (List Cand) :=
      if member then do
        let o := ops.headD default
        let some cls := classOf o.type | throw "no class"
        let ms ← memberLookup w op cls
        return ms.map fun (g, ctx) => fnCand p w g ctx (some (o.type, .lvalue)) args
      else if f.friendOf.isSome || f.ns == "" then
        pure ((nonMemberCands w op (args.map (·.1))).map fun (g, _) => fnCand p w g "" none args)
      else
        let reach := qualifiedNs w 4 f.ns
        let decls := (w.allFns.filter fun g => g.op == op && g.member.isNone && g.friendOf.isNone && reach.contains g.ns) ++
          reach.flatMap fun m => (usingTargets w m).filter (·.op == op)
        pure ((dedupFns (decls.map (·, ""))).map fun (g, _) => fnCand p w g "" none args)
    match cands with
    | .error e => .err "JIT" e
    | .ok cs => match bestViable cs with
      | (some c', _) => if c'.fn?.any (·.deleted) then .err "JIT" s!"`{c'.key}` is deleted" else candOut c'
      | (none, []) => .err "JIT" "no matching function for the emitted call"
      | (none, g) => .err "JIT" s!"the emitted call is ambiguous ({g.length})"

def jankOut (p : Platform) (w : W5) (fx : Fix) (op : Cxx.Op) (ops : List Operand) : Out :=
  match jankAnalyze p w fx op ops with
  | .error m => .err "analysis" m
  | .builtin t => .builtinT (nonRef t).canonical.unqual
  | .chosen c => jit p w fx op ops c

def cppOut (p : Platform) (w : W5) (op : Cxx.Op) (ops : List Operand) : Out :=
  match cppResolve p w op (ops.map fun o => (o.type, o.cxxVK)) with
  | .error e => .err "C++" e
  | .ok c => candOut c

def agree : Out → Out → Bool
  | .err .., .err .. => true
  | .val _ a, .val _ b => a == b
  | .builtinT a, .builtinT b => a == b
  | _, _ => false

end Jank.R5.Interop.Ops5
