import Jank.R4.Interop.TopLevel

/-!
# Round 4: class templates through jank's constructor syntax

Round 3 settled class templates by reading (SemaTemplate 5639-5650: an integral template argument,
passed as `long long` text, is converted back to an expression and checked against the parameter
as C++ would). This file replicates the path round 3 did not follow: a constructor call on a class
template's *name*, `(cpp/X. args…)`.

jank: `analyze_cpp_symbol` (processor.cpp 3855) strips the trailing `.`, `resolve_scope` finds the
`ClassTemplateDecl`, and `build_cpp_value` (3700-3760) instantiates it with *no* arguments
(`cpp_util::instantiate(scope, {})`, cpp_util.cpp 84-106 → CppInterOp.cpp 6644
`CompleteTemplateArguments` → `Sema::CheckTemplateArgumentList`), which succeeds exactly when every
template parameter has a default, giving `X<defaults…>`; otherwise "`X` cannot be constructed
because it is missing the necessary template parameters" (documented in the book's
`reference/error/analyze/invalid-cpp-constructor-call.md`). The constructor is then chosen in
`X<defaults…>` (`build_cpp_call`, `lookup_constructors` + `BestOverloadMatch`) and the arguments are
converted to its parameters (codegen `static_cast<P>(arg)`, cpp_processor.cpp 1670-1720).

C++ ([over.match.class.deduct], C++17 class template argument deduction): `X(args…)` forms one
deduction guide per constructor, deduces the template parameters from the arguments (a by-value
`T` deduces the argument's decayed type), and uses a default only for a parameter the guide cannot
deduce. So when a parameter is deducible from the arguments, C++ uses the argument's type where
jank uses the default.
-/

namespace Jank.R4.Interop.Templates

open Jank.Interop
open Jank.R3.Interop
open Jank.R3.Interop.Clang
open Jank.R4.Interop.TopLevel (Val convertTo)

/-- A class template: its type parameters' defaults, its constructors (by-value parameters as
patterns) and the member `v` the program reads back (`(cpp/.-v (cpp/X. …))`), initialized from the
constructor's first parameter (or `0` for a constructor without parameters). -/
structure ClassTmpl where
  name : String
  source : String
  defaults : List (Option CType)
  ctors : List (List TPat)
  member : TPat
  deriving Inhabited

def ClassTmpl.tparams (t : ClassTmpl) : Nat := t.defaults.length

def subst (args : List CType) : TPat → Option CType
  | .param i => args[i]?
  | .fixed t => some t

/-- Constructor overload resolution in a specialization: the best viable constructor
(round 3's `paramConv` and `bestViable`), with the implicit copy constructor never viable for the
builtin arguments searched here. -/
def chooseCtor (p : Platform) (targs : List CType) (t : ClassTmpl) (args : List CType) : Option (List CType) :=
  let cands : List (Clang.Cand × List CType) := t.ctors.zipIdx.filterMap fun (ps, i) => do
    let pts ← ps.mapM (subst targs)
    let ics := (args.zip pts).map fun (a, prm) => paramConv p Jank.R3.Interop.Worlds.x3 false a .prvalue prm
    let f : FnDecl := { name := s!"{t.name}#{i}", params := pts, required := pts.length, isCtor := true }
    some ({ fn := f, ics, viable := args.length == pts.length && ics.all ICS.ok }, pts)
  match Clang.bestViable (cands.map (·.1)) with
  | (some b, _) => (cands.find? (·.1.fn.name == b.fn.name)).map (·.2)
  | _ => none

/-- jank: `X<defaults…>`, then its constructor. `.ok (specialization arguments, chosen ctor's
parameter types)` or the analysis error. -/
def jankCtor (p : Platform) (t : ClassTmpl) (args : List CType) : Except String (List CType × List CType) :=
  if !t.defaults.all Option.isSome then
    .error s!"`{t.name}` cannot be constructed because it is missing the necessary template parameters."
  else
    let targs := t.defaults.filterMap id
    match chooseCtor p targs t args with
    | some ps => .ok (targs, ps)
    | none => .error s!"No matching constructor of `{t.name}<…>` for these arguments."

/-- Deduction for one guide: by-value `T` deduces the argument's decayed unqualified type;
conflicting deductions fail; an undeduced parameter takes its default, else the guide fails. -/
def deduceGuide (t : ClassTmpl) (ps : List TPat) (args : List CType) : Option (List CType) := Id.run do
  if ps.length != args.length then return none
  let mut got : List (Option CType) := List.replicate t.tparams none
  for (pp, a) in ps.zip args do
    match pp with
    | .param i =>
      let d := (decayed a).canonical.unqual
      match got[i]? with
      | some (some prev) => if prev.canonical != d then return none
      | _ => got := got.set i (some d)
    | .fixed _ => pure ()
  let filled := (got.zip t.defaults).map fun (g, d) => g <|> d
  if filled.all Option.isSome then return some (filled.filterMap id) else return none

/-- C++: the guides that deduce, then the best of them by overload resolution on the deduced
parameter types (the copy deduction candidate is never viable for builtin arguments). -/
def cppCtor (p : Platform) (t : ClassTmpl) (args : List CType) : Except String (List CType × List CType) :=
  let guides : List (Clang.Cand × List CType × List CType) := t.ctors.zipIdx.filterMap fun (ps, i) => do
    let targs ← deduceGuide t ps args
    let pts ← ps.mapM (subst targs)
    let ics := (args.zip pts).map fun (a, prm) => paramConv p Jank.R3.Interop.Worlds.x3 false a .prvalue prm
    let f : FnDecl := { name := s!"guide#{i}", params := pts, required := pts.length }
    some ({ fn := f, ics, viable := ics.all ICS.ok, fromTemplate := true }, targs, pts)
  match Clang.bestViable (guides.map (·.1)) with
  | (some b, _) =>
    match guides.find? (·.1.fn.name == b.fn.name) with
    | some (_, targs, _) =>
      match chooseCtor p targs t args with
      | some ps => .ok (targs, ps)
      | none => .error "no viable constructor"
    | none => .error "?"
  | (none, []) => .error "class template argument deduction failed"
  | (none, _) => .error "ambiguous deduction guides"

/-- The value `(cpp/.-v (cpp/X. args…))` reads: the first argument converted to the chosen
constructor's first parameter, then to the member's type, then boxed (`0` without arguments). -/
def memberValue (p : Platform) (t : ClassTmpl) (targs : List CType) (ctorParams : List CType)
    (argVals : List Val) : Option Val := do
  let mt ← subst targs t.member
  let v0 : Val := match argVals.head?, ctorParams.head? with
    | some v, some pt => match (nonRef pt).canonical.unqual with
      | .b k => (convertTo p k v).getD v
      | _ => v
    | _, _ => .int 0
  match (nonRef mt).canonical.unqual with
  | .b k => convertTo p k v0
  | _ => none

def templates : List ClassTmpl :=
  [{ name := "wrap", source := "template <typename T = int> struct wrap { T v; wrap(T x) : v(x) {} };",
     defaults := [some (.b .int)], ctors := [[.param 0]], member := .param 0 },
   { name := "hold", source := "template <typename T> struct hold { T v; hold(T x) : v(x) {} };",
     defaults := [none], ctors := [[.param 0]], member := .param 0 },
   { name := "both", source := "template <typename A = int, typename B = double> struct both { A v; B w; both(A a, B b) : v(a), w(b) {} };",
     defaults := [some (.b .int), some (.b .double)], ctors := [[.param 0, .param 1]], member := .param 0 },
   { name := "dflt", source := "template <typename T = double> struct dflt { T v; dflt() : v(0) {} dflt(int x) : v(x) {} };",
     defaults := [some (.b .double)], ctors := [[], [.fixed (.b .int)]], member := .param 0 },
   { name := "mixed", source := "template <typename T = long> struct mixed { T v; mixed(T x, int) : v(x) {} mixed(double x) : v(x) {} };",
     defaults := [some (.b .long)], ctors := [[.param 0, .fixed (.b .int)], [.fixed (.b .double)]], member := .param 0 }]

/-- The arguments: jank literals with their C++ types and values. -/
def argForms : List (String × CType × Val) :=
  [("1", .b .int, .int 1), ("2.5", .b .double, .dbl 2.5), ("true", .b .bool, .bool true),
   ("(cpp/long 3)", .b .long, .int 3)]

structure TCase where
  t : ClassTmpl
  args : List (String × CType × Val)
  deriving Inhabited

def TCase.text (c : TCase) : String :=
  s!"(cpp/.-v (cpp/{c.t.name}. {" ".intercalate (c.args.map (·.1))}))"

def allTCases : List TCase :=
  let lists : List (List (String × CType × Val)) :=
    [[]] ++ argForms.map (fun a => [a]) ++ argForms.flatMap fun a => argForms.map fun b => [a, b]
  templates.flatMap fun t => lists.map fun args => { t, args }

def showV : Option Val → String | some v => v.show | none => "no value"

def tJudge (p : Platform) (c : TCase) : Option (String × String) :=
  let tys := c.args.map (·.2.1)
  let vals := c.args.map (·.2.2)
  let tyS (ts : List CType) := ", ".intercalate (ts.map Jank.Interop.CppInterop.getTypeAsString)
  match cppCtor p c.t tys, jankCtor p c.t tys with
  | .error _, .error _ => none
  | .ok (ct, cps), .ok (jt, jps) =>
    let cv := memberValue p c.t ct cps vals
    let jv := memberValue p c.t jt jps vals
    let same := match cv, jv with | some a, some b => a.same b | none, none => true | _, _ => false
    if same && ct.map (·.canonical) == jt.map (·.canonical) then none
    else if same then some ("defaults-instead-of-deduction-same-value",
      s!"{c.text}: C++ deduces `{c.t.name}<{tyS ct}>`; jank uses the defaults `{c.t.name}<{tyS jt}>`; v is {showV cv} in both")
    else some ("defaults-instead-of-deduction",
      s!"{c.text}: C++ deduces `{c.t.name}<{tyS ct}>`, v = {showV cv}; jank uses the defaults `{c.t.name}<{tyS jt}>`, v = {showV jv}")
  | .ok (ct, cps), .error e =>
    let cls := if c.t.defaults.all Option.isSome then "rejects" else "missing-template-arguments (documented)"
    some (cls, s!"{c.text}: C++ deduces `{c.t.name}<{tyS ct}>`, v = {showV (memberValue p c.t ct cps vals)}; jank: {e}")
  | .error ce, .ok (jt, jps) =>
    some ("accepts-ill-formed", s!"{c.text}: C++ {ce}; jank `{c.t.name}<{tyS jt}>`, v = {showV (memberValue p c.t jt jps vals)}")

end Jank.R4.Interop.Templates
