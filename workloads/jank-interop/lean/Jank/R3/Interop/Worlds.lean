import Jank.R3.Interop.JankPaths

/-!
# Round 3 interop worlds: replica (CppInterOp replica + jank paths) against the spec

Each world enumerates its cases (`all*`), judges one case (`judge*`: `none` when jank agrees with
the spec, else `(class, detail)`), and draws a case from named decisions (`body*`) for
Determinismo's `explore`/`exhaust`. A judge can set classes aside (`skip`): the residual search
reruns `exhaust` with every found class set aside until a complete run finds nothing.

Specs: the C++20 standard for what the equivalent C++ does (Clang's own answer where CppInterOp
asks it), jank's book (`book/src/cpp-interop/dsl.md`, `native-exceptions.md`) where it documents
the form, Clojure for the jank-visible value.
-/

namespace Jank.R3.Interop.Worlds

open Determinismo
open Jank.Interop
open Jank.Interop.Search (W runW pickW exploreMixed)
open Jank.R3.Interop.Clang
open Jank.R3.Interop.CppInterOp
open Jank.R3.Interop.Paths

abbrev Verdict := Option (String × String)

def tshow (t : CType) : String := CppInterop.getTypeAsString t

def aarch64 : Platform := linuxAArch64

/-! ## The world the round-3 programs declare (`cpp/raw`) -/

def fooClass : ClassDecl :=
  { name := "Foo",
    fields := [{ name := "x", type := .b .int }, { name := "secret", type := .b .int, isPrivate := true }],
    methods := [{ name := "get", isMethod := true, isConst := true, ret := .b .int },
                { name := "set", isMethod := true, params := [.b .int], required := 1 },
                { name := "f", isMethod := true, params := [.b .int], required := 1, ret := .b .int },
                { name := "f", isMethod := true, params := [.b .double], required := 1, ret := .b .double },
                { name := "scale", isMethod := true, params := [.lref (.const (.b .long))], required := 1, ret := .b .long },
                { name := "make", isMethod := true, isStatic := true, ret := .ptr (.record "Foo") },
                { name := "sf", isMethod := true, isStatic := true, params := [.b .int], required := 1, ret := .b .int },
                { name := "sf", isMethod := true, isStatic := true, params := [.b .double], required := 1, ret := .b .double }] }

def barClass : ClassDecl := { name := "Bar", bases := ["Foo"] }
def pbClass : ClassDecl := { name := "PB", bases := ["Foo"] }
def leftClass : ClassDecl := { name := "L", fields := [{ name := "y", type := .b .int }] }
def rightClass : ClassDecl := { name := "R", fields := [{ name := "y", type := .b .int }] }
def ambClass : ClassDecl := { name := "Amb", bases := ["L", "R"] }
def metersClass : ClassDecl := { name := "meters", convertsTo := [.b .double] }
def flagClass : ClassDecl := { name := "flag" }
def stdException : ClassDecl := { name := "std::exception" }
def stdRuntimeError : ClassDecl := { name := "std::runtime_error", bases := ["std::exception"] }

/-- Round 2's `world0` plus the round-3 declarations. -/
def x3 : XWorld :=
  { w := { world0 with classes := world0.classes ++
             [fooClass, barClass, pbClass, leftClass, rightClass, ambClass, metersClass, flagClass,
              stdException, stdRuntimeError] },
    privateBases := [("PB", "Foo")],
    explicitConvertsTo := [("flag", .b .bool)],
    staticFields := [("Foo", "count", .b .int)],
    templates :=
      [{ name := "add", tparams := 1, params := [.param 0, .param 0], ret := .param 0 },
       { name := "zero", tparams := 1, params := [], ret := .param 0 },
       { name := "ident", tparams := 1, params := [.param 0], ret := .param 0 },
       { name := "cast_to", tparams := 2, params := [.param 1], ret := .param 0 }] }

/-- Public, unambiguous base ([conv.ptr]/3, [class.access.base]). -/
def publicBase (x : XWorld) (d b : CType) : Bool :=
  derivedFrom x d b && !(x.privateBases.any fun (dd, bb) =>
    (view d).canonical.unqual == .record dd && (bb == (match (view b).canonical.unqual with | .record n => n | _ => "") ||
      derivedFrom x (.record bb) (view b)))

/-! ## VIII'. The DSL's integer modifiers, on CppInterOp's `Get{Signed,Unsigned,Short,Long}Type` -/

structure DslCase where
  p : Platform
  base : String
  mods : List String
  deriving Inhabited

def dslBases : List String :=
  ["char", "int", "short", "long", "bool", "double", "float", "wchar_t", "char16_t", "size_t", "color"]
def dslMods : List String := ["signed", "unsigned", "short", "long", "const"]

def DslCase.text (c : DslCase) : String :=
  c.mods.foldr (fun m acc => s!"(:{m} {acc})") s!"cpp/{c.base}"

/-- The type the same specifiers name in C++ (`[dcl.type.simple]`, Table 17): `const` anywhere;
`signed`/`unsigned`/`short`/`long` only with `char`, `int`, `double` (one `long`) as the rules
allow; never with a typedef name, an enum, `bool`, `float`, `wchar_t` or `charN_t`. -/
def dslSpec (c : DslCase) : Option CType :=
  let cnt (m : String) := (c.mods.filter (· == m)).length
  let (b, s0, l0) : String × Nat × Nat := match c.base with
    | "short" => ("int", 1, 0) | "long" => ("int", 0, 1) | b => (b, 0, 0)
  let fixed : Option CType := match b with
    | "wchar_t" => some (.b .wchar) | "char16_t" => some (.b .char16)
    | "size_t" => some sizeT | "color" => some (.enum "color") | _ => none
  let core : Option CType := match fixed with
    | some t => if cnt "signed" + cnt "unsigned" + cnt "short" + cnt "long" == 0 then some t else none
    | none => (Spec.specifierType b (cnt "signed") (cnt "unsigned") (cnt "short" + s0) (cnt "long" + l0)).map CType.b
  core.map fun t => if cnt "const" > 0 then CType.cv true false t else t

def dslJank (c : DslCase) : Except String CType :=
  match c.mods.foldr (fun m acc => .kw m [acc]) (Paths.TForm.sym c.base) with
  | f => Paths.analyzeType c.p x3 f

def dslJudge (c : DslCase) : Verdict :=
  let plat := if c.p.charSigned then "x86-64" else "AArch64 Linux"
  match dslSpec c, dslJank c with
  | none, .error _ => none
  | some t, .ok u =>
    if t.canonical == u.canonical then none
    else
      let cls :=
        if (builtin? t == some .llong || builtin? t == some .ullong) then "long-long-unreachable"
        else if builtin? t == some .schar && builtin? u == some .char then "signed-char-is-char"
        else if builtin? t == some .uchar && builtin? u == some .char then "unsigned-char-is-char"
        else "wrong-type"
      some (cls, s!"{c.text} ({plat}): C++ `{tshow t}`; jank `{tshow u}`")
  | none, .ok u => some ("accepts-non-type", s!"{c.text} ({plat}): not a C++ type; jank accepts it as `{tshow u}`")
  | some t, .error e => some ("rejects-type", s!"{c.text} ({plat}): C++ `{tshow t}`; jank: {e}")

def dslChains (n : Nat) : List (List String) :=
  (List.range (n + 1)).flatMap fun k =>
    (List.replicate k dslMods).foldr (fun ms acc => ms.flatMap fun m => acc.map (m :: ·)) [[]]
    |>.filter fun ch => (ch.filter (· == "const")).length ≤ 1

def allDsl (ps : List Platform) (bases : List String) (n : Nat) : List DslCase :=
  ps.flatMap fun p => bases.flatMap fun b => (dslChains n).map fun ms => { p, base := b, mods := ms }

/-- Round 2's world VIII exactly (x86-64, 7 bases, chains of ≤ 2 of the four integer modifiers),
now on CppInterOp's answers. -/
def round2Dsl (p : Platform) : List DslCase :=
  let mods := ["signed", "unsigned", "short", "long"]
  let chains : List (List String) := [[]] ++ mods.map (fun m => [m]) ++ mods.flatMap (fun m => mods.map fun m' => [m, m'])
  ["char", "int", "short", "long", "bool", "double", "float"].flatMap fun b => chains.map fun ms => { p, base := b, mods := ms }

def dslBody (skip : List String) : EStateM Stop W Unit := do
  let p ← pickW "r3.dsl.platform" [x86_64, aarch64]
  let n ← decide (σ := W) "r3.dsl.depth" 4
  let mut mods := []
  for _ in List.range n do
    mods := mods ++ [← pickW "r3.dsl.modifier" dslMods]
  let base ← pickW "r3.dsl.base" dslBases
  if (mods.filter (· == "const")).length ≤ 1 then
    if let some (cls, d) := dslJudge { p, base, mods } then
      if !skip.contains cls then violate (σ := W) s!"dsl:{cls}" d

/-! ## X. `(:member t m)`, `(:member* t m)`, `(:&member t m)` against the book and C++ -/

structure MemCase where
  kw : String
  t : Paths.TForm
  m : Paths.TForm
  /-- Type position (`analyze_type`) or value position (`#cpp`). -/
  typePos : Bool
  deriving Inhabited

def memTypes : List Paths.TForm := [.sym "Foo", .sym "Bar", .kw "*" [.sym "Foo"], .sym "int"]
def memSeconds : List Paths.TForm :=
  [.sym "x", .sym "secret", .sym "get", .sym "f", .sym "make", .sym "sf", .sym "count", .sym "missing",
   .sym "int", .kw "fn" [.sym "int", .vec []], .kw "*" [.kw "fn" [.sym "void", .vec []]]]

def MemCase.text (c : MemCase) : String :=
  let f := s!"(:{c.kw} {c.t.text} {c.m.text})"
  if c.typePos then s!"(cpp/cast {f} ...)" else s!"#cpp {f}"

/-- What the book (dsl.md: "`(:member t name)` nests into a type", "`(:member* t mt)` builds a
pointer to member type", "`(:&member t mt)` builds a pointer to member value", with the examples
`(:member* Foo (:fn int [...]))` and `#cpp (:&member (std.pair int bool) first)`) and C++
(`Foo::name`, `mt Foo::*`, `&Foo::name`) give: the type, the value's type, or an error. -/
def memSpec (c : MemCase) : Except String DslOut :=
  match Paths.analyzeType x86_64 x3 c.t with
  | .error e => .error e
  | .ok ty =>
    let cls? := match view ty with | .record n => some n | _ => none
    match cls? with
    | none => .error "not a class"
    | some cls =>
      match c.kw with
      | "member*" =>
        -- `mt` is a type
        match Paths.analyzeType x86_64 x3 c.m with
        | .ok mt => if c.typePos then .ok (.type (.memPtr cls mt)) else .error "a type, not a value"
        | .error e => .error e
      | "member" =>
        let name := match c.m with | .sym n => n | _ => ""
        if name.isEmpty then .error "not a member name" else
        match memberLookup x3 cls name with
        | [d] => match d with
          | .variable _ t _ _ => if c.typePos then .error "a value, not a type" else .ok (.value (.lref t) d)
          | .function f => if f.isStatic && !c.typePos then .ok (.value (.ptr (.fn f.ret f.params)) d) else .error "not a type, not a value"
          | _ => .error "not a type, not a value"
        | ds => if !c.typePos && ds.length > 1 && ds.all (fun d => match d with | .function f => f.isStatic | _ => false)
                then .ok (.value .null (ds.headD default)) else .error "no such member"
      | _ =>
        let name := match c.m with | .sym n => n | _ => ""
        if name.isEmpty then .error "not a member name" else
        if c.typePos then .error "a value, not a type"
        else match memberLookup x3 cls name with
          | [d@(.field o f)] => if f.isPrivate then .error "private" else .ok (.value (.memPtr o f.type) d)
          | [d@(.function f)] =>
            if f.isStatic then .error "static" else
            .ok (.value (.memPtr f.owner (if f.isConst then .cv true false (.fn f.ret f.params) else .fn f.ret f.params)) d)
          | _ => .error "no single member"

def memJank (c : MemCase) : Except String DslOut :=
  if c.typePos then (Paths.analyzeType x86_64 x3 (.kw c.kw [c.t, c.m])).map DslOut.type
  else if c.kw == "member*" then
    -- processor.cpp:5539: a `cpp_type` in value position (rejected where a value is used)
    match Paths.analyzeType.memberForm x86_64 x3 c.kw c.t c.m with
    | .ok _ => .error "A C++ value was expected here, but a type was found."
    | .error e => .error e
  else Paths.analyzeType.memberForm x86_64 x3 (if c.kw == "&member" then "&member" else c.kw) c.t c.m

def outType : DslOut → CType | .type t => t | .value t _ => t

def memJudge (c : MemCase) : Verdict :=
  let ptrClass := match c.t with | .kw "*" _ => true | _ => false
  match memSpec c, memJank c with
  | .error e, .ok b =>
    if ptrClass then some ("pointer-type-as-class", s!"{c.text}: C++/book: {e}; jank looks through the pointer (GetScopeFromType) and gives `{tshow (outType b)}`")
    else
      let cls := if c.kw == "member*" then "member*-takes-a-name" else if c.kw == "&member" then "&member-skips-access" else "member-function-as-value"
      some (cls, s!"{c.text}: C++/book: {e}; jank gives `{tshow (outType b)}`")
  | .error _, .error _ => none
  | .ok a, .ok b =>
    let ta := outType a
    if ta.isNull || ta.canonical == (outType b).canonical then none
    else some ("member-type", s!"{c.text}: C++/book `{tshow ta}`; jank `{tshow (outType b)}`")
  | .ok a, .error e =>
    let cls := if c.kw == "member*" then "member*-takes-a-name" else if c.kw == "member" then "member-overloaded-static" else "rejects"
    some (cls, s!"{c.text}: C++/book `{tshow (outType a)}`; jank: {e}")

def allMem : List MemCase :=
  ["member", "member*", "&member"].flatMap fun kw => memTypes.flatMap fun t => memSeconds.flatMap fun m =>
    [true, false].map fun typePos => { kw, t, m, typePos }

def memBody (skip : List String) : EStateM Stop W Unit := do
  let kw ← pickW "r3.member.kw" ["member", "member*", "&member"]
  let t ← pickW "r3.member.type" memTypes
  let m ← pickW "r3.member.second" memSeconds
  let typePos := (← decide (σ := W) "r3.member.type_position" 2) == 0
  if let some (cls, d) := memJudge { kw, t, m, typePos } then
    if !skip.contains cls then violate (σ := W) s!"member:{cls}" d

/-! ## XI. Calls through function pointers and pointers to members (`build_indirect_cpp_call`) -/

structure Callee where
  text : String
  type : CType
  deriving Inhabited

def callees : List Callee :=
  [{ text := "(:&member Foo x)", type := .memPtr "Foo" (.b .int) },
   { text := "(:&member Foo get)", type := .memPtr "Foo" (.cv true false (.fn (.b .int) [])) },
   { text := "(:&member Foo set)", type := .memPtr "Foo" (.fn (.b .void) [.b .int]) },
   { text := "(:&member Foo scale)", type := .memPtr "Foo" (.fn (.b .long) [.lref (.const (.b .long))]) },
   { text := "cpp/fp_cref_long", type := .lref (.ptr (.fn (.b .long) [.lref (.const (.b .long))])) },
   { text := "cpp/fp_double", type := .lref (.ptr (.fn (.b .void) [.b .double])) },
   { text := "cpp/fp_string", type := .lref (.ptr (.fn (.b .void) [.lref (.const stdString)])) },
   { text := "cpp/fp_vector", type := .lref (.ptr (.fn (.b .void) [vectorInt])) }]

/-- An argument: jank text, its analyzed type, and whether C++ sees an lvalue. -/
structure Arg where
  text : String
  type : CType
  deriving Inhabited

def objArgs : List Arg :=
  [{ text := "foo", type := .record "Foo" }, { text := "cpp/gfoo", type := .lref (.record "Foo") },
   { text := "cfoo", type := .lref (.const (.record "Foo")) },
   { text := "pfoo", type := .ptr (.record "Foo") }, { text := "cpfoo", type := .ptr (.const (.record "Foo")) },
   { text := "pbar", type := .ptr (.record "Bar") }, { text := "ppb", type := .ptr (.record "PB") }]

def valArgs : List Arg :=
  [{ text := "1", type := .b .int }, { text := "(cpp/long 2)", type := .b .long },
   { text := "2.5", type := .b .double }, { text := "(cpp/size_t 3)", type := sizeT },
   { text := "\"abc\"", type := .lref (cStringT 3) }]
where cStringT (n : Nat) : CType := .array (.cv true false (.b .char)) (some (n + 1))

structure CallCase where
  callee : Callee
  args : List Arg
  deriving Inhabited

def CallCase.text (c : CallCase) : String :=
  s!"(#cpp {c.callee.text} " ++ " ".intercalate (c.args.map (·.text)) ++ ")"

/-- C++: `(obj.*pm)(args)` / `(p->*pm)(args)` / `fp(args)`: the object's class is the member's
class or a public unambiguous base of it, a const object needs a const member function, and each
argument copy-initializes its parameter ([over.ics] / [dcl.init.ref]: a `const T&` binds a
converted temporary; explicit constructors are not used). -/
def callSpec (c : CallCase) : Bool :=
  let argOk (a : Arg) (prm : CType) : Bool :=
    let vk : VK := if isLValueReferenceType a.type then .lvalue else .prvalue
    (paramConv x86_64 x3 false (nonRef a.type) vk prm).ok
  match view (nonRef c.callee.type) with
  | .memPtr cls mt =>
    match c.args with
    | [] => false
    | o :: rest =>
      let ot := nonRef o.type
      let (objCls, objConst) := match view ot with
        | .ptr u => (view u, isConstQualified u)
        | u => (u, isConstQualified ot)
      let clsOk := objCls.canonical.unqual == .record cls || publicBase x3 objCls (.record cls)
      match view mt with
      | .fn _ ps =>
        let constOk := !objConst || isConstQualified mt
        clsOk && constOk && ps.length == rest.length && (rest.zip ps).all fun (a, p) => argOk a p
      | _ => clsOk && rest.isEmpty
  | .ptr u => match view u with
    | .fn _ ps => ps.length == c.args.length && (c.args.zip ps).all fun (a, p) => argOk a p
    | _ => false
  | _ => false

def callJudge (c : CallCase) : Verdict :=
  let jank := Paths.indirectCall x86_64 x3 c.callee.type (c.args.map (·.type))
  match callSpec c, jank with
  | true, .ok _ | false, .error _ => none
  | true, .error e =>
    let cls := if e.contains "not convertible" && c.args.any (fun a => Clang.isPointerType (nonRef a.type) && isConstQualified (pointeeOf (nonRef a.type)))
                  && isPointerToMemberType (nonRef c.callee.type) then "pm-const-object-pointer"
               else if e.contains "not convertible" then "converting-reference-parameter"
               else "rejects-valid"
    some (cls, s!"{c.text}: C++ valid; jank: {e}")
  | false, .ok _ =>
    let cls := if c.args.any (fun a => a.text == "ppb") then "private-base-object"
               else if c.callee.text == "cpp/fp_vector" then "explicit-constructor-argument" else "accepts-invalid"
    some (cls, s!"{c.text}: C++ ill-formed; jank accepts")

def allCalls : List CallCase :=
  callees.flatMap fun ce =>
    if isPointerToMemberType (nonRef ce.type) then
      objArgs.flatMap fun o => [[o]] ++ valArgs.map (fun v => [o, v]) |>.map fun as => { callee := ce, args := as }
    else valArgs.map fun v => { callee := ce, args := [v] }

def callBody (skip : List String) : EStateM Stop W Unit := do
  let c ← pickW "r3.call.case" allCalls
  if let some (cls, d) := callJudge c then
    if !skip.contains cls then violate (σ := W) s!"call:{cls}" d

/-! ## XII. Function templates with explicit template arguments (`(#cpp (f T) args...)`) -/

structure TmplCase where
  tmpl : FnTemplate
  explicitArgs : List CType
  callArgs : List CType
  deriving Inhabited

def TmplCase.text (c : TmplCase) : String :=
  let ta := " ".intercalate (c.explicitArgs.map fun t => "cpp/" ++ tshow t)
  let lit (t : CType) := if t == .b .double then "2.5" else if t == .b .long then "(cpp/long 2)" else "1"
  s!"(#cpp ({c.tmpl.name} {ta})" ++ String.join (c.callArgs.map (" " ++ lit ·)) ++ ")"

def substT (args : List CType) : TPat → Option CType
  | .param i => args[i]?
  | .fixed t => some t

/-- Deduction of the remaining template parameters from call arguments ([temp.deduct.call]: a
by-value parameter `T` deduces the argument's decayed, unqualified type; conflicting deductions
fail). -/
def deduce (t : FnTemplate) (explicitArgs : List CType) (callArgs : List CType) : Option (List CType) := Id.run do
  let mut got : List (Option CType) := (List.range t.tparams).map fun i => explicitArgs[i]?
  if t.params.length != callArgs.length then return none
  for (pp, a) in t.params.zip callArgs do
    match pp with
    | .param i =>
      if i < explicitArgs.length then continue
      let d := (decayed a).canonical.unqual
      match got[i]? with
      | some (some prev) => if prev.canonical != d then return none
      | _ => got := got.set i (some d)
    | .fixed _ => pure ()
  if got.all Option.isSome then return some (got.filterMap id) else return none

/-- C++ `f<explicit...>(args...)`: the specialization's return type, or none (not viable). -/
def tmplSpec (p : Platform) (c : TmplCase) : Option CType := do
  let args ← deduce c.tmpl c.explicitArgs c.callArgs
  let ps ← c.tmpl.params.mapM (substT args)
  if !(c.callArgs.zip ps).all (fun (a, prm) => (standardConv p x3 a .prvalue prm).isSome) then none
  substT args c.tmpl.ret

/-- jank: processor.cpp:5601-5735 instantiates the template from the explicit arguments alone
(CppInterOp.cpp:6580 `DeduceTemplateArguments(FTD, &TLI, ..., IsAddressOfFunction)`: every
template parameter must be given), then the call (processor.cpp:4111 → build_cpp_call:551-553)
looks the name up again (`get_functions_using_name(get_parent_scope(spec), get_name(spec))`
finds the template, not the specialization) and `BestOverloadMatch` deduces from the call
arguments alone (CppInterOp.cpp:2114 `AddTemplateOverloadCandidate` with empty explicit
arguments). -/
def tmplJank (p : Platform) (c : TmplCase) : Except String CType := do
  if c.explicitArgs.length < c.tmpl.tparams then
    throw "Unable to instantiate this template with these arguments."
  match tmplSpec p { c with explicitArgs := [] } with
  | some r => pure r
  | none => throw s!"No matching overload of the `{c.tmpl.name}` function was found for this call."

def tmplJudge (c : TmplCase) : Verdict :=
  match tmplSpec x86_64 c, tmplJank x86_64 c with
  | none, .error _ => none
  | some t, .ok u => if t.canonical == u.canonical then none
      else some ("explicit-args-dropped", s!"{c.text}: C++ `{c.tmpl.name}<{", ".intercalate (c.explicitArgs.map tshow)}>` returns `{tshow t}`; jank deduces from the arguments and returns `{tshow u}`")
  | some t, .error e => some ("explicit-args-dropped", s!"{c.text}: C++ returns `{tshow t}`; jank: {e}")
  | none, .ok u => some ("accepts-invalid", s!"{c.text}: C++ ill-formed; jank returns `{tshow u}`")

def tmplArgTypes : List CType := [.b .int, .b .double, .b .long]

def allTmpl : List TmplCase :=
  x3.templates.flatMap fun t =>
    let explicits : List (List CType) :=
      [[]] ++ tmplArgTypes.map (fun a => [a]) ++ (if t.tparams ≥ 2 then tmplArgTypes.flatMap fun a => tmplArgTypes.map fun b => [a, b] else [])
    let calls : List (List CType) := (List.range (t.params.length + 1)).flatMap fun n =>
      if n != t.params.length then [] else
      (List.replicate n tmplArgTypes).foldr (fun ts acc => ts.flatMap fun a => acc.map (a :: ·)) [[]]
    (explicits.filter (!·.isEmpty)).flatMap fun e => calls.map fun ca => { tmpl := t, explicitArgs := e, callArgs := ca }

def tmplBody (skip : List String) : EStateM Stop W Unit := do
  let c ← pickW "r3.template.case" allTmpl
  if c.explicitArgs.isEmpty then return
  if let some (cls, d) := tmplJudge c then
    if !skip.contains cls then violate (σ := W) s!"template:{cls}" d

/-! ## XIII. Operators on class operands (`GetOperator`, no built-in candidates) -/

structure OpCase where
  op : Cxx.Op
  opText : String
  args : List CType
  deriving Inhabited

/-- C++ [over.match.oper]: with no operator functions declared, the built-in candidates
([over.built]) take the operands through their implicit conversion functions (an `explicit
operator bool` serves only the contextual conversions of `!`, `&&`, `||`). -/
def opSpec (c : OpCase) : Bool :=
  let conv (t : CType) : List CType :=
    match view (nonRef t) with
    | .record n =>
      let imp := (x3.findClass n).map (·.convertsTo) |>.getD []
      let expl := if c.op == .exclaim || c.op == .ampAmp || c.op == .pipePipe then
          (x3.explicitConvertsTo.filter (·.1 == n)).map (·.2) else []
      imp ++ expl
    | _ => [nonRef t]
  let combos : List (List CType) := c.args.foldr (fun a acc => (conv a).flatMap fun t => acc.map (t :: ·)) [[]]
  combos.any fun ts => !(builtinOp x86_64 x3 c.op (ts.map fun t => { type := t, lvalue := false })).isNull

def opJudge (c : OpCase) : Verdict :=
  let txt := s!"(cpp/{c.opText} " ++ " ".intercalate (c.args.map fun t => if isRecordType t then (match view t with | .record n => n | _ => "") ++ "-value" else tshow t) ++ ")"
  match opSpec c, Paths.classOperatorCall x86_64 x3 c.op c.args with
  | true, .ok _ | false, .error _ => none
  | true, .error e => some ("no-builtin-candidates", s!"{txt}: C++ valid (built-in operator through the conversion function); jank: {e}")
  | false, .ok _ => some ("accepts-invalid", s!"{txt}: C++ ill-formed; jank accepts")

def opOps : List (Cxx.Op × String) :=
  [(.plus, "+"), (.minus, "-"), (.less, "<"), (.equalEqual, "=="), (.exclaim, "!"), (.ampAmp, "&&")]
def opOperands : List CType := [.record "meters", .record "flag", .b .double, .b .int]

def allOps : List OpCase :=
  opOps.flatMap fun (op, t) =>
    let unary := op == .exclaim
    if unary then (opOperands.take 2).map fun a => { op, opText := t, args := [a] }
    else (opOperands.take 2).flatMap fun a => opOperands.map fun b => { op, opText := t, args := [a, b] }

def opBody (skip : List String) : EStateM Stop W Unit := do
  let c ← pickW "r3.operator.case" allOps
  if let some (cls, d) := opJudge c then
    if !skip.contains cls then violate (σ := W) s!"operator:{cls}" d

/-! ## XIV. Data member access `(cpp/.-name obj)` -/

def maObjects : List (String × CType) :=
  [("foo", .record "Foo"), ("bar", .record "Bar"), ("pb", .record "PB"), ("amb", .record "Amb"),
   ("pfoo", .ptr (.record "Foo")), ("pbar", .ptr (.record "Bar"))]
def maNames : List String := ["x", "secret", "count", "y", "missing"]

/-- C++ `obj.name` / `p->name`: class member lookup through the bases (ambiguity is an error),
public access, and a public path to the member's class. -/
def maSpec (cls : String) (name : String) : Bool :=
  match memberLookup x3 cls name with
  | [.field o f] => !f.isPrivate && !f.isProtected && (o == cls || publicBase x3 (.record cls) (.record o))
  | [.variable q _ _ _] => let o := (q.splitOn "::").headD ""; o == cls || publicBase x3 (.record cls) (.record o)
  | _ => false

def maJudge (obj : String × CType) (name : String) : Verdict :=
  let cls := match view (match view obj.2 with | .ptr u => u | t => t) with | .record n => n | _ => ""
  let txt := s!"(cpp/.-{name} {obj.1})"
  match maSpec cls name, Paths.memberAccess x3 name obj.2 with
  | true, .ok _ | false, .error _ => none
  | true, .error e => some ("inherited-static-member", s!"{txt}: C++ valid; jank: {e}")
  | false, .ok t => some ("private-base-member", s!"{txt}: C++ ill-formed (inaccessible through a private base); jank gives `{tshow t}`")

def allMa : List ((String × CType) × String) := maObjects.flatMap fun o => maNames.map fun n => (o, n)

def maBody (skip : List String) : EStateM Stop W Unit := do
  let o ← pickW "r3.member_access.object" maObjects
  let n ← pickW "r3.member_access.name" maNames
  if let some (cls, d) := maJudge o n then
    if !skip.contains cls then violate (σ := W) s!"member-access:{cls}" d

/-! ## XV. `cpp/unsafe-cast` (`IsCStyleConvertible`) against C-style cast validity -/

def ucTypes : List (String × CType) :=
  [("cpp/int", .b .int), ("cpp/long", .b .long), ("cpp/double", .b .double), ("cpp/bool", .b .bool),
   ("cpp/color", .enum "color"), ("cpp/mode", .enum "mode"), ("(:* cpp/int)", .ptr (.b .int)),
   ("(:* (:const cpp/int))", .ptr (.cv true false (.b .int))), ("(:* cpp/void)", .ptr (.b .void)),
   ("std.nullptr_t", .b .nullptr), ("(:member* Foo x)", .memPtr "Foo" (.b .int)), ("std.string", stdString)]

/-- C++ `(T)v` for a non-constant value `v` of the source type ([expr.cast]); only a
`std::nullptr_t` value is a null pointer constant. -/
def ucSpec (src dst : CType) : Bool := cStyleCastOk x86_64 x3 { type := src, npc := isNullPtrType src } dst

def ucJudge (s d : String × CType) : Verdict :=
  let txt := s!"(cpp/unsafe-cast {d.1} <{tshow s.2} value>)"
  match ucSpec s.2 d.2, Paths.unsafeCast x86_64 x3 d.2 s.2 with
  | true, .ok _ | false, .error _ => none
  | true, .error _ =>
    let cls := if isFloatingType s.2 then "floating-source" else if isNullPtrType s.2 then "nullptr-source" else "rejects-valid"
    some (cls, s!"{txt}: a valid C-style cast; jank: Invalid unsafe-cast")
  | false, .ok _ => some ("null-constant-dummy", s!"{txt}: an invalid C-style cast for a non-constant value; jank accepts (CppInterOp casts a literal 0)")

def allUc : List ((String × CType) × (String × CType)) := ucTypes.flatMap fun s => ucTypes.map fun d => (s, d)

def ucBody (skip : List String) : EStateM Stop W Unit := do
  let s ← pickW "r3.unsafe_cast.source" ucTypes
  let d ← pickW "r3.unsafe_cast.target" ucTypes
  if let some (cls, dd) := ucJudge s d then
    if !skip.contains cls then violate (σ := W) s!"unsafe-cast:{cls}" dd

/-! ## XVI. `if` branches of native types, references included (`find_branch_common_type`) -/

def brTypes : List (String × CType) :=
  [("1", .b .int), ("3000000000", .b .long), ("2.5", .b .double), ("true", .b .bool),
   ("cpp/gint", .lref (.b .int)), ("cpp/glong", .lref (.b .long)), ("cpp/gdouble", .lref (.b .double)),
   ("cpp/guint", .lref (.b .uint)), ("cpp/red", .enum "color")]

/-- C++ `c ? a : b` ([expr.cond]): two lvalues of one type → that lvalue; otherwise the usual
arithmetic conversions on the (promoted) operands. Clojure's `(if c a b)` returns the chosen
branch's value unchanged, which the C++ type keeps for these operands except `long`/`double` and
the signed/unsigned mixes (the round-2 IX classes). -/
def brSpec (a b : CType) : CType :=
  if isLValueReferenceType a && isLValueReferenceType b && (nonRef a).canonical == (nonRef b).canonical then a
  else if (nonRef a).canonical.unqual == (nonRef b).canonical.unqual then (nonRef a).canonical.unqual
  else (usualArithmetic x86_64 x3 (nonRef a) (nonRef b)).getD .null

def brJudge (a b : String × CType) : Verdict :=
  let txt := s!"(if c {a.1} {b.1})"
  let spec := brSpec a.2 b.2
  match Paths.findBranchCommonType x86_64 x3 a.2 b.2 with
  | .error e => if spec.isNull then none else some ("rejects", s!"{txt}: C++ `{tshow spec}`; jank: {e}")
  | .ok (t, _, _) =>
    if Jank.Interop.CppUtil.isAnyObject x3.w t then none
    else if (nonRef t).canonical.unqual != (nonRef spec).canonical.unqual then
      some ("reference-branch-narrowed", s!"{txt}: C++ (and the value either branch holds) `{tshow spec}`; jank types the `if` `{tshow t}`")
    else if Clang.isReferenceType t && !Clang.isReferenceType spec then
      some ("reference-typed-if", s!"{txt}: C++ a prvalue `{tshow spec}`; jank types the `if` `{tshow t}` (codegen declares the local without the reference, cpp_processor.cpp:913)")
    else none

def allBr : List ((String × CType) × (String × CType)) := brTypes.flatMap fun a => brTypes.map fun b => (a, b)

def brBody (skip : List String) : EStateM Stop W Unit := do
  let a ← pickW "r3.branch.then" brTypes
  let b ← pickW "r3.branch.else" brTypes
  if let some (cls, d) := brJudge a b then
    if !skip.contains cls then violate (σ := W) s!"branch:{cls}" d

/-! ## XVII. Native exceptions: `(catch T e ...)` against C++ handlers -/

def excThrown : List (String × CType) :=
  [("int", .b .int), ("long", .b .long), ("std::runtime_error", .record "std::runtime_error"),
   ("int *", .ptr (.b .int)), ("const char *", .ptr (.cv true false (.b .char)))]

def excHandlers : List (String × CType) :=
  [("cpp/int", .b .int), ("(:const cpp/int)", .cv true false (.b .int)), ("std.exception", .record "std::exception"),
   ("std.runtime_error", .record "std::runtime_error"), ("(:* cpp/int)", .ptr (.b .int)),
   ("(:array cpp/int 3)", .array (.b .int) (some 3)), ("(:&& cpp/int)", .rref (.b .int)),
   ("(:* (:const cpp/char))", .ptr (.cv true false (.b .char))), ("cpp/long", .b .long)]

/-- [except.handle]/3: does a handler of (adjusted, reference-stripped, cv-stripped) type `h` catch
an exception object of type `e`. -/
def handles (h e : CType) : Bool :=
  let h := (nonRef h).canonical.unqual
  let e := e.canonical.unqual
  if h == e then true
  else if isRecordType h && isRecordType e then publicBase x3 e h
  else match h, e with
    | .ptr hu, .ptr eu => (standardConv x86_64 x3 (.ptr eu) .prvalue (.ptr hu)).isSome && !Clang.isPointerType hu == !Clang.isPointerType eu
    | _, _ => false

/-- C++ for the handler as written: an array (or function) handler type is adjusted to a pointer
([except.handle]/2); an rvalue-reference handler is ill-formed ([except.handle]/1). Returns
(well-formed, catches, a change to `e` is seen by a later `throw;`). -/
def excSpec (h e : CType) : Bool × Bool × Bool :=
  if isRValueReferenceType h then (false, false, false)
  else
    let adj := if Clang.isArrayType h then .ptr (arrayElem h) else h
    (true, handles adj e, isLValueReferenceType h)

def excJank (h e : CType) : Bool × Bool × Bool :=
  match Paths.catchType h with
  | .error _ => (false, false, false)
  | .ok t =>
    let catches := if Clang.isArrayType (nonRef t) then false else handles t e
    (true, catches, isLValueReferenceType t)

def excJudge (h e : String × CType) : Verdict :=
  let txt := s!"(try (throw-native <{e.1}>) (catch {h.1} e ...))"
  let (sOk, sCatch, sSeen) := excSpec h.2 e.2
  let (jOk, jCatch, jSeen) := excJank h.2 e.2
  if sOk != jOk then some ("rvalue-reference-handler", s!"{txt}: C++ ill-formed (rvalue-reference handler); jank declares `catch({tshow ((Paths.catchType h.2).toOption.getD .null)} e)`")
  else if !sOk then none
  else if sCatch != jCatch then some ("array-handler", s!"{txt}: C++ {if sCatch then "catches" else "does not catch"} (handler adjusted to a pointer); jank {if jCatch then "catches" else "does not catch"} (`{tshow ((Paths.catchType h.2).toOption.getD .null)}`)")
  else if sCatch && sSeen != jSeen then some ("by-value-handler-is-a-reference", s!"{txt}: C++ catches a copy (a change to e is not rethrown by `(throw)`); jank binds `{tshow ((Paths.catchType h.2).toOption.getD .null)}` to the exception object itself")
  else none

def allExc : List ((String × CType) × (String × CType)) := excHandlers.flatMap fun h => excThrown.map fun e => (h, e)

def excBody (skip : List String) : EStateM Stop W Unit := do
  let h ← pickW "r3.exception.handler" excHandlers
  let e ← pickW "r3.exception.thrown" excThrown
  if let some (cls, d) := excJudge h e then
    if !skip.contains cls then violate (σ := W) s!"exception:{cls}" d

/-! ## III on AArch64: round 2's parameter world, `char` unsigned -/

/-- Round 2's `runProgram` with the platform as a parameter (Search.lean:58). -/
def runProgramP (p : Platform) (params : List (String × Jank.Analyzer.Obj)) (src : String) (fuel : Nat := 64) : Spec.Outcome :=
  match Analyze.analyzeFnBody { p := p } (params.map (·.1)) (Read.read1 src) with
  | .error f => .fault f
  | .ok e =>
    let env : Eval.Env := params.map fun (n, o) => (n, CVal.obj o, objectRef)
    match Eval.runBody p world0 env e fuel with
    | .ok (.obj o) => .value o
    | .ok v => .native v
    | .error f => .fault f

def paramJudgeP (p : Platform) (c : Search.ParamCase) : Option String :=
  let (src, params) := c.program
  let out := runProgramP p params src
  let exp := Spec.nativeParam p world0 c.paramType c.v.clj
  if Spec.agrees exp out then none
  else some s!"{src} with {params.map (fun (n, o) => s!"{n} = {showObj o}")}: expected {exp.show}, jank {out.show}"

/-! ## Residual searches -/

/-- `exhaust` over `body skip`, setting each found class aside and searching again, until a
complete run finds nothing (or `rounds` runs). Returns one line per run. -/
def residual (name : String) (body : List String → EStateM Stop W Unit) (maxRuns : Nat) (rounds : Nat := 12) :
    List String := Id.run do
  let mut skip : List String := []
  let mut out : List String := []
  for _ in List.range rounds do
    match exhaust (runW (body skip)) maxRuns with
    | .found c =>
      let cls := (c.property.splitOn ":").getLast!
      out := out ++ [s!"{name}: found after {c.runs} timelines ({c.property}): {c.detail}"]
      skip := skip ++ [cls]
    | .complete n =>
      out := out ++ [s!"{name}: complete, {n} timelines, nothing (set aside: {skip})"]
      return out
    | .stopped n =>
      out := out ++ [s!"{name}: stopped at {n} timelines, nothing (set aside: {skip})"]
      return out
  return out

end Jank.R3.Interop.Worlds
