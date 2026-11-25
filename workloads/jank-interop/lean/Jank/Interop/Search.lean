import Jank.Interop.Spec
import Determinismo

/-!
# Searching the interop replica against the spec

Each world draws a small jank program (forms, native types, values) with named decisions, runs it
through the replica (analysis → emitted C++ → its meaning) and through the spec, and breaks the
property when they disagree. `explore` (seeds), `exhaust` (every timeline), `shrink` and `tape`
come from Determinismo; `table` enumerates every case for counts.
-/

namespace Jank.Interop.Search

open Determinismo
open Jank.Analyzer (Obj)
open Spec

structure W where
  decisions : Decisions := {}

instance : Chaotic W where
  decisions w := w.decisions
  setDecisions w d := { w with decisions := d }

def runW (body : EStateM Stop W Unit) (source : Source) : Ended :=
  match body.run { decisions := { source } } with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }
  | .error (.nodeDown _) w => { taken := w.decisions.taken, violation := none }

/-- SplitMix64's finalizer: consecutive small seeds spread over the generator's seed space. -/
def mixSeed (i : Nat) : Nat :=
  let z : UInt64 := (UInt64.ofNat i) * 0x9E3779B97F4A7C15
  let z := (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31)).toNat % 2147483562

/-- `explore` over mixed seeds (Library gap: `mkStdGen` of consecutive small seeds gives the same
first draw, so `explore`'s seeds 0..n-1 all start with the same decision). -/
def exploreMixed (run : Source → Ended) (count : Nat) : Option Counterexample := Id.run do
  for i in List.range count do
    let o := run { gen := mkStdGen (mixSeed i) }
    if let some (property, detail) := o.violation then
      return some { taken := o.taken, property, detail, runs := i + 1 }
  return none

def pickW {α : Type} [Inhabited α] (name : String) (xs : List α) : EStateM Stop W α := do
  return (← pick (σ := W) name xs).getD default

/-! ## Running a program through the replica -/

def p0 : Platform := x86_64
def w0 : World := world0

/-- Analyze `src` as a function body with object parameters `params`, run it (at most `fuel`
loop iterations). -/
def runProgram (params : List (String × Obj)) (src : String) (fuel : Nat := 64) : Outcome :=
  match Analyze.analyzeFnBody {} (params.map (·.1)) (Read.read1 src) with
  | .error f => .fault f
  | .ok e =>
    let env : Eval.Env := params.map fun (n, o) => (n, CVal.obj o, objectRef)
    match Eval.runBody p0 w0 env e fuel with
    | .ok (.obj o) => .value o
    | .ok v => .native v
    | .error f => .fault f

/-- The emitted C++ of a program's interop nodes (for the report). -/
def cppOf (params : List String) (src : String) : List String :=
  match Analyze.analyzeFnBody {} params (Read.read1 src) with
  | .ok e => Codegen.cppText w0 e
  | .error _ => []

/-- The native value of one expression (analyzed in value position), and its C++ type; for a
`cpp/new`, the object it points to. -/
def nativeOf (src : String) : Except Fault (CVal × CType) :=
  match Analyze.analyze {} (Read.read1 src) .value false with
  | .error f => .error f
  | .ok e =>
    match (Eval.evalVal p0 w0 [] e).run {} with
    | .ok (.ptr t a, pt) s => match s.heap[a - 1]? with
      | some v => .ok (v, t)
      | none => .ok (.ptr t a, pt)
    | .ok r _ => .ok r
    | .error f _ => .error f

/-! ## The values programs draw -/

/-- A jank value: its source text, its object (when passed through a function parameter) and its
Clojure meaning. -/
structure Val where
  text : String
  obj : Obj
  deriving Inhabited

def Val.clj (v : Val) : CljV := cljOfObj v.obj

def ival (i : Int) : Val := { text := toString i, obj := Read.atom (toString i) }
def dval (t : String) : Val := { text := t, obj := Read.atom t }

def ints : List Val :=
  [0, 1, -1, 2, 65536, 1000000000, 2147483647, -2147483648, 2147483648, 3000000000].map ival
def doubles : List Val := [dval "0.5", dval "1.5"]
def numbers : List Val := ints ++ doubles

/-- An operand: written as a literal, or passed in as a function parameter. -/
def operand (v : Val) (lit : Bool) (name : String) : String × List (String × Obj) :=
  if lit then (v.text, []) else (name, [(name, v.obj)])

/-! ## I. Arithmetic on literals and parameters (clojure.core's inlined `+ - * < inc dec`) -/

structure ArithCase where
  op : String
  a : Val
  b : Val
  aLit : Bool
  bLit : Bool
  deriving Inhabited

def ArithCase.unary (c : ArithCase) : Bool := c.op == "inc" || c.op == "dec"

def ArithCase.program (c : ArithCase) : String × List (String × Obj) :=
  let (ta, pa) := operand c.a c.aLit "x"
  let (tb, pb) := operand c.b c.bLit "y"
  if c.unary then (s!"({c.op} {ta})", pa) else (s!"({c.op} {ta} {tb})", pa ++ pb)

def ArithCase.judge (c : ArithCase) : Option String :=
  let (src, params) := c.program
  let out := runProgram params src
  let exp := cljArith c.op c.a.clj c.b.clj
  if agrees exp out then none
  else some s!"{src} with {params.map (fun (n, o) => s!"{n} = {showObj o}")}: expected {exp.show}, jank {out.show}"

def ops : List String := ["+", "-", "*", "<", "inc", "dec"]

def drawArith : EStateM Stop W ArithCase := do
  let op ← pickW "interop.arith.op" ops
  let a ← pickW "interop.arith.a" numbers
  let aLit := (← decide (σ := W) "interop.arith.a_literal" 2) == 0
  if op == "inc" || op == "dec" then return { op, a, b := a, aLit, bLit := true }
  let b ← pickW "interop.arith.b" numbers
  let bLit := (← decide (σ := W) "interop.arith.b_literal" 2) == 0
  return { op, a, b, aLit, bLit }

def arithBody : EStateM Stop W Unit := do
  let c ← drawArith
  if let some d := c.judge then violate (σ := W) "arithmetic on literals and native locals = Clojure's" d

def allArith : List ArithCase :=
  ops.flatMap fun op => numbers.flatMap fun a => [true, false].flatMap fun aLit =>
    if op == "inc" || op == "dec" then [{ op, a, b := a, aLit, bLit := true }]
    else numbers.flatMap fun b => [true, false].map fun bLit => { op, a, b, aLit, bLit }

/-! ## II. `loop`/`recur` with native loop locals -/

structure LoopCase where
  init : Val
  step : String
  k : Val
  kLit : Bool
  deriving Inhabited

def loopInits : List Val := [ival 0, dval "0.0", ival 2147483000]
def loopSteps : List String := ["(+ x K)", "(* x K)", "(- x K)", "(identity K)"]

def LoopCase.program (c : LoopCase) : String × List (String × Obj) :=
  let (tk, pk) := operand c.k c.kLit "k"
  let step := (c.step.splitOn "K").foldl (fun acc s => if acc.isEmpty then s else acc ++ tk ++ s) ""
  (s!"(loop [x {c.init.text} n 0] (if (< n 1) (recur {step} (inc n)) x))", pk)

def LoopCase.expect (c : LoopCase) : Expect :=
  match c.step with
  | "(+ x K)" => cljArith "+" c.init.clj c.k.clj
  | "(* x K)" => cljArith "*" c.init.clj c.k.clj
  | "(- x K)" => cljArith "-" c.init.clj c.k.clj
  | _ => .value c.k.clj

def LoopCase.judge (c : LoopCase) : Option String :=
  let (src, params) := c.program
  let out := runProgram params src
  if agrees c.expect out then none
  else some s!"{src} with {params.map (fun (n, o) => s!"{n} = {showObj o}")}: expected {c.expect.show}, jank {out.show}"

def drawLoop : EStateM Stop W LoopCase := do
  let init ← pickW "interop.loop.init" loopInits
  let step ← pickW "interop.loop.step" loopSteps
  let k ← pickW "interop.loop.k" numbers
  let kLit := (← decide (σ := W) "interop.loop.k_literal" 2) == 0
  return { init, step, k, kLit }

def loopBody : EStateM Stop W Unit := do
  let c ← drawLoop
  if let some d := c.judge then violate (σ := W) "a loop local holds the recur value (Clojure)" d

def allLoops : List LoopCase :=
  loopInits.flatMap fun init => loopSteps.flatMap fun step => numbers.flatMap fun k =>
    [true, false].map fun kLit => { init, step, k, kLit }

/-! ## III. Jank values passed to native parameters, and returned -/

def paramVals : List Val :=
  [ival 0, ival 65, ival (-1), ival 3000000000, dval "1.5", dval "4.0",
   { text := "true", obj := .boolean true }, { text := "nil", obj := .nil },
   { text := "\\a", obj := .character "a" }, { text := "\\é", obj := .character "é" },
   { text := "\"abc\"", obj := .persistentString "abc" }, { text := ":k", obj := .keyword "" "k" }]

def paramFnNames : List String :=
  ["take_bool", "take_char", "take_uchar", "take_short", "take_int", "take_uint", "take_long",
   "take_ulong", "take_float", "take_double", "take_cstr", "take_mut_cstr", "take_string"]

structure ParamCase where
  fn : String
  v : Val
  lit : Bool
  deriving Inhabited

def ParamCase.program (c : ParamCase) : String × List (String × Obj) :=
  let (t, ps) := operand c.v c.lit "x"
  (s!"(cpp/{c.fn} {t})", ps)

def ParamCase.paramType (c : ParamCase) : CType :=
  ((w0.functions.find? (·.name == c.fn)).map (·.params.headD .null)).getD .null

def ParamCase.expect (c : ParamCase) : Expect := nativeParam p0 w0 c.paramType c.v.clj

def ParamCase.judge (c : ParamCase) : Option String :=
  let (src, params) := c.program
  let out := runProgram params src
  if agrees c.expect out then none
  else some s!"{src} with {params.map (fun (n, o) => s!"{n} = {showObj o}")}: expected {c.expect.show}, jank {out.show}"

def drawParam : EStateM Stop W ParamCase := do
  let fn ← pickW "interop.param.fn" paramFnNames
  let v ← pickW "interop.param.value" paramVals
  let lit := (← decide (σ := W) "interop.param.literal" 2) == 0
  return { fn, v, lit }

def paramBody : EStateM Stop W Unit := do
  let c ← drawParam
  if let some d := c.judge then violate (σ := W) "a jank value passed to a native parameter means its C++ value" d

def allParams : List ParamCase :=
  paramFnNames.flatMap fun fn => paramVals.flatMap fun v => [true, false].map fun lit => { fn, v, lit }

/-- The literal and the parameter forms of the same call disagree. -/
def literalVsParam (fn : String) (v : Val) : Option String :=
  let a := runProgram [] s!"(cpp/{fn} {v.text})"
  let b := runProgram [("x", v.obj)] s!"(cpp/{fn} x)"
  let sameClass := match a, b with
    | .value x, .value y => sameValue (cljOfObj x) (cljOfObj y)
    | .fault (.analyzeError ..), .fault (.analyzeError ..) | .fault (.thrown _), .fault (.thrown _) => true
    | .fault (.analyzeError ..), .fault (.thrown _) | .fault (.thrown _), .fault (.analyzeError ..) => true
    | .fault (.unmodeled _), _ | _, .fault (.unmodeled _) => true
    | _, _ => false
  if sameClass then none
  else some s!"(cpp/{fn} {v.text}) → {a.show}; ((fn [x] (cpp/{fn} x)) {v.text}) → {b.show}"

/-! ## IV. `if` on native values -/

structure CondCase where
  text : String
  /-- The jank value the native converts to (`into_object`), if any. -/
  jank : Option CljV
  /-- Its C++ boolean conversion, for a type with no jank value. -/
  cxx : Option Bool
  deriving Inhabited

def conds : List CondCase :=
  [{ text := "0", jank := some (.long 0), cxx := none },
   { text := "0.0", jank := some (.double 0.0), cxx := none },
   { text := "false", jank := some (.bool false), cxx := none },
   { text := "(cpp/cast cpp/char 0)", jank := some (.char 0), cxx := none },
   { text := "(cpp/cast cpp/float 0)", jank := some (.double 0.0), cxx := none },
   { text := "cpp/red", jank := some (.long 0), cxx := none },
   { text := "cpp/green", jank := some (.long 1), cxx := none },
   { text := "cpp/mode.off", jank := some (.long 0), cxx := none },
   { text := "cpp/nullptr", jank := some .nil, cxx := none },
   { text := "(cpp/cast (:* (:const cpp/char)) cpp/nullptr)", jank := some .nil, cxx := none },
   { text := "(cpp/cast (:* cpp/int) cpp/nullptr)", jank := none, cxx := some false },
   { text := "\"\"", jank := some (.string ""), cxx := none },
   { text := "(cpp/std.string)", jank := some (.string ""), cxx := none }]

def CondCase.judge (c : CondCase) : Option String :=
  let src := s!"(if {c.text} :t :f)"
  let out := runProgram [] src
  let exp := nativeTruthy c.jank c.cxx
  if agrees exp out then none else some s!"{src}: expected {exp.show}, jank {out.show}"

def condBody : EStateM Stop W Unit := do
  let c ← pickW "interop.if.condition" conds
  if let some d := c.judge then violate (σ := W) "an `if` on a native value follows Clojure truthiness" d

/-! ## V. `cpp/cast` between native types vs `static_cast` -/

structure TypeChoice where
  text : String
  type : CType
  /-- A value of this type, as jank text. -/
  value : String
  deriving Inhabited

def tptr (text : String) (t : CType) : TypeChoice := { text, type := t, value := s!"(cpp/cast {text} cpp/nullptr)" }

def castTypes : List TypeChoice :=
  [{ text := "cpp/int", type := .b .int, value := "0" },
   { text := "cpp/double", type := .b .double, value := "0.5" },
   { text := "cpp/bool", type := .b .bool, value := "true" },
   { text := "cpp/color", type := .enum "color", value := "cpp/red" },
   { text := "cpp/mode", type := .enum "mode", value := "cpp/mode.off" },
   tptr "(:* cpp/int)" (.ptr (.b .int)),
   tptr "(:* (:const cpp/int))" (.ptr (.cv true false (.b .int))),
   tptr "(:* cpp/void)" (.ptr (.b .void)),
   tptr "(:* (:const cpp/void))" (.ptr (.cv true false (.b .void))),
   tptr "(:* base)" (.ptr (.record "base")),
   tptr "(:* derived)" (.ptr (.record "derived")),
   tptr "(:* (:const base))" (.ptr (.cv true false (.record "base"))),
   tptr "(:* (:const derived))" (.ptr (.cv true false (.record "derived"))),
   tptr "(:* (:fn cpp/void []))" (.ptr (.fn (.b .void) []))]

structure CastCase where
  src : TypeChoice
  dst : TypeChoice
  deriving Inhabited

def CastCase.program (c : CastCase) : String := s!"(let [v {c.src.value}] (let [r (cpp/cast {c.dst.text} v)] 1))"

def CastCase.judge (c : CastCase) : Option String :=
  let out := runProgram [] c.program
  let valid := Cxx.staticCastValid p0 w0 c.src.type c.dst.type
  let ok := match out with
    | .value _ => valid
    | .fault (.analyzeError ..) => !valid
    | .fault (.unmodeled _) => true
    | _ => false
  if ok then none
  else some s!"(cpp/cast {c.dst.text} v) with v a `{CppInterop.getTypeAsString c.src.type}`: static_cast is {if valid then "well-formed" else "ill-formed"}; jank {out.show}"

def castBody : EStateM Stop W Unit := do
  let src ← pickW "interop.cast.from" castTypes
  let dst ← pickW "interop.cast.to" castTypes
  if let some d := (CastCase.judge { src, dst }) then violate (σ := W) "cpp/cast accepts exactly the static_casts" d

def allCasts : List CastCase := castTypes.flatMap fun src => castTypes.map fun dst => { src, dst }

/-! ## VI. `cpp/new` vs constructing the type -/

structure NewCase where
  typeText : String
  ctorHead : String
  args : List String
  deriving Inhabited

def newTypes : List (String × String) :=
  [("cpp/int", "cpp/int"), ("cpp/long", "cpp/long"), ("cpp/double", "cpp/double"),
   ("cpp/float", "cpp/float"), ("cpp/unsigned", "cpp/unsigned"),
   ("(std.vector cpp/int)", "(cpp/dsl (std.vector cpp/int))"), ("wide", "cpp/wide")]

def newArgs : List (List String) := [[], ["1"], ["3"], ["1.5"], ["3000000000"]]

def NewCase.judge (c : NewCase) : Option String :=
  let argText := " ".intercalate c.args
  let stack := nativeOf s!"({c.ctorHead} {argText})"
  let heap := nativeOf s!"(cpp/new {c.typeText} {argText})"
  match stack with
  | .ok (v, _) =>
    match heap with
    | .ok (h, _) => if h == v then none
      else some s!"({c.ctorHead} {argText}) is {reprStr v}; (cpp/new {c.typeText} {argText}) points to {reprStr h}"
    | .error f => some s!"({c.ctorHead} {argText}) is {reprStr v}; (cpp/new {c.typeText} {argText}): {(Outcome.fault f).show}"
  | .error _ => none

def newBody : EStateM Stop W Unit := do
  let (typeText, ctorHead) ← pickW "interop.new.type" newTypes
  let args ← pickW "interop.new.args" newArgs
  if let some d := (NewCase.judge { typeText, ctorHead, args }) then
    violate (σ := W) "(cpp/new T args) holds what (T args) constructs" d

def allNews : List NewCase :=
  newTypes.flatMap fun (typeText, ctorHead) => newArgs.map fun args => { typeText, ctorHead, args }

/-! ## VII. Opaque boxes: unboxing checks the type -/

def boxTypes : List TypeChoice :=
  [tptr "(:* base)" (.ptr (.record "base")),
   tptr "(:* (:const base))" (.ptr (.cv true false (.record "base"))),
   tptr "(:* (:volatile base))" (.ptr (.cv false true (.record "base"))),
   tptr "(:* derived)" (.ptr (.record "derived")),
   tptr "(:* cpp/int)" (.ptr (.b .int)),
   tptr "(:* (:const cpp/int))" (.ptr (.cv true false (.b .int))),
   tptr "(:* (:fn base [cpp/int]))" (.ptr (.fn (.record "base") [.b .int])),
   tptr "(:* (:fn base []))" (.ptr (.fn (.record "base") []))]

def boxJudge (pB qU : TypeChoice) : Option String :=
  let src := s!"(let [v {pB.value} b (cpp/box v) u (cpp/unbox {qU.text} b)] 1)"
  let out := runProgram [] src
  let same := pB.type.canonical == qU.type.canonical
  let ok := match out with
    | .value _ => same
    | .fault (.thrown _) => !same
    | .fault (.unmodeled _) => true
    | _ => false
  if ok then none
  else some s!"a `{CppInterop.getTypeAsString pB.type}` boxed, unboxed as `{CppInterop.getTypeAsString qU.type}`: jank {out.show}"

def boxBody : EStateM Stop W Unit := do
  let pB ← pickW "interop.box.boxed" boxTypes
  let qU ← pickW "interop.box.unboxed" boxTypes
  if let some d := boxJudge pB qU then violate (σ := W) "cpp/unbox succeeds exactly for the boxed type" d

/-! ## VIII. The DSL's integer modifiers -/

def dslBases : List String := ["char", "int", "short", "long", "bool", "double", "float"]
def dslMods : List String := ["signed", "unsigned", "short", "long"]

/-- The specifier counts a base symbol contributes (`short` and `long` are `short int`,
`long int`). -/
def baseSpec (b : String) : String × Nat × Nat :=
  match b with
  | "short" => ("int", 1, 0)
  | "long" => ("int", 0, 1)
  | b => (b, 0, 0)

def dslJudge (mods : List String) (base : String) : Option String :=
  let text := mods.foldr (fun m acc => s!"(:{m} {acc})") s!"cpp/{base}"
  let (b, s0, l0) := baseSpec base
  let count (m : String) := (mods.filter (· == m)).length
  let spec := specifierType b (count "signed") (count "unsigned") (count "short" + s0) (count "long" + l0)
  let out := Analyze.analyzeType {} (Read.read1 text)
  match spec, out with
  | none, .error (.analyzeError ..) => none
  | some k, .ok t => if t.canonical == .b k then none
      else some s!"{text}: C++ `{k.spelling}`; jank `{CppInterop.getTypeAsString t}`"
  | none, .ok t => some s!"{text}: not a C++ type; jank accepts it as `{CppInterop.getTypeAsString t}`"
  | some k, .error f => some s!"{text}: C++ `{k.spelling}`; jank {(Outcome.fault f).show}"
  | none, .error _ => none

def dslBody : EStateM Stop W Unit := do
  let n ← decide (σ := W) "interop.dsl.depth" 3
  let mut mods := []
  for _ in List.range n do
    mods := mods ++ [← pickW "interop.dsl.modifier" dslMods]
  let base ← pickW "interop.dsl.base" dslBases
  if let some d := dslJudge mods base then violate (σ := W) "a DSL type form names the C++ type its specifiers name" d

def allDsl : List (List String × String) :=
  let chains : List (List String) := [[]] ++ dslMods.map (fun m => [m]) ++
    dslMods.flatMap (fun m => dslMods.map fun m' => [m, m'])
  chains.flatMap fun ms => dslBases.map fun b => (ms, b)

/-! ## IX. `if` with native branches of different types (cpp_util.cpp:find_branch_common_type) -/

def branchVals : List Val :=
  [ival 1, ival 3000000000, dval "2.5", { text := "true", obj := .boolean true },
   { text := "nil", obj := .nil }, { text := ":k", obj := .keyword "" "k" },
   { text := "\"s\"", obj := .persistentString "s" }]

structure BranchCase where
  a : Val
  b : Val
  cond : Bool
  condLit : Bool
  deriving Inhabited

def BranchCase.program (c : BranchCase) : String × List (String × Obj) :=
  let (tc, pc) := operand { text := toString c.cond, obj := .boolean c.cond } c.condLit "c"
  (s!"(if {tc} {c.a.text} {c.b.text})", pc)

def BranchCase.judge (c : BranchCase) : Option String :=
  let (src, params) := c.program
  let out := runProgram params src
  let exp : Expect := .value (if c.cond then c.a.clj else c.b.clj)
  if agrees exp out then none
  else some s!"{src} with {params.map (fun (n, o) => s!"{n} = {showObj o}")}: expected {exp.show}, jank {out.show}"

def branchBody : EStateM Stop W Unit := do
  let a ← pickW "interop.branch.then" branchVals
  let b ← pickW "interop.branch.else" branchVals
  let cond := (← decide (σ := W) "interop.branch.condition" 2) == 0
  let condLit := (← decide (σ := W) "interop.branch.condition_literal" 2) == 0
  if let some d := (BranchCase.judge { a, b, cond, condLit }) then
    violate (σ := W) "an `if` returns its chosen branch's value" d

def allBranches : List BranchCase :=
  branchVals.flatMap fun a => branchVals.flatMap fun b => [true, false].flatMap fun cond =>
    [true, false].map fun condLit => { a, b, cond, condLit }

end Jank.Interop.Search
