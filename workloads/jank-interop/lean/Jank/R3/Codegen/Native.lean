import Jank.Analyzer.Types
import Jank.Analyzer.Builtins
import Jank.R3.Codegen.Flags

/-!
# Native values in emitted code, and what the optimizer may do with them

The programs of this world use what jank's analyzer types natively: number and boolean literals
(`cpp_literal`s, `literal_type`, cpp_util.cpp 603-861), the `:inline` arithmetic of core.jank
(`+ - * /` → `jank::runtime::add/sub/mul/div`, `<` → `lt`, `int` → `to_int`: core.jank 1372-1424,
1552, 204), `if`, `let`, `loop`/`recur`, `fn` with object or native-typed (`^cpp/long`,
`^cpp/double`, `^cpp/int`) parameters, calls, and `user/log` (a call with an output).

The jank side has two parts, as in jank:

- **analysis** (`tyck`): the types the analyzer gives (analyze/processor.cpp `analyze_if`
  2676-2787 with `find_branch_common_type`, `analyze_let`/`analyze_loop` (loop shadows take
  `mutable_type`), `analyze_recur` 2183-2219 (`apply_implicit_conversion` into the shadow's
  type: `cast`, `into_object`, `from_object`), `analyze_fn_arity` 1797-1923 (typed parameters;
  the last expression converted into an object), `analyze_call` 3612-3634 (arguments into
  objects), `analyze_primitive_literal` 3233-3246, `apply_implicit_conversion` 1032-1129 (a
  `cpp_literal` boxed becomes a boxed constant, through non-loop `let` locals:
  `resolved_expression`), the inline templates' result types (core/math.hpp: both operands
  primitive → `l op r` in C++'s usual arithmetic conversions; else `object_ref`; `lt` → `bool`;
  `to_int` → `i64`);
- **execution** of the emitted C++ under one optimization level: the C++ types of the emitted
  text (a `cpp_literal` is `auto v(<text>)`, cpp_processor.cpp 1278-1285; the text of `-2147483648`
  is a `long` in C++), templates re-resolved on those types (`auto &&v(jank::runtime::add(a, b))`,
  cpp_processor.cpp 1352-1440: the call names the function, not the specialization), locals of a
  spelled type (`if`/loop `T v{ }`, cpp_processor.cpp 909-919) assigned with C++'s implicit
  conversions, `-fwrapv` (Flags), integer division and float-to-integer conversion as C++ and
  LLVM define them, and the loops (`while(true){…}`, cpp_processor.cpp 992-1022), which are
  `mustprogress`.

At `-O0` the program does what x86-64 does with the instructions (`idiv` traps on a zero divisor
or `INT_MIN / -1`; `cvttsd2si` gives the "integer indefinite" `INT_MIN` of its width; a loop runs).
At `-O1`..`-O3` the same program is undefined wherever C++ says so: the optimizer may assume it
does not happen (LangRef: `sdiv` by zero or overflowing is immediate UB, `fptosi` out of range is
poison; a `mustprogress` loop without side effects must terminate, and `LoopDeletion` (O1+
pipelines, PassBuilderPipelines.cpp 564, 746) deletes one that does not).

Top level (eval target): `evaluate::eval` interprets `if`, `do`, calls and literals
(evaluate.cpp 376-399, 594-606, 651-654) and JIT-compiles `let`, `loop` and every native
expression in a wrapper fn (wrap_expression, 171-296); AOT (module target) compiles the whole file
as one fn (context_dynamic.cpp 82-125).

The spec is Clojure 1.12 (clojure-ref: Numbers.java long ops with overflow checks, `divide`
giving ratios, `RT.intCast`, Compiler.java's `loop`/`recur`/`fn`).
-/

namespace Jank.R3.Codegen

open Jank.Analyzer

/-! ## Programs -/

inductive AOp where
  | add | sub | mul | div | lt
  deriving Repr, BEq, DecidableEq, Inhabited

def AOp.sym : AOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .lt => "<"

/-- A parameter's declared native type (`^cpp/int`, `^cpp/long`, `^cpp/double`). -/
inductive PTy where
  | obj | int | long | double
  deriving Repr, BEq, DecidableEq, Inhabited

def PTy.ct : PTy → CT
  | .obj => .objectRef | .int => .int | .long => .long | .double => .double

inductive NF where
  | int (v : Int)
  | dbl (f : Float)
  | bool (b : Bool)
  | kw (n : String)
  | nil
  | sym (n : String)
  | op (o : AOp) (a b : NF)
  | toInt (a : NF)
  | if_ (c t e : NF)
  | let_ (x : String) (v body : NF)
  | loop (bs : List (String × NF)) (body : NF)
  | recur (args : List NF)
  | fn_ (params : List (String × PTy)) (body : NF)
  | call (f : NF) (args : List NF)
  | log (a : NF)
  deriving Inhabited

/-- A double as Clojure prints it (display only: the comparisons use the bits). -/
def fmtF (f : Float) : String :=
  if f.isNaN then "##NaN" else if f.isInf then (if f > 0 then "##Inf" else "##-Inf") else
  let trim (s : String) : String :=
    if s.contains '.' then
      let t := (s.toList.reverse.dropWhile (· == '0')).reverse
      let t := if t.getLast? == some '.' then t ++ ['0'] else t
      String.ofList t
    else s
  let a := f.abs
  if a ≥ 1e7 then
    let e := (Float.log10 a).floor
    let m := f / Float.pow 10.0 e
    trim (toString m) ++ "E" ++ toString e.toInt64.toInt
  else if f == f.floor then s!"{f.toInt64.toInt}.0"
  else trim (toString f)

partial def NF.code : NF → String
  | .int v => toString v
  | .dbl f => fmtF f
  | .bool b => toString b
  | .kw n => ":" ++ n
  | .nil => "nil"
  | .sym n => n
  | .op o a b => s!"({o.sym} {a.code} {b.code})"
  | .toInt a => s!"(int {a.code})"
  | .if_ c t e => s!"(if {c.code} {t.code} {e.code})"
  | .let_ x v b => s!"(let [{x} {v.code}] {b.code})"
  | .loop bs b => "(loop [" ++ " ".intercalate (bs.map fun (x, v) => x ++ " " ++ v.code) ++ "] " ++ b.code ++ ")"
  | .recur as => "(recur" ++ String.join (as.map (" " ++ ·.code)) ++ ")"
  | .fn_ ps b => "(fn [" ++ " ".intercalate (ps.map fun (x, t) => (match t with
      | .obj => "" | .int => "^cpp/int " | .long => "^cpp/long " | .double => "^cpp/double ") ++ x) ++ "] " ++ b.code ++ ")"
  | .call f as => "(" ++ f.code ++ String.join (as.map (" " ++ ·.code)) ++ ")"
  | .log a => s!"(log {a.code})"

/-! ## Values -/

/-- A jank object (or a Clojure value). Integers are longs; `ratio` and `big` only on Clojure's
side (jank has no ratio from `/` on integers, round 1's D2). -/
inductive Val where
  | long (v : Int)
  | dbl (f : Float)
  | bool (b : Bool)
  | kw (n : String)
  | nil
  | fn (k : Nat)
  | ratio (n d : Int)
  | big (v : Int)
  deriving Inhabited

def Val.show : Val → String
  | .long v => toString v | .dbl f => fmtF f | .bool b => toString b | .kw n => ":" ++ n
  | .nil => "nil" | .fn _ => "#<fn>" | .ratio n d => s!"{n}/{d}" | .big v => s!"{v}N"

def Val.truthy : Val → Bool
  | .nil | .bool false => false
  | _ => true

/-- Same value: `=` within a category, doubles by bits (NaN equal to NaN), functions alike. -/
def Val.same : Val → Val → Bool
  | .long a, .long b => a == b
  | .dbl a, .dbl b => a.toBits == b.toBits || (a.isNaN && b.isNaN)
  | .bool a, .bool b => a == b
  | .kw a, .kw b => a == b
  | .nil, .nil => true
  | .fn _, .fn _ => true
  | .ratio a b, .ratio c d => a == c && b == d
  | .big a, .big b => a == b
  | _, _ => false

def inI32 (v : Int) : Bool := -2147483648 ≤ v && v ≤ 2147483647
def inI64 (v : Int) : Bool := -9223372036854775808 ≤ v && v ≤ 9223372036854775807
def wrapTo (bits : Nat) (v : Int) : Int := (BitVec.ofInt bits v).toInt

/-- Truncation toward zero of a finite double whose magnitude is below 2^63 (exact). -/
def truncF (f : Float) : Int :=
  let a := f.abs.floor
  let n : Int := (a.toUInt64.toNat : Int)
  if f < 0 then -n else n

/-- `trunc(f)` is in `[-2^31, 2^31)` (doubles compared exactly). -/
def dblFitsI32 (f : Float) : Bool := !f.isNaN && f > -2147483649.0 && f < 2147483648.0
def dblFitsI64 (f : Float) : Bool := !f.isNaN && f ≥ -9223372036854775808.0 && f < 9223372036854775808.0

/-! ## Optimization levels -/

inductive Lvl where
  | o0 | o1 | o2 | o3
  deriving Repr, BEq, DecidableEq, Inhabited

def Lvl.n : Lvl → Nat | .o0 => 0 | .o1 => 1 | .o2 => 2 | .o3 => 3
def Lvl.optimizes (l : Lvl) : Bool := l != .o0

/-- Where the program runs: the REPL / `jank run` (eval target, top-level forms interpreted) or
an AOT module (every form compiled). -/
inductive Target where
  | eval | module
  deriving Repr, BEq, DecidableEq, Inhabited

/-! ## The analyzer's typing (jank) -/

/-- The C++ type of an integer literal's text as `lift_constant`/`gen_constant` print it
(`o.to_code_string()` / `"{}"` of the i64): a decimal literal takes the first of int, long that
holds its magnitude, and a minus sign is an operator on it ([lex.icon], [expr.unary.op]). -/
def cppDecimalType (v : Int) : CT :=
  if v.natAbs ≤ 2147483647 then .int else .long

/-- A typed expression: what the analyzer built, with the conversions it inserted. -/
inductive TE where
  /-- A `cpp_literal`: its analyzer type and the C++ type of its text. -/
  | lit (t actual : CT) (v : Val)
  /-- A `primitive_literal` (an object constant). -/
  | const (v : Val)
  | local_ (x : String) (t : CT)
  /-- `cpp_conversion` into an object from native type `t`. -/
  | box (t : CT) (e : TE)
  /-- `cpp_conversion` from an object to native type `t`. -/
  | unbox (t : CT) (e : TE)
  /-- `apply_implicit_conversion`'s `cast`: `T(e)` (a C++ functional cast). -/
  | cast (t : CT) (e : TE)
  | arith (o : AOp) (t : CT) (a b : TE)
  | toInt (a : TE)
  /-- `if` with its local's type; the condition is a `bool` or an object (`truthy`). -/
  | if_ (t : CT) (c t' e : TE)
  | let_ (x : String) (v body : TE)
  /-- `loop`: each binding's shadow type (`mutable_type`). -/
  | loop (bs : List (String × CT × TE)) (body : TE)
  | recur (args : List TE)
  /-- `fn`: parameter types, whether it uses fn-level `recur`, the body (its last value boxed). -/
  | fn_ (params : List (String × CT)) (fnRecur : Bool) (body : TE)
  | call (f : TE) (args : List TE)
  | log (a : TE)
  deriving Inhabited

partial def TE.type : TE → CT
  | .lit t .. => t
  | .const v => match v with
    | .kw _ => .typed "keyword" | .nil => .typed "nil" | .bool _ => .typed "boolean"
    | .long _ => .typed "integer" | .dbl _ => .typed "real" | _ => .objectRef
  | .local_ _ t => t
  | .box .. => .objectRef
  | .unbox t _ | .cast t _ => t
  | .arith _ t .. => t
  | .toInt _ => .long
  | .if_ t .. => t
  | .let_ _ _ b => b.type
  | .loop _ b => b.type
  | .recur _ => .objectRef
  | .fn_ .. => .typed "jit_function"
  | .call .. => .objectRef
  | .log _ => .objectRef

/-- The tail expression (`resolve_tail_expression`). -/
partial def TE.isRecurTail : TE → Bool
  | .recur _ => true
  | .let_ _ _ b => b.isRecurTail
  | .loop _ _ => false
  | _ => false

structure TEnv where
  locals : List (String × (CT × Option TE)) := []
  /-- The innermost `recur` target: `some (some shadowTypes)` a loop, `some none` a fn. -/
  recurTarget : Option (Option (List CT)) := none
  fnParamCount : Nat := 0
  deriving Inhabited

abbrev TM := StateT (List String) (Except String)

def note (s : String) : TM Unit := modify (· ++ [s])

/-- `apply_implicit_conversion(expr, expected)` (processor.cpp 1032-1129). Boxing a literal (also
through non-loop `let` locals) gives the literal's boxed constant. -/
def convertTo (env : TEnv) (e : TE) (expected : CT) : TM TE := do
  let et := e.type
  match determineImplicitConversion et expected with
  | .none => pure e
  | .intoObject =>
    let resolved := match e with
      | .local_ x _ => match env.locals.lookup x with
        | some (_, some (.lit _ _ v)) => some v
        | _ => none
      | .lit _ _ v => some v
      | _ => none
    match resolved with
    | some v => pure (.const v)
    | none => pure (.box et e)
  | .fromObject => pure (.unbox expected e)
  | .cast => pure (.cast expected e)
  | .unknown => throw s!"analyze/invalid-cpp-conversion: no implicit conversion from {et.spelling} to {expected.spelling}"

partial def tyck (env : TEnv) (f : NF) : TM TE := do
  match f with
  | .int v =>
    if inI64 v then
      let t := literalType (.integer (BitVec.ofInt 64 v)) false
      pure (.lit t (cppDecimalType v) (.long v))
    else throw "reader: integer literal outside i64 (a BigInt)"
  | .dbl x => pure (.lit .double .double (.dbl x))
  | .bool b => pure (.lit .bool .bool (.bool b))
  | .kw n => pure (.const (.kw n))
  | .nil => pure (.const .nil)
  | .sym x => match env.locals.lookup x with
    | some (t, _) => pure (.local_ x t)
    | none => throw s!"Unable to resolve symbol: {x}"
  | .op o a b =>
    let ea ← tyck { env with recurTarget := none } a
    let eb ← tyck { env with recurTarget := none } b
    let ta := ea.type
    let tb := eb.type
    if ta == .bool || tb == .bool then note "bool-arith"
    let t : CT := match o with
      | .lt => .bool
      | _ => if isArithmetic ta && isArithmetic tb then (getCommonType ta tb).getD .objectRef else .objectRef
    pure (.arith o t ea eb)
  | .toInt a => pure (.toInt (← tyck { env with recurTarget := none } a))
  | .if_ c t e =>
    let ec ← tyck { env with recurTarget := none } c
    let ct := ec.type
    let ec ← if !isAnyObject ct && ct != .bool then
        (if isBuiltin ct then convertTo env ec .objectRef else convertTo env ec .bool)
      else pure ec
    let et ← tyck env t
    let ee ← tyck env e
    let hasRecur := et.isRecurTail || ee.isRecurTail
    match findBranchCommonType et.type (some ee.type) hasRecur with
    | .error m => throw s!"analyze/mismatched-if-types: {m}"
    | .ok bct =>
      let et ← if bct.thenNeedsConversion then convertTo env et .objectRef else pure et
      let ee ← if bct.elseNeedsConversion then convertTo env ee .objectRef else pure ee
      pure (.if_ bct.type ec et ee)
  | .let_ x v body =>
    let ev ← tyck { env with recurTarget := none } v
    let eb ← tyck { env with locals := (x, (ev.type, some ev)) :: env.locals } body
    pure (.let_ x ev eb)
  | .loop bs body =>
    let mut locals := env.locals
    let mut out : List (String × CT × TE) := []
    for (x, v) in bs do
      let ev ← tyck { env with locals, recurTarget := none } v
      let st := mutableType ev.type
      locals := (x, (st, none)) :: locals
      out := out ++ [(x, st, ev)]
    let eb ← tyck { env with locals, recurTarget := some (some (out.map (·.2.1))) } body
    pure (.loop out eb)
  | .recur args =>
    match env.recurTarget with
    | none => throw "analyze/invalid-recur-position"
    | some (some types) =>
      if types.length != args.length then throw "analyze/invalid-recur-args"
      let mut out : List TE := []
      for (a, t) in args.zip types do
        let ea ← tyck { env with recurTarget := none } a
        if isAnyObject t && !isAnyObject ea.type then
          -- `(cpp/= local form)` on an object local and a native value (R36, low confidence)
          note "R36"
        out := out ++ [← convertTo env ea t]
      pure (.recur out)
    | some none =>
      if env.fnParamCount != args.length then throw "analyze/invalid-recur-args"
      let mut out : List TE := []
      for a in args do
        let ea ← tyck { env with recurTarget := none } a
        out := out ++ [← convertTo env ea .objectRef]
      pure (.recur out)
  | .fn_ params body =>
    let locals := params.map (fun (x, t) => (x, (t.ct, (none : Option TE)))) ++ env.locals
    let eb ← tyck { locals, recurTarget := some none, fnParamCount := params.length } body
    let t := eb.type
    if !isAnyObject t && !isTraitConvertible t then throw "analyze/invalid-cpp-conversion (fn return)"
    let eb ← convertTo { env with locals } eb .objectRef
    let usesRecur := usesFnRecur body
    pure (.fn_ (params.map fun (x, t) => (x, t.ct)) usesRecur eb)
  | .call fe args =>
    let ef ← tyck { env with recurTarget := none } fe
    if !isAnyObject ef.type then throw "analyze/invalid-cpp-call: a native value is not callable"
    let mut out : List TE := []
    for a in args do
      let ea ← tyck { env with recurTarget := none } a
      out := out ++ [← convertTo env ea .objectRef]
    pure (.call ef out)
  | .log a =>
    let ea ← tyck { env with recurTarget := none } a
    pure (.log (← convertTo env ea .objectRef))
where
  /-- Whether a fn body has a `recur` aimed at the fn (not inside a nested loop or fn). -/
  usesFnRecur : NF → Bool
    | .recur _ => true
    | .if_ c t e => usesFnRecur c || usesFnRecur t || usesFnRecur e
    | .let_ _ v b => usesFnRecur v || usesFnRecur b
    | .op _ a b => usesFnRecur a || usesFnRecur b
    | .toInt a | .log a => usesFnRecur a
    | .call f as => usesFnRecur f || as.any usesFnRecur
    | _ => false

/-! ## Running the emitted C++ -/

/-- A native value in C++, with its actual C++ type. -/
structure NV where
  t : CT
  v : Val
  deriving Inhabited

inductive RV where
  | obj (o : Val)
  | nat (n : NV)
  deriving Inhabited

structure Closure where
  params : List (String × CT)
  fnRecur : Bool
  body : TE
  env : List (String × RV)
  deriving Inhabited

/-- How a jank run ended. -/
inductive JOut where
  | value (v : Val) (out : List String)
  | threw (msg : String) (out : List String)
  | compileError (msg : String)
  /-- SIGFPE (x86 `idiv`) or another hardware fault. -/
  | trap (why : String) (out : List String)
  /-- A loop that repeats its state forever. -/
  | hang (out : List String)
  /-- Undefined behavior the optimizer may exploit (-O1+): the kind and what LLVM is likely to do. -/
  | ub (kind : String) (likely : String) (out : List String)
  | fuel
  | unsupported (m : String)
  deriving Inhabited

def JOut.show : JOut → String
  | .value v o => s!"{v.show}" ++ (if o.isEmpty then "" else s!" printing {o}")
  | .threw m o => s!"throws ({m})" ++ (if o.isEmpty then "" else s!" after printing {o}")
  | .compileError m => s!"compile error ({m})"
  | .trap w _ => s!"crash ({w})"
  | .hang o => "never ends" ++ (if o.isEmpty then "" else s!" (printing {o})")
  | .ub k l _ => s!"undefined: {k} ({l})"
  | .fuel => "out of fuel"
  | .unsupported m => s!"unsupported ({m})"

inductive Stop where
  | threw (msg : String)
  | trap (why : String)
  | hang
  | ub (kind likely : String)
  | fuel
  | unsupported (m : String)
  deriving Inhabited

structure XS where
  closures : Array Closure := #[]
  out : List String := []
  /-- Side effects so far (calls, allocations, possible throws): what keeps LLVM from deleting a
  loop. -/
  effects : Nat := 0
  fuel : Nat := 20000
  /-- Events the run went through (for classifying deviations). -/
  events : List String := []
  deriving Inhabited

abbrev XM := EStateM Stop XS

def tick : XM Unit := do
  let s ← get
  if s.fuel == 0 then throw .fuel
  set { s with fuel := s.fuel - 1 }

def effect : XM Unit := modify fun s => { s with effects := s.effects + 1 }
def event (e : String) : XM Unit := modify fun s =>
  if s.events.contains e then s else { s with events := s.events ++ [e] }

/-- Undefined behavior: at -O0 the hardware result (given), at -O1+ the optimizer's license. -/
def ubAt {α : Type} (lvl : Lvl) (kind likely : String) (atO0 : XM α) : XM α := do
  event kind
  if lvl.optimizes then throw (.ub kind likely) else atO0

/-- The x86-64 `cvttsd2si` "integer indefinite" result of an out-of-range conversion. -/
def indefinite (t : CT) : Int := if t == .int then -2147483648 else -9223372036854775808

/-- C++ conversion of a native value to native type `to` (assignment, functional cast,
`static_cast`): integers wrap (C++20 [conv.integral]), doubles truncate ([conv.fpint]: UB out of
range), booleans 0/1 and `!= 0`. -/
def convNat (lvl : Lvl) (to : CT) (n : NV) (why : String) : XM NV := do
  match to, n.v with
  | .int, .long x => pure ⟨.int, .long (wrapTo 32 x)⟩
  | .long, .long x => pure ⟨.long, .long (wrapTo 64 x)⟩
  | .int, .bool b | .long, .bool b => pure ⟨to, .long (if b then 1 else 0)⟩
  | .double, .long x => pure ⟨.double, .dbl (Float.ofInt x)⟩
  | .double, .bool b => pure ⟨.double, .dbl (if b then 1.0 else 0.0)⟩
  | .double, .dbl f => pure ⟨.double, .dbl f⟩
  | .bool, .long x => pure ⟨.bool, .bool (x != 0)⟩
  | .bool, .dbl f => pure ⟨.bool, .bool (f != 0.0)⟩
  | .bool, .bool b => pure ⟨.bool, .bool b⟩
  | .int, .dbl f =>
    if dblFitsI32 f then pure ⟨.int, .long (truncF f)⟩
    else ubAt lvl "double out of int range" s!"{why}: fptosi poison" (pure ⟨.int, .long (indefinite .int)⟩)
  | .long, .dbl f =>
    if dblFitsI64 f then pure ⟨.long, .long (truncF f)⟩
    else ubAt lvl "double out of long range" s!"{why}: fptosi poison" (pure ⟨.long, .long (indefinite .long)⟩)
  | _, _ => throw (.unsupported s!"conversion to {to.spelling}")

/-- `convert<T>::into_object` / `make_box` (convert/builtin.hpp 221-226, 272-276; make_box.hpp
24-27, 80-101): an integer in the small range is a tagged pointer, a larger one a heap `integer`
(a GC allocation: a side effect); doubles are tagged; booleans the two globals. -/
def boxNat (n : NV) : XM Val := do
  match n.v with
  | .long x =>
    if n.t == .long then effect
    pure (.long x)
  | v => pure v

/-- `object_ref::to_integer` (number.cpp, the runtime library: reals truncate with a
`static_cast<i64>` compiled into libjank at -O2: x86's indefinite out of range), booleans 0/1. -/
def objToInteger (o : Val) : XM Int := do
  match o with
  | .long x => pure x
  | .bool b => event "bool as number"; pure (if b then 1 else 0)
  | .dbl f =>
    if f.isNaN then pure 0
    else if dblFitsI64 f then pure (truncF f)
    else event "runtime static_cast<i64> out of range"; pure (indefinite .long)
  | _ => throw (.threw "not a number")

def objToReal (o : Val) : XM Float := do
  match o with
  | .long x => pure (Float.ofInt x)
  | .bool b => event "bool as number"; pure (if b then 1.0 else 0.0)
  | .dbl f => pure f
  | _ => throw (.threw "not a number")

/-- `convert<T>::from_object` (convert/builtin.hpp 228-236, 278-285, bool via `try_object`). -/
def unboxTo (lvl : Lvl) (t : CT) (o : Val) : XM NV := do
  effect
  match t with
  | .int | .long =>
    let x ← objToInteger o
    convNat lvl t ⟨.long, .long x⟩ "from_object"
  | .double => pure ⟨.double, .dbl (← objToReal o)⟩
  | .bool => match o with
    | .bool b => pure ⟨.bool, .bool b⟩
    | _ => throw (.threw "invalid object type (expected boolean)")
  | _ => throw (.unsupported s!"from_object to {t.spelling}")

def RV.toObj : RV → XM Val
  | .obj o => pure o
  | .nat n => boxNat n

/-- The usual arithmetic conversions on the actual C++ types. -/
def commonActual (a b : CT) : CT := (getCommonType a b).getD .double

/-- `jank::runtime::add/sub/mul/div/lt` on two native values (core/math.hpp, the
`primitive_number` overloads: `l op r` in C++, `-fwrapv`). -/
def natArith (lvl : Lvl) (o : AOp) (a b : NV) : XM NV := do
  if a.t == .bool || b.t == .bool then event "bool as number"
  let ct := commonActual a.t b.t
  let ct := if ct == .bool then .int else ct
  let a' ← convNat lvl ct a "operand"
  let b' ← convNat lvl ct b "operand"
  match o, a'.v, b'.v with
  | .lt, .long x, .long y => pure ⟨.bool, .bool (x < y)⟩
  | .lt, .dbl x, .dbl y => pure ⟨.bool, .bool (x < y)⟩
  | .add, .long x, .long y => wrapped ct (x + y)
  | .sub, .long x, .long y => wrapped ct (x - y)
  | .mul, .long x, .long y => wrapped ct (x * y)
  | .div, .long x, .long y =>
    let min : Int := if ct == .int then -2147483648 else -9223372036854775808
    if y == 0 then
      ubAt lvl "integer division by zero" "sdiv by zero: immediate UB (folded to poison when constant)"
        (throw (.trap "SIGFPE: integer division by zero"))
    else if x == min && y == -1 then
      ubAt lvl "integer division overflow" "sdiv INT_MIN / -1: immediate UB"
        (throw (.trap "SIGFPE: integer division overflow"))
    else
      if x.tmod y != 0 then event "integer division truncates"
      pure ⟨ct, .long (x.tdiv y)⟩
  | .add, .dbl x, .dbl y => pure ⟨.double, .dbl (x + y)⟩
  | .sub, .dbl x, .dbl y => pure ⟨.double, .dbl (x - y)⟩
  | .mul, .dbl x, .dbl y => pure ⟨.double, .dbl (x * y)⟩
  | .div, .dbl x, .dbl y => pure ⟨.double, .dbl (x / y)⟩
  | _, _, _ => throw (.unsupported "arith")
where
  wrapped (ct : CT) (x : Int) : XM NV := do
    let w := if ct == .int then 32 else 64
    if wrapTo w x != x then event (if w == 32 then "int arithmetic wraps (32-bit)" else "long arithmetic wraps")
    pure ⟨ct, .long (wrapTo w x)⟩

/-- The `object_ref` overloads (`visit_number_like`, then `make_box` of the C++ operation on the
two `data` members: an `integer`'s data is i64): a non-number throws. -/
def objArith (lvl : Lvl) (o : AOp) (a b : Val) : XM Val := do
  effect
  let na ← asNum a
  let nb ← asNum b
  let before := (← get).events
  let r ← natArith lvl o na nb
  -- a small integer's `data` is an `i32` (round 1's D1), not a literal's arithmetic (R25)
  if !before.contains "int arithmetic wraps (32-bit)" && (← get).events.contains "int arithmetic wraps (32-bit)" then
    modify fun s => { s with events := s.events.filter (· != "int arithmetic wraps (32-bit)") ++ ["object arithmetic wraps (32-bit)"] }
  boxNat r
where
  asNum : Val → XM NV
    | .long x => pure ⟨if inI32 x then .int else .long, .long x⟩
    | .dbl f => pure ⟨.double, .dbl f⟩
    | .bool _ => throw (.threw "Can't do math on a boolean object")
    | _ => throw (.threw "not a number")

/-- `to_int` of a native double (core/math.hpp 1413-1420): NaN is 0, else `static_cast<i64>`. -/
def toIntDbl (lvl : Lvl) (f : Float) : XM NV :=
  if f.isNaN then pure (NV.mk .long (.long 0))
  else if dblFitsI64 f then pure (NV.mk .long (.long (truncF f)))
  else ubAt lvl "double out of long range" "to_int: static_cast<i64> is poison"
    (pure (NV.mk .long (.long (indefinite .long))))

def loopFuel : Nat := 400

mutual

partial def run (lvl : Lvl) (env : List (String × RV)) (e : TE) : XM (Sum RV (List RV)) := do
  tick
  match e with
  | .lit _ actual v => pure (.inl (.nat ⟨actual, v⟩))
  | .const v => pure (.inl (.obj v))
  | .local_ x _ => match env.lookup x with
    | some v => pure (.inl v)
    | none => throw (.unsupported s!"unbound {x}")
  | .box t x =>
    let v ← val lvl env x
    match v with
    | .obj o => pure (.inl (.obj o))
    | .nat n =>
      -- `convert<T>::into_object(v)`: `v` converted to the analyzer's type `T` first
      let n' ← convNat lvl t n "into_object"
      if !n'.v.same n.v then event "narrowed to the analyzer's type when boxed"
      pure (.inl (.obj (← boxNat n')))
  | .unbox t x =>
    match ← val lvl env x with
    | .obj o =>
      -- a `from_object` conversion: only `recur` into a native loop local inserts one here
      event "from_object of a non-number"
      let r ← unboxTo lvl t o
      if !r.v.same o then event "recur/cast changes the value"
      pure (.inl (.nat r))
    | .nat n => pure (.inl (.nat (← convNat lvl t n "from_object")))
  | .cast t x =>
    match ← val lvl env x with
    | .nat n =>
      let before := n.v
      let r ← convNat lvl t n "cast"
      if !before.same r.v then event "recur/cast changes the value"
      pure (.inl (.nat r))
    | .obj o => pure (.inl (.nat (← unboxTo lvl t o)))
  | .arith o _ a b =>
    let va ← val lvl env a
    let vb ← val lvl env b
    match va, vb with
    | .nat x, .nat y => pure (.inl (.nat (← natArith lvl o x y)))
    | _, _ =>
      let oa ← va.toObj
      let ob ← vb.toObj
      if o == .lt then
        effect
        let r ← objArith lvl .lt oa ob
        pure (.inl (.nat ⟨.bool, r⟩))
      else pure (.inl (.obj (← objArith lvl o oa ob)))
  | .toInt a =>
    let r : NV ← match ← val lvl env a with
      | .nat n => match n.v with
        | .dbl f => toIntDbl lvl f
        | .long x => pure ⟨.long, .long x⟩
        | .bool b => do event "bool as number"; pure ⟨.long, .long (if b then 1 else 0)⟩
        | _ => throw (.unsupported "to_int")
      | .obj o =>
        effect
        match o with
        | .long _ | .dbl _ | .bool _ => pure ⟨.long, .long (← objToInteger o)⟩
        | _ => throw (.threw "Can't convert to integer")
    pure (.inl (.nat r))
  | .if_ t c th el =>
    let cv ← val lvl env c
    let truthy ← match cv with
      | .nat ⟨_, .bool b⟩ => pure b
      | .nat _ => throw (.unsupported "native condition")
      | .obj o => pure o.truthy
    match ← run lvl env (if truthy then th else el) with
    | .inr args => pure (.inr args)
    | .inl v =>
      -- `T loc{ }; loc = std::move(branch);` (ir/processor.cpp 659-700, cpp_processor.cpp 909-926)
      if isAnyObject t then
        match v with
        | .obj o => pure (.inl (.obj o))
        | .nat _ => throw (.unsupported "native into object local")
      else match v with
        | .nat n =>
          let n' ← convNat lvl t n "if local"
          if !n'.v.same n.v || n.t != t then event "if merges branch types"
          pure (.inl (.nat n'))
        | .obj _ => throw (.unsupported "object into native local")
  | .let_ x v b =>
    let vv ← val lvl env v
    run lvl ((x, vv) :: env) b
  | .loop bs body => runLoop lvl env bs body
  | .recur args =>
    let mut vs : List RV := []
    for a in args do vs := vs ++ [← val lvl env a]
    pure (.inr vs)
  | .fn_ ps r b =>
    let s ← get
    set { s with closures := s.closures.push { params := ps, fnRecur := r, body := b, env } }
    pure (.inl (.obj (.fn s.closures.size)))
  | .call f args =>
    let fv ← val lvl env f
    let mut vs : List Val := []
    for a in args do vs := vs ++ [← (← val lvl env a).toObj]
    effect
    match fv with
    | .obj (.fn k) => pure (.inl (.obj (← invoke lvl k vs)))
    | .obj o => throw (.threw s!"{o.show} is not callable")
    | .nat _ => throw (.unsupported "native callee")
  | .log a =>
    let v ← (← val lvl env a).toObj
    effect
    modify fun s => { s with out := s.out ++ [v.show] }
    pure (.inl (.obj v))

partial def val (lvl : Lvl) (env : List (String × RV)) (e : TE) : XM RV := do
  match ← run lvl env e with
  | .inl v => pure v
  | .inr _ => throw (.unsupported "recur in value position")

/-- `while(true){…}` with shadows declared `auto s(init)` (native: the init's C++ type) or
`object_ref s(init)` (cpp_processor.cpp 996-1009); `recur` assigns `s = v` (implicit conversion to
the shadow's type). A state seen before means the loop never ends: without side effects in
between it is undefined at -O1+ (forward progress). -/
partial def runLoop (lvl : Lvl) (env : List (String × RV)) (bs : List (String × CT × TE)) (body : TE) :
    XM (Sum RV (List RV)) := do
  let mut shadows : List (String × RV) := []
  for (x, st, v) in bs do
    let vv ← val lvl (shadows ++ env) v
    let vv ← match vv with
      | .nat n => if isAnyObject st then pure (RV.obj (← boxNat n)) else pure (RV.nat n)
      | .obj o => pure (RV.obj o)
    shadows := shadows ++ [(x, vv)]
  let mut seen : List (List String × Nat) := []
  for _ in [0:loopFuel] do
    let key := shadows.map fun (_, v) => match v with
      | .obj o => "o" ++ o.show ++ (match o with | .dbl f => toString f.toBits | _ => "")
      | .nat n => n.t.spelling ++ ":" ++ n.v.show ++ (match n.v with | .dbl f => toString f.toBits | _ => "")
    let eff := (← get).effects
    match seen.find? (·.1 == key) with
    | some (_, eff0) =>
      if eff0 == eff then
        event "side-effect-free loop never ends"
        if lvl.optimizes then
          throw (.ub "forward progress (a side-effect-free mustprogress loop never ends)"
            "LoopDeletion removes the loop: the code continues at its exit, or becomes unreachable")
        else throw .hang
      else throw .hang
    | none => seen := (key, eff) :: seen
    match ← run lvl (shadows.reverse ++ env) body with
    | .inl v => return .inl v
    | .inr args =>
      let mut ns : List (String × RV) := []
      for ((x, old), a) in shadows.zip args do
        let nv ← match old, a with
          | .nat o, .nat n =>
            let r ← convNat lvl o.t n "recur assignment"
            if !r.v.same n.v then event "narrowed to the analyzer's type when boxed"
            pure (RV.nat r)
          | .obj _, .obj v => pure (RV.obj v)
          | .obj _, .nat n => pure (RV.obj (← boxNat n))
          | .nat _, .obj _ => throw (.unsupported "object into native shadow")
        ns := ns ++ [(x, nv)]
      shadows := ns
  throw .fuel

/-- A dynamic call of a closure: arity check, typed parameters converted
(`convert<T>::from_object`, cpp_processor.cpp 1995-2003), fn-level `recur` loop. -/
partial def invoke (lvl : Lvl) (k : Nat) (args : List Val) : XM Val := do
  let some c := (← get).closures[k]? | throw (.unsupported "closure")
  if c.params.length != args.length then throw (.threw s!"Wrong number of args ({args.length})")
  let mut cur := args
  let mut seen : List (List String × Nat) := []
  for _ in [0:loopFuel] do
    let key := cur.map fun v => v.show ++ (match v with | .dbl f => toString f.toBits | _ => "")
    let eff := (← get).effects
    if c.fnRecur then
      match seen.find? (·.1 == key) with
      | some (_, eff0) =>
        if eff0 == eff then
          event "side-effect-free loop never ends"
          if lvl.optimizes then
            throw (.ub "forward progress (a side-effect-free mustprogress loop never ends)"
              "LoopDeletion removes the loop: the code continues at its exit, or becomes unreachable")
          else throw .hang
        else throw .hang
      | none => seen := (key, eff) :: seen
    let mut env : List (String × RV) := c.env
    for ((x, t), a) in c.params.zip cur do
      let v ← if isAnyObject t then pure (RV.obj a) else pure (RV.nat (← unboxTo lvl t a))
      env := (x, v) :: env
    match ← run lvl env c.body with
    | .inl v => return ← v.toObj
    | .inr vs =>
      let mut objs : List Val := []
      for v in vs do objs := objs ++ [← v.toObj]
      cur := objs
  throw .fuel

end

/-- C++'s check of the emitted text that the model knows to fail: a fn with a native-typed
parameter and fn-level `recur` declares its shadow `jank::runtime::object_ref s(param)` from the
native local (ir/processor.cpp 262-270 gives every shadow `untyped_object_ref_type()`;
cpp_processor.cpp 996-1003 and 1995-2003): `object_ref` has no constructor from `int`, `long`,
`double` (oref.hpp 219-290). -/
partial def cppCheck : TE → Option String
  | .fn_ ps r b =>
    if r && ps.any (fun (_, t) => !isAnyObject t) then
      some "no matching constructor for initialization of 'jank::runtime::object_ref' (a fn-level recur shadow from a native-typed parameter)"
    else cppCheck b
  | .box _ x | .unbox _ x | .cast _ x | .toInt x | .log x => cppCheck x
  | .arith _ _ a b => cppCheck a <|> cppCheck b
  | .if_ _ c t e => cppCheck c <|> cppCheck t <|> cppCheck e
  | .let_ _ v b => cppCheck v <|> cppCheck b
  | .loop bs b => (bs.findSome? fun (_, _, v) => cppCheck v) <|> cppCheck b
  | .recur as => as.findSome? cppCheck
  | .call f as => cppCheck f <|> as.findSome? cppCheck
  | _ => none

/-- The top-level form run by `evaluate::eval` (eval target): `if` and calls are interpreted,
`let`/`loop` and native expressions are compiled in a wrapper fn whose result is boxed. The
interpreter evaluates a `cpp_literal` to its object (evaluate.cpp 651-654). -/
partial def evalTop (lvl : Lvl) (e : TE) : XM Val := do
  match e with
  | .lit _ _ v => pure v
  | .const v => pure v
  | .if_ _ c t el =>
    let cv ← evalTop lvl c
    evalTop lvl (if cv.truthy then t else el)
  | .call f args =>
    let fv ← evalTop lvl f
    let mut vs : List Val := []
    for a in args do vs := vs ++ [← evalTop lvl a]
    match fv with
    | .fn k => invoke lvl k vs
    | o => throw (.threw s!"{o.show} is not callable")
  | .log a =>
    let v ← evalTop lvl a
    modify fun s => { s with out := s.out ++ [v.show] }
    pure v
  | other =>
    -- wrapped and JIT compiled; a native result is boxed (`into_object` of its type)
    match ← run lvl [] other with
    | .inl (.obj o) => pure o
    | .inl (.nat n) =>
      let n' ← convNat lvl other.type n "top-level box"
      if !n'.v.same n.v then event "narrowed to the analyzer's type when boxed"
      boxNat n'
    | .inr _ => throw (.unsupported "recur at top level")

/-- Round 2's model of the same tree: every literal of the C++ type the analyzer gave it (the text
`-2147483648` taken as an `int`). -/
partial def TE.analyzerLiterals : TE → TE
  | .lit t _ v => .lit t t v
  | .box t e => .box t e.analyzerLiterals
  | .unbox t e => .unbox t e.analyzerLiterals
  | .cast t e => .cast t e.analyzerLiterals
  | .arith o t a b => .arith o t a.analyzerLiterals b.analyzerLiterals
  | .toInt a => .toInt a.analyzerLiterals
  | .if_ t c x e => .if_ t c.analyzerLiterals x.analyzerLiterals e.analyzerLiterals
  | .let_ x v b => .let_ x v.analyzerLiterals b.analyzerLiterals
  | .loop bs b => .loop (bs.map fun (x, t, v) => (x, t, v.analyzerLiterals)) b.analyzerLiterals
  | .recur as => .recur (as.map TE.analyzerLiterals)
  | .fn_ ps r b => .fn_ ps r b.analyzerLiterals
  | .call f as => .call f.analyzerLiterals (as.map TE.analyzerLiterals)
  | .log a => .log a.analyzerLiterals
  | e => e

structure JRun where
  out : JOut
  events : List String
  notes : List String
  deriving Inhabited

def runJank (lvl : Lvl) (tgt : Target) (f : NF) (analyzerLiterals : Bool := false) : JRun := Id.run do
  match (tyck {} f).run [] with
  | .error m => return JRun.mk (.compileError m) [] []
  | .ok (te0, notes) =>
    let te := if analyzerLiterals then te0.analyzerLiterals else te0
    if let some m := cppCheck te then return JRun.mk (.compileError m) ["typed param fn recur"] notes
    let prog : XM Val := match tgt with
      | .eval => evalTop lvl te
      | .module => do
        match ← run lvl [] te with
        | .inl (.obj o) => pure o
        | .inl (.nat n) =>
          let n' ← convNat lvl te.type n "top-level box"
          if !n'.v.same n.v then event "narrowed to the analyzer's type when boxed"
          boxNat n'
        | .inr _ => throw (.unsupported "recur at top level")
    match prog.run {} with
    | .ok v s => return JRun.mk (.value v s.out) s.events notes
    | .error st s =>
      let o : JOut := match st with
        | .threw m => .threw m s.out
        | .trap w => .trap w s.out
        | .hang => .hang s.out
        | .ub k l => .ub k l s.out
        | .fuel => .fuel
        | .unsupported m => .unsupported m
      return JRun.mk o s.events notes

end Jank.R3.Codegen
