import Jank.Analyzer.Processor
import Jank.Analyzer.Builtins

/-!
# What jank runs: the meaning of an analyzed tree

The analyzer's output is lowered by `ir/processor.cpp` and `codegen/cpp_processor.cpp` (other
agents' components). This evaluator gives the analyzed tree the meaning those files give it, as
far as the analyzer's choices are concerned (read for reachability, assumption A6):

- an `if` gets a local of the `if`'s type, and each branch's value is assigned to it with C++'s
  implicit conversion (`ir/processor.cpp:659`, `set_local` → `local = std::move(value)`,
  `codegen/cpp_processor.cpp:921`); a `case` gets a local of the `case`'s type the same way
  (`ir/processor.cpp:808`; `case_::get_type`, case.cpp:71, since 7135b7708) and dispatches on the
  integer key (`jank_shift_mask_case_integer`, c_api.cpp:1028, read for reachability);
- `let` locals take their value's C++ type; `loop` shadows take `mutable_type` of it, and `recur`
  assigns to them (`ir/processor.cpp:533`, `branch_set`);
- `cpp_conversion` into/from objects is `jank::runtime::convert<T>` (convert/builtin.hpp at
  7135b7708): `from_object` to an integral type is `static_cast<T>(o.to_integer())` (builtin.hpp:238:
  reals truncate, NaN is 0, booleans are 0/1, non-numbers throw), to `double` is `o.to_real()`
  (builtin.hpp:288), to `bool` requires a boolean (`try_object`, unchanged); `into_object` boxes;
- `cpp_constructor_call` of a primitive type is a C++ functional cast;
- a top-level form of a non-object type is boxed (`evaluate.cpp:206`).
-/

namespace Jank.Analyzer

/-- A native C++ value. -/
inductive NV where
  | i (v : Int)
  | d (f : Float)
  | b (b : Bool)
  | cs (s : String)
  deriving Inhabited

/-- A value at run time: an object, or a native value with its C++ type. -/
inductive Val where
  | obj (o : Obj)
  | nat (t : CT) (v : NV)
  deriving Inhabited

/-- How a run ended. -/
inductive Outcome where
  /-- A value (printed with `pr-str`). -/
  | value (o : Obj)
  /-- An exception thrown at run time (a jank or Clojure exception). -/
  | thrown (msg : String)
  /-- Rejected at analysis (`error_ref`) or by the C++ compiler. -/
  | compileError (msg : String)
  /-- Undefined behaviour. -/
  | ub (msg : String)
  /-- Out of the model's fuel (a bound). -/
  | fuel
  /-- Outside what the models cover. -/
  | unsupported (msg : String)
  deriving Inhabited

def Outcome.show : Outcome → String
  | .value o => o.pr
  | .thrown m => s!"throws ({m})"
  | .compileError m => s!"compile error ({m})"
  | .ub m => s!"undefined behaviour ({m})"
  | .fuel => "out of fuel"
  | .unsupported m => s!"unsupported ({m})"

/-- Two outcomes agree: equal values (Clojure `=` and the same printed form), or both
exceptions/compile errors. Fuel and unsupported never count as a disagreement. -/
def Outcome.agrees : Outcome → Outcome → Bool
  | .value a, .value b => cljEquals a b && a.norm.pr == b.norm.pr
  | .thrown _, .thrown _ | .thrown _, .compileError _ | .compileError _, .thrown _
  | .compileError _, .compileError _ => true
  | .fuel, _ | _, .fuel | .unsupported _, _ | _, .unsupported _ => true
  | _, _ => false

def wrapSigned (bits : Nat) (v : Int) : Int := (BitVec.ofInt bits v).toInt

/-- `Float` → integer truncation toward zero (exact for the values that occur). -/
def truncF (f : Float) : Int :=
  let t := if f < 0 then -((-f).floor) else f.floor
  if t < 0 then -(((-t).toUInt64).toNat : Int) else ((t.toUInt64).toNat : Int)

/-- C++ conversion of a native value to a native type (assignment / functional cast). -/
def convNative (target : CT) (v : NV) : Except Outcome NV :=
  match target, v with
  | .int, .i x => .ok (.i (wrapSigned 32 x))
  | .long, .i x => .ok (.i (wrapSigned 64 x))
  | .int, .d f =>
    let t := truncF f
    if f.isNaN || t < -2147483648 || t > 2147483647 then .error (.ub "double out of int range") else .ok (.i t)
  | .long, .d f =>
    let t := truncF f
    if f.isNaN || t < -9223372036854775808 || t > 9223372036854775807 then .error (.ub "double out of long range") else .ok (.i t)
  | .int, .b b | .long, .b b => .ok (.i (if b then 1 else 0))
  | .double, .i x => .ok (.d (Float.ofInt x))
  | .double, .d f => .ok (.d f)
  | .double, .b b => .ok (.d (if b then 1.0 else 0.0))
  | .bool, .i x => .ok (.b (x != 0))
  | .bool, .d f => .ok (.b (f != 0.0))
  | .bool, .b b => .ok (.b b)
  | .bool, .cs _ => .ok (.b true)
  | .cstr _, .cs s => .ok (.cs s)
  | .other "char const*", .cs s => .ok (.cs s)
  | t, _ => .error (.compileError s!"no conversion to {t.spelling}")

/-- `convert<T>::into_object`: boxing a native value. -/
def intoObject (v : NV) : Obj :=
  match v with
  | .i x => Obj.ofInt x
  | .d f => Obj.dbl f
  | .b b => .boolean b
  | .cs s => .persistentString s

/-- `object_ref::to_integer` (oref.hpp:958, number.cpp:73, 358): integers as is, reals truncated
(NaN → 0; out of range is UB), booleans 0/1, anything else throws. -/
def objToInteger (o : Obj) : Except Outcome Int :=
  match o with
  | .smallInteger v => .ok v.toInt
  | .integer v => .ok v.toInt
  | .bigInteger v => .ok (wrapSigned 64 v)
  | .boolean b => .ok (if b then 1 else 0)
  | .smallReal b | .real b =>
    let f := Float.ofBits b
    if f.isNaN then .ok 0
    else
      let t := truncF f
      if t < -9223372036854775808 || t > 9223372036854775807 then .error (.ub "double out of i64 range") else .ok t
  | _ => .error (.thrown s!"unsupported behavior number_like on {reprStr o.type}")

/-- `object_ref::to_real` (oref.hpp:977, number.cpp:78, 250). -/
def objToReal (o : Obj) : Except Outcome Float :=
  match o with
  | .smallInteger v => .ok (Float.ofInt v.toInt)
  | .integer v => .ok (Float.ofInt v.toInt)
  | .bigInteger v => .ok (Float.ofInt v)
  | .boolean b => .ok (if b then 1.0 else 0.0)
  | .smallReal b | .real b => .ok (Float.ofBits b)
  | _ => .error (.thrown s!"unsupported behavior number_like on {reprStr o.type}")

/-- `convert<T>::from_object` (convert/builtin.hpp at 7135b7708). -/
def fromObject (target : CT) (o : Obj) : Except Outcome NV :=
  match target with
  | .int | .long =>
    match o with
    | .smallInteger v => convNative target (.i v.toInt)
    | _ => do convNative target (.i (← objToInteger o))
  | .double =>
    match o with
    | .smallReal b => .ok (.d (Float.ofBits b))
    | _ => do pure (.d (← objToReal o))
  | .bool =>
    match o with
    | .boolean b => .ok (.b b)
    | _ => .error (.thrown s!"invalid object type (expected boolean found {reprStr o.type})")
  | t => .error (.compileError s!"no from_object to {t.spelling}")

/-- Whether an object is of the typed object type (`try_object<T>` succeeds); `small_integer_ref`
and `small_real_ref` also accept boxed integers and reals (builtin.hpp:71-100). -/
def typedMatches (t : CT) (o : Obj) : Bool :=
  match t with
  | .objectRef => true
  | .typed n =>
    match n, o with
    | "nil", .nil | "boolean", .boolean _ | "integer", .integer _ | "small_integer", .smallInteger _
    | "small_integer", .integer _ | "real", .real _ | "small_real", .smallReal _ | "small_real", .real _
    | "keyword", .keyword .. | "symbol", .symbol .. | "character", .character _
    | "persistent_string", .persistentString _ | "persistent_list", .persistentList ..
    | "persistent_vector", .persistentVector .. | "persistent_hash_set", .persistentHashSet ..
    | "persistent_array_map", .persistentArrayMap .. | "persistent_hash_map", .persistentHashMap ..
    | "var", .var .. => true
    | _, _ => false
  | _ => false

def Val.toObj : Val → Obj
  | .obj o => o
  | .nat _ v => intoObject v

/-- Assigns `v` to a C++ local of type `t` (`local = std::move(v)`). -/
def assignTo (t : CT) (v : Val) : Except Outcome Val :=
  if isAnyObject t then
    match v with
    | .obj o => .ok (.obj o)
    | .nat _ _ => .error (.compileError s!"no conversion from a native value to {t.spelling}")
  else match v with
    | .nat _ n => (convNative t n).map (.nat t)
    | .obj _ => .error (.compileError s!"no conversion from an object to {t.spelling}")

/-- A closure: its function expression, the bindings in scope at its creation, and the enclosing
functions' objects (for named recursion). -/
structure Closure where
  fnExpr : ExprId
  env : List (BindingId × Val)
  selfs : List (FnCtxId × Obj)
  deriving Inhabited

inductive VarRoot where
  | unbound
  | obj (o : Obj)
  | builtin (name : String)
  deriving Inhabited

structure EvState where
  arena : Arena
  closures : Array Closure := #[]
  roots : List (VarRef × VarRoot) := []
  fuel : Nat := 200000

abbrev EvM := StateT EvState (Except Outcome)

/-- A step's result: a value or a `recur` to the enclosing loop or function. -/
inductive Flow where
  | val (v : Val)
  | recur (args : List Val)
  deriving Inhabited

def tick : EvM Unit := do
  let s ← get
  if s.fuel == 0 then throw .fuel
  set { s with fuel := s.fuel - 1 }

def liftE {α : Type} (e : Except Outcome α) : EvM α := match e with
  | .ok v => pure v
  | .error o => throw o

def closureObj (k : Nat) : Obj := .opaque .jitClosure k
def builtinObj (k : Nat) : Obj := .opaque .nativeFunctionWrapper k

def builtinNames : List String := ["=", "nil?", "meta", "vector", "list", "count", "first", "rest", "str", "inc", "+", "<", "pos?", "*"]

/-- The parameters' bindings of an arity frame, in order. -/
def paramBindings (a : Arena) (frame : FrameId) : List BindingId :=
  let ids := ((a.frame frame).locals.flatMap (·.2))
  ids.mergeSort (· ≤ ·)

mutual

partial def evalVal (i : ExprId) (env : List (BindingId × Val)) (selfs : List (FnCtxId × Obj)) : EvM Val := do
  match ← evalE i env selfs with
  | .val v => pure v
  | .recur _ => throw (.compileError "recur outside of a loop or function")

/-- Evaluates an expression. -/
partial def evalE (i : ExprId) (env : List (BindingId × Val)) (selfs : List (FnCtxId × Obj)) : EvM Flow := do
  tick
  let a := (← get).arena
  let e := a.expr i
  match e.data with
  | .primitiveLiteral d => pure (.val (.obj d))
  | .cppLiteral d =>
    let t := literalType d false
    match d with
    | .smallInteger v => pure (.val (.nat t (.i v.toInt)))
    | .integer v => pure (.val (.nat t (.i v.toInt)))
    | .smallReal b | .real b => pure (.val (.nat t (.d (Float.ofBits b))))
    | .boolean b => pure (.val (.nat t (.b b)))
    | .persistentString s => pure (.val (.nat t (.cs s)))
    | _ => throw (.unsupported "cpp literal")
  | .localReference _ b =>
    match env.lookup b with
    | some v => pure (.val v)
    | none => throw (.unsupported s!"unbound local {b}")
  | .varDeref _ vr | .varRef _ vr =>
    if e.kind == .varRef then return .val (.obj (.var vr.ns vr.name))
    match (← get).roots.lookup vr with
    | some (.obj o) => pure (.val (.obj o))
    | some (.builtin n) => pure (.val (.obj (builtinObj (builtinNames.idxOf n))))
    | _ => throw (.thrown s!"unbound var {vr.ns}/{vr.name}")
  | .recursionReference ctx =>
    match selfs.lookup ctx with
    | some o => pure (.val (.obj o))
    | none => throw (.unsupported "recursion reference without its function")
  | .function .. =>
    let s ← get
    let k := s.closures.size
    let ctxs := match e.data with
      | .function _ _ ars _ _ => ars.map (fun (ar : FunctionArity) => ar.fnCtx)
      | _ => []
    let self := closureObj k
    -- Each arity frame's captures: the copy is bound to the originating binding's value.
    let arityFrames := match e.data with
      | .function _ _ ars _ _ => ars.filterMap (fun (ar : FunctionArity) => ar.frame)
      | _ => []
    let captured := arityFrames.flatMap fun fr => ((a.frame fr).captures.filterMap fun (_, c) =>
      (env.lookup c.originatingBinding).map (c.binding, ·))
    set { s with closures := s.closures.push { fnExpr := i, env := captured ++ env, selfs := selfs ++ ctxs.map (·, self) } }
    pure (.val (.obj self))
  | .do_ vs =>
    let mut last : Flow := .val (.obj .nil)
    for v in vs do
      last ← evalE v env selfs
      if let .recur _ := last then return last
    pure last
  | .let pairs body kind =>
    let mut env := env
    let mut shadows : List (BindingId × CT) := []
    for (b, v) in pairs do
      let x ← evalVal v env selfs
      if kind == .loopWithRecur then
        let t := mutableType (exprType a v 10000)
        let x' ← liftE (assignTo t x)
        env := (b, x') :: env
        shadows := shadows ++ [(b, t)]
      else env := (b, x) :: env
    if kind != .loopWithRecur then return ← evalE body env selfs
    let mut cur := env
    for _ in [0:100000] do
      match ← evalE body cur selfs with
      | .val v => return .val v
      | .recur args =>
        let mut nenv := cur
        for ((b, t), x) in shadows.zip args do
          nenv := (b, ← liftE (assignTo t x)) :: nenv
        cur := nenv
    throw .fuel
  | .letfn pairs body =>
    -- Closures see each other: the bindings are filled after creation.
    let s ← get
    let base := s.closures.size
    let mut env := env
    let mut idx := 0
    for (b, _) in pairs do
      env := (b, .obj (closureObj (base + idx))) :: env
      idx := idx + 1
    for (_, f) in pairs do
      let st ← get
      let ctxs := match (st.arena.expr f).data with
        | .function _ _ ars _ _ => ars.map (fun (ar : FunctionArity) => ar.fnCtx)
        | _ => []
      let self := closureObj st.closures.size
      set { st with closures := st.closures.push { fnExpr := f, env, selfs := selfs ++ ctxs.map (·, self) } }
    evalE body env selfs
  | .if_ t c th el =>
    let cv ← evalVal c env selfs
    let truthy := match cv with
      | .obj o => o.truthy
      | .nat _ (.b b) => b
      | .nat _ (.i x) => x != 0
      | .nat _ (.d f) => f != 0.0
      | .nat _ (.cs _) => true
    let branch := if truthy then some th else el
    let r ← match branch with
      | some x => evalE x env selfs
      | none => pure (.val (.obj .nil))
    match r with
    | .recur args => pure (.recur args)
    | .val v => pure (.val (← liftE (assignTo t.toCT v)))
  | .case_ v shift mask dflt keys exprs =>
    -- The case's local has the case's type; each branch is assigned to it (ir/processor.cpp:808).
    let cv ← evalVal v env selfs
    let key : Option Int := match cv.toObj with
      | .smallInteger x => some x.toInt
      | .integer x => some x.toInt
      | _ => none
    if shift != 0 || mask != 0 then throw (.unsupported "case with shift/mask")
    let branch := match key with
      | some k => match (keys.zip exprs).find? (fun (kk, _) => kk.toInt == k) with
        | some (_, x) => x
        | none => dflt
      | none => dflt
    match ← evalE branch env selfs with
    | .recur args => pure (.recur args)
    | .val r => pure (.val (← liftE (assignTo e.caseType.toCT r)))
  | .recur _ args _ _ =>
    let mut vs := []
    for x in args do vs := vs ++ [← evalVal x env selfs]
    pure (.recur vs)
  | .def name value =>
    let (ns, n) := symKey name
    let vr : VarRef := ⟨ns, n⟩
    match value with
    | some v =>
      let x ← evalVal v env selfs
      modify fun s => { s with roots := (vr, .obj x.toObj) :: s.roots.filter (·.1 != vr) }
    | none => modify fun s => if (s.roots.lookup vr).isSome then s else { s with roots := (vr, .unbound) :: s.roots }
    pure (.val (.obj (.var ns n)))
  | .vector xs md =>
    let vs ← xs.mapM fun x => evalVal x env selfs
    let m ← md.mapM fun x => evalVal x env selfs
    pure (.val (.obj (.persistentVector (m.map (·.toObj)) (vs.map (·.toObj)))))
  | .list xs md =>
    let vs ← xs.mapM fun x => evalVal x env selfs
    let m ← md.mapM fun x => evalVal x env selfs
    pure (.val (.obj (.persistentList (m.map (·.toObj)) (vs.map (·.toObj)))))
  | .set xs md =>
    let vs ← xs.mapM fun x => evalVal x env selfs
    let m ← md.mapM fun x => evalVal x env selfs
    pure (.val (.obj (.persistentHashSet (m.map (·.toObj)) (vs.map (·.toObj)))))
  | .map kvs md =>
    let vs ← kvs.mapM fun (k, v) => do pure ((← evalVal k env selfs).toObj, (← evalVal v env selfs).toObj)
    let m ← md.mapM fun x => evalVal x env selfs
    pure (.val (.obj (.persistentArrayMap (m.map (·.toObj)) vs)))
  | .cppConversion t ct v pol =>
    let x ← evalVal v env selfs
    match pol with
    | .intoObject =>
      if isVoid ct.toCT then return .val (.obj .nil)
      pure (.val (.obj x.toObj))
    | .fromObject =>
      match x with
      | .obj o =>
        if isAnyObject t.toCT then
          -- `convert<oref<T>>::from_object` = `try_object<T>` (builtin.hpp:56): throws on another type.
          if typedMatches t.toCT o then pure (.val (.obj o))
          else throw (.thrown s!"invalid object type (expected {t.toCT.spelling} found {reprStr o.type})")
        else pure (.val (.nat t.toCT (← liftE (fromObject t.toCT o))))
      | .nat _ n => pure (.val (.nat t.toCT n))
  | .cppConstructorCall t _ [arg] _ =>
    match ← evalVal arg env selfs with
    | .nat _ n => pure (.val (.nat t.toCT (← liftE (convNative t.toCT n))))
    | .obj o => pure (.val (.nat t.toCT (← liftE (fromObject t.toCT o))))
  | .cppCall t src args _ =>
    let fname := match (a.expr src).data with
      | .cppValue _ _ _ (.named n) _ => n
      | _ => ""
    let vs ← args.mapM fun x => evalVal x env selfs
    evalCppCall t.toCT fname vs
  | .call src args _ =>
    let f ← evalVal src env selfs
    let vs ← args.mapM fun x => evalVal x env selfs
    pure (.val (.obj (← invoke f.toObj (vs.map (·.toObj)))))
  | .namedRecursion rref _ args =>
    let f ← evalVal rref env selfs
    let vs ← args.mapM fun x => evalVal x env selfs
    pure (.val (.obj (← invoke f.toObj (vs.map (·.toObj)))))
  | .throw_ (some v) =>
    let x ← evalVal v env selfs
    throw (.thrown x.toObj.pr)
  | _ => throw (.unsupported s!"expression {reprStr e.kind}")

/-- `jank::runtime::<fn>` called from a `cpp_call`. -/
partial def evalCppCall (t : CT) (fname : String) (vs : List Val) : EvM Flow := do
  match fname, vs with
  | "jank.runtime.inc", [.nat _ (.i x)] =>
    if Obj.isLongRange (x + 1) then pure (.val (.nat t (.i (x + 1)))) else throw (.thrown "Overflow on increment.")
  | "jank.runtime.inc", [.nat _ (.d f)] => pure (.val (.nat t (.d (f + 1.0))))
  | "jank.runtime.inc", [.nat _ (.b b)] => pure (.val (.nat t (.i ((if b then 1 else 0) + 1))))
  | "jank.runtime.inc", [.obj o] =>
    match builtin "inc" [o] with
    | some (.ok r) => pure (.val (.obj r))
    | some (.error m) => throw (.thrown m)
    | none => throw (.unsupported "inc")
  | "jank.runtime.mul", [.nat lt l, .nat rt r] =>
    match getCommonType lt rt with
    | some ct =>
      let l' ← liftE (convNative ct l)
      let r' ← liftE (convNative ct r)
      match l', r' with
      | .i x, .i y => pure (.val (.nat ct (← liftE (convNative ct (.i (x * y))))))
      | .d x, .d y => pure (.val (.nat ct (.d (x * y))))
      | _, _ => throw (.unsupported "mul")
    | none => throw (.unsupported "mul")
  | "jank.runtime.add", [.nat lt l, .nat rt r] =>
    match getCommonType lt rt, l, r with
    | some ct, _, _ =>
      let l' ← liftE (convNative ct l)
      let r' ← liftE (convNative ct r)
      match l', r' with
      | .i x, .i y => pure (.val (.nat ct (← liftE (convNative ct (.i (x + y))))))
      | .d x, .d y => pure (.val (.nat ct (.d (x + y))))
      | _, _ => throw (.unsupported "add")
    | none, _, _ => throw (.unsupported "add")
  | "jank.runtime.add", [x, y] =>
    match builtin "+" [x.toObj, y.toObj] with
    | some (.ok r) => pure (.val (.obj r))
    | some (.error m) => throw (.thrown m)
    | none => throw (.unsupported "add")
  | "jank.runtime.is_pos", [x] =>
    match builtin "pos?" [x.toObj] with
    | some (.ok (.boolean b)) => pure (.val (.nat t (.b b)))
    | some (.error m) => throw (.thrown m)
    | _ => throw (.unsupported "is_pos")
  | "jank.runtime.get", [m, k] => pure (.val (.obj (builtinGet m.toObj k.toObj)))
  | "jank.runtime.get", [m, k, d] => pure (.val (.obj (builtinGet m.toObj k.toObj d.toObj)))
  | _, _ => throw (.unsupported s!"C++ call {fname}")

/-- Calls a function object with argument objects. -/
partial def invoke (f : Obj) (args : List Obj) : EvM Obj := do
  tick
  match f with
  | .opaque .nativeFunctionWrapper k =>
    match builtin (builtinNames.getD k "") args with
    | some (.ok r) => pure r
    | some (.error m) => throw (.thrown m)
    | none => throw (.thrown s!"wrong number of args to {builtinNames.getD k ""}")
  | .opaque .jitClosure k =>
    let s ← get
    let c := s.closures[k]!
    let a := s.arena
    let arities := match (a.expr c.fnExpr).data with
      | .function _ _ ars _ _ => ars
      | _ => []
    let n := args.length
    let fixed := arities.find? fun ar => !(a.fnCtx ar.fnCtx).isVariadic && ar.params.length == n
    let variadic := arities.find? fun ar => (a.fnCtx ar.fnCtx).isVariadic && ar.params.length - 1 ≤ n
    let some ar := fixed <|> variadic | throw (.thrown s!"Wrong number of args ({n}) passed to a function")
    let isVar := (a.fnCtx ar.fnCtx).isVariadic
    let pbs := paramBindings a (ar.frame.getD 0)
    let bind (xs : List Obj) : List (BindingId × Val) :=
      if isVar then
        let req := ar.params.length - 1
        let restV : Obj := if xs.length > req then .persistentList none (xs.drop req) else .nil
        (pbs.zip ((xs.take req).map Val.obj ++ [Val.obj restV])) ++ c.env
      else (pbs.zip (xs.map Val.obj)) ++ c.env
    let mut cur := args
    for _ in [0:100000] do
      match ← evalE ar.body (bind cur) c.selfs with
      | .val v => return v.toObj
      | .recur vs =>
        cur := vs.map (·.toObj)
        if isVar then
          -- A variadic arity's recur passes the rest argument as one value.
          let req := ar.params.length - 1
          cur := (cur.take req) ++ ((cur.drop req).headD .nil |>.elems |>.getD [])
    throw .fuel
  | .keyword .. =>
    match args with
    | [m] => pure (builtinGet m f)
    | [m, d] => pure (builtinGet m f d)
    | _ => throw (.thrown "keyword called with the wrong number of args")
  | _ => throw (.thrown s!"{f.pr} is not callable")

end

/-- Evaluates a top-level analyzed form (`evaluate::eval` of `wrap_expression`): a non-object
result is boxed. -/
def evalTop (i : ExprId) : EvM Obj := do
  let v ← evalVal i [] []
  pure v.toObj

end Jank.Analyzer
