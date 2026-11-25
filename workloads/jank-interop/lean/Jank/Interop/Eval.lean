import Jank.Interop.Codegen

/-!
# What the emitted C++ does

An interpreter of the analyzed program that follows, aty each interop node, the C++ text
`Codegen.lean` emits, under the C++ meaning of `Value.lean`. Where that text lets C++ decide (an
`auto` variable's type, a call by name that C++ resolves again, `T{ ... }` list-initialization),
the interpreter decides as C++ does, from the actual types of the emitted variables, not from the
analyzer's types. A construct C++ rejects is `Fault.illFormed` (a JIT compile error).

jank's runtime functions the emitted code calls are modeled: the math templates of core/math.hpp
(`add`, `sub`, `mul`, `div`, `lt`, `lte`, `inc`, `dec`, including their `visit_number_like` paths
on objects), `convert<T>` (Convert.lean), `truthy`, opaque boxes, and the few clojure.core
functions the searched programs call (`identity`, `f` = a user function returning its argument).
-/

namespace Jank.Interop.Eval

open Jank.Analyzer (Obj ObjectType ExprPosition ExprKind CppValueKind ConversionPolicy LoopKind)
open CppUtil

structure EvalState where
  boxes : Array OpaqueBox := #[]
  heap : Array CVal := #[]
  /-- Loop iterations left (a loop past it is reported as not terminating). -/
  fuel : Nat := 64

abbrev EM := EStateM Fault EvalState

/-- How an expression's evaluation ended: a value with its actual C++ type, or a `recur`. -/
inductive Flow where
  | val (v : CVal) (t : CType)
  | recur (vals : List (CVal × CType))
  deriving Inhabited

def fault {α : Type} (f : Fault) : EM α := throw f

def liftC {α : Type} (r : CRes α) : EM α := match r with | .ok a => pure a | .error f => throw f

/-- The C++ type and value of a literal's emitted text ([lex.icon], [lex.fcon]): a decimal
integer is `int`, else `long`, else `long long`, else (Clang, IA10) `unsigned long long`; a leading
`-` is unary minus on that type. `INFINITY`/`NAN` are `float` constant expressions (<cmath>). A
string literal's `auto` copy is a `char const *`. -/
def literalOfText (p : Platform) (o : Obj) : CVal × CType :=
  match o with
  | .smallInteger v | .integer (v := v) =>
    let i := v.toInt
    let mag := i.natAbs
    let k : Builtin :=
      if (mag : Int) ≤ Builtin.int.maxVal p then .int
      else if (mag : Int) ≤ Builtin.long.maxVal p then .long
      else .ullong
    let value : Int := if i < 0 then Cxx.wrapTo p k (-(mag : Int)) else Cxx.wrapTo p k mag
    (.int k value, .b k)
  | .smallReal b | .real b =>
    let x := Float.ofBits b
    if x.isInf || x.isNaN then (.flt .float x, .b .float) else (.flt .double x, .b .double)
  | .boolean b => (.bool b, .b .bool)
  | .persistentString s => (.cstr (some s), .ptr (.const (.b .char)))
  | o => (.obj o, untypedObjectRefType)

/-- The numeric value and C++ type of a typed numeric object's `data` (oref.hpp: `i32` for a small
integer, `i64` for an integer, `f64` for reals). -/
def objData : Obj → Option (CVal × CType)
  | .smallInteger v => some (.int .int v.toInt, .b .int)
  | .integer v => some (.int .long v.toInt, .b .long)
  | .smallReal b | .real b => some (.flt .double (Float.ofBits b), .b .double)
  | _ => none

/-- `make_box` of an arithmetic C++ result (make_box.hpp). -/
def boxResult (p : Platform) (w : World) (v : CVal) : CRes Obj :=
  match v with
  | .int k x => .ok (makeBoxIntegral p w k x)
  | .flt _ x => .ok (makeBoxReal x)
  | .bool b => .ok (makeBoxBool b)
  | _ => .error (.unmodeled "make_box")

def opOfMath : String → Cxx.Op
  | "add" => .plus | "sub" => .minus | "mul" => .star | "div" => .slash
  | "lt" => .less | "lte" => .lessEqual | _ => .plus

/-- The math templates of core/math.hpp applied to argument values of the given actual types. -/
def evalMath (p : Platform) (w : World) (k : TemplateKind) (args : List (CVal × CType)) : CRes (CVal × CType) := do
  let types := args.map (·.2)
  let some inst := CppInterop.instantiateMath p w k types | .error (.illFormed "no matching math template")
  match k, args with
  | .mathBinary opName, [(a, ta), (b, tb)] =>
    let op := opOfMath opName
    let cmp := opName == "lt" || opName == "lte"
    let primA := CppInterop.isPrimitiveNumber ta
    let primB := CppInterop.isPrimitiveNumber tb
    let operand (v : CVal) (t : CType) (prim : Bool) : CRes (CVal × CType) :=
      if prim then .ok (v, t)
      else match v with
        | .obj o => match objData o with
          | some d => .ok d
          | none => .error (.thrown s!"not a number: {objTypeName o}")
        | _ => .error (.unmodeled "math operand")
    if primA && primB then
      let r ← Cxx.evalBinop p w op ta tb a b
      return (r, inst.ret)
    if (!primA && !CppInterop.isValidBoxedMath ta) || (!primB && !CppInterop.isValidBoxedMath tb) then
      .error (.thrown s!"Can't {opName} these types.")
    let (x, tx) ← operand a ta primA
    let (y, ty) ← operand b tb primB
    let r ← Cxx.evalBinop p w op tx ty x y
    if cmp then return (r, .b .bool)
    if inst.ret == objectRef then return (.obj (← boxResult p w r), objectRef)
    return (r, inst.ret)
  | .mathUnary opName, [(a, ta)] =>
    let delta : Int := if opName == "inc" then 1 else -1
    if CppInterop.isPrimitiveNumber ta then
      match a with
      | .flt kk x => return (.flt kk (x + Float.ofInt delta), inst.ret)
      | _ =>
        let some x := Cxx.asInt? a | .error (.unmodeled "inc")
        -- __builtin_add_overflow(l, 1ll, &res) into an i64: throws on overflow
        if !Builtin.long.fits p (x + delta) then .error (.thrown "Overflow on increment.")
        return (.int .long (x + delta), .b .long)
    match a with
    | .obj o => match objData o with
      | some (.int _ x, _) =>
        if !Builtin.long.fits p (x + delta) then .error (.thrown "Overflow on increment.")
        return (.obj (makeBoxI64 (x + delta)), objectRef)
      | some (.flt _ x, _) => return (.obj (makeBoxReal (x + Float.ofInt delta)), objectRef)
      | _ => .error (.thrown s!"Can't increment a {objTypeName o}.")
    | _ => .error (.unmodeled "inc operand")
  | _, _ => .error (.unmodeled "math arity")

/-- The value a `cpp/value`-style literal function returns. -/
def literalFnValue (name : String) : Option (CVal × CType) :=
  (literalValues.find? fun (n, _, _) => s!"jank_literal_{n}" == name).map fun (_, t, v) => (v, t)

/-- What the program's declared functions do: `take_X(x)` returns its parameter. -/
def callDeclared (f : FnDecl) (args : List CVal) : CRes CVal :=
  if f.name.startsWith "take_" then
    match args with
    | [v] => .ok v
    | _ => .error (.unmodeled "arity")
  else .error (.unmodeled s!"function {f.name}")

/-- Copy-initializing a parameter of type `param` from a value of actual type `t`: well-formed iff
C++ has an implicit conversion; the value converted. -/
def passArg (p : Platform) (w : World) (v : CVal) (t param : CType) : CRes CVal :=
  if (Cxx.implicitConv p w t param).isNone then
    .error (.illFormed s!"no conversion from `{CppInterop.getTypeAsString t}` to `{CppInterop.getTypeAsString param}`")
  else Cxx.convertTo p w param v

/-- A class constructed from argument values (the model's classes). -/
def constructClass (p : Platform) (w : World) (cls : String) (f : Option FnDecl) (args : List CVal) (listInit : Bool) : CRes CVal :=
  match cls, f, args with
  | "std::vector<int>", some f, vs =>
    if f.initListElem.isSome then .ok (.vec vs)
    else match vs with
      | [] => .ok (.vec [])
      | [n] => match Cxx.asInt? n with
        | some k => if k > 4096 then .error (.unmodeled "a vector of more than 4096 elements")
                    else .ok (.vec (List.replicate k.toNat (.int .int 0)))
        | none => .error (.unmodeled "vector size")
      | [n, x] => match Cxx.asInt? n with
        | some k => if k > 4096 then .error (.unmodeled "a vector of more than 4096 elements")
                    else .ok (.vec (List.replicate k.toNat x))
        | none => .error (.unmodeled "vector size")
      | _ => .error (.unmodeled "vector ctor")
  | "std::basic_string<char>", _, [.cstr (some s)] => .ok (.str s)
  | "std::basic_string<char>", _, [.str s] => .ok (.str s)
  | "std::basic_string<char>", _, [] => .ok (.str "")
  | c, _, vs => let _ := (p, w, listInit); .ok (.record c vs)

/-- Whether a narrowing conversion in list-initialization stops the JIT. Clang makes it an error
by default (group `-Wc++11-narrowing`), but jank's JIT passes `-w -Wno-c++11-narrowing`
(jit/processor_dynamic.cpp:248 at f3d82d654, :250 at 7135b7708), so it compiles and converts. -/
def narrowingIsError : Bool := false

/-- `T{ args }` ([dcl.init.list]) for the class or builtin `t`: an initializer-list constructor
first when the elements convert to its element type, else the constructors; a narrowing
conversion is ill-formed only when `narrowingIsError`. -/
def listInit (p : Platform) (w : World) (t : CType) (args : List (CVal × CType)) : CRes CVal := do
  match (Cxx.nonRef t).canonical.unqual with
  | .b k =>
    match args with
    | [] => Cxx.convertNum p k (.i 0)
    | [(v, aty)] =>
      if narrowingIsError && Cxx.isNarrowing p w aty t then .error (.illFormed s!"narrowing conversion from `{CppInterop.getTypeAsString aty}` to `{CppInterop.getTypeAsString t}` in an initializer list")
      else Cxx.convertTo p w t v
    | _ => .error (.illFormed "excess elements in a scalar initializer")
  | .record n =>
    let some cls := w.findClass n | .error (.unmodeled "class")
    let ilist := cls.ctors.find? fun f => f.initListElem.isSome &&
      args.all fun (_, aty) => (Cxx.implicitConv p w aty (f.initListElem.getD .null)).isSome
    match ilist with
    | some f =>
      let e := f.initListElem.getD .null
      if narrowingIsError && args.any fun (_, aty) => Cxx.isNarrowing p w aty e then
        .error (.illFormed s!"narrowing conversion to `{CppInterop.getTypeAsString e}` in the initializer list of `{n}`")
      let vs ← args.mapM fun (v, _) => Cxx.convertTo p w e v
      constructClass p w n (some f) vs true
    | none =>
      if cls.isAggregate then
        let members := cls.fields.map (·.type)
        if members.length < args.length then .error (.illFormed "too many initializers")
        let vs ← (args.zip members).mapM fun ((v, aty), mt) =>
          if narrowingIsError && Cxx.isNarrowing p w aty mt then .error (.illFormed "narrowing in aggregate initialization")
          else passArg p w v aty mt
        constructClass p w n none vs true
      else
        match CppInterop.bestOverloadMatch p w cls.ctors (args.map (·.2)) with
        | [f] =>
          if narrowingIsError && (args.zip f.params).any fun ((_, aty), pt) => Cxx.isNarrowing p w aty (Cxx.nonRef pt) then
            .error (.illFormed "narrowing conversion in a list-initialized constructor call")
          let vs ← (args.zip f.params).mapM fun ((v, aty), pt) => passArg p w v aty pt
          constructClass p w n (some f) vs true
        | _ => .error (.illFormed s!"no constructor of `{n}` for this initializer list")
  | _ => .error (.unmodeled "list-initialization")

/-- Environment: let/loop bindings, their values and actual C++ types. -/
abbrev Env := List (String × CVal × CType)

mutual

partial def evalVal (p : Platform) (w : World) (env : Env) (e : IExpr) : EM (CVal × CType) := do
  match ← eval p w env e with
  | .val v t => pure (v, t)
  | .recur _ => fault (.unmodeled "recur in value position")

/-- The meaning of an analyzed expression. -/
partial def eval (p : Platform) (w : World) (env : Env) (e : IExpr) : EM Flow := do
  match e.data with
  | .primitiveLiteral d => pure (.val (.obj d) (literalType d true))
  -- cpp_processor.cpp:1278: `auto name(<lifted text>);`
  | .cppLiteral d => let (v, t) := literalOfText p d; pure (.val v t)
  | .localReference b _ =>
    match env.lookup b.name with
    | some (v, t) => pure (.val v t)
    | none => fault (.unmodeled s!"local {b.name}")
  | .varDeref n => pure (.val (.obj (.opaque .jitFunction n.length)) objectRef)
  | .call fnName args => do
    let vs ← args.mapM (evalVal p w env)
    match fnName, vs with
    | "identity", [(v, _)] | "f", [(v, _)] => pure (.val v objectRef)
    | _, _ => fault (.unmodeled s!"jank function {fnName}")
  | .if_ chosen cond thenE elseE => do
    let (cv, ct) ← evalVal p w env cond
    let b ← match cv with
      | .obj o => pure (cljOfObj o).truthy
      | .bool b => pure b
      | _ => fault (.illFormed s!"`if` on a `{CppInterop.getTypeAsString ct}`")
    let branch := if b then some thenE else elseE
    match branch with
    | none => pure (.val (.obj .nil) chosen)
    | some be =>
      match ← eval p w env be with
      | .recur vs => pure (.recur vs)
      | .val v t =>
        -- `{chosen} local{ }; local = std::move(branch);`
        if isAnyObject w chosen then pure (.val v chosen)
        else pure (.val (← liftC (Cxx.convertTo p w chosen v)) chosen)
        |> fun r => let _ := t; r
  | .let_ pairs body kind => do
    let mut env' := env
    for (b, ve) in pairs do
      let (v, t) ← evalVal p w env' ve
      env' := (b.name, v, t) :: env'
    if kind != .loopWithRecur then
      let mut last : Flow := .val (.obj .nil) objectRef
      for x in body do last ← eval p w env' x
      return last
    -- ir/processor.cpp:531: shadows `auto shadow(init)` (or `object_ref` for object types),
    -- `shadow = new_value;` at each recur.
    let shadowTypes := pairs.map fun (b, ve) =>
      if isAnyObject w (mutableType w (getType ve)) then objectRef
      else match env'.lookup b.name with
        | some (_, t) => t
        | none => b.type
    let mut cur := env'
    let mut iter := 0
    repeat
      if iter ≥ (← get).fuel then return ← fault (.ub "the loop did not end within the model's iteration bound")
      iter := iter + 1
      let mut last : Flow := .val (.obj .nil) objectRef
      for x in body do last ← eval p w cur x
      match last with
      | .val v t => return .val v t
      | .recur vs =>
        let mut next := cur
        for ((b, _), (v, t), st) in (pairs.zip vs).zip shadowTypes |>.map (fun ((a, b), c) => (a, b, c)) do
          let v' ← if isAnyObject w st then pure v
            else if (Cxx.implicitConv p w t st).isNone then fault (.illFormed "loop assignment")
            else liftC (Cxx.convertTo p w st v)
          let _ := t
          next := (b.name, v', st) :: next
        cur := next
    fault (.unmodeled "loop")
  | .recur args => do
    let vs ← args.mapM (evalVal p w env)
    pure (.recur vs)
  | .cppRaw _ => pure (.val .void (.b .void))
  | .cppType .. => fault (.unmodeled "cpp_type in codegen")
  | .cppValue _ t scope k =>
    match k with
    | .null => pure (.val .nullptr (.b .nullptr))
    | .boolTrue => pure (.val (.bool true) (.b .bool))
    | .boolFalse => pure (.val (.bool false) (.b .bool))
    | .enumConstant =>
      match scope with
      | some (.enumConstant en _ v) => pure (.val (.enumv en v) (.enum en))
      | _ => fault (.unmodeled "enum constant")
    | _ => let _ := t; fault (.unmodeled "cpp value")
  -- cpp_processor.cpp:1287: `convert<T>::into_object` / `from_object`, `T` the canonical cv-free
  -- conversion type
  | .cppConversion t ct v policy => do
    let (x, xt) ← evalVal p w env v
    if policy == .intoObject then
      if CppInterop.isVoid ct then return .val (.obj .nil) t
      if isUntypedObject t && isAnyObject w ct then return .val x t
      if integerRefType.canonical == t.canonical then
        match Cxx.asInt? x with
        | some i => return .val (.obj (.integer (BitVec.ofInt 64 i))) t
        | none => return ← fault (.unmodeled "make_box<integer>")
      let some s := convertSpec w ct | fault (.illFormed s!"convert<{CppInterop.getTypeAsString ct}> is incomplete")
      -- the argument (actual type `xt`) converts to the parameter `T const`
      let x' ← if isAnyObject w ct then pure x else liftC (Cxx.convertTo p w ct x)
      let _ := xt
      let o ← liftC (intoObject p w s x')
      return .val (.obj o) t
    else
      let some s := convertSpec w ct | fault (.illFormed s!"convert<{CppInterop.getTypeAsString ct}> is incomplete")
      match x with
      | .obj o => return .val (← liftC (fromObject p w s o)) (fromObjectReturnType s ct)
      | _ => fault (.unmodeled "from_object of a native value")
  -- cpp_processor.cpp:1340: `(T)(value)`
  | .cppUnsafeCast t v => do
    let (x, _) ← evalVal p w env v
    match x with
    | .cstr s => pure (.val (.cstr s) t)
    | _ => pure (.val (← liftC (Cxx.convertTo p w t x)) t)
  -- cpp_processor.cpp:1352: `f(args)`, resolved again by C++ on the arguments' actual types
  | .cppCall t source args _ => do
    let vs ← args.mapM (evalVal p w env)
    match source.data with
    | .cppValue _ _ (some (.function f)) _ =>
      if let some (v, rt) := literalFnValue f.name then return .val v rt
      match f.template with
      | .none =>
        let cands := w.functions.filter (·.name == f.name)
        match CppInterop.bestOverloadMatch p w cands (vs.map (·.2)) with
        | [g] =>
          let xs ← (vs.zip g.params).mapM fun ((v, aty), pt) => liftC (passArg p w v aty pt)
          let r ← liftC (callDeclared g xs)
          let rt := g.ret
          let _ := t
          return .val (← liftC (Cxx.convertTo p w rt r)) rt
        | _ => fault (.illFormed s!"no matching function for call to `{f.name}` with the emitted argument types")
      | k =>
        let (r, rt) ← liftC (evalMath p w k vs)
        return .val r rt
    | _ => fault (.unmodeled "indirect call")
  -- cpp_processor.cpp:1563
  | .cppConstructorCall t fn args isAgg => do
    let vs ← args.mapM (evalVal p w env)
    let nonRefT := CppInterop.getNonReferenceType t
    let paramTypes : List CType :=
      match fn with
      | some f => f.params
      | none => if isPrimitive nonRefT then [t] else aggregateInitializationTypes w (CppInterop.getScopeFromType w t)
    let mut xs : List (CVal × CType) := []
    -- the codegen decides from the analyzer's argument type (`expression_type(arg_expr)`); the
    -- emitted cast applies to the variable's actual type `act`
    for ((ae, (v, act)), i) in (args.zip vs).zipIdx do
      let aty := expressionType ae
      let pt := paramTypes.getD i .null
      if isAnyObject w pt && !isAnyObject w aty then
        let some s := convertSpec w aty | return ← fault (.illFormed "convert into_object")
        xs := xs ++ [(.obj (← liftC (intoObject p w s v)), pt)]
      else if !isAnyObject w pt && isAnyObject w aty then
        let some s := convertSpec w pt | return ← fault (.illFormed "convert from_object")
        match v with
        | .obj o => xs := xs ++ [(← liftC (fromObject p w s o), fromObjectReturnType s pt)]
        | _ => return ← fault (.unmodeled "from_object")
      else if pt != aty then
        -- `static_cast<NAME(pt)>(arg)`: the type the printed name denotes; well-formed only as
        -- [expr.static.cast] allows
        let pt := typeOfName w pt
        if !Cxx.staticCastValid p w act pt then
          return ← fault (.illFormed s!"static_cast from `{CppInterop.getTypeAsString act}` to `{CppInterop.getTypeAsString pt}`")
        let cv ← if Cxx.isPointer pt then
            match v with
            | .ptr _ a => pure (CVal.ptr (Cxx.pointee pt) a)
            | .cstr s => pure (CVal.cstr s)
            | _ => liftC (Cxx.convertTo p w pt v)
          else liftC (Cxx.convertTo p w pt v)
        xs := xs ++ [(cv, pt)]
      else xs := xs ++ [(v, act)]
    if isAgg then
      return .val (← liftC (listInit p w t xs)) nonRefT
    -- the variable is declared with the printed name of the type
    let nonRefT := CppInterop.getNonReferenceType (typeOfName w t)
    match nonRefT.canonical.unqual with
    | .record n =>
      let f := fn
      let ys ← (xs.zip (f.map (·.params) |>.getD [])).mapM fun ((v, aty), pt) => liftC (passArg p w v aty pt)
      return .val (← liftC (constructClass p w n f ys false)) nonRefT
    | _ =>
      match xs with
      | [] => return .val (← liftC (Cxx.convertTo p w nonRefT (.int .int 0))) nonRefT
      | [(v, aty)] =>
        if !Cxx.isConstructible p w nonRefT aty then
          return ← fault (.illFormed s!"`{CppInterop.getTypeAsString nonRefT}` from `{CppInterop.getTypeAsString aty}`")
        if Cxx.isPointer nonRefT then
          match v with
          | .ptr _ a => return .val (.ptr (Cxx.pointee nonRefT) a) nonRefT
          | .cstr s => return .val (.cstr s) nonRefT
          | _ => return .val (← liftC (Cxx.convertTo p w nonRefT v)) nonRefT
        else return .val (← liftC (Cxx.convertTo p w nonRefT v)) nonRefT
      | _ => fault (.illFormed "builtin constructed from several values")
  | .cppMemberCall _ fn args => do
    let vs ← args.mapM (evalVal p w env)
    match fn.name, vs with
    | "size", [(.vec xs, _)] => pure (.val (.int .ulong xs.length) sizeT)
    | "size", [(.str s, _)] => pure (.val (.int .ulong s.utf8ByteSize) sizeT)
    | "size", [(.ptr _ a, _)] =>
      match (← get).heap[a - 1]? with
      | some (.vec xs) => pure (.val (.int .ulong xs.length) sizeT)
      | _ => fault (.unmodeled "size through a pointer")
    | _, _ => fault (.unmodeled s!"member {fn.name}")
  | .cppMemberAccess t _ name o => do
    let (x, _) ← evalVal p w env o
    match x with
    | .record _ fs =>
      let idx := match o with
        | _ => if name == "name" || name == "x" then 0 else 1
      pure (.val (fs.getD idx .void) t)
    | _ => fault (.unmodeled "member access")
  -- cpp_processor.cpp:1794: `auto &&name( a op b );` on the actual operand types
  | .cppBuiltinOperatorCall op args _ => do
    let vs ← args.mapM (evalVal p w env)
    let rt := Cxx.builtinOperatorType p w op (vs.map (·.2))
    if rt.isNull then return ← fault (.illFormed "builtin operator on the emitted types")
    match vs with
    | [(a, ta), (b, tb)] => pure (.val (← liftC (Cxx.evalBinop p w op ta tb a b)) rt)
    | [(a, ta)] =>
      if op == .minus then pure (.val (← liftC (Cxx.evalBinop p w .minus (.b .int) ta (.int .int 0) a)) rt)
      else if op == .exclaim then
        match Cxx.toNum a with
        | some (.i x) => pure (.val (.bool (x == 0)) (.b .bool))
        | _ => fault (.unmodeled "!")
      else fault (.unmodeled "unary operator")
    | _ => fault (.unmodeled "operator arity")
  -- cpp_processor.cpp:1824: the box records the canonical value type's qualified name
  | .cppBox v => do
    let (x, _) ← evalVal p w env v
    let .ptr _ addr := x | fault (.unmodeled "box of a non-pointer")
    let name := getQualifiedTypeName w (CppInterop.getNonReferenceType (expressionType v)).canonical
    let st ← get
    set { st with boxes := st.boxes.push { addr, canonicalType := name } }
    pure (.val (.obj (Obj.opaque ObjectType.opaqueBox st.boxes.size)) (typedRef "opaque_box"))
  -- cpp_processor.cpp:1848: `static_cast<T>(jank_unbox_with_source("T", ...))`
  | .cppUnbox t v => do
    let (x, _) ← evalVal p w env v
    let i ← match x with
      | .obj (Obj.opaque ObjectType.opaqueBox j) => pure j
      | _ => fault (.thrown "invalid object type (expected opaque_box)")
    let some box := (← get).boxes[i]? | fault (.unmodeled "box")
    let addr ← liftC (jankUnboxWithSource (getQualifiedTypeName w t.canonical) box)
    let tt := typeOfName w t.canonical
    pure (.val (.ptr (Cxx.pointee tt) addr) tt)
  -- cpp_processor.cpp:1866: `new (UseGC) T{ args, }`
  | .cppNew t v => do
    match v.data with
    | .cppConstructorCall _ _ args _ =>
      let vs ← args.mapM (evalVal p w env)
      let obj ← liftC (listInit p w t vs)
      let st ← get
      set { st with heap := st.heap.push obj }
      pure (.val (.ptr t (st.heap.size + 1)) (.ptr t))
    | _ => fault (.unmodeled "cpp/new")
  | .cppDelete _ => pure (.val (.obj .nil) (typedRef "nil"))

end

/-- Runs an analyzed function body; the result object, or how it stopped. -/
def runBody (p : Platform) (w : World) (env : Env) (e : IExpr) (fuel : Nat := 64) : Except Fault CVal :=
  match (eval p w env e).run { fuel } with
  | .ok (.val v _) _ => .ok v
  | .ok (.recur _) _ => .error (.unmodeled "recur escaped")
  | .error f _ => .error f

end Jank.Interop.Eval
