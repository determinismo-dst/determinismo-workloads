import Jank.R3.Codegen.Native

/-!
# Clojure 1.12's meaning of the native-world programs

From clojure-ref (Clojure 1.12 sources):

- `Numbers.add/minus/multiply` on longs: exact, `ArithmeticException("integer overflow")` past the
  long range (`Numbers.add(long,long)`); a double operand makes the operation a double one; a
  ratio or BigInt operand an exact one (`RatioOps`, `BigIntOps`).
- `Numbers.divide(long,long)`: `ArithmeticException("Divide by zero")`; otherwise the normalized
  ratio, a long when exact (`normalize`, `reduceBigInt`), a BigInt past the long range.
- `Numbers.lt`: numbers only (`ClassCastException` otherwise).
- `RT.intCast(Object)`: a long or double outside the int range throws
  `IllegalArgumentException("Value out of range for int")`; NaN passes the check and is 0; other
  objects throw.
- `loop`: locals rebound by `recur` (a primitive local recurred with another type is boxed:
  Compiler.java 6955-6980, 7205-7245); `fn` with `^long`/`^double` parameters converts the
  arguments with `RT.longCast`/`RT.doubleCast` and rejects a `recur` argument of another
  primitive type at compile time (Compiler.java 7100-7150). jank's `^cpp/long`, `^cpp/double` are
  compared with Clojure's `^long`, `^double`; `^cpp/int` has no Clojure counterpart (Clojure has no
  int primitive parameters) and is compared with `^long`.
- `if`: `nil` and `false` are false. Calls: operator, then operands, left to right.
-/

namespace Jank.R3.Codegen

structure CClosure where
  params : List (String × PTy)
  body : NF
  env : List (String × Val)
  deriving Inhabited

structure CS where
  closures : Array CClosure := #[]
  out : List String := []
  effects : Nat := 0
  fuel : Nat := 20000
  deriving Inhabited

inductive CStop where
  | threw (m : String)
  | hang
  | fuel
  | unsupported (m : String)
  deriving Inhabited

abbrev CM := EStateM CStop CS

def ctick : CM Unit := do
  let s ← get
  if s.fuel == 0 then throw .fuel
  set { s with fuel := s.fuel - 1 }

def gcdN (a b : Nat) : Nat := Nat.gcd a b

/-- A normalized exact number: long when it fits and `isLongOp`, else BigInt; a ratio otherwise. -/
def normRatio (n d : Int) (fromLongDivide : Bool) : Val :=
  let g : Int := (Nat.gcd n.natAbs d.natAbs : Int)
  let (n, d) := if d < 0 then (-(n / g), -(d / g)) else (n / g, d / g)
  if d == 1 then
    if fromLongDivide && inI64 n then .long n else .big n
  else .ratio n d

def asRat : Val → Option (Int × Int)
  | .long v => some (v, 1)
  | .big v => some (v, 1)
  | .ratio n d => some (n, d)
  | _ => none

def ratToF (n d : Int) : Float := Float.ofInt n / Float.ofInt d

def cArith (o : AOp) (a b : Val) : CM Val := do
  match a, b with
  | .bool _, _ | _, .bool _ => throw (.threw "ClassCastException: Boolean cannot be cast to Number")
  | .kw _, _ | _, .kw _ | .fn _, _ | _, .fn _ => throw (.threw "ClassCastException")
  | .nil, _ | _, .nil => throw (.threw "NullPointerException")
  | .dbl x, _ | _, .dbl x =>
    let fx : Float := match a with | .dbl f => f | .long v => Float.ofInt v | .big v => Float.ofInt v | .ratio n d => ratToF n d | _ => 0
    let fy : Float := match b with | .dbl f => f | .long v => Float.ofInt v | .big v => Float.ofInt v | .ratio n d => ratToF n d | _ => 0
    let _ := x
    match o with
    | .add => pure (.dbl (fx + fy)) | .sub => pure (.dbl (fx - fy)) | .mul => pure (.dbl (fx * fy))
    | .div => pure (.dbl (fx / fy)) | .lt => pure (.bool (fx < fy))
  | .long x, .long y =>
    match o with
    | .add => let r := x + y; if inI64 r then pure (.long r) else throw (.threw "ArithmeticException: integer overflow")
    | .sub => let r := x - y; if inI64 r then pure (.long r) else throw (.threw "ArithmeticException: integer overflow")
    | .mul => let r := x * y; if inI64 r then pure (.long r) else throw (.threw "ArithmeticException: integer overflow")
    | .lt => pure (.bool (x < y))
    | .div => if y == 0 then throw (.threw "ArithmeticException: Divide by zero") else pure (normRatio x y true)
  | _, _ =>
    match asRat a, asRat b with
    | some (n1, d1), some (n2, d2) =>
      match o with
      | .add => pure (normRatio (n1 * d2 + n2 * d1) (d1 * d2) false)
      | .sub => pure (normRatio (n1 * d2 - n2 * d1) (d1 * d2) false)
      | .mul => pure (normRatio (n1 * n2) (d1 * d2) false)
      | .lt => pure (.bool (n1 * d2 < n2 * d1))
      | .div => if n2 == 0 then throw (.threw "ArithmeticException: Divide by zero")
                else pure (normRatio (n1 * d2) (d1 * n2) false)
    | _, _ => throw (.unsupported "arith")

/-- `RT.intCast(Object)`. -/
def cIntCast (v : Val) : CM Val := do
  match v with
  | .long x => if inI32 x then pure (.long x) else throw (.threw s!"IllegalArgumentException: Value out of range for int: {x}")
  | .dbl f =>
    if f < -2147483648.0 || f > 2147483647.0 then throw (.threw s!"IllegalArgumentException: Value out of range for int: {fmtF f}")
    else pure (.long (if f.isNaN then 0 else truncF f))
  | .big x => if inI32 x then pure (.long x) else throw (.threw "IllegalArgumentException: Value out of range for int")
  | .ratio n d => let t := n.tdiv d; if inI32 t then pure (.long t) else throw (.threw "IllegalArgumentException: Value out of range for int")
  | _ => throw (.threw "ClassCastException")

/-- `RT.longCast(Object)` / `RT.doubleCast(Object)` for a primitive parameter. -/
def cParamCast (t : PTy) (v : Val) : CM Val := do
  match t, v with
  | .obj, _ => pure v
  | .long, .long _ | .int, .long _ => pure v
  | .long, .dbl f | .int, .dbl f =>
    if f < -9223372036854775808.0 || f ≥ 9223372036854775808.0 then throw (.threw "IllegalArgumentException: Value out of range for long")
    else pure (.long (if f.isNaN then 0 else truncF f))
  | .long, .big x | .int, .big x => if inI64 x then pure (.long x) else throw (.threw "IllegalArgumentException: Value out of range for long")
  | .long, .ratio n d | .int, .ratio n d => pure (.long (n.tdiv d))
  | .double, .long x => pure (.dbl (Float.ofInt x))
  | .double, .dbl f => pure (.dbl f)
  | .double, .big x => pure (.dbl (Float.ofInt x))
  | .double, .ratio n d => pure (.dbl (ratToF n d))
  | _, _ => throw (.threw "ClassCastException")

/-- Clojure's primitive type of an expression (`maybePrimitiveType`): `some true` long, `some false`
double. -/
partial def cPrim (prims : List (String × Option Bool)) : NF → Option Bool
  | .int _ => some true
  | .dbl _ => some false
  | .sym x => (prims.lookup x).join
  | .op o a b =>
    match o with
    | .lt | .div => none
    | _ => match cPrim prims a, cPrim prims b with
      | some true, some true => some true
      | some _, some _ => some false
      | _, _ => none
  | .toInt _ => some true
  | .if_ _ t e => match cPrim prims t, cPrim prims e with
    | some a, some b => if a == b then some a else none
    | _, _ => none
  | .let_ x v b => cPrim ((x, cPrim prims v) :: prims) b
  | _ => none

/-- Compile-time check: a `recur` to a fn with primitive parameters must pass the same primitive. -/
partial def cCheck (prims : List (String × Option Bool)) (fnPrims : Option (List (Option Bool))) : NF → Option String
  | .recur args =>
    match fnPrims with
    | some ps =>
      (args.zip ps).findSome? fun (a, p) => match p with
        | some isLong =>
          let pc := cPrim prims a
          if pc == some isLong then none
          else some s!"IllegalArgumentException: recur arg for primitive local is not matching primitive"
        | none => none
    | none => args.findSome? (cCheck prims none)
  | .fn_ ps b =>
    let pp := ps.map fun (x, t) => (x, match t with | .long | .int => some true | .double => some false | .obj => none)
    cCheck (pp ++ prims) (some (pp.map (·.2))) b
  | .loop bs b =>
    -- loop locals: mismatches are boxed, never an error; the recur inside targets the loop
    let prims' := bs.map (fun (x, _) => (x, (none : Option Bool))) ++ prims
    (bs.findSome? fun (_, v) => cCheck prims none v) <|> cCheck prims' none b
  | .if_ c t e => cCheck prims none c <|> cCheck prims fnPrims t <|> cCheck prims fnPrims e
  | .let_ x v b => cCheck prims none v <|> cCheck ((x, cPrim prims v) :: prims) fnPrims b
  | .op _ a b => cCheck prims none a <|> cCheck prims none b
  | .toInt a | .log a => cCheck prims none a
  | .call f as => cCheck prims none f <|> as.findSome? (cCheck prims none)
  | _ => none

mutual

partial def cEval (env : List (String × Val)) (f : NF) : CM (Sum Val (List Val)) := do
  ctick
  match f with
  | .int v => pure (.inl (.long v))
  | .dbl x => pure (.inl (.dbl x))
  | .bool b => pure (.inl (.bool b))
  | .kw n => pure (.inl (.kw n))
  | .nil => pure (.inl .nil)
  | .sym x => match env.lookup x with
    | some v => pure (.inl v)
    | none => throw (.unsupported s!"unbound {x}")
  | .op o a b =>
    let va ← cVal env a
    let vb ← cVal env b
    pure (.inl (← cArith o va vb))
  | .toInt a => pure (.inl (← cIntCast (← cVal env a)))
  | .if_ c t e => if (← cVal env c).truthy then cEval env t else cEval env e
  | .let_ x v b => cEval ((x, ← cVal env v) :: env) b
  | .loop bs body =>
    let mut e := env
    for (x, v) in bs do e := (x, ← cVal e v) :: e
    let names := bs.map (·.1)
    let mut cur := (names.map fun n => (e.lookup n).getD .nil)
    let mut seen : List (List String × Nat) := []
    for _ in [0:loopFuel] do
      let key := cur.map fun v => v.show ++ (match v with | .dbl f => toString f.toBits | _ => "")
      let eff := (← get).effects
      match seen.find? (·.1 == key) with
      | some _ => throw .hang
      | none => seen := (key, eff) :: seen
      match ← cEval ((names.zip cur).reverse ++ env) body with
      | .inl v => return .inl v
      | .inr args => cur := args
    throw .fuel
  | .recur args =>
    let mut vs : List Val := []
    for a in args do vs := vs ++ [← cVal env a]
    pure (.inr vs)
  | .fn_ ps b =>
    let s ← get
    set { s with closures := s.closures.push { params := ps, body := b, env } }
    pure (.inl (.fn s.closures.size))
  | .call fe args =>
    let fv ← cVal env fe
    let mut vs : List Val := []
    for a in args do vs := vs ++ [← cVal env a]
    match fv with
    | .fn k => pure (.inl (← cInvoke k vs))
    | o => throw (.threw s!"ClassCastException: {o.show} cannot be cast to IFn")
  | .log a =>
    let v ← cVal env a
    modify fun s => { s with out := s.out ++ [v.show], effects := s.effects + 1 }
    pure (.inl v)

partial def cVal (env : List (String × Val)) (f : NF) : CM Val := do
  match ← cEval env f with
  | .inl v => pure v
  | .inr _ => throw (.unsupported "recur in value position")

partial def cInvoke (k : Nat) (args : List Val) : CM Val := do
  let some c := (← get).closures[k]? | throw (.unsupported "closure")
  if c.params.length != args.length then throw (.threw s!"ArityException: Wrong number of args ({args.length})")
  let mut cur := args
  let mut seen : List (List String) := []
  for _ in [0:loopFuel] do
    let key := cur.map fun v => v.show ++ (match v with | .dbl f => toString f.toBits | _ => "")
    if seen.contains key then throw .hang
    seen := key :: seen
    let mut env := c.env
    for ((x, t), a) in c.params.zip cur do env := (x, ← cParamCast t a) :: env
    match ← cEval env c.body with
    | .inl v => return v
    | .inr vs => cur := vs
  throw .fuel

end

inductive COut where
  | value (v : Val) (out : List String)
  | threw (m : String) (out : List String)
  | compileError (m : String)
  | hang (out : List String)
  | fuel
  | unsupported (m : String)
  deriving Inhabited

def COut.show : COut → String
  | .value v o => v.show ++ (if o.isEmpty then "" else s!" printing {o}")
  | .threw m o => s!"throws ({m})" ++ (if o.isEmpty then "" else s!" after printing {o}")
  | .compileError m => s!"compile error ({m})"
  | .hang o => "never ends" ++ (if o.isEmpty then "" else s!" (printing {o})")
  | .fuel => "out of fuel"
  | .unsupported m => s!"unsupported ({m})"

def runClojure (f : NF) : COut :=
  if let some m := cCheck [] none f then .compileError m else
  match (cVal [] f).run {} with
  | .ok v s => .value v s.out
  | .error (.threw m) s => .threw m s.out
  | .error .hang s => .hang s.out
  | .error .fuel _ => .fuel
  | .error (.unsupported m) _ => .unsupported m

/-- Do the outcomes agree? `none`: not comparable (a model bound or gap). -/
def agreeCJ (c : COut) (j : JOut) : Option Bool :=
  match c, j with
  | .fuel, _ | .unsupported _, _ | _, .fuel | _, .unsupported _ => none
  | .value a o, .value b p => some (a.same b && o == p)
  | .threw _ o, .threw _ p => some (o == p)
  | .compileError _, .compileError _ => some true
  | .hang o, .hang p => some (o == p)
  | _, _ => some false

/-- Do two jank runs (two optimization levels) agree? -/
def agreeJJ (a b : JOut) : Option Bool :=
  match a, b with
  | .fuel, _ | .unsupported _, _ | _, .fuel | _, .unsupported _ => none
  | .value x o, .value y p => some (x.same y && o == p)
  | .threw _ o, .threw _ p => some (o == p)
  | .compileError _, .compileError _ => some true
  | .hang o, .hang p => some (o == p)
  | .trap _ o, .trap _ p => some (o == p)
  | _, _ => some false

end Jank.R3.Codegen
