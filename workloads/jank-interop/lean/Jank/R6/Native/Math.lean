import Jank.R6.Native.Types

/-!
# core/math.hpp's templates on native and boxed operands, and Clojure 1.12's Numbers

**jank** (include/cpp/jank/runtime/core/math.hpp at 94d32623). Each binary operation has four
templates, chosen by `detail::primitive_number<T>` (`std::is_integral_v<T> ||
std::is_floating_point_v<T>`, 28-29, so `bool` and `char` count): both objects (71-112 for `add`),
a primitive left (114-141), a primitive right (143-170), both primitive (172-178). An object
operand is visited (`visit_number_like`, visit.hpp 463-497): a small integer's `data` is `i32`, an
integer's `i64`, a real's `f64`, a ratio's `ratio_data` (boost `cpp_int`s, exact against integral
operands: ratio.hpp 249-275), and anything else throws `std::runtime_error` "not a number". The
operation on two `data`/primitive values is C++'s built-in operator (usual arithmetic conversions).
`lt` 522-628, `lte` 630-736, `min` 738-863 (`std::min` over `std::common_type_t` of the two
primitives, 856-863), `max` 865-990, `add` 68-178, `sub` 182-292, `div` 296-406, `mul` 408-518.
A native result is boxed by `convert<T>::into_object` (convert/builtin.hpp 221-226:
`make_box(static_cast<i64>(o))`); the templates box with `make_box(T)` (make_box.hpp 80-101).

**Clojure** (clojure-ref/src/jvm/clojure/lang/Numbers.java): `lt`/`lte` by category (long, double,
ratio), `min`/`max` 4044-4228 (`x < y ? x : y`, `x > y ? x : y`, a NaN operand wins), `add`,
`minus`, `multiply` (long overflow throws "integer overflow"), `divide` (a ratio, or a long when
exact; divide by zero throws), and `RT.intCast`, `RT.floatCast`, `Murmur3.hashLong` for the sources.
-/

namespace Jank.R6.Native

/-! ## jank's side -/

/-- An object as `visit_number_like` sees it. -/
inductive Obj where
  /-- small_integer (`data` is `int`), integer (`data` is `long long`), real (`data` is `double`). -/
  | num (d : NV)
  /-- A ratio (exact against integers). -/
  | ratio (n d : Int)
  | boolean (b : Bool)
  | character (c : Int)
  deriving Inhabited

/-- `make_box(T)` (make_box.hpp): `bool` → boolean, `char` → character, floating → real, integral →
a small integer when `min_small_integer <= i && i <= max_small_integer` holds in C++ (an `i32`
compared with `T`: for an unsigned `T` of rank ≥ int, `INT32_MIN` converts to a huge unsigned
value, the test fails and the value becomes an `integer` holding `static_cast<i64>(i)`). -/
def makeBox (n : NV) : Obj :=
  match n with
  | .i .bool v => .boolean (v != 0)
  | .i .char v => .character v
  | .i _ v =>
    if cppLe (.i .int (-2147483648)) n && cppLe n (.i .int 2147483647) then .num (.i .int v)
    else .num (.i .llong (wrapTo .llong v))
  | .f _ x => .num (.f .double x)

/-- `convert<T>::into_object` (convert/builtin.hpp 155-226, 270-276): integral → `make_box(
static_cast<i64>(o))`, bool/char/floating → `make_box`. -/
def intoObject (n : NV) : Obj :=
  match n with
  | .i t v => if t.isNonNumber then makeBox n else makeBox (.i .llong (wrapTo .llong v))
  | _ => makeBox n

inductive Opd where
  | prim (n : NV)
  | obj (o : Obj)
  deriving Inhabited

/-- What a jank template returns. -/
inductive JR where
  | prim (n : NV)
  | obj (o : Obj)
  /-- `std::runtime_error` (not an object: `thrown?` and `(catch Exception …)` miss it, V7's class). -/
  | threwNative (m : String)
  /-- An object (a string), like `inc`'s "Overflow on increment.". -/
  | threwObj (m : String)
  | ub (m : String)
  deriving Inhabited

inductive Op where
  | lt | lte | gt | gte | min | max | add | sub | mul | div
  deriving Repr, BEq, DecidableEq, Inhabited

def Op.all : List Op := [.lt, .lte, .gt, .gte, .min, .max, .add, .sub, .mul, .div]

def Op.sym : Op → String
  | .lt => "<" | .lte => "<=" | .gt => ">" | .gte => ">=" | .min => "min" | .max => "max"
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/"

/-- The template a core.jank `:inline` reaches (core.jank 1372-1424, 1552-1633): `>` is `lt` with
the operands swapped, `>=` is `lte` swapped. -/
def Op.tmpl : Op → Op
  | .gt => .lt | .gte => .lte | o => o

def Op.swaps : Op → Bool
  | .gt | .gte => true
  | _ => false

/-- Switches: each one a change to jank (the diffs written this round, by this area and by the
overflow area N), so that every disagreement is attributed to a cause. `Sw.mine` is exactly
fixes/LG1.diff: `lg1Widen` and `minmax`. -/
structure Sw where
  /-- R33a.diff + R33b.diff: a `bool` operand is not a primitive number, and the type error is an
  object. -/
  rejectBool : Bool := false
  /-- No diff (P9, char part): a `char` operand throws. -/
  rejectChar : Bool := false
  /-- LG1.diff: `lt`, `lte`, `min`, `max`, `div` (and `inc`/`dec`) widen every primitive operand to
  `i64`/`f64` (`detail::widen`) before C++'s conversions. -/
  lg1Widen : Bool := false
  /-- LG1.diff: two primitives of different widened types: `min`/`max` compare the numbers and
  give the chosen operand, boxed in its own type (P4: `std::common_type`). -/
  minmax : Bool := false
  /-- LG2a.diff (agent N): `+ - *` on two integers compute the exact result in `i64` (overflow
  throws), whatever their C++ types (R25, D1, and the `u32` hash's 32-bit wrap). -/
  checkedOps : Bool := false
  /-- No diff (P8): `+ - * /` widen a `float` operand to `f64`. -/
  floatArith : Bool := false
  /-- No diff (P5): `max` keeps its second operand on a tie, as Numbers.max (`x > y ? x : y`). -/
  maxTie : Bool := false
  /-- No diff (P6): `hash` is a signed 32-bit int. -/
  hashSigned : Bool := false
  /-- No diff (P7): `float` rounds to binary32. -/
  floatF32 : Bool := false
  /-- R122a.diff: byte arrays hold `i8`. -/
  bytesSigned : Bool := false
  deriving Repr, Inhabited

def Sw.none : Sw := {}
def Sw.mine : Sw := { lg1Widen := true, minmax := true }
def Sw.every : Sw :=
  { rejectBool := true, rejectChar := true, lg1Widen := true, minmax := true, checkedOps := true,
    floatArith := true, maxTie := true, hashSigned := true, floatF32 := true, bytesSigned := true }

def Op.lg1 : Op → Bool
  | .lt | .lte | .gt | .gte | .min | .max | .div => true
  | _ => false

/-- An operand as the (switched) template body uses it: LG1.diff's `detail::widen` for the
comparison, min/max and division templates; bool/char rejected under their switches; a float
widened in arithmetic under `floatArith`. -/
def widenNV (sw : Sw) (op : Op) (n : NV) : Except String NV :=
  match n with
  | .i .bool _ => if sw.rejectBool then .error "Can't add a bool" else
      if sw.lg1Widen && op.lg1 then .ok (.i .llong (n.ival)) else .ok n
  | .i .char _ => if sw.rejectChar then .error "a char is not a number" else
      if sw.lg1Widen && op.lg1 then .ok (.i .llong (n.ival)) else .ok n
  | .i _ v => if sw.lg1Widen && op.lg1 then .ok (.i .llong (wrapTo .llong v)) else .ok n
  | .f t x => if (sw.lg1Widen && op.lg1) || (sw.floatArith && !op.lg1 && t == .float) then .ok (.f .double x) else .ok n

/-- The order of numbers, as Clojure has it (a long against a double compares `(double)x < y`). -/
def mathLt : NV → NV → Bool
  | .i _ x, .i _ y => decide (x < y)
  | .i _ x, .f _ y => Float.ofInt x < y
  | .f _ x, .i _ y => x < Float.ofInt y
  | .f _ x, .f _ y => x < y

/-- Exact comparison of a native value with a ratio (ratio.hpp 249-275: integral `l * den < num`
in `cpp_int`; floating against `to_real()`). -/
def ltRatio (n : NV) (p q : Int) : Bool :=
  match n with
  | .i _ v => decide (v * q < p)
  | .f _ x => x < Float.ofInt p / Float.ofInt q

def ratioLt (p q : Int) (n : NV) : Bool :=
  match n with
  | .i _ v => decide (p < v * q)
  | .f _ x => Float.ofInt p / Float.ofInt q < x

def leRatio (n : NV) (p q : Int) : Bool :=
  match n with
  | .i _ v => decide (v * q ≤ p)
  | .f _ x => x ≤ Float.ofInt p / Float.ofInt q

def ratioLe (p q : Int) (n : NV) : Bool :=
  match n with
  | .i _ v => decide (p ≤ v * q)
  | .f _ x => Float.ofInt p / Float.ofInt q ≤ x

/-- An operand's value as a template body uses it: a primitive (switched as above) or an object's
`data`. -/
inductive DV where
  | n (v : NV)
  | r (p q : Int)
  deriving Inhabited

def dataOf (sw : Sw) (op : Op) : Opd → Except JR DV
  | .prim n => match widenNV sw op n with
      | .ok v => .ok (.n v) | .error m => .error (.threwObj m)
  | .obj (.num d) => .ok (.n d)
  | .obj (.ratio p q) => .ok (.r p q)
  | .obj (.boolean b) => .error (.threwNative s!"not a number: {b}")
  | .obj (.character _) => .error (.threwNative "not a number: a character")

def dvLt : DV → DV → Bool
  | .n a, .n b => cppLt a b
  | .n a, .r p q => ltRatio a p q
  | .r p q, .n b => ratioLt p q b
  | .r p q, .r p' q' => decide (p * q' < p' * q)

def dvLe : DV → DV → Bool
  | .n a, .n b => cppLe a b
  | .n a, .r p q => leRatio a p q
  | .r p q, .n b => ratioLe p q b
  | .r p q, .r p' q' => decide (p * q' ≤ p' * q)

def boxOf : Opd → Obj
  | .prim n => makeBox n
  | .obj o => o

def inI64' (v : Int) : Bool := -9223372036854775808 ≤ v && v ≤ 9223372036854775807

def isNaNDV : DV → Bool
  | .n (.f _ x) => x.isNaN
  | _ => false

/-- One math.hpp binary template on two operands. -/
def jankBin (sw : Sw) (op : Op) (l r : Opd) : JR :=
  match dataOf sw op l, dataOf sw op r with
  | .error e, _ => e
  | _, .error e => e
  | .ok dl, .ok dr =>
    let bothPrim := match l, r with | .prim _, .prim _ => true | _, _ => false
    match op with
    | .lt | .gt => .prim (.i .bool (if dvLt dl dr then 1 else 0))
    | .lte | .gte => .prim (.i .bool (if dvLe dl dr then 1 else 0))
    | .min | .max =>
      if bothPrim then
        match dl, dr with
        | .n a, .n b =>
          if sw.minmax && a.ty != b.ty then
            -- the fix: a NaN operand wins; else the chosen operand, boxed in its own type
            if isNaNDV dl then .obj (makeBox a) else if isNaNDV dr then .obj (makeBox b)
            else if op == .min then .obj (makeBox (if mathLt a b then a else b))
            else .obj (makeBox (if mathLt b a then a else b))
          else
            -- `using C = std::common_type_t<…>; return std::min(static_cast<C>(l), static_cast<C>(r));`
            let c := commonType a.ty b.ty
            let cv := fun (x : NV) => match x.conv c with | .ok v => v | .ub _ => x
            .prim (if op == .min then stdMin (cv a) (cv b) else stdMax (cv a) (cv b))
        | _, _ => .ub "unreachable"
      else
        -- mixed or object branches keep the operand: min `l < r ? l : r`, max `l < r ? r : l`
        let lo := boxOf l
        let ro := boxOf r
        let lo := match l, dl with | .prim _, .n v => makeBox v | _, _ => lo
        let ro := match r, dr with | .prim _, .n v => makeBox v | _, _ => ro
        if op == .min then .obj (if dvLt dl dr then lo else ro)
        else if sw.maxTie then .obj (if dvLt dr dl then lo else ro)
        else .obj (if dvLt dl dr then ro else lo)
    | .add | .sub | .mul | .div =>
      let bop : BinOp := match op with
        | .add => .add | .sub => .sub | .mul => .mul | _ => .div
      match dl, dr with
      | .n (.i ta x), .n (.i tb y) =>
        if sw.checkedOps && op != .div && ta != .bool && tb != .bool then
          -- LG2a's checked_add/sub/mul: the exact result in i64, or "integer overflow"
          let r := match op with | .add => x + y | .sub => x - y | _ => x * y
          if inI64' r then (if bothPrim then .prim (.i .llong r) else .obj (makeBox (.i .llong r)))
          else .threwObj "integer overflow"
        else
        match cppArith bop (.i ta x) (.i tb y) with
        | .ok v => if bothPrim then .prim v else .obj (makeBox v)
        | .ub m => .ub m
      | .n a, .n b =>
        match cppArith bop a b with
        | .ok v => if bothPrim then .prim v else .obj (makeBox v)
        | .ub m => .ub m
      | _, _ => .ub "ratio arithmetic is not part of the walk"

/-- A two-operand call as core.jank's `:inline` expands it (`(> a b)` is `(lt b a)`). -/
def jankInline (sw : Sw) (op : Op) (a b : Opd) : JR :=
  if op.swaps then jankBin sw op.tmpl b a else jankBin sw op.tmpl a b

/-- The same call through a fn value (`(apply op [a b])`, a `defn` wrapper): the arguments are
boxed (`convert<T>::into_object`), and the fn's body runs the template on two objects. -/
def jankFnValue (sw : Sw) (op : Op) (a b : Opd) : JR :=
  let bx : Opd → Opd := fun o => match o with
    | .prim n => .obj (intoObject n)
    | o => o
  jankInline sw op (bx a) (bx b)

/-! ## Clojure's side -/

/-- A Clojure value as Numbers sees it: Long/Integer/Short/Byte (long category), Double/Float
(a Float as the double it widens to; `float?` marks one), Ratio, and non-numbers. -/
inductive CV where
  | long (v : Int)
  | dbl (x : Float) (isFloat : Bool := false)
  | ratio (n d : Int)
  | bool (b : Bool)
  | char (c : Int)
  deriving Inhabited

inductive CR where
  | val (v : CV)
  | threw (m : String)
  /-- A result jank documents as its own (D2: integer `/` truncates; LG2's overflow), so any jank
  answer is not counted against this area. -/
  | accepted
  deriving Inhabited

def ratioNorm (n d : Int) : CV :=
  let g := (Int.gcd n d : Int)
  let s : Int := if d < 0 then -1 else 1
  let n' := s * n / g
  let d' := s * d / g
  if d' == 1 then .long n' else .ratio n' d'

def CV.toF : CV → Float
  | .long v => Float.ofInt v
  | .dbl x _ => x
  | .ratio n d => Float.ofInt n / Float.ofInt d
  | _ => 0.0

/-- Numbers.lt by category: two longs exactly; a double makes it double; ratios exactly. -/
def cLt : CV → CV → Bool
  | .long a, .long b => decide (a < b)
  | .ratio p q, .long b => decide (p < b * q)
  | .long a, .ratio p q => decide (a * q < p)
  | .ratio p q, .ratio p' q' => decide (p * q' < p' * q)
  | a, b => a.toF < b.toF

def cLe : CV → CV → Bool
  | .long a, .long b => decide (a ≤ b)
  | .ratio p q, .long b => decide (p ≤ b * q)
  | .long a, .ratio p q => decide (a * q ≤ p)
  | .ratio p q, .ratio p' q' => decide (p * q' ≤ p' * q)
  | a, b => a.toF ≤ b.toF

def CV.isNum : CV → Bool
  | .bool _ | .char _ => false
  | _ => true

def CV.isNaN : CV → Bool
  | .dbl x _ => x.isNaN
  | _ => false

def inI64 (v : Int) : Bool := -9223372036854775808 ≤ v && v ≤ 9223372036854775807

/-- Clojure 1.12 on two values (`ref` = true: D2's truncating integer `/` and LG2's wrapping long
overflow counted as jank's documented own behavior, the reference this area measures against). -/
def cljBin (ref : Bool) (op : Op) (a b : CV) (objDiv : Bool := false) : CR :=
  if !a.isNum || !b.isNum then .threw "ClassCastException"
  else match op with
  | .lt => .val (.bool (cLt a b))
  | .lte => .val (.bool (cLe a b))
  | .gt => .val (.bool (cLt b a))
  | .gte => .val (.bool (cLe b a))
  | .min => if a.isNaN then .val a else if b.isNaN then .val b
      else .val (if cLt a b then a else b)
  | .max => if a.isNaN then .val a else if b.isNaN then .val b
      else .val (if cLt b a then a else b)
  | .add | .sub | .mul | .div =>
    match a, b with
    | .long x, .long y =>
      match op with
      | .div =>
        if y == 0 then (if ref then .accepted else .threw "ArithmeticException: Divide by zero")
        else if ref then .val (.long (wrapTo .llong (x.tdiv y)))
        else if x % y == 0 && inI64 (x / y) then .val (.long (x / y)) else .val (ratioNorm x y)
      | _ =>
        let r := match op with | .add => x + y | .sub => x - y | _ => x * y
        if inI64 r then .val (.long r)
        else if ref then .accepted else .threw "ArithmeticException: integer overflow"
    | .ratio _ _, _ | _, .ratio _ _ => .accepted
    | _, _ =>
      let x := a.toF
      let y := b.toF
      -- Numbers.divide(Object, Object) throws on a zero divisor of any type; the primitive
      -- overloads (`divide(double, long)`, chosen when both static types are primitive) do not
      if op == .div && y == 0.0 && (objDiv || ref) then
        (if ref then .accepted else .threw "ArithmeticException: Divide by zero")
      else .val (.dbl (match op with | .add => x + y | .sub => x - y | .mul => x * y | _ => x / y))

/-! ## Comparing outcomes -/

/-- What a jank result is, as a Clojure program sees it (a native result is boxed by
`convert<T>::into_object`). -/
def JR.seen : JR → CR
  | .prim n => .val (match intoObject n with
      | .num (.i _ v) => .long v | .num (.f _ x) => .dbl x | .ratio p q => .ratio p q
      | .boolean b => .bool b | .character c => .char c)
  | .obj o => .val (match o with
      | .num (.i _ v) => .long v | .num (.f _ x) => .dbl x | .ratio p q => .ratio p q
      | .boolean b => .bool b | .character c => .char c)
  | .threwNative m => .threw m
  | .threwObj m => .threw m
  | .ub m => .threw s!"undefined behavior: {m}"

def CV.same : CV → CV → Bool
  | .long a, .long b => a == b
  | .dbl a _, .dbl b _ => a.toBits == b.toBits || (a.isNaN && b.isNaN)
  | .ratio a b, .ratio c d => a == c && b == d
  | .bool a, .bool b => a == b
  | .char a, .char b => a == b
  | _, _ => false

/-- Agreement: equal values in the same category, or both throw (the kind of exception is a
separate question, V7's), or Clojure's result is one jank documents as its own. -/
def agrees (j c : CR) : Bool :=
  match j, c with
  | _, .accepted => true
  | .val a, .val b => a.same b
  | .threw m, .threw _ => !m.startsWith "undefined"
  | _, _ => false

def CV.show : CV → String
  | .long v => toString v
  | .dbl x f => if f then s!"{showF x} (a Float)" else showF x
  | .ratio n d => s!"{n}/{d}"
  | .bool b => toString b
  | .char c => s!"char {c}"

def CR.show : CR → String
  | .val v => v.show
  | .threw m => s!"throws {m}"
  | .accepted => "(documented)"

/-! ## Murmur3 (jank hash.cpp 8-114 and Clojure Murmur3.java: the same `hashLong`) -/

def rotl32 (x : UInt32) (r : UInt32) : UInt32 := (x <<< r) ||| (x >>> (32 - r))
def mixK1 (k : UInt32) : UInt32 := rotl32 (k * 0xcc9e2d51) 15 * 0x1b873593
def mixH1 (h k : UInt32) : UInt32 := rotl32 (h ^^^ k) 13 * 5 + 0xe6546b64
def fmix (h len : UInt32) : UInt32 :=
  let h := h ^^^ len
  let h := h ^^^ (h >>> 16)
  let h := h * 0x85ebca6b
  let h := h ^^^ (h >>> 13)
  let h := h * 0xc2b2ae35
  h ^^^ (h >>> 16)

/-- `hash::integer(u64)` (hash.cpp 87-104) = `Murmur3.hashLong` (Murmur3.java). -/
def hashLong (v : Int) : UInt32 :=
  if v == 0 then 0 else
  let u := (BitVec.ofInt 64 v).toNat
  let lo := UInt32.ofNat (u % 2 ^ 32)
  let hi := UInt32.ofNat (u / 2 ^ 32)
  fmix (mixH1 (mixH1 0 (mixK1 lo)) (mixK1 hi)) 8

/-! ## Sources: where a native number comes from in a plain Clojure program -/

inductive Src where
  /-- An integer literal (`int` when it fits 32 bits, else `long`), or a let-bound one. -/
  | lit (v : Int)
  | dlit (x : Float)
  /-- A long through a fn parameter (an object). -/
  | param (v : Int)
  | dparam (x : Float)
  | ratioP (p q : Int)
  /-- `(count [..n..])`: `sequence_length` returns `usize` (seq.hpp 132). -/
  | count (n : Nat)
  /-- `(alength (long-array n))`: `usize` (array.hpp 89-100). -/
  | alength (n : Nat)
  /-- `(hash v)`: `to_hash` returns `uhash` = `u32` (core.hpp 87). -/
  | hash (v : Int)
  /-- `(int v)`: `to_int` returns `i64` (math.hpp 1411). -/
  | int_ (v : Int)
  /-- `(bit-and v -1)`: `i64` (math.hpp 1392). -/
  | bitAnd (v : Int)
  /-- `(aget (byte-array [v]) 0)`: the inline `byte_array` returns `u8_array_ref` and `aget` a `u8&`. -/
  | byteA (v : Int)
  | shortA (v : Int)
  | intA (v : Int)
  /-- `(aget (float-array [x]) 0)`: a `float&`. -/
  | floatA (x : Float)
  /-- `(float x)`: `to_real` returns `f64` (math.hpp 1440). -/
  | float_ (x : Float)
  /-- An inlined predicate, `(nil? x)`, `(zero? x)`, `(empty? x)`…: `bool`. -/
  | pred (b : Bool)
  /-- `(aget (char-array "a") 0)`: a `char&`. -/
  | charA (c : Nat)
  deriving Inhabited

/-- A walk literal as Clojure source (the walk's doubles have one decimal). -/
def fmtF (x : Float) : String :=
  let n := truncF (x * 10.0)
  let a := n.natAbs
  (if n < 0 then "-" else "") ++ s!"{a / 10}.{a % 10}"

def Src.code : Src → String
  | .lit v => toString v
  | .dlit x => fmtF x
  | .param _ => "x"
  | .dparam _ => "x"
  | .ratioP _ _ => "x"
  | .count n => "(count [" ++ " ".intercalate ((List.range n).map (fun _ => "0")) ++ "])"
  | .alength n => s!"(alength (long-array {n}))"
  | .hash v => s!"(hash {v})"
  | .int_ v => s!"(int {v})"
  | .bitAnd v => s!"(bit-and {v} -1)"
  | .byteA v => s!"(aget (byte-array [{v}]) 0)"
  | .shortA v => s!"(aget (short-array [{v}]) 0)"
  | .intA v => s!"(aget (int-array [{v}]) 0)"
  | .floatA x => s!"(aget (float-array [{fmtF x}]) 0)"
  | .float_ x => s!"(float {fmtF x})"
  | .pred b => if b then "(nil? nil)" else "(nil? 0)"
  | .charA c => s!"(aget (char-array \"{Char.ofNat c}\") 0)"

/-- The value a fn parameter is called with (when the source is one). -/
def Src.paramArg : Src → Option String
  | .param v => some (toString v)
  | .dparam x => some (fmtF x)
  | .ratioP p q => some s!"{p}/{q}"
  | _ => none

def Src.kind : Src → String
  | .lit _ => "literal" | .dlit _ => "double literal" | .param _ => "long param"
  | .dparam _ => "double param" | .ratioP _ _ => "ratio param" | .count _ => "count"
  | .alength _ => "alength" | .hash _ => "hash" | .int_ _ => "int" | .bitAnd _ => "bit-and"
  | .byteA _ => "byte aget" | .shortA _ => "short aget" | .intA _ => "int aget"
  | .floatA _ => "float aget" | .float_ _ => "float" | .pred _ => "predicate" | .charA _ => "char aget"

/-- The operand jank's inlined template receives. -/
def Src.jank (sw : Sw) : Src → Opd
  | .lit v => .prim (.i (if -2147483648 ≤ v && v ≤ 2147483647 then .int else .long) v)
  | .dlit x => .prim (.f .double x)
  | .param v => .obj (intoObject (.i .llong v))
  | .dparam x => .obj (.num (.f .double x))
  | .ratioP p q => .obj (.ratio p q)
  | .count n => .prim (.i .ullong n)
  | .alength n => .prim (.i .ullong n)
  | .hash v =>
    let h := (hashLong v).toNat
    if sw.hashSigned then .prim (.i .int (wrapTo .int h)) else .prim (.i .uint h)
  | .int_ v => .prim (.i .llong v)
  | .bitAnd v => .prim (.i .llong v)
  | .byteA v => if sw.bytesSigned then .prim (.i .schar (wrapTo .schar v)) else .prim (.i .uchar (wrapTo .uchar v))
  | .shortA v => .prim (.i .short (wrapTo .short v))
  | .intA v => .prim (.i .int (wrapTo .int v))
  | .floatA x => .prim (.f .float (toF32 x))
  | .float_ x => .prim (.f .double (if sw.floatF32 then toF32 x else x))
  | .pred b => .prim (.i .bool (if b then 1 else 0))
  | .charA c => .prim (.i .char c)

/-- The value Clojure 1.12 has. -/
def Src.clj : Src → CV
  | .lit v | .param v | .int_ v | .bitAnd v => .long v
  | .dlit x | .dparam x => .dbl x
  | .ratioP p q => ratioNorm p q
  | .count n | .alength n => .long n
  | .hash v => .long (wrapTo .int (hashLong v).toNat)
  | .byteA v => .long (wrapTo .schar v)
  | .shortA v => .long (wrapTo .short v)
  | .intA v => .long (wrapTo .int v)
  | .floatA x | .float_ x => .dbl (toF32 x) true
  | .pred b => .bool b
  | .charA c => .char c

/-- The form of a two-operand call, wrapped in a fn when a source is a parameter. -/
def formOf (op : Op) (a b : Src) (fnValue : Bool) : String :=
  let call := if fnValue then s!"(apply {op.sym} [{a.code} {b.code}])" else s!"({op.sym} {a.code} {b.code})"
  match a.paramArg, b.paramArg with
  | some x, some y => s!"((fn [x] {call}) {x} {y})"
  | some x, none => s!"((fn [x] {call}) {x})"
  | none, some y => s!"((fn [x] {call}) {y})"
  | none, none => call

/-- The walk's sources: every kind, a few values each (negative, zero, small, past 32 bits). -/
def sources : List Src :=
  ([-2, -1, 0, 1, 2, 2147483647, 4294967296].map Src.lit) ++
  ([-1.5, 0.5, 1.0, 2.5].map Src.dlit) ++
  ([-2, -1, 0, 3, 2147483647].map Src.param) ++
  ([-0.5, 1.0].map Src.dparam) ++
  [Src.ratioP (-1) 2, .ratioP 1 2] ++
  ([0, 1, 3].map Src.count) ++ ([0, 2].map Src.alength) ++
  ([0, 1, 2, 3].map Src.hash) ++
  ([-1, 2].map Src.int_) ++ ([-1, 5].map Src.bitAnd) ++
  ([-1, 1, 200].map Src.byteA) ++ [Src.shortA (-1), .intA (-1)] ++
  ([0.1, -1.0].map Src.floatA) ++ ([0.1, 2.0].map Src.float_) ++
  [Src.pred true, .pred false, .charA 97]

/-- Two parameters would both be named `x`; the walk pairs a parameter only with a non-parameter
(the both-parameter case is the fn-value path's object × object). -/
def pairOk (a b : Src) : Bool := !(a.paramArg.isSome && b.paramArg.isSome)

/-- One case of the walk. -/
structure Case where
  op : Op
  a : Src
  b : Src
  fnValue : Bool

def Case.jank (sw : Sw) (c : Case) : JR :=
  if c.fnValue then jankFnValue sw c.op (c.a.jank sw) (c.b.jank sw)
  else jankInline sw c.op (c.a.jank sw) (c.b.jank sw)

/-- Whether Clojure's compiler sees an Object operand (a fn parameter, or `apply`'s arguments),
which picks `Numbers.divide(Object, Object)`. -/
def Case.objStatic (c : Case) : Bool :=
  -- `divide(double, Object)` converts the divisor and divides doubles (no zero check)
  let aPrimDouble := match c.a with | .dlit _ | .floatA _ | .float_ _ => true | _ => false
  c.fnValue || c.a.paramArg.isSome || (c.b.paramArg.isSome && !aPrimDouble)

def Case.clj (ref : Bool) (c : Case) : CR := cljBin ref c.op c.a.clj c.b.clj c.objStatic

def Case.form (c : Case) : String := formOf c.op c.a c.b c.fnValue

def Case.deviates (sw : Sw) (c : Case) : Bool := !agrees (c.jank sw).seen (c.clj true)

def allCases : List Case := Id.run do
  let mut out := #[]
  for fv in [false, true] do
    for op in Op.all do
      for a in sources do
        for b in sources do
          if pairOk a b then out := out.push { op, a, b, fnValue := fv }
  return out.toList

end Jank.R6.Native
