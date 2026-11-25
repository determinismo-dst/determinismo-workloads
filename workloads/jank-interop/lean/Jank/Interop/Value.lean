import Jank.Interop.Facts
import Jank.Analyzer.Expr

/-!
# C++ values, the builtin operators' meaning, and Clojure values

The meaning of the code jank emits: values of the `Cxx` types and what the builtin operators and
conversions do to them, by the C++ standard ([conv], [expr]), with jank's documented math
(book/src/differences-from-clojure.md): "Signed integer overflow is well defined" (two's
complement wrapping, `-fwrapv`), "Unsigned integer overflow is well defined", "Division by integer
`0` is undefined behavior". Other undefined behavior is reported as `UB`.

Beside them, the Clojure values a jank value means, for the spec.
-/

namespace Jank.Interop

open Jank.Analyzer (Obj)

/-- A runtime C++ value. Integers (and characters) keep their builtin kind and mathematical value
(always within the kind's range); `float` values are kept as the `Float` their `Float32` widens
to; `long double` values are exact dyadics `m * 2^e` with `|m| < 2^64` (x87 extended). -/
inductive CVal where
  | int (k : Builtin) (v : Int)
  | flt (k : Builtin) (x : Float)
  | ldbl (m : Int) (e : Int)
  | bool (b : Bool)
  | enumv (name : String) (v : Int)
  | nullptr
  | ptr (pointee : CType) (addr : Nat)
  /-- `char const *` / `char *`: the string it points to (`none`: null). -/
  | cstr (s : Option String)
  /-- `std::string`. -/
  | str (s : String)
  /-- A jank object (`object_ref` or a typed `oref`). -/
  | obj (o : Obj)
  | vec (xs : List CVal)
  | record (name : String) (fields : List CVal)
  | void
  deriving Repr, BEq, Inhabited

/-- How an evaluation stopped early. -/
inductive Fault where
  /-- Undefined behavior in the emitted C++ (what happens is not defined). -/
  | ub (what : String)
  /-- A C++ exception thrown at run time (jank's `try_object` failures, `throw`). -/
  | thrown (what : String)
  /-- The C++ jank emitted does not compile (a JIT compile error). -/
  | illFormed (what : String)
  /-- The analyzer rejected the program (a jank diagnostic). -/
  | analyzeError (kind : String) (what : String)
  /-- Outside what this model covers. -/
  | unmodeled (what : String)
  deriving Repr, BEq, Inhabited

abbrev CRes := Except Fault

namespace Cxx

variable (p : Platform) (w : World)

/-- [conv.integral] (C++20: modular): the value of `v` converted to the integer kind `k`. -/
def wrapTo (k : Builtin) (v : Int) : Int :=
  if k == .bool then (if v == 0 then 0 else 1)
  else
    let m : Int := 2 ^ k.width
    let r := v % m
    if k.isSigned p && r ≥ 2 ^ (k.width - 1) then r - m else r

/-- `Float` of an integer, rounded to nearest (Lean's `Float.ofInt`). -/
def floatOfInt (v : Int) : Float := Float.ofInt v

def roundF32 (x : Float) : Float := x.toFloat32.toFloat

/-- The exact value of a finite `Float`, as a dyadic. -/
def floatToDyadic (x : Float) : Int × Int :=
  let bits : Nat := x.toBits.toNat
  let sign : Nat := bits / 2 ^ 63
  let expo : Nat := (bits / 2 ^ 52) % 2048
  let frac : Nat := bits % 2 ^ 52
  let (m, e) : Nat × Int :=
    if expo == 0 then (frac, -1074) else (frac + 2 ^ 52, (expo : Int) - 1075)
  ((if sign == 1 then -(m : Int) else m), e)

/-- A dyadic `m * 2^e` rounded to the nearest `Float`. -/
def dyadicToFloat (m e : Int) : Float :=
  if e ≥ 0 then Float.ofInt (m * 2 ^ e.toNat)
  else
    let k := (-e).toNat
    let mag := (m.natAbs * 5 ^ k)
    let f := Float.ofScientific mag true k
    if m < 0 then -f else f

/-- Truncation of a dyadic toward zero. -/
def dyadicTrunc (m e : Int) : Int :=
  if e ≥ 0 then m * 2 ^ e.toNat
  else
    let q := m.natAbs / 2 ^ (-e).toNat
    if m < 0 then -(q : Int) else q

/-- The arithmetic value of a numeric `CVal`: an exact integer or a float. -/
inductive Num where
  | i (v : Int)
  | f (x : Float)
  | d (m e : Int)
  deriving Repr, BEq, Inhabited

def toNum : CVal → Option Num
  | .int _ v => some (.i v)
  | .bool b => some (.i (if b then 1 else 0))
  | .enumv _ v => some (.i v)
  | .flt _ x => some (.f x)
  | .ldbl m e => some (.d m e)
  | _ => none

/-- The kind of a numeric value (an unscoped enum's is its underlying type). -/
def kindOf : CVal → Option Builtin
  | .int k _ => some k
  | .bool _ => some .bool
  | .flt k _ => some k
  | .ldbl .. => some .ldouble
  | .enumv n _ => some ((w.findEnum n).map (·.underlying) |>.getD .int)
  | _ => none

/-- A numeric value converted to the arithmetic kind `k` ([conv.integral], [conv.double],
[conv.fpint], [conv.bool]). A floating value out of the integer range is UB ([conv.fpint] p1). -/
def convertNum (k : Builtin) (n : Num) : CRes CVal :=
  if k == .bool then
    match n with
    | .i v => .ok (.bool (v != 0))
    | .f x => .ok (.bool (x != 0.0))
    | .d m _ => .ok (.bool (m != 0))
  else if k.isIntegerKind then
    match n with
    | .i v => .ok (.int k (wrapTo p k v))
    | .f x =>
      if x.isNaN || x.isInf then .error (.ub s!"{x} converted to {k.spelling}")
      else
        let (m, e) := floatToDyadic x
        let t := dyadicTrunc m e
        if k.fits p t then .ok (.int k t)
        else .error (.ub s!"{x} out of the range of {k.spelling}")
    | .d m e =>
      let t := dyadicTrunc m e
      if k.fits p t then .ok (.int k t) else .error (.ub s!"long double out of the range of {k.spelling}")
  else if k == .float then
    match n with
    | .i v => .ok (.flt .float (roundF32 (floatOfInt v)))
    | .f x => .ok (.flt .float (roundF32 x))
    | .d m e => .ok (.flt .float (roundF32 (dyadicToFloat m e)))
  else if k == .double then
    match n with
    | .i v => .ok (.flt .double (floatOfInt v))
    | .f x => .ok (.flt .double x)
    | .d m e => .ok (.flt .double (dyadicToFloat m e))
  else if k == .ldouble then
    match n with
    | .i v => .ok (.ldbl v 0)
    | .f x => let (m, e) := floatToDyadic x; .ok (.ldbl m e)
    | .d m e => .ok (.ldbl m e)
  else .error (.unmodeled s!"conversion to {k.spelling}")

/-- The value of `v` as the type `t` (a conversion the program performs, implicit or
`static_cast`). -/
def convertTo (t : CType) (v : CVal) : CRes CVal :=
  let d := (nonRef t).canonical.unqual
  match d, v with
  | .b k, _ =>
    if k.isArithmetic then
      match toNum v with
      | some n => convertNum p k n
      | none =>
        match v with
        | .ptr _ a => if k == .bool then .ok (.bool (a != 0)) else .error (.unmodeled "pointer to integer")
        | .cstr s => if k == .bool then .ok (.bool s.isSome) else .error (.unmodeled "pointer to integer")
        | .nullptr => if k == .bool then .ok (.bool false) else .error (.unmodeled "nullptr to integer")
        | _ => .error (.unmodeled s!"{reprStr v} to {k.spelling}")
    else if k == .nullptr then .ok .nullptr
    else if k == .void then .ok .void
    else .error (.unmodeled s!"to {k.spelling}")
  | .enum n, _ =>
    match toNum v with
    | some (.i x) => .ok (.enumv n (wrapTo p ((w.findEnum n).map (·.underlying) |>.getD .int) x))
    | _ => .error (.unmodeled "to an enum")
  | .ptr u, .nullptr => .ok (.ptr u 0)
  | .ptr u, .ptr _ a => .ok (.ptr u a)
  | .ptr _, .cstr s => .ok (.cstr s)
  | _, _ => .ok v

/-- The integer value of a numeric `CVal` in kind `k` after promotion/conversion. -/
def asInt? : CVal → Option Int
  | .int _ v => some v
  | .bool b => some (if b then 1 else 0)
  | .enumv _ v => some v
  | _ => none

/-- `a op b` on builtin operands, per [expr.add], [expr.mul], [expr.shift], [expr.rel],
[expr.eq], [expr.bit.and]... after the usual arithmetic conversions. Signed overflow wraps
(jank's documented behavior); integer division by zero, `INT_MIN / -1` and out-of-range shifts are
UB. `ta`, `tb` are the operands' static types. -/
def evalBinop (op : Op) (ta tb : CType) (a b : CVal) : CRes CVal := do
  let some ka := promote p w ta | .error (.unmodeled s!"operand of type {reprStr ta}")
  let some kb := promote p w tb | .error (.unmodeled s!"operand of type {reprStr tb}")
  let some na := toNum a | .error (.unmodeled "non-numeric operand")
  let some nb := toNum b | .error (.unmodeled "non-numeric operand")
  if op == .lessLess || op == .greaterGreater then
    let .int _ x ← convertNum p ka na | .error (.unmodeled "shift")
    let .int _ s ← convertNum p kb nb | .error (.unmodeled "shift")
    if s < 0 || s ≥ ka.width then .error (.ub s!"shift by {s} of a {ka.width}-bit value")
    else if op == .lessLess then .ok (.int ka (wrapTo p ka (x * 2 ^ s.toNat)))
    else .ok (.int ka (if x ≥ 0 then x / 2 ^ s.toNat else -((-x - 1) / 2 ^ s.toNat) - 1))
  else
    let k := usualArith p ka kb
    let x ← convertNum p k na
    let y ← convertNum p k nb
    match x, y with
    | .int _ i, .int _ j =>
      match op with
      | .plus => .ok (.int k (wrapTo p k (i + j)))
      | .minus => .ok (.int k (wrapTo p k (i - j)))
      | .star => .ok (.int k (wrapTo p k (i * j)))
      | .slash =>
        if j == 0 then .error (.ub "integer division by zero")
        else if !k.fits p (i.tdiv j) then .error (.ub s!"{i} / {j} overflows {k.spelling} (SIGFPE on x86-64)")
        else .ok (.int k (i.tdiv j))
      | .percent =>
        if j == 0 then .error (.ub "integer remainder by zero")
        else if !k.fits p (i.tdiv j) then .error (.ub s!"{i} % {j} overflows")
        else .ok (.int k (i.tmod j))
      | .less => .ok (.bool (decide (i < j)))
      | .lessEqual => .ok (.bool (decide (i ≤ j)))
      | .greater => .ok (.bool (decide (i > j)))
      | .greaterEqual => .ok (.bool (decide (i ≥ j)))
      | .equalEqual => .ok (.bool (i == j))
      | .exclaimEqual => .ok (.bool (i != j))
      | .amp => .ok (.int k (wrapTo p k (BitVec.ofInt 64 i &&& BitVec.ofInt 64 j).toInt))
      | .pipe => .ok (.int k (wrapTo p k (BitVec.ofInt 64 i ||| BitVec.ofInt 64 j).toInt))
      | .caret => .ok (.int k (wrapTo p k (BitVec.ofInt 64 i ^^^ BitVec.ofInt 64 j).toInt))
      | _ => .error (.unmodeled "operator")
    | .flt _ u, .flt _ v =>
      let r (z : Float) : CVal := .flt k (if k == .float then roundF32 z else z)
      match op with
      | .plus => .ok (r (u + v))
      | .minus => .ok (r (u - v))
      | .star => .ok (r (u * v))
      | .slash => .ok (r (u / v))
      | .less => .ok (.bool (u < v))
      | .lessEqual => .ok (.bool (u ≤ v))
      | .greater => .ok (.bool (u > v))
      | .greaterEqual => .ok (.bool (u ≥ v))
      | .equalEqual => .ok (.bool (u == v))
      | .exclaimEqual => .ok (.bool (u != v))
      | _ => .error (.unmodeled "floating operator")
    | _, _ => .error (.unmodeled "operands")

end Cxx

/-! ## Clojure values (the spec's side) -/

/-- A Clojure value, as clojure.lang sees it (1.12). `char` is a UTF-16 code unit. -/
inductive CljV where
  | nil
  | bool (b : Bool)
  | long (v : Int)
  | double (x : Float)
  | bigint (v : Int)
  | ratio (n d : Int)
  | char (c : Nat)
  | string (s : String)
  | keyword (s : String)
  | other (what : String)
  deriving Repr, BEq, Inhabited

def CljV.truthy : CljV → Bool
  | .nil => false
  | .bool b => b
  | _ => true

/-- `clojure.core/=` on the values this model draws (numbers of one category compare by value,
doubles by `==`, except that Clojure's `=` treats longs and doubles as different categories). -/
def CljV.eq : CljV → CljV → Bool
  | .long a, .long b => a == b
  | .long a, .bigint b | .bigint a, .long b | .bigint a, .bigint b => a == b
  | .double a, .double b => a == b
  | .ratio a b, .ratio c d => a == c && b == d
  | .nil, .nil => true
  | .bool a, .bool b => a == b
  | .char a, .char b => a == b
  | .string a, .string b => a == b
  | .keyword a, .keyword b => a == b
  | _, _ => false

/-- The bytes of a jank character's `data`. A lone byte `b ≥ 0x80` (which `character(char)`
makes, character.cpp) is represented in the `String` by the private-use scalar `U+F700 + b`. -/
def charDataBytes (s : String) : List UInt8 :=
  s.toList.flatMap fun c =>
    if 0xF780 ≤ c.toNat && c.toNat ≤ 0xF7FF then [UInt8.ofNat (c.toNat - 0xF700)]
    else (String.singleton c).toUTF8.toList

/-- The `data` string of `obj::character(char)` for a byte. -/
def charDataOfByte (b : Nat) : String :=
  if b < 0x80 then String.singleton (Char.ofNat b) else String.singleton (Char.ofNat (0xF700 + b))

/-- The Clojure value a jank object stands for. -/
def cljOfObj : Obj → CljV
  | .nil => .nil
  | .boolean b => .bool b
  | .smallInteger v => .long v.toInt
  | .integer v => .long v.toInt
  | .smallReal bits => .double (Float.ofBits bits)
  | .real bits => .double (Float.ofBits bits)
  | .bigInteger v => .bigint v
  | .ratio n d => .ratio n d
  | .character d =>
    match d.toList with
    | [c] => if 0xF780 ≤ c.toNat && c.toNat ≤ 0xF7FF then .other s!"invalid byte {c.toNat - 0xF700}" else .char c.toNat
    | _ => .other "multi-scalar character"
  | .persistentString s => .string s
  | .keyword ns n => .keyword (if ns.isEmpty then n else ns ++ "/" ++ n)
  | o => .other (reprStr o.type)

def showClj : CljV → String
  | .nil => "nil"
  | .bool b => toString b
  | .long v => toString v
  | .double x => if x.isNaN then "##NaN" else if x.isInf then (if x > 0 then "##Inf" else "##-Inf") else toString x
  | .bigint v => s!"{v}N"
  | .ratio n d => s!"{n}/{d}"
  | .char c => s!"\\{Char.ofNat c}"
  | .string s => s!"\"{s}\""
  | .keyword s => s!":{s}"
  | .other s => s!"#<{s}>"

def showObj (o : Obj) : String := showClj (cljOfObj o)

end Jank.Interop
