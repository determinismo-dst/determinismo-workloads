import Jank.Interop.Read

/-!
# The spec: what each interop program means

Kept apart from the replica. Sources, in order of authority:

1. jank's book at 7135b7708 (book/src/cpp-interop/*.md, differences-from-cpp.md: "Signed integer
   overflow is well defined and will wrap", `NULL` does not convert to a pointer, use
   `cpp/nullptr`): native values and trait conversions ("the jank
   compiler will detect if conversion is necessary and will implicitly handle conversions"),
   native types ("a value can be constructed by calling the type ... C++ initializer lists are
   not currently supported"), `cpp/cast` ("closely maps to C++ `static_cast`" plus trait
   conversions), opaque boxes ("ensure that unboxing uses the correct type"), the DSL ("adds the
   corresponding C++ qualification"); differences-from-clojure.md (signed and unsigned overflow
   well defined, integer division by 0 undefined).
2. The C++20 standard for the meaning of native code: implicit conversions ([conv]),
   `static_cast` ([expr.static.cast]), list-initialization and narrowing ([dcl.init.list]),
   simple type specifiers ([dcl.type.simple]).
3. Clojure 1.12 for values that are Clojure's: integer literals are longs, `+ - * inc dec` on
   longs are exact (overflow throws; jank documents wrapping, so an overflowing result is any
   value), a `loop` local holds whatever `recur` gives it (the compiler boxes a primitive local
   whose `recur` value does not match, "recur arg for primitive local"), only `nil` and `false`
   are falsy.
-/

namespace Jank.Interop.Spec

open Jank.Analyzer (Obj)

/-- What a program must do. -/
inductive Expect where
  /-- Evaluate to this value. -/
  | value (v : CljV)
  /-- Be rejected: a jank diagnostic, or a runtime exception. -/
  | reject
  /-- Anything (a documented undefined behavior or overflow). -/
  | anything
  deriving Repr, Inhabited

/-- What the replica predicts jank does. -/
inductive Outcome where
  | value (o : Obj)
  | native (v : CVal)
  | fault (f : Fault)
  deriving Repr, Inhabited

def Outcome.show : Outcome → String
  | .value o => showObj o
  | .native v => s!"native {reprStr v}"
  | .fault (.analyzeError k m) => s!"rejected ({k}: {m})"
  | .fault (.thrown m) => s!"throws ({m})"
  | .fault (.illFormed m) => s!"JIT compile error ({m})"
  | .fault (.ub m) => s!"undefined behavior ({m})"
  | .fault (.unmodeled m) => s!"outside the model ({m})"

def Expect.show : Expect → String
  | .value v => showClj v
  | .reject => "rejected"
  | .anything => "anything (documented)"

def sameValue (a b : CljV) : Bool :=
  match a, b with
  | .double x, .double y => x == y || (x.isNaN && y.isNaN)
  | _, _ => CljV.eq a b

/-- Does the outcome meet the expectation. A JIT compile error is never acceptable: jank's own
analysis accepted the program. An outcome outside the model is not judged. -/
def agrees (e : Expect) (o : Outcome) : Bool :=
  match e, o with
  | _, .fault (.unmodeled _) => true
  | .anything, .fault (.illFormed _) => false
  | .anything, _ => true
  | .reject, .fault (.analyzeError ..) | .reject, .fault (.thrown _) => true
  | .reject, _ => false
  | .value v, .value obj => sameValue v (cljOfObj obj)
  | .value _, _ => false

/-! ## Clojure arithmetic on the values drawn -/

def i64min : Int := -(2 ^ 63)
def i64max : Int := 2 ^ 63 - 1

/-- Clojure `+ - *` (Numbers.add/minus/multiply), `<`, `inc`, `dec` on longs and doubles. A long
overflow is jank's documented wrapping: anything. -/
def cljArith (op : String) (a b : CljV) : Expect :=
  let long (v : Int) : Expect := if i64min ≤ v ∧ v ≤ i64max then .value (.long v) else .anything
  match op, a, b with
  | "+", .long x, .long y => long (x + y)
  | "-", .long x, .long y => long (x - y)
  | "*", .long x, .long y => long (x * y)
  | "<", .long x, .long y => .value (.bool (decide (x < y)))
  | "+", .long x, .double y | "+", .double y, .long x => .value (.double (Float.ofInt x + y))
  | "-", .long x, .double y => .value (.double (Float.ofInt x - y))
  | "-", .double x, .long y => .value (.double (x - Float.ofInt y))
  | "*", .long x, .double y | "*", .double y, .long x => .value (.double (Float.ofInt x * y))
  | "<", .long x, .double y => .value (.bool (Float.ofInt x < y))
  | "<", .double x, .long y => .value (.bool (x < Float.ofInt y))
  | "+", .double x, .double y => .value (.double (x + y))
  | "-", .double x, .double y => .value (.double (x - y))
  | "*", .double x, .double y => .value (.double (x * y))
  | "<", .double x, .double y => .value (.bool (x < y))
  | "inc", .long x, _ => long (x + 1)
  | "dec", .long x, _ => long (x - 1)
  | "inc", .double x, _ => .value (.double (x + 1.0))
  | "dec", .double x, _ => .value (.double (x - 1.0))
  | _, _, _ => .reject

/-! ## Native parameters: the C++ value a jank value denotes, converted -/

/-- The C++ meaning of passing the Clojure value `v` to a parameter of type `param`, then
returning it to jank (the function returns its parameter): the value C++'s implicit conversion
gives, back as a Clojure value, without loss; or a rejection where neither C++ nor the trait
conversions give one. -/
def nativeParam (p : Platform) (w : World) (param : CType) (v : CljV) : Expect :=
  let t := (Cxx.nonRef param).canonical.unqual
  let backInt (k : Builtin) (x : Int) : Expect := .value (.long (Cxx.wrapTo p k x))
  match t, v with
  -- integral parameters
  | .b .char, .char c => if c < 128 then .value (.char c) else .reject
  | .b .char, .long x => if 0 ≤ x ∧ x < 128 then .value (.char x.toNat) else .anything
  | .b .char, .double _ => .anything
  | .b .bool, .bool b => .value (.bool b)
  -- a number or a string to `bool`, a boolean to a number: C++ converts, Clojure does not; the
  -- book says nothing: no claim
  | .b .bool, .long _ | .b .bool, .double _ | .b .bool, .string _ | .b .bool, .char _ => .anything
  | .b _, .bool _ => .anything
  -- a character to an integer parameter: its code (C++'s char→int, Clojure's `int` of a char);
  -- to a floating parameter: C++ converts, Clojure does not: no claim
  | .b k, .char c => if k.isIntegerKind then backInt k (c : Int) else if k.isFloating then .anything else .reject
  | .b k, .long x =>
    if k.isIntegerKind then backInt k x
    else if k == .float then .value (.double (Cxx.roundF32 (Float.ofInt x)))
    else if k == .double then .value (.double (Float.ofInt x))
    else .reject
  | .b k, .double x =>
    if k.isIntegerKind then
      if x.isNaN || x.isInf then .anything
      else
        let (m, e) := Cxx.floatToDyadic x
        let tr := Cxx.dyadicTrunc m e
        if k.fits p tr then .value (.long tr) else .anything
    else if k == .float then .value (.double (Cxx.roundF32 x))
    else if k == .double then .value (.double x)
    else .reject
  -- C strings: a string, or nil for a null pointer (convert<char const *>::into_object maps a null
  -- pointer to nil)
  | .ptr u, .string s =>
    if u.canonical == (CType.cv true false (.b .char)) then .value (.string s) else .reject
  | .ptr u, .nil =>
    if u.canonical == (CType.cv true false (.b .char)) then .value .nil else .reject
  | .record "std::basic_string<char>", .string s => .value (.string s)
  | _, _ => .reject

/-! ## `if` on a native value -/

/-- The truthiness of a native value: the jank value it converts to (`into_object`), else its
C++ boolean conversion when it has no jank value. -/
def nativeTruthy (o : Option CljV) (cxxBool : Option Bool) : Expect :=
  match o with
  | some v => .value (.keyword (if v.truthy then "t" else "f"))
  | none => match cxxBool with
    | some b => .value (.keyword (if b then "t" else "f"))
    | none => .reject

/-! ## The DSL's integer modifiers ([dcl.type.simple], Table 17) -/

/-- A type built from simple type specifiers: the specifier multiset and the base. The valid
combinations and the type they name; `none`: not a C++ type. -/
def specifierType (base : String) (signedN unsignedN shortN longN : Nat) : Option Builtin :=
  if signedN + unsignedN > 1 || shortN > 1 || longN > 2 || (shortN > 0 && longN > 0) then none
  else
    let uns := unsignedN == 1
    let sgn := signedN == 1
    match base with
    | "char" =>
      if shortN + longN > 0 then none else if uns then some .uchar else if sgn then some .schar else some .char
    | "int" =>
      if shortN == 1 then some (if uns then .ushort else .short)
      else if longN == 1 then some (if uns then .ulong else .long)
      else if longN == 2 then some (if uns then .ullong else .llong)
      else some (if uns then .uint else .int)
    | "double" => if signedN + unsignedN + shortN > 0 || longN > 1 then none
                  else if longN == 1 then some .ldouble else some .double
    | "float" | "bool" => if signedN + unsignedN + shortN + longN > 0 then none
                          else if base == "float" then some .float else some .bool
    | _ => none

end Jank.Interop.Spec
