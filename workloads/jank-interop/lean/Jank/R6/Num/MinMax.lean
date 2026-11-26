import Jank.R3.Boost.Num

/-!
# Round 6, numbers: `min`, `max`, the comparisons and `==` across kinds and paths

jank (upstream-r5/compiler+runtime):
- math.hpp `lt` 522-630, `lte` 630-736: `typed_l->data < typed_r->data` (the C++ operator for the
  pair of data types; i64 vs f64 converts the i64; ratio.hpp 241-311 templates; boost pairs as
  round 3's `jLt`);
- math.hpp `min` 738-865, `max` 865-992: object/object and native/object
  `l < r ? l : r` (min) and `l < r ? r : l` (max), returning one of the operands; native/native
  `std::min/std::max(static_cast<C>(l), static_cast<C>(r))` with `C` the common type (a long and a
  double literal give a double), where libstdc++/libc++ `std::min(a, b)` is `b < a ? b : a` and
  `std::max(a, b)` is `a < b ? b : a`;
- `compare` (number.cpp 139-153, 228-242, 342-356; R3 `jCompare`); `==` is math.cpp `is_equiv`
  469-489 (both `to_real`).

Clojure 1.12 (Numbers.java):
- `min`/`max` (4044-4228): two primitive longs or doubles use `Math.min/max` (NaN wins; -0.0 is
  below 0.0); a double with a long checks the double for NaN, then `x < y ? x : y` (min) /
  `x > y ? x : y` (max); any Object operand: `isNaN(x) ? x : isNaN(y) ? y : lt(x, y) ? x : y`
  (min) and `... gt(x, y) ? x : y` (max). On a tie the second operand wins.
- `lt` etc. through `ops(x).combine(ops(y))` (R3 `cLt`, `cLe`, `cCompare`, `cEquiv`).
-/

namespace Jank.R6.Num.MinMax

open Jank.R3.Boost Jank.R3.Boost.Num Jank.R3.Boost.Dec Jank.R3.Boost.Java

/-- A value as written in a program, with whether it reaches the call natively. -/
structure Arg where
  /-- jank's object/native value. -/
  j : JV
  /-- Clojure's value. -/
  c : CV
  /-- The program text of the value. -/
  text : String
  /-- Written as a literal (or a let-bound literal) at the call: only long and double literals are
  native in jank (cpp_util.cpp `literal_type`) and primitive in Clojure. -/
  lit : Bool

def Arg.native (a : Arg) : Bool :=
  a.lit && (match a.j with | .long _ | .dbl _ => true | _ => false)

/-- `to_real` of a ratio (ratio.cpp 108-111): numerator and denominator to f64, divided. -/
def ratioReal (n d : Int) : Float := CppInt.toDouble n / CppInt.toDouble d

/-- jank `typed_l->data < typed_r->data`. -/
def jLtAll : JV → JV → Option Bool
  | .long a, .long b => some (decide (a < b))
  | .long a, .dbl b => some (Ieee.ofIntRN a < b)
  | .dbl a, .long b => some (a < Ieee.ofIntRN b)
  | .dbl a, .dbl b => some (a < b)
  | .ratio n d, .long b => some (decide (n < b * d))
  | .long a, .ratio n d => some (decide (a * d < n))
  | .ratio n d, .ratio n' d' => some (decide (n * d' < n' * d))
  | .ratio n d, .dbl b => some (ratioReal n d < b)
  | .dbl a, .ratio n d => some (a < ratioReal n d)
  | a, b => jLt a b

def jLeAll : JV → JV → Option Bool
  | .long a, .long b => some (decide (a ≤ b))
  | .long a, .dbl b => some (Ieee.ofIntRN a ≤ b)
  | .dbl a, .long b => some (a ≤ Ieee.ofIntRN b)
  | .dbl a, .dbl b => some (a ≤ b)
  | .ratio n d, .long b => some (decide (n ≤ b * d))
  | .long a, .ratio n d => some (decide (a * d ≤ n))
  | .ratio n d, .ratio n' d' => some (decide (n * d' ≤ n' * d))
  | .ratio n d, .dbl b => some (ratioReal n d ≤ b)
  | .dbl a, .ratio n d => some (a ≤ ratioReal n d)
  | a, b => jLe a b

def jCompareAll (a b : JV) : Option Int :=
  match a, b with
  | .ratio n d, .dec y => some ((ratioToDec n d).compare y)
  | _, _ => do
    let x ← jLtAll b a
    let y ← jLtAll a b
    return (if x then 1 else 0) - (if y then 1 else 0)

/-- The common type of two native operands, and each converted to it. -/
def nativeCommon : JV → JV → JV × JV
  | .long a, .dbl b => (.dbl (Ieee.ofIntRN a), .dbl b)
  | .dbl a, .long b => (.dbl a, .dbl (Ieee.ofIntRN b))
  | a, b => (a, b)

/-- jank `min`/`max` (`isMax`) on two args. -/
def jMinMax (isMax : Bool) (x y : Arg) : Option JV :=
  if x.native && y.native then
    let (a, b) := nativeCommon x.j y.j
    if isMax then do let lt ← jLtAll a b; pure (if lt then b else a)    -- std::max(a, b)
    else do let lt ← jLtAll b a; pure (if lt then b else a)             -- std::min(a, b)
  else do
    let lt ← jLtAll x.j y.j
    pure (if isMax then (if lt then y.j else x.j) else (if lt then x.j else y.j))

def cIsNaN : CV → Bool
  | .dbl d => d.isNaN
  | _ => false

def negZero (d : Float) : Bool := d == 0.0 && d.toBits >>> 63 == 1

/-- Java `Math.min/max(double, double)`. -/
def javaMinMax (isMax : Bool) (a b : Float) : Float :=
  if a.isNaN then a else if b.isNaN then b
  else if a == 0.0 && b == 0.0 then
    (if isMax then (if negZero a then b else a) else (if negZero b then b else a))
  else if isMax then (if a ≥ b then a else b) else (if a ≤ b then a else b)

/-- Clojure `min`/`max` on two args. -/
def cMinMax (isMax : Bool) (x y : Arg) : Option CV :=
  let primitive := fun (a : Arg) => a.lit && (match a.c with | .long _ | .dbl _ => true | _ => false)
  if primitive x && primitive y then
    match x.c, y.c with
    | .long a, .long b => some (.long (if isMax then max a b else min a b))
    | .dbl a, .dbl b => some (.dbl (javaMinMax isMax a b))
    | .dbl a, .long b =>
      let bd := Ieee.ofIntRN b
      if a.isNaN then some x.c
      else some (if isMax then (if a > bd then x.c else y.c) else (if a < bd then x.c else y.c))
    | .long a, .dbl b =>
      let ad := Ieee.ofIntRN a
      if b.isNaN then some y.c
      else some (if isMax then (if ad > b then x.c else y.c) else (if ad < b then x.c else y.c))
    | _, _ => none
  else if cIsNaN x.c then some x.c
  else if cIsNaN y.c then some y.c
  else if isMax then do let gt ← cLt y.c x.c; pure (if gt then x.c else y.c)
  else do let lt ← cLt x.c y.c; pure (if lt then x.c else y.c)

/-! ## Values for the walk -/

def lng (v : Int) (lit : Bool) : Arg := ⟨.long v, .long v, toString v, lit⟩
def dbl (d : Float) (txt : String) (lit : Bool) : Arg := ⟨.dbl d, .dbl d, txt, lit⟩
def bigA (v : Int) (lit : Bool) : Arg := ⟨.big v, .big v, s!"{v}N", lit⟩
def ratA (n d : Int) (lit : Bool) : Arg := ⟨.ratio n d, .ratio n d, s!"{n}/{d}", lit⟩
def decA (s : String) (lit : Bool) : Option Arg :=
  match rdString (bytes s), BD.ofString (bytes s) with
  | .ok j, .ok c => some ⟨.dec j, .dec c, s ++ "M", lit⟩
  | _, _ => none

def nan : Float := 0.0 / 0.0
def inf : Float := 1.0 / 0.0

/-- The value set: every kind, ties across kinds, -0.0, NaN, infinities, 2^53 neighbours. -/
def values (lit : Bool) : List Arg :=
  [lng 0 lit, lng 1 lit, lng (-1) lit, lng 2 lit, lng 9007199254740993 lit, lng 9007199254740992 lit,
   lng 9223372036854775807 lit,
   dbl 0.0 "0.0" lit, dbl (-0.0) "-0.0" lit, dbl 1.0 "1.0" lit, dbl (-1.0) "-1.0" lit,
   dbl 2.5 "2.5" lit, dbl 0.5 "0.5" lit, dbl 9007199254740992.0 "9007199254740992.0" lit,
   dbl nan "##NaN" lit, dbl inf "##Inf" lit, dbl (-inf) "##-Inf" lit,
   bigA 0 lit, bigA 1 lit, bigA 9007199254740993 lit, bigA (2 ^ 70) lit,
   ratA 1 2 lit, ratA (-1) 2 lit, ratA 1 3 lit, ratA 7 3 lit] ++
  ([decA "1" lit, decA "0.5" lit, decA "0.1" lit, decA "2.5" lit].filterMap id)

def sameOpt : Option JV → Option CV → Bool
  | some j, some c => sameNum j c
  | none, none => true
  | _, _ => false

def showJ : Option JV → String
  | some v => v.prStr ++ " (" ++ v.kind ++ ")"
  | none => "not modeled"

def showC : Option CV → String
  | some v => v.prStr ++ " (" ++ v.kind ++ ")"
  | none => "not modeled"

/-- One question: an op on two args. -/
structure Q where
  op : String
  x : Arg
  y : Arg

def Q.path (q : Q) : String :=
  if q.x.lit && q.y.lit then "literals" else if q.x.lit || q.y.lit then "literal+param" else "params"

def Q.program (q : Q) : String :=
  if q.x.lit && q.y.lit then s!"({q.op} {q.x.text} {q.y.text})"
  else if q.x.lit then s!"((fn [b] ({q.op} {q.x.text} b)) {q.y.text})"
  else if q.y.lit then s!"((fn [a] ({q.op} a {q.y.text})) {q.x.text})"
  else s!"((fn [a b] ({q.op} a b)) {q.x.text} {q.y.text})"

/-- The two answers as text, and whether they agree. -/
def Q.answer (q : Q) : String × String × Bool :=
  match q.op with
  | "min" | "max" =>
    let isMax := q.op == "max"
    let j := jMinMax isMax q.x q.y
    let c := cMinMax isMax q.x q.y
    (showJ j, showC c, sameOpt j c)
  | "<" => let j := jLtAll q.x.j q.y.j; let c := cLt q.x.c q.y.c; (toString j, toString c, j == c)
  | "<=" => let j := jLeAll q.x.j q.y.j; let c := cLe q.x.c q.y.c; (toString j, toString c, j == c)
  | "compare" =>
    let j := jCompareAll q.x.j q.y.j; let c := cCompare q.x.c q.y.c; (toString j, toString c, j == c)
  | _ =>  -- "=="
    let j := some (jEquiv q.x.j q.y.j); let c := cEquiv q.x.c q.y.c; (toString j, toString c, j == c)

def questions (op : String) : List Q := Id.run do
  let mut out := #[]
  for lx in [true, false] do
    for ly in [true, false] do
      for x in values lx do
        for y in values ly do
          out := out.push ⟨op, x, y⟩
  return out.toList

/-- A one-word class for a min/max disagreement. -/
def Q.minmaxClass (q : Q) : String :=
  let isMax := q.op == "max"
  let nanIn := cIsNaN q.x.c || cIsNaN q.y.c
  let j := jMinMax isMax q.x q.y
  let c := cMinMax isMax q.x q.y
  if nanIn then "NaN"
  else match j, c with
    | some jv, some cv =>
      if sameValue jv cv then
        (if q.x.native && q.y.native then "kind (native common type)" else "tie (operand chosen)")
      else if q.x.native && q.y.native then "value (native)" else "value"
    | _, _ => "unmodeled"

end Jank.R6.Num.MinMax
