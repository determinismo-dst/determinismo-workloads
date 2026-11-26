import Jank.R6.Native.Math
import Jank.R7.Gen.Core

/-!
# Round 7, area G: draws from round 6's native-values model (`Jank.R6.Native.Math`)

Universe: `Jank.R6.Native.sources` without its parameter sources (literals `int`/`long`, double
literals, `count`, `alength`, `hash`, `int`, `bit-and`, byte/short/int/float array elements,
`float`, an inlined predicate's `bool`, a char array's `char`), every pair, the ten operations
`< <= > >= min max + - * /`. Paths: [literals] (`jankInline` on both natives), [let] (the same:
a let keeps its init's C++ type), [fn] (`jankFnValue`: both boxed by `convert<T>::into_object`),
[mixed] (an integer or double literal operand passed instead through the local fn's parameter,
R6's `.param`/`.dparam`, the other operand native, `jankInline`).

Clojure's value is `cljBin false` (Clojure 1.12 itself, no documented difference set aside), with
`Case.objStatic` choosing `Numbers.divide(Object, Object)` where an operand is an Object. Draws
whose jank outcome is undefined behavior (integer division by zero, `INT_MIN / -1`) are left out:
nothing can be predicted there.
-/

namespace Jank.R7.Gen.Native

open Jank.R7.Gen Jank.R6.Native

def slug : Op → String
  | .lt => "lt" | .lte => "lte" | .gt => "gt" | .gte => "gte" | .min => "min" | .max => "max"
  | .add => "add" | .sub => "sub" | .mul => "mul" | .div => "div"

def isParam (s : Src) : Bool := s.paramArg.isSome

def nonParam : List Src := sources.filter (!isParam ·)

/-- The literal operand as a fn parameter of the same value (R6's `.param`/`.dparam`). -/
def asParam : Src → Option Src
  | .lit v => some (.param v)
  | .dlit x => some (.dparam x)
  | _ => none

/-- One draw: two native sources, the [mixed] parameter's side, the [fn] route. -/
structure T where
  op : Op
  a : Src
  b : Src
  leftParam : Bool
  via : Via

/-- The [mixed] case, when the chosen side is a literal. -/
def T.mixedCase (t : T) : Option Case :=
  if t.leftParam then (asParam t.a).map fun p => { op := t.op, a := p, b := t.b, fnValue := false }
  else (asParam t.b).map fun p => { op := t.op, a := t.a, b := p, fnValue := false }

def T.caseOn (t : T) : Path → Option Case
  | .literals | .letp => some { op := t.op, a := t.a, b := t.b, fnValue := false }
  | .fn => some { op := t.op, a := t.a, b := t.b, fnValue := true }
  | .mixed => t.mixedCase

def T.form (t : T) : Path → String
  | .literals => s!"({t.op.sym} {t.a.code} {t.b.code})"
  | .letp => s!"(let [a {t.a.code} b {t.b.code}] ({t.op.sym} a b))"
  | .fn =>
    match t.via with
    | .defn => s!"(g-{slug t.op} {t.a.code} {t.b.code})"
    | .lam => s!"((fn [a b] ({t.op.sym} a b)) {t.a.code} {t.b.code})"
    | .app => s!"(apply {t.op.sym} [{t.a.code} {t.b.code}])"
  | .mixed =>
    match t.mixedCase with
    | some c => formOf c.op c.a c.b false
    | none => ""

def T.detail (t : T) : Path → String
  | .fn => t.via.slug
  | p => p.slug

def assertV (x : CV) (e : String) : String :=
  match x with
  | .long v => s!"(= \"{v}\" (pr-str {e}))"
  | .dbl d _ =>
    if d.isNaN then s!"(NaN? {e})"
    else if d == 0.0 then s!"(= \"{if isNegZero d then "-0.0" else "0.0"}\" (str {e}))"
    else s!"(= {plainDouble d} {e})"
  | .ratio n d => s!"(= {n}/{d} {e})"
  | .bool true => s!"(true? {e})"
  | .bool false => s!"(false? {e})"
  | .char c => s!"(= {c} (int {e}))"

def assertion (c : CR) (e : String) : String :=
  match c with
  | .val x => assertV x e
  | _ => s!"(thrown? {e})"

/-- What the assertion on Clojure's value gives on jank's value as a program sees it (`JR.seen`):
`pr-str` of a long is its digits (a double prints `.0`, a boolean `true`); `=` of a double literal
is `==` with a real and false with anything else; `str` of a real zero shows its sign; `NaN?` of a
non-real is false (math.cpp `is_nan` 641–656). -/
def passesV (x : CV) (y : CV) : Bool :=
  match x, y with
  | .long a, .long b => a == b
  | .dbl d _, .dbl e _ =>
    if d.isNaN then e.isNaN
    else if d == 0.0 then e == 0.0 && isNegZero d == isNegZero e
    else d == e
  | .ratio a b, .ratio c d => a == c && b == d
  | .bool a, .bool b => a == b
  | _, _ => false

def verdictOf (j : JR) (c : CR) : Option Jank.R7.Gen.Verdict :=
  match j with
  | .ub _ => none
  | .threwNative _ => some .throws
  | .threwObj _ => some (match c with | .threw _ => .pass | _ => .throws)
  | _ =>
    match j.seen, c with
    | .val y, .val x => some (if passesV x y then .pass else .fail)
    | .val _, .threw _ => some .fail
    | _, _ => none

def jankText (j : JR) : String :=
  match j with
  | .threwNative m => s!"throws {m} (a std::runtime_error, not an object)"
  | .threwObj m => s!"throws {m} (an object)"
  | _ => j.seen.show

/-- Switches of `Jank.R6.Native.Sw`, each one cause, with the id REPORT-6 gives it. -/
def switches : List (Sw × String) :=
  [({ rejectBool := true }, "V64"), ({ rejectChar := true }, "V64"), ({ lg1Widen := true }, "LG1"),
   ({ checkedOps := true }, "R25"), ({ floatArith := true }, "V63"), ({ minmax := true }, "V58"),
   ({ maxTie := true }, "V57"), ({ hashSigned := true }, "V51"), ({ floatF32 := true }, "V62"),
   ({ bytesSigned := true }, "R122")]

def isHash : Src → Bool
  | .hash _ => true
  | _ => false

def refine (c : Case) (p : Path) (id : String) : String :=
  if id == "LG1" && c.op == .div then "V50"
  else if id == "R25" then
    (if isHash c.a || isHash c.b then "V51"
     else match p with | .literals => "R25" | .letp => "V53" | _ => "D1")
  else id

def dedup (xs : List String) : List String := xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

/-- The deviation that explains a disagreement with Clojure 1.12: D2 (truncating integer `/`, or
a zero divisor) and LG2 (long overflow) where Clojure-with-those-set-aside (`cljBin true`, round
6's reference) agrees; else the switches whose fix alone makes the case agree ("a|b": each alone);
else a pair that does ("a+b": both needed); else every switch that changes jank's answer. -/
def explain (c : Case) (p : Path) : String :=
  let jr := c.jank Sw.none
  let j := jr.seen
  match jr, c.clj false with
  | .threwNative _, .threw _ => "V64"   -- a boxed bool/char through a fn: "not a number", not an object
  | _, _ =>
  if agrees j (c.clj true) then
    (if c.op == .div then "D2" else "LG2")
  else
    let singles := switches.filter fun (sw, _) => agrees (c.jank sw).seen (c.clj true)
    if !singles.isEmpty then "|".intercalate (dedup (singles.map fun (_, id) => refine c p id))
    else
      let pairs := (switches.zip (List.range switches.length)).flatMap fun ((s1, i1), k1) =>
        (switches.drop (k1 + 1)).filterMap fun (s2, i2) =>
          let sw : Sw := { rejectBool := s1.rejectBool || s2.rejectBool, rejectChar := s1.rejectChar || s2.rejectChar,
                           lg1Widen := s1.lg1Widen || s2.lg1Widen, minmax := s1.minmax || s2.minmax,
                           checkedOps := s1.checkedOps || s2.checkedOps, floatArith := s1.floatArith || s2.floatArith,
                           maxTie := s1.maxTie || s2.maxTie, hashSigned := s1.hashSigned || s2.hashSigned,
                           floatF32 := s1.floatF32 || s2.floatF32, bytesSigned := s1.bytesSigned || s2.bytesSigned }
          if agrees (c.jank sw).seen (c.clj true) then some ("+".intercalate (dedup [refine c p i1, refine c p i2])) else none
      match pairs with
      | pr :: _ => pr
      | [] =>
        let movers := switches.filter fun (sw, _) => !(agrees (c.jank sw).seen j && agrees j (c.jank sw).seen)
        if movers.isEmpty then "?" else "+".intercalate (dedup (movers.map fun (_, id) => refine c p id))

def item (t : T) (p : Path) : Option Item := do
  let c ← t.caseOn p
  let j := c.jank Sw.none
  let cr := c.clj false
  let v ← verdictOf j cr
  let e := t.form p
  pure { group := "native", op := slug t.op, path := p, detail := t.detail p, form := e,
         assertion := assertion cr e, clj := cr.show, jank := jankText j, verdict := v,
         id := if v == .pass then "" else explain c p }

def draws (op : Op) : Array Draw := Id.run do
  let mut out := #[]
  let mut n := 0
  for a in nonParam do
    for b in nonParam do
      for lp in [true, false] do
        let t : T := { op, a, b, leftParam := lp, via := viaOf n }
        n := n + 1
        let paths := if t.mixedCase.isSome then Path.all else [.literals, .letp, .fn]
        let items := paths.filterMap (item t)
        if items.length == paths.length then
          out := out.push { key := t.form .literals ++ "|" ++ t.form .mixed, items := items.toArray }
  return out

end Jank.R7.Gen.Native
