import Jank.R6.Num.MinMax
import Jank.R7.Gen.Core

/-!
# Round 7, area G: draws from round 6's min/max and comparison model (`Jank.R6.Num.MinMax`)

Universe: `MinMax.values` (29 values: longs, doubles with ±0.0, ##NaN, ±##Inf and 2^53's
neighbours, BigInts, ratios, BigDecimals), the operations `min max < <= compare ==`, every pair.
On [literals] and [let] both operands are `Arg.lit` (jank types a long or double literal natively,
and a let keeps it; Clojure compiles them as primitives); on [fn] neither is; on [mixed] one is.

The model's answers are `jMinMax`/`cMinMax`, `jLtAll`/`cLt`, `jLeAll`/`cLe`,
`jCompareAll`/`cCompare`, `jEquiv`/`cEquiv`, unchanged. Where round 6's Clojure side answers
`none` because `toBD` of a non-terminating ratio fails (`(compare 1/3 1M)`), Clojure 1.12 throws
ArithmeticException "Non-terminating decimal expansion" (Numbers.java `toBigDecimal` →
BigDecimal.divide), so the generator predicts a throw there (round 3's S3); the JVM run checks it.
-/

namespace Jank.R7.Gen.MinMax

open Jank.R7.Gen Jank.R6.Num.MinMax Jank.R3.Boost Jank.R3.Boost.Num Jank.R3.Boost.Dec
  Jank.R3.Boost.Java

/-- Clojure's outcome. -/
inductive CO where
  | v (x : CV) | b (x : Bool) | i (x : Int) | throws | none

/-- jank's outcome (no modeled pair throws). -/
inductive JO where
  | v (x : JV) | b (x : Bool) | i (x : Int) | none

def ops : List String := ["min", "max", "<", "<=", "compare", "=="]

def slug : String → String
  | "min" => "min" | "max" => "max" | "<" => "lt" | "<=" => "lte" | "compare" => "compare"
  | _ => "equiv"

def isDec : CV → Bool
  | .dec _ => true
  | _ => false

/-- Clojure's `none` is a throw when a BigDecimal takes part (the non-terminating `toBD`). -/
def cNone (x y : Arg) : CO := if isDec x.c || isDec y.c then .throws else .none

def eval (op : String) (x y : Arg) : JO × CO :=
  match op with
  | "min" | "max" =>
    let isMax := op == "max"
    let j := match jMinMax isMax x y with | some v => JO.v v | none => .none
    let c := match cMinMax isMax x y with | some v => CO.v v | none => cNone x y
    (j, c)
  | "<" =>
    (match jLtAll x.j y.j with | some b => .b b | none => .none,
     match cLt x.c y.c with | some b => .b b | none => cNone x y)
  | "<=" =>
    (match jLeAll x.j y.j with | some b => .b b | none => .none,
     match cLe x.c y.c with | some b => .b b | none => cNone x y)
  | "compare" =>
    (match jCompareAll x.j y.j with | some i => .i i | none => .none,
     match cCompare x.c y.c with | some i => .i i | none => cNone x y)
  | _ =>
    (.b (jEquiv x.j y.j),
     match cEquiv x.c y.c with | some b => .b b | none => cNone x y)

/-- The one assertion on Clojure's value `x` of expression `e`. -/
def assertV (x : CV) (e : String) : String :=
  match x with
  | .long _ | .big _ => s!"(= \"{x.prStr}\" (pr-str {e}))"
  | .dbl d =>
    if d.isNaN then s!"(NaN? {e})"
    else if d == 0.0 then s!"(= \"{if isNegZero d then "-0.0" else "0.0"}\" (str {e}))"
    else s!"(= {plainDouble d} {e})"
  | .ratio .. => s!"(= {x.prStr} {e})"
  | .dec _ => s!"(let [v {e}] (and (decimal? v) (zero? (compare {x.prStr} v))))"

def assertion (c : CO) (e : String) : String :=
  match c with
  | .v x => assertV x e
  | .b true => s!"(true? {e})"
  | .b false => s!"(false? {e})"
  | .i n => s!"(= {n} {e})"
  | _ => s!"(thrown? {e})"

/-- What the assertion on Clojure's value gives on jank's value: `pr-str` (round 3's `JV.prStr`),
`str` (`JV.str`), `NaN?`, `=` with a double (jank `equal` of two reals is `==`, of a real and
anything else false: round 3's `jEqual`), `=` with a ratio, `decimal?` and `compare` (exact on
two BigDecimals). -/
def passesV (x : CV) (j : JV) : Bool :=
  match x with
  | .long _ | .big _ => j.prStr == x.prStr
  | .dbl d =>
    if d.isNaN then (match j with | .dbl y => y.isNaN | _ => false)
    else if d == 0.0 then j.str == (if isNegZero d then "-0.0" else "0.0")
    else jEqual (.dbl d) j
  | .ratio n dd => jEqual (.ratio n dd) j
  | .dec _ => (match j with | .dec _ => sameNum j x | _ => false)

def verdictOf (j : JO) (c : CO) : Option Jank.R7.Gen.Verdict :=
  match c, j with
  | .none, _ | _, .none => none
  | .throws, _ => some .fail
  | .v x, .v y => some (if passesV x y then .pass else .fail)
  | .b x, .b y => some (if x == y then .pass else .fail)
  | .i x, .i y => some (if x == y then .pass else .fail)
  | _, _ => some .fail

def showC : CO → String
  | .v x => x.prStr | .b b => toString b | .i n => toString n
  | .throws => "throws ArithmeticException (non-terminating decimal expansion)" | .none => "not modeled"

def showJ : JO → String
  | .v x => x.prStr | .b b => toString b | .i n => toString n | .none => "not modeled"

def kindC : CV → String
  | .long _ => "long" | .dbl _ => "double" | .big _ => "BigInt" | .dec _ => "BigDecimal" | .ratio .. => "ratio"

/-- The deviation that explains a disagreement: S3 (a non-terminating ratio against a BigDecimal,
where Clojure throws), V56 (NaN in min/max), V58 (two natives of different types or signed
zeros: their common C++ type), V57 (a tie returns the other operand), D5 (`==` through doubles),
R99 (a BigInt or BigDecimal against a double compared exactly, round 2, extended in round 3),
S21 (a ratio against a double: jank's ratio-to-double). -/
def explain (op : String) (x y : Arg) (j : JO) (c : CO) : String :=
  let kinds := [kindC x.c, kindC y.c]
  let has := fun (k : String) => kinds.contains k
  match c with
  | .throws => "S3"
  | _ =>
  if op == "min" || op == "max" then
    if cIsNaN x.c || cIsNaN y.c then "V56"
    else
      -- a tie: equal values, or neither below the other under jank's comparison (a long and a
      -- double compared as doubles: 9007199254740993 and 9007199254740992.0)
      let tie := (match j, c with
        | .v jv, .v cv => sameValue jv cv
        | _, _ => false) || (jLtAll x.j y.j == some false && jLtAll y.j x.j == some false)
      if x.native && y.native then "V58"
      else if tie then "V57"
      else if has "double" && (has "BigInt" || has "BigDecimal") then "R99"
      else if has "double" && has "ratio" then "S21"
      else "?"
  else if op == "==" then "D5"
  else if has "double" && (has "BigInt" || has "BigDecimal") then "R99"
  else if has "double" && has "ratio" then "S21"
  else "?"

/-- One draw: two values (indices into `values`), the [mixed] parameter's side, the [fn] route. -/
structure T where
  op : String
  i : Nat
  k : Nat
  leftParam : Bool
  via : Via

instance : Inhabited Arg := ⟨lng 0 true⟩

def argOf (i : Nat) (lit : Bool) : Arg := (values lit)[i]!

def wrapperOf (op : String) : String := "g-" ++ slug op

def T.form (t : T) : Path → String
  | .literals => s!"({t.op} {(argOf t.i true).text} {(argOf t.k true).text})"
  | .letp => s!"(let [a {(argOf t.i true).text} b {(argOf t.k true).text}] ({t.op} a b))"
  | .fn =>
    let a := (argOf t.i false).text
    let b := (argOf t.k false).text
    match t.via with
    | .defn => s!"({wrapperOf t.op} {a} {b})"
    | .lam => s!"((fn [a b] ({t.op} a b)) {a} {b})"
    | .app => s!"(apply {t.op} [{a} {b}])"
  | .mixed =>
    if t.leftParam then s!"((fn [a] ({t.op} a {(argOf t.k true).text})) {(argOf t.i false).text})"
    else s!"((fn [b] ({t.op} {(argOf t.i true).text} b)) {(argOf t.k false).text})"

def T.args (t : T) : Path → Arg × Arg
  | .literals | .letp => (argOf t.i true, argOf t.k true)
  | .fn => (argOf t.i false, argOf t.k false)
  | .mixed => if t.leftParam then (argOf t.i false, argOf t.k true) else (argOf t.i true, argOf t.k false)

def T.detail (t : T) : Path → String
  | .fn => t.via.slug
  | p => p.slug

def item (group : String) (t : T) (p : Path) : Option Item := do
  let (x, y) := t.args p
  let (j, c) := eval t.op x y
  let v ← verdictOf j c
  let e := t.form p
  pure { group, op := slug t.op, path := p, detail := t.detail p, form := e,
         assertion := assertion c e, clj := showC c, jank := showJ j, verdict := v,
         id := if v == .pass then "" else explain t.op x y j c }

def nvals : Nat := (values true).length

def draws (op : String) : Array Draw := Id.run do
  let mut out := #[]
  let mut n := 0
  for i in List.range nvals do
    for k in List.range nvals do
      for lp in [true, false] do
        let t : T := { op, i, k, leftParam := lp, via := viaOf n }
        n := n + 1
        let items := Path.all.filterMap (item "minmax" t)
        if items.length == 4 then
          out := out.push { key := t.form .literals ++ "|" ++ t.form .mixed, items := items.toArray }
  return out

def nanIdx : Nat := ((values true).findIdx? (fun a => cIsNaN a.c)).getD 0

/-- The brief's class: `min`/`max` with ##NaN through a fn (the real jank: `(max ##NaN 1)` through a
fn agrees, `(min ##NaN 1)` gives 1). Draws on the [fn] path only, NaN on either side. -/
def nanDraws (op : String) : Array Draw := Id.run do
  let mut out := #[]
  let mut n := 0
  for k in List.range nvals do
    if k == nanIdx then continue
    for first in [true, false] do
      for via in Via.all do
        let t : T := if first then { op, i := nanIdx, k, leftParam := true, via }
                     else { op, i := k, k := nanIdx, leftParam := true, via }
        n := n + 1
        match item "brief" t .fn with
        | some it => out := out.push { key := it.form, items := #[it] }
        | none => pure ()
  return out

end Jank.R7.Gen.MinMax
