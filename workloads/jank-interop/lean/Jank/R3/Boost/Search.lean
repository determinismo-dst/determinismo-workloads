import Jank.R3.Boost.Tables
import Determinismo

/-!
# Round 3, Boost: classes of disagreement and the residual searches

Every disagreeing question is put in one class by what decides it in the code (the classes
are the deviations MP1… and the round 1/2 entries they extend). A search draws one question per
timeline (`decide "boost.question"`); the property is "jank answers as Clojure", minus the
classes set aside. Each residual search sets aside the class the previous one found, until an
exhaustive run over every question is complete with nothing found.
-/

namespace Jank.R3.Boost.Search

open Determinismo Jank.R3.Boost Jank.R3.Boost.Dec Jank.R3.Boost.Java Jank.R3.Boost.Num Jank.R3.Boost.Tables

def isDbl : JV → Bool | .dbl _ => true | _ => false
def isDec : JV → Bool | .dec _ => true | _ => false
def isBig : JV → Bool | .big _ => true | _ => false
def isRatio : JV → Bool | .ratio .. => true | _ => false
def isInt : JV → Bool | .long _ | .big _ => true | _ => false

def cErr (c : CR) (msg : String) : Bool :=
  match c with | .err m => (m.splitOn msg).length > 1 | _ => false

def nonterm (c : CR) : Bool := cErr c "Non-terminating"
def div0 (c : CR) : Bool := cErr c "Divide by zero"

/-- Significant digits of a BigDecimal (trailing zeros dropped). -/
def sigDigits (d : BD) : Nat :=
  if d.u == 0 then 0 else (Nat.toDigits 10 d.u.natAbs).length - tz d.u.natAbs

/-- The class of a disagreeing question (`""` when it agrees). -/
def classify (q : Q) : String :=
  let a := q.answer
  if a.agree then "" else
  match q with
  | .arith op x y =>
    let c := cArith op x.c y.c
    let j := jArith op x.j y.j
    if div0 c then "div0 (documented: division by 0)"
    else if nonterm c then "MP2 non-terminating quotient returns a value"
    else if combine x.c.cat y.c.cat == .dbl && (match j with | .num (.dec _) => true | _ => false) then
      "MP5 BigDecimal with a double gives a BigDecimal"
    else if op == .div && isInt x.j && isInt y.j then "MP18 (D2) BigInt / truncates"
    else match c, j with
      | .num (.big v), .num (.long w) => if v == w then "MP19 ratio: an integral result is a long, not a BigInt" else "UNCLASSIFIED"
      | .num (.dec d), .num (.dec _) =>
        if op == .div || isRatio x.j || isRatio y.j then "MP1 decimal division through a truncated inverse"
        else if sigDigits d > 120 then "MP3 128-digit precision"
        else "UNCLASSIFIED"
      | _, _ => "UNCLASSIFIED"
  | .lt x y | .le x y | .cmp x y =>
    let c := match q with | .lt .. => cLt x.c y.c | .le .. => cLe x.c y.c | _ => (cCompare x.c y.c).map (· == 0)
    if c.isNone then "MP2 non-terminating quotient returns a value"
    else if isDbl x.j || isDbl y.j then "R99 exact comparison against a double"
    else "UNCLASSIFIED"
  | .equiv x y =>
    if (cEquiv x.c y.c).isNone then "MP2 non-terminating quotient returns a value"
    else "D5 == through doubles"
  | .equal x y => if isDec x.j && isDec y.j then "D8 BigDecimal = within 2^-52" else "UNCLASSIFIED"
  | .hashEq x y =>
    if isInt x.j && isInt y.j then "D12 long/BigInt hashes"
    else if isDec x.j && isDec y.j then "MP9 BigDecimals jank calls = hash differently (D8 with D12)"
    else "UNCLASSIFIED"
  | .quot x y =>
    let c := cQuot x.c y.c
    if div0 c then "div0 (documented: division by 0)"
    else if nonterm c then "MP2 non-terminating quotient returns a value"
    else "D4 quot through doubles (a long)"
  | .rem x y =>
    let c := cRem x.c y.c
    if div0 c then "div0 (documented: division by 0)"
    else if isRatio x.j || isRatio y.j then "MP7 rem of a ratio and a decimal truncates the decimal"
    else if isDec x.j || isDec y.j then "MP6 rem of decimals through 128-digit fmod"
    else "UNCLASSIFIED"
  | .str x | .prStr x =>
    if isDec x.j then
      if (x.j.str.splitOn "e").length > 1 then "MP4 BigDecimal printed in boost's scientific form"
      else "R72 BigDecimal printing: scale lost, .0 added"
    else "UNCLASSIFIED"
  | .toDouble x =>
    if isDec x.j then "MP10 BigDecimal to double rounds twice (19 digits, then strtod)"
    else if isRatio x.j then "MP20 double of a ratio divides two doubles"
    else "UNCLASSIFIED"
  | .toLong x =>
    if isDec x.j then "MP11 long of a BigDecimal: exact truncation, saturating"
    else "UNCLASSIFIED"
  | .bigdec x =>
    if (match x.j with | .long _ => true | _ => false) then "D7 bigdec of a long through a double"
    else if isDbl x.j then "MP8 bigdec/bigint of a double: the binary value, not Double.toString"
    else if isRatio x.j then "MP2 non-terminating quotient returns a value"
    else "UNCLASSIFIED"
  | .bigint x =>
    if isDbl x.j then "MP8 bigdec/bigint of a double: the binary value, not Double.toString"
    else if isRatio x.j then "MP17 bigint of a ratio goes through i64"
    else "UNCLASSIFIED"

/-! ## The world -/

structure World where
  decisions : Decisions := {}

instance : Chaotic World where
  decisions w := w.decisions
  setDecisions w d := { w with decisions := d }

abbrev WM := EStateM Stop World

def runW (body : WM Unit) (source : Source) : Ended :=
  match body.run { decisions := { source } } with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }
  | .error (.nodeDown _) w => { taken := w.decisions.taken, violation := none }

/-- One timeline: a question kind, then its operands, each a decision. -/
def body (qs : Array Q) (aside : List String) : WM Unit := do
  let i ← decide (σ := World) "boost.question" qs.size
  let q := qs[i]!
  let cls := classify q
  if cls != "" && !aside.contains cls then
    let a := q.answer
    violate (σ := World) s!"jank answers as Clojure [{cls}]" s!"{q.program}: jank {a.jank}, Clojure {a.clj}"

end Jank.R3.Boost.Search

namespace Jank.R3.Boost.Search

open Determinismo Jank.R3.Boost Jank.R3.Boost.Dec Jank.R3.Boost.Java Jank.R3.Boost.Num Jank.R3.Boost.Tables

/-! ## `bigint`/`bigdec` of strings -/

/-- The class of `(bigint s)` / `(bigdec s)` disagreeing (`""` when they agree). -/
def strClass (dec : Bool) (s : List Nat) : String :=
  let j := if dec then jBigdecStr s else jBigintStr s
  let c := if dec then cBigdecStr s else cBigintStr s
  if numAgree j c then "" else
  if dec then
    match j, c with
    | .num _, .err _ => "MP13 bigdec of a string: boost's grammar accepts what BigDecimal rejects"
    | .err _, .num _ => "MP13 bigdec of a string: boost's grammar rejects what BigDecimal accepts"
    | _, _ => "MP13 bigdec of a string: another value"
  else
    match j, c with
    | .num _, .err _ => "MP14 bigint of a string: boost's grammar accepts what BigInteger rejects"
    | .err _, .num _ => "MP14 bigint of a string: boost's grammar rejects what BigInteger accepts"
    | _, _ => "MP14 bigint of a string: another value (octal or hexadecimal prefix)"

/-! ## Random operands beyond the fixed universe -/

/-- A literal drawn by decisions: a long, a double, a BigInt, a BigDecimal (digits, point,
exponent) or a ratio. -/
def drawLiteral : WM String := do
  let kind ← decide (σ := World) "lit.kind" 5
  let digit := fun (name : String) => do
    let d ← decide (σ := World) name 10
    pure (Char.ofNat (48 + d))
  let mut ds : List Char := []
  let n ← decide (σ := World) "lit.digits" 24
  for _ in [0:n + 1] do ds := ds ++ [← digit "lit.digit"]
  let ds' := match ds.dropWhile (· == '0') with | [] => ['0'] | x => x
  let neg ← decide (σ := World) "lit.neg" 2
  let sgn := if neg == 1 then "-" else ""
  match kind with
  | 0 => pure (sgn ++ String.ofList (ds'.take 18))
  | 1 =>
    let e ← decide (σ := World) "lit.exp" 41
    pure (sgn ++ String.ofList (ds'.take 16) ++ ".5e" ++ toString ((e : Int) - 20))
  | 2 => pure (sgn ++ String.ofList ds' ++ "N")
  | 3 =>
    let p ← decide (σ := World) "lit.point" (ds'.length + 1)
    let e ← decide (σ := World) "lit.exp" 61
    let body := String.ofList (ds'.take p) ++ "." ++ String.ofList (ds'.drop p)
    let body := if p == 0 then "0" ++ body else body
    pure (sgn ++ body ++ "e" ++ toString ((e : Int) - 30) ++ "M")
  | _ =>
    let dn ← decide (σ := World) "lit.den" 12
    pure (sgn ++ String.ofList ds' ++ "/" ++ toString (dn + 2))

def drawQ : WM Q := do
  let a := mkOperand (← drawLiteral)
  let b := mkOperand (← drawLiteral)
  let k ← decide (σ := World) "q.kind" 14
  pure <| match k with
    | 0 => .arith .add a b | 1 => .arith .sub a b | 2 => .arith .mul a b | 3 => .arith .div a b
    | 4 => .lt a b | 5 => .cmp a b | 6 => .equiv a b | 7 => .equal a b | 8 => .hashEq a b
    | 9 => .rem a b | 10 => .str a | 11 => .toDouble a | 12 => .bigdec a | _ => .bigint a

/-- Random questions over drawn literals; questions with no BigInt/BigDecimal are skipped
(not this area). -/
def randomBody (aside : List String) : WM Unit := do
  let q ← drawQ
  let boostQ := match q with
    | .arith _ a b | .lt a b | .cmp a b | .equiv a b | .equal a b | .hashEq a b | .rem a b
    | .le a b | .quot a b => a.j.boost || b.j.boost
    | .str a | .prStr a | .toDouble a | .toLong a | .bigdec a | .bigint a =>
      a.j.boost || isDbl a.j || isRatio a.j
  let skipRemDbl := match q with | .rem a b => isDbl a.j || isDbl b.j | _ => false
  let skipStrDbl := match q with | .str a => isDbl a.j | _ => false
  if boostQ && !skipRemDbl && !skipStrDbl then
    let cls := classify q
    if cls != "" && !aside.contains cls then
      let a := q.answer
      violate (σ := World) s!"jank answers as Clojure [{cls}]" s!"{q.program}: jank {a.jank}, Clojure {a.clj}"

end Jank.R3.Boost.Search
