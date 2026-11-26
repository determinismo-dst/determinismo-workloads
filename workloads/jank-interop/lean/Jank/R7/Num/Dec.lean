import Jank.R3.Boost.Num

/-!
# Round 7, numbers: BigDecimal with a scale (S2–S5, S7, U1) beside jank's `cpp_dec_float<100>`

Extends round 3's `Jank.R3.Boost.Java` (a `BigDecimal` as unscaled `u` and `scale s`) and
`Jank.R3.Boost.Num` (Clojure's `Numbers` over it, jank's number objects over the boost replica).

**Clojure 1.12 / JDK** (clojure-ref Numbers.java; java.math.BigDecimal's documented semantics,
checked by running every walk question on Clojure 1.12.3, JDK 23):
- `BigDecimalOps` (Numbers.java 964-1092): with `*math-context*` nil, `add`/`multiply`/`divide`
  are exact (`divide` throws "Non-terminating decimal expansion; no exact representable decimal
  result."); `quotient` is `divideToIntegralValue`, `remainder` is `remainder`; `equiv`, `lt`,
  `lte`, `gte` use `compareTo`; `minus(x, y)` is `add(x, ops(y).negate(y))` (Numbers.java 162-165);
  `toBigDecimal` (298-322): a Ratio through `divide(new BigDecimal(n), d)`, a long through
  `BigDecimal.valueOf`.
- `divideToIntegralValue` (JDK): preferred scale `this.scale − divisor.scale`; the integer part
  `t` of the exact quotient, at scale `max(preferred, −trailingZeros(t))`; zero (|this| <
  |divisor|) at the preferred scale. `remainder` = `this − q·divisor` (exact).
- `hasheq` (Numbers.java 1132-1145): 0 for a zero, else `stripTrailingZeros().hashCode()`, where
  `BigDecimal.hashCode` = `31 · unscaledValue().hashCode() + scale` and `BigInteger.hashCode`
  folds the 32-bit magnitude words, most significant first (`h = 31·h + w`), times the signum.

**jank** (paths under upstream-r5/compiler+runtime): a BigDecimal is `cpp_dec_float<100>` (type.hpp
35): a value with no scale. Printing: big_decimal.cpp 157-175 → string_builder.cpp 240-249
(`str()`, then ".0" when the text has no '.'). Arithmetic: math.hpp `add`/`sub`/`mul`/`div`
(68-518) on the boost values (round 3's `jArith`; division is `calculate_inv`'s Newton inverse,
S2). `quot` is math.cpp 321-345 (both through `to_real`, a long: D4), `rem` math.cpp 223-304
(`fmod` for decimals: S7; a ratio truncates the decimal: S8). `compare` big_decimal.cpp 182-190,
`=` 146-155 (D8), `hash` 177-180 (`std::hash<native_big_decimal>`, a `uhash`).
-/

namespace Jank.R7.Num.Dec

open Jank.R3.Boost Jank.R3.Boost.Dec Jank.R3.Boost.Num Jank.R3.Boost.Java

/-! ## Java: trailing zeros, stripping, hashing -/

/-- Trailing decimal zeros of `n` (0 for 0), by recursion. -/
def tz10 : Nat → Nat
  | 0 => 0
  | n + 1 => if (n + 1) % 10 = 0 then tz10 ((n + 1) / 10) + 1 else 0
decreasing_by omega

/-- `stripTrailingZeros()` (JDK 8+: a zero becomes `BigDecimal.ZERO`, scale 0). -/
def strip (b : BD) : BD :=
  if b.u = 0 then ⟨0, 0⟩
  else ⟨b.u / (10 : Int) ^ (tz10 b.u.natAbs), b.s - (tz10 b.u.natAbs : Int)⟩

/-- Java `int` arithmetic: wrap to [−2^31, 2^31). -/
def wrapI32 (z : Int) : Int := z.bmod (2 ^ 32)

/-- The magnitude's 32-bit words, most significant first (`BigInteger.mag`). -/
def words32 (n : Nat) : List Nat :=
  if h : n = 0 then [] else words32 (n / 2 ^ 32) ++ [n % 2 ^ 32]
decreasing_by omega

/-- `BigInteger.hashCode()`. -/
def bigIntegerHash (v : Int) : Int :=
  let h := (words32 v.natAbs).foldl (fun (h : Int) (w : Nat) => wrapI32 (31 * h + (w : Int))) 0
  wrapI32 (h * v.sign)

/-- `BigDecimal.hashCode()` (the compact form computes the same value). -/
def bdHashCode (b : BD) : Int := wrapI32 (31 * bigIntegerHash b.u + b.s)

/-- Clojure's `hash` of a BigDecimal (`Numbers.hasheqFrom`, 1132-1145). -/
def cljHashDec (b : BD) : Int := if b.u = 0 then 0 else bdHashCode (strip b)

/-! ## Java: divideToIntegralValue and remainder (no MathContext) -/

/-- `t` at scale `sc` (exact: `sc ≥ −trailingZeros t`). -/
def atScaleI (t : Int) (sc : Int) : BD :=
  if sc ≥ 0 then ⟨t * (10 : Int) ^ sc.toNat, sc⟩ else ⟨Int.tdiv t ((10 : Int) ^ (-sc).toNat), sc⟩

/-- `divideToIntegralValue(divisor)`. -/
def _root_.Jank.R3.Boost.Java.BD.divToIntegral (x y : BD) : Except String BD :=
  if y.u = 0 then .error (if x.u = 0 then "Division undefined" else "Division by zero")
  else
    let pref := x.s - y.s
    let (p, q) := x.rat
    let (p', q') := y.rat
    if x.u = 0 || p.natAbs * q' < p'.natAbs * q then .ok ⟨0, pref⟩
    else
      let t : Int := Int.tdiv (p * (q' : Int)) ((q : Int) * p')
      .ok (atScaleI t (max pref (-(tz10 t.natAbs : Int))))

/-- `remainder(divisor)` = `this − divideToIntegralValue(divisor) · divisor`. -/
def _root_.Jank.R3.Boost.Java.BD.remainder (x y : BD) : Except String BD := do
  let q ← x.divToIntegral y
  return x.sub (q.mul y)

/-! ## Clojure: Numbers with a BigDecimal operand (`*math-context*` nil) -/

/-- An operand's value: what `ops(x).negate` does to a Long/MIN_VALUE matters (`minus`). -/
def i64min : Int := -9223372036854775808

/-- Clojure's binary operations on two numbers, at least one a BigDecimal. -/
inductive Op where
  | add | sub | mul | div | quot | rem | compare | equiv | equal | max | min | lt
  deriving BEq, Repr, Inhabited

def Op.name : Op → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .quot => "quot" | .rem => "rem"
  | .compare => "compare" | .equiv => "==" | .equal => "=" | .max => "max" | .min => "min"
  | .lt => "<"

def ops : List Op := [.add, .sub, .mul, .div, .quot, .rem, .compare, .equiv, .equal, .max, .min, .lt]

/-- A result as a program sees it. -/
inductive Out where
  | num (k : String) (text : String) (value : Option (Int × Nat))
  | bool (b : Bool)
  | int (i : Int)
  | err (m : String)
  deriving BEq, Inhabited

def Out.show : Out → String
  | .num k t _ => s!"{t} ({k})"
  | .bool b => toString b
  | .int i => toString i
  | .err m => s!"throws ({m})"

def cvOut (v : CV) : Out :=
  let r : Option (Int × Nat) := match v with
    | .long x | .big x => some (x, 1)
    | .dec d => some d.rat
    | .ratio n d => some (n, d.toNat)
    | .dbl _ => none
  .num v.kind v.prStr r

def jvOut (v : JV) : Out :=
  let r : Option (Int × Nat) := match v with
    | .long x | .big x => some (x, 1)
    | .dec d => d.rat
    | .ratio n d => some (n, d.toNat)
    | .dbl _ => none
  .num v.kind v.prStr r

def crOut : CR → Out
  | .num v => cvOut v | .bool b => .bool b | .int i => .int i | .str s => .num "String" s none
  | .err m => .err m

def jrOut : JR → Out
  | .num v => jvOut v | .bool b => .bool b | .int i => .int i | .str s => .num "String" s none
  | .err m => .err m

def isZeroC : CV → Bool
  | .long v | .big v => v == 0 | .dbl x => x == 0.0 | .dec d => d.u == 0 | .ratio n _ => n == 0

/-- `ops(y).negate(y)` as `minus` uses it (LongOps.negate throws on Long/MIN_VALUE). -/
def cNegate : CV → Except String CV
  | .long v => if v == i64min then .error "long overflow" else .ok (.long (-v))
  | .big v => .ok (.big (-v))
  | .dbl x => .ok (.dbl (-x))
  | .dec d => .ok (.dec d.neg)
  | .ratio n d => .ok (.ratio (-n) d)

/-- `Numbers.quotient`/`remainder` (189-205) with a BigDecimal (BigDecimalOps.quotient/remainder). -/
def cQuotRem (isQuot : Bool) (a b : CV) : CR :=
  if isZeroC b then .err "Divide by zero"
  else match combine a.cat b.cat with
  | .dec =>
    match toBD a, toBD b with
    | .ok x, .ok y =>
      match (if isQuot then x.divToIntegral y else x.remainder y) with
      | .ok r => .num (.dec r) | .error e => .err e
    | .error e, _ | _, .error e => .err e
  | .dbl =>
    if isQuot then
      -- `Numbers.quotient(double, double)` (207-218): `(double)(long) q`, so |q| < 1 gives +0.0
      -- (round 3's `cQuot` negated a floor and gave -0.0: corrected here).
      let q := a.toDouble / b.toDouble
      if q.abs ≥ 9223372036854775808.0 then
        -- past the long range: `new BigDecimal(q).toBigInteger().doubleValue()`, q itself
        .num (.dbl (if q < 0.0 then -((-q).floor) else q.floor))
      else
        let t : Int := if q < 0.0 then -((-q).floor.toUInt64.toNat : Int) else (q.floor.toUInt64.toNat : Int)
        .num (.dbl (Float.ofInt t))
    else cRem a b
  | _ => if isQuot then cQuot a b else cRem a b

/-- Clojure 1.12's answer to `(op a b)`. `static` is the literal path (the compiler picks
`Numbers.divide(Object, double)` for a double literal: no zero check). -/
def cAnswer (op : Op) (a b : CV) (static : Bool) : CR :=
  match op with
  | .add => cArith .add a b
  | .sub => match cNegate b with
    | .error e => .err e
    | .ok nb => cArith .add a nb
  | .mul => cArith .mul a b
  | .div =>
    match static, a, b with
    | true, _, .dbl y => .num (.dbl (a.toDouble / y))
    | true, .dbl x, _ => .num (.dbl (x / b.toDouble))
    | _, _, _ => cArith .div a b
  | .quot => cQuotRem true a b
  | .rem => cQuotRem false a b
  | .compare => match cCompare a b with | some i => .int i | none => .err "Non-terminating decimal expansion; no exact representable decimal result."
  | .equiv => match cEquiv a b with | some x => .bool x | none => .err "Non-terminating decimal expansion; no exact representable decimal result."
  | .equal => match cEqual a b with | some x => .bool x | none => .err "Non-terminating decimal expansion; no exact representable decimal result."
  | .lt => match cLt a b with | some x => .bool x | none => .err "Non-terminating decimal expansion; no exact representable decimal result."
  | .max | .min =>
    -- Numbers.max/min(Object, Object): NaN first, then `gt(x, y) ? x : y` / `lt(x, y) ? x : y`.
    let isNaN := fun (v : CV) => match v with | .dbl x => x.isNaN | _ => false
    if isNaN a then .num a else if isNaN b then .num b
    else
      let r := if op == .max then cLt b a else cLt a b
      match r with
      | some true => .num a
      | some false => .num b
      | none => .err "Non-terminating decimal expansion; no exact representable decimal result."

/-- Clojure's unary answers on one number. -/
inductive UOp where
  | str | hash | inc | dec | neg | abs | bigdec | long | double | bigint
  deriving BEq, Repr, Inhabited

def UOp.name : UOp → String
  | .str => "str" | .hash => "hash" | .inc => "inc" | .dec => "dec" | .neg => "-" | .abs => "abs"
  | .bigdec => "bigdec" | .long => "long" | .double => "double" | .bigint => "bigint"

def uops : List UOp := [.str, .hash, .inc, .dec, .neg, .abs, .bigdec, .long, .double, .bigint]

def cUnary (op : UOp) (a : CV) : CR :=
  match op, a with
  | .str, v => .str v.str
  | .hash, .dec d => .int (cljHashDec d)
  | .hash, _ => .err "not modeled"
  | .inc, .dec d => .num (.dec (d.add ⟨1, 0⟩))
  | .dec, .dec d => .num (.dec (d.sub ⟨1, 0⟩))
  | .neg, .dec d => .num (.dec d.neg)
  | .abs, .dec d => .num (.dec d.abs)
  | .bigdec, v => cBigdec v
  | .long, v => match cLong v with | .int i => .num (.long i) | r => r
  | .double, v => cDouble v
  | .bigint, v => cBigint v
  | _, _ => .err "not modeled"

/-! ## jank -/

/-- `rem` (math.cpp 223-304): `jRem` of round 3, with the division by zero of each branch. -/
def jRemZ (a b : JV) : JR :=
  let zero := match b with
    | .long v | .big v => v == 0 | .dbl x => x == 0.0 | .dec d => d.iszero | .ratio n _ => n == 0
  -- the double branch checks inside `rem(f64, f64)`; the ratio branch, `r.numerator == 0`;
  -- the decimal and integer branches, `typed_r->data == 0`: each throws a std::runtime_error.
  if zero then .err "Division by zero is not permitted." else jRem a b

/-- jank's answer to `(op a b)` today. -/
def jAnswer (op : Op) (a b : JV) : JR :=
  match op with
  | .add => jArith .add a b
  | .sub => jArith .sub a b
  | .mul => jArith .mul a b
  | .div => jArith .div a b
  | .quot => jQuot a b
  | .rem => jRemZ a b
  | .compare => match jCompare a b with | some i => .int i | none => .err "not modeled"
  | .equiv => .bool (jEquiv a b)
  | .equal => .bool (jEqual a b)
  | .lt => match jLt a b with | some x => .bool x | none => .err "not modeled"
  | .max | .min =>
    -- math.hpp max: `l < r ? r : l`; min: `l < r ? l : r` (both operands objects here).
    match jLt a b with
    | some lt => .num (if op == .max then (if lt then b else a) else (if lt then a else b))
    | none => .err "not modeled"

/-- An exact rational value of a jank number (none for a double or a non-finite decimal). -/
def jRat : JV → Option (Int × Nat)
  | .long v | .big v => some (v, 1)
  | .dec d => d.rat
  | .ratio n d => some (n, d.toNat)
  | .dbl _ => none

/-- The exact decimal text of a terminating quotient `c · 10^-k` (for `rd_string`). -/
def decText (c : Int) (k : Int) : String :=
  let digits := toString c.natAbs
  let sign := if c < 0 then "-" else ""
  s!"{sign}{digits}e{-k}"

/-- The coordinator's exact division (fixes/S2.diff, being written): the exact quotient when it
terminates, stored into `cpp_dec_float<100>` (modeled as reading its exact text with `rd_string`:
at most 128 significant digits are kept, as for a literal, S4), else the throw. A zero divisor and
a double operand keep today's path (the fix's text decides those). -/
def jDivFixed (a b : JV) : JR :=
  match jRat a, jRat b with
  | some (p, q), some (p', q') =>
    if p' == 0 then jArith .div a b
    else
      -- a/b = (p·q') / (q·p')
      let n := p * q'
      let d := (q : Int) * p'
      let (n, d) := if d < 0 then (-n, -d) else (n, d)
      match Java.terminating n d.toNat with
      | none => .err "Non-terminating decimal expansion; no exact representable decimal result."
      | some (c, k) =>
        match rdString (bytes (decText c k)) with
        | .ok x => .num (.dec x)
        | .error e => .err e
  | _, _ => jArith .div a b

/-- jank's answer with exact division (S2's fix) and nothing else changed. -/
def jAnswerFixed (op : Op) (a b : JV) : JR :=
  match op with
  | .div => jDivFixed a b
  | _ => jAnswer op a b

def jUnary (op : UOp) (a : JV) : JR :=
  match op, a with
  | .str, v => .str v.str
  | .hash, v => .int (jHash v).toNat
  -- math.hpp inc/dec object branch (1186-1340): `make_box(typed_l->data + 1ll)` (- for dec).
  | .inc, .dec d => .num (.dec (d.add (ofLL 1)))
  | .dec, .dec d => .num (.dec (d.sub (ofLL 1)))
  -- `(- x)` is `(- 0 x)` (core.jank 1393): `0 − data`, round 3's decOpL.
  | .neg, v => jArith .sub (.long 0) v
  -- math.hpp abs (994-1040) object branch: `data < 0ll ? make_box(-1ll * data) : ...`
  | .abs, .dec d => .num (.dec (if dlt d zero then d.mul (ofLL (-1)) else d))
  | .bigdec, v => jBigdec v
  | .long, v => match jLong v with | .int i => .num (.long i) | r => r
  | .double, v => jDouble v
  | .bigint, v => jBigint v
  | _, _ => .err "not modeled"

/-! ## Comparing the answers -/

/-- How a disagreement shows. -/
inductive Verdict where
  | agree
  /-- Same kind and value, different text: the scale (R72), or the notation (S5). -/
  | text
  /-- Same kind, different value (S2, S4, S7). -/
  | value
  /-- A different kind (D4's long quotient, S6's decimal with a double, V57's tie). -/
  | kind
  /-- One throws, the other does not. -/
  | throws
  /-- Both booleans or ints, different. -/
  | other
  deriving BEq, Repr, Inhabited

def verdict (j c : Out) : Verdict :=
  match j, c with
  | .err _, .err _ => .agree
  | .err _, _ | _, .err _ => .throws
  | .num jk jt jv, .num ck ct cv =>
    if jk != ck then .kind
    else if jt == ct then .agree
    else
      let sameV := match jv, cv with
        | some a, some b => ratEq a b
        | none, none => true
        | _, _ => false
      if sameV then .text else .value
  | .bool a, .bool b => if a == b then .agree else .other
  | .int a, .int b => if a == b then .agree else .other
  | _, _ => .other

/-- Whether a text-only disagreement is the notation (one side scientific). -/
def isNotation (j c : Out) : Bool :=
  match j, c with
  | .num _ jt _, .num _ ct _ => (jt.contains 'e') != (ct.contains 'E')
  | _, _ => false

end Jank.R7.Num.Dec
