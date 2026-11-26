import Jank.R6.Num.Int
import Jank.R6.Num.MinMax

/-!
# Round 6, numbers: complete walks

The integer walk: every operator below × every pair of values from `ints` × every pair of
sources (literal / literal through a fn / computed value through a fn), compared with Clojure's
answer on the same path. The value set holds each boundary that changes a C++ type or a check:
0, ±1, ±2, ±3, 65536, i32 max/min and their neighbours, 2^32, 3037000500 (√2^63), i64 max/min
and their neighbours, and three BigInts.
-/

namespace Jank.R6.Num.Search

open Jank.R6.Num Jank.Numbers

def i64minI : Int := -9223372036854775808

def ints : List CInt :=
  [.long 0, .long 1, .long (-1), .long 2, .long (-2), .long 3, .long (-3), .long 65536,
   .long 2147483647, .long (-2147483647), .long (-2147483648), .long 2147483648, .long (-2147483649),
   .long 4294967296, .long 3037000500, .long (-3037000500),
   .long 9223372036854775807, .long 9223372036854775806, .long i64minI, .long (i64minI + 1),
   .big 1, .big (-1), .big 9223372036854775808]

def srcs : List Src := [.lit, .fnLit, .fnVal]

/-- The literal -2147483648 is typed `int` by the analyzer but emitted as a C++ `long` (round 3's
correction); a computed value is not a literal. Those questions are left out. -/
def admissible (x : CInt) (s : Src) : Bool :=
  match x, s with
  | .long v, .lit => v != -2147483648
  | .long v, .fnLit => v != -2147483648
  | .big _, .fnVal => false   -- a BigInt reaches a fn from a literal: fnLit covers it
  | _, _ => true

def _root_.Jank.R6.Num.CInt.text : CInt → String
  | .long v => if v == i64minI then "-9223372036854775808" else toString v
  | .big v => s!"{v}N"

/-- How a computed value is written: a value the reader would otherwise mangle (R5) is computed. -/
def valText (x : CInt) : String :=
  match x with
  | .long v => if v == i64minI then "(dec' -9223372036854775807)" else s!"(identity {v})"
  | .big v => s!"{v}N"

def argText (x : CInt) (s : Src) : String :=
  match s with
  | .lit | .fnLit => x.text
  | .fnVal => valText x

inductive IOp where
  | bin (op : Op) | binP (op : Op) | neg | inc | dec | incP | decP | abs | quot | rem
  deriving Repr, BEq, Inhabited

def IOp.name : IOp → String
  | .bin .add => "+" | .bin .sub => "-" | .bin .mul => "*"
  | .binP .add => "+'" | .binP .sub => "-'" | .binP .mul => "*'"
  | .neg => "-" | .inc => "inc" | .dec => "dec" | .incP => "inc'" | .decP => "dec'"
  | .abs => "abs" | .quot => "quot" | .rem => "rem"

def IOp.unary : IOp → Bool
  | .neg | .inc | .dec | .incP | .decP | .abs => true
  | _ => false

def ops : List IOp :=
  [.bin .add, .bin .sub, .bin .mul, .binP .add, .binP .sub, .binP .mul, .neg, .inc, .dec,
   .incP, .decP, .abs, .quot, .rem]

def _root_.Jank.R6.Num.Rep.toJNum : Rep → JNum
  | .i32 v => .small (BitVec.ofInt 32 v)
  | .i64 v => .int (BitVec.ofInt 64 v)
  | .big v => .big v

/-- jank's `quot` (math.cpp 321-345, through doubles; x86-64's out-of-range cast). -/
def jQuot (a b : Rep) : Out :=
  match jankQuot .x86_64 a.toJNum b.toJNum with
  | .ok (.small v) => .ok (.long v.toInt)
  | .ok (.int v) => .ok (.long v.toInt)
  | .ok _ => .error "unreachable"
  | .error e => .error e

/-- Clojure `quot`: LongOps.quotient (Java `/`, MIN / -1 = MIN), BigIntOps.quotient. -/
def cQuot (x y : CInt) : Out :=
  if y.val == 0 then .error "Divide by zero"
  else match x, y with
    | .long a, .long b => .ok (.long (if a == i64minI && b == -1 then a else a.tdiv b))
    | _, _ => .ok (.big (x.val.tdiv y.val))

/-- jank's and Clojure's answers to one question. -/
def answer (op : IOp) (x y : CInt) (sx sy : Src) : Out × Out :=
  let rx := jRep x sx
  let ry := jRep y sy
  let static := staticPath x y sx sy
  match op with
  | .bin o => (.ok (jArith o rx ry), cArith o x y static)
  | .binP o => (.ok (jArithP o rx ry), cArithP o x y static)
  | .neg => (.ok (jNeg rx), cNeg x)
  | .inc => (jIncDec true rx, cIncDec true x)
  | .dec => (jIncDec false rx, cIncDec false x)
  | .incP => (.ok (jIncDecP true rx), cIncDecP true x)
  | .decP => (.ok (jIncDecP false rx), cIncDecP false x)
  | .abs => (.ok (jAbs rx), .ok (cAbs x))
  | .quot => (jQuot rx ry, cQuot x y)
  | .rem => (jRem rx ry, cRem x y)

/-- The program for one question, in the shape the path needs. -/
def program (op : IOp) (x y : CInt) (sx sy : Src) : String :=
  let ax := argText x sx
  let ay := argText y sy
  if op.unary then
    if sx == .lit then s!"({op.name} {ax})" else s!"((fn [a] ({op.name} a)) {ax})"
  else
    match sx == .lit, sy == .lit with
    | true, true => s!"({op.name} {ax} {ay})"
    | true, false => s!"((fn [b] ({op.name} {ax} b)) {ay})"
    | false, true => s!"((fn [a] ({op.name} a {ay})) {ax})"
    | false, false => s!"((fn [a b] ({op.name} a b)) {ax} {ay})"

def repClass : Rep → String
  | .i32 _ => "int" | .i64 _ => "long" | .big _ => "BigInt"

structure Row where
  op : IOp
  x : CInt
  y : CInt
  sx : Src
  sy : Src
  j : Out
  c : Out
  v : Verdict

def walk : Array Row := Id.run do
  let mut out := #[]
  for op in ops do
    for x in ints do
      for sx in srcs do
        if !admissible x sx then continue
        if op.unary then
          let (j, c) := answer op x x sx sx
          out := out.push ⟨op, x, x, sx, sx, j, c, verdict j c⟩
        else
          for y in ints do
            for sy in srcs do
              if !admissible y sy then continue
              let (j, c) := answer op x y sx sy
              out := out.push ⟨op, x, y, sx, sy, j, c, verdict j c⟩
  return out

def Row.repPair (r : Row) : String :=
  if r.op.unary then repClass (jRep r.x r.sx)
  else s!"{repClass (jRep r.x r.sx)}×{repClass (jRep r.y r.sy)}"

def Row.pathName (r : Row) : String :=
  let one := fun (s : Src) => match s with | .lit => "lit" | .fnLit => "fn(lit)" | .fnVal => "fn(val)"
  if r.op.unary then one r.sx else s!"{one r.sx},{one r.sy}"

def Row.line (r : Row) : String :=
  s!"{program r.op r.x r.y r.sx r.sy}  [{r.repPair}; {r.pathName}]  jank {showOut r.j}  Clojure {showOut r.c}  {reprStr r.v}"

/-! ## The fixed jank (fixes/LG2a.diff + fixes/R5.diff) on the same walk -/

def answerFixed (op : IOp) (x y : CInt) (sx sy : Src) : Out :=
  let rx := jRepFixed x sx
  let ry := jRepFixed y sy
  match op with
  | .bin o => jArithFixed o rx ry
  | .binP o => .ok (jArithP o rx ry)
  | .neg => jArithFixed .sub (.i32 0) rx
  | .inc => jIncDec true rx
  | .dec => jIncDec false rx
  | .incP => .ok (jIncDecP true rx)
  | .decP => .ok (jIncDecP false rx)
  | .abs => .ok (jAbs rx)
  | .quot => jQuot rx ry
  | .rem => jRem rx ry

end Jank.R6.Num.Search
