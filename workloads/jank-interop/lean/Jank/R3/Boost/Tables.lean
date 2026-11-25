import Jank.R3.Boost.Num
import Jank.Lex

/-!
# Round 3, Boost: operand universe and the questions asked of it

Each operand is written as a Clojure literal; jank reads it through round 2's lexer replica
(`Jank.Lex.tokens`: the token's kind and literal text) and this round's boost replica for the
value (`rd_string` for `M`, `big_integer(s, radix, neg)` for `N`/ERANGE integers, cpp_int
arithmetic for ratios); Clojure reads it with LispReader `matchNumber` semantics
(`new BigDecimal(s)` keeps the scale).
-/

namespace Jank.R3.Boost.Tables

open Jank.R3.Boost Jank.R3.Boost.Dec Jank.R3.Boost.Java Jank.R3.Boost.Num

structure Operand where
  src : String
  j : JV
  c : CV
  deriving Inhabited

def litBytes (s : String) : List Nat := s.toUTF8.toList.map (·.toNat)

/-- jank's reading of a number literal: the first token of round 2's lexer, then the boost
replica for its value. -/
def jankLiteral (src : String) : Except String JV :=
  if src == "##Inf" then .ok (.dbl (1.0/0.0)) else if src == "##-Inf" then .ok (.dbl (-1.0/0.0))
  else if src == "##NaN" then .ok (.dbl (0.0/0.0)) else
  match Jank.Lex.tokens src.toUTF8.toList.toArray with
  | .tok t :: _ =>
    match t.kind, t.data with
    | .integer, .int v => .ok (.long v)
    | .real, .real d =>
      .ok (.dbl (Ieee.strtodDec d.neg d.mant d.exp))
    | .bigInteger, .big lit radix neg =>
      match bigCreate (lit.map (·.toNat)) radix neg with
      | .ok v => .ok (.big v) | .error e => .error e
    | .bigDecimal, .bigdec lit =>
      match rdString (lit.map (·.toNat)) with
      | .ok d => .ok (.dec d) | .error e => .error e
    | .ratio, .ratio n d =>
      match ratioCreate n d with
      | .ok v => .ok v | .error e => .error e
    | k, _ => .error s!"token {reprStr k}"
  | .err m :: _ => .error m
  | _ => .error "no token"

/-- Clojure's reading (matchNumber): `…M` is `new BigDecimal(s)`, `…N` a BigInt, `n/d` a
reduced Ratio (BigInt when integral), else a long or a double. -/
def cljLiteral (src : String) : Except String CV :=
  if src == "##Inf" then .ok (.dbl (1.0/0.0)) else if src == "##-Inf" then .ok (.dbl (-1.0/0.0))
  else if src == "##NaN" then .ok (.dbl (0.0/0.0)) else
  let cs := litBytes src
  if cs.getLast? == some 77 then
    match BD.ofString cs.dropLast with | .ok d => .ok (.dec d) | .error e => .error e
  else if cs.getLast? == some 78 then
    match bigIntegerOfString cs.dropLast with | .ok v => .ok (.big v) | .error e => .error e
  else if cs.contains 47 then
    let (a, b) := cs.span (· != 47)
    match bigIntegerOfString a, bigIntegerOfString (b.drop 1) with
    | .ok n, .ok d => match cljDivide n d with | .ok v => .ok v | .error e => .error e
    | _, _ => .error "ratio"
  else if cs.any (fun c => c == 46 || c == 101 || c == 69) then
    match BD.ofString cs with
    | .ok d => .ok (.dbl d.toDouble)
    | .error e => .error e
  else
    match bigIntegerOfString cs with
    | .ok v => .ok (if CppInt.fitsI64 v then .long v else .big v)
    | .error e => .error e

def mkOperand (src : String) : Operand :=
  match jankLiteral src, cljLiteral src with
  | .ok j, .ok c => ⟨src, j, c⟩
  | _, _ => ⟨src, .long 0, .long 0⟩

def operandSrcs : List String :=
  ["0", "1", "-1", "3", "9007199254740993", "9223372036854775807",
   "0.1", "0.5", "-1.5", "1.0E23", "9.007199254740992E15", "##Inf", "##NaN",
   "0N", "1N", "-7N", "3N", "9007199254740993N", "18446744073709551616N", "100000000000000000000000000000N",
   "0M", "1M", "1.50M", "0.1M", "-2.5M", "3M", "6M", "0.00001M", "1E130M", "123456789.123456789M",
   "9007199254740993.00000000000000000001M", "1.0000000000000000001M", "1.75M",
   "1/2", "-7/3", "1/3", "100000000000000000000/3"]

def operands : List Operand := operandSrcs.map mkOperand

def _root_.Jank.R3.Boost.Num.JV.boost : JV → Bool | .big _ | .dec _ => true | _ => false

/-! ## Questions -/

inductive Q where
  | arith (op : AOp) (a b : Operand)
  | lt (a b : Operand)
  | le (a b : Operand)
  | cmp (a b : Operand)
  | equiv (a b : Operand)
  | equal (a b : Operand)
  | hashEq (a b : Operand)
  | quot (a b : Operand)
  | rem (a b : Operand)
  | str (a : Operand)
  | prStr (a : Operand)
  | toDouble (a : Operand)
  | toLong (a : Operand)
  | bigdec (a : Operand)
  | bigint (a : Operand)
  deriving Inhabited

def Q.name : Q → String
  | .arith op .. => op.sym | .lt .. => "<" | .le .. => "<=" | .cmp .. => "compare" | .equiv .. => "=="
  | .equal .. => "=" | .hashEq .. => "hash" | .quot .. => "quot" | .rem .. => "rem" | .str _ => "str"
  | .prStr _ => "pr-str" | .toDouble _ => "double" | .toLong _ => "long" | .bigdec _ => "bigdec"
  | .bigint _ => "bigint"

def Q.program : Q → String
  | .arith op a b => s!"({op.sym} {a.src} {b.src})"
  | .lt a b => s!"(< {a.src} {b.src})" | .le a b => s!"(<= {a.src} {b.src})"
  | .cmp a b => s!"(compare {a.src} {b.src})" | .equiv a b => s!"(== {a.src} {b.src})"
  | .equal a b => s!"(= {a.src} {b.src})"
  | .hashEq a b => s!"(= (hash {a.src}) (hash {b.src})) given (= {a.src} {b.src})"
  | .quot a b => s!"(quot {a.src} {b.src})" | .rem a b => s!"(rem {a.src} {b.src})"
  | .str a => s!"(str {a.src})" | .prStr a => s!"(pr-str {a.src})" | .toDouble a => s!"(double {a.src})"
  | .toLong a => s!"(long {a.src})" | .bigdec a => s!"(bigdec {a.src})" | .bigint a => s!"(bigint {a.src})"

/-- An answer, as both sides' printed results plus whether they agree. -/
structure Answer where
  jank : String
  clj : String
  agree : Bool

def optB : Option Bool → String | some b => toString b | none => "throws"
def optI : Option Int → String | some b => toString b | none => "throws"

/-- Results compared: numbers by kind and value; doubles by bits. -/
def numAgree (j : JR) (c : CR) : Bool :=
  match j, c with
  | .num a, .num b => sameNum a b
  | .int a, .int b => a == b
  | .bool a, .bool b => a == b
  | .err _, .err _ => true
  | _, _ => false

def Q.answer : Q → Answer
  | .arith op a b =>
    let j := jArith op a.j b.j
    let c := cArith op a.c b.c
    ⟨j.show, c.show, numAgree j c⟩
  | .lt a b => let j := jLt a.j b.j; let c := cLt a.c b.c; ⟨optB j, optB c, j == c⟩
  | .le a b => let j := jLe a.j b.j; let c := cLe a.c b.c; ⟨optB j, optB c, j == c⟩
  | .cmp a b => let j := jCompare a.j b.j; let c := cCompare a.c b.c; ⟨optI j, optI c, j == c⟩
  | .equiv a b => let j := jEquiv a.j b.j; let c := cEquiv a.c b.c; ⟨toString j, optB c, some j == c⟩
  | .equal a b => let j := jEqual a.j b.j; let c := cEqual a.c b.c; ⟨toString j, optB c, some j == c⟩
  | .hashEq a b =>
    -- Clojure: = implies equal hashes. jank: when jank's = holds, do the hashes agree?
    let eq := jEqual a.j b.j
    let same := jHash a.j == jHash b.j
    ⟨s!"= {eq}, hashes {jHash a.j} {jHash b.j}", "hashes equal", !eq || same⟩
  | .quot a b => let j := jQuot a.j b.j; let c := cQuot a.c b.c
    let ok := match j, c with
      | .int x, .num (.big y) => x == y   -- the type differs (long vs BigInt): D4's class
      | _, _ => numAgree j c
    ⟨j.show, c.show, ok⟩
  | .rem a b => let j := jRem a.j b.j; let c := cRem a.c b.c; ⟨j.show, c.show, numAgree j c⟩
  | .str a => ⟨a.j.str, a.c.str, a.j.str == a.c.str⟩
  | .prStr a => ⟨a.j.prStr, a.c.prStr, a.j.prStr == a.c.prStr⟩
  | .toDouble a => let j := jDouble a.j; let c := cDouble a.c; ⟨j.show, c.show, numAgree j c⟩
  | .toLong a => let j := jLong a.j; let c := cLong a.c; ⟨j.show, c.show, numAgree j c⟩
  | .bigdec a => let j := jBigdec a.j; let c := cBigdec a.c; ⟨j.show, c.show, numAgree j c⟩
  | .bigint a => let j := jBigint a.j; let c := cBigint a.c; ⟨j.show, c.show, numAgree j c⟩

/-- The binary questions over pairs with at least one BigInt/BigDecimal operand. -/
def binaryQs : List Q := Id.run do
  let mut out : Array Q := #[]
  for a in operands do
    for b in operands do
      if a.j.boost || b.j.boost then
        for op in [AOp.add, .sub, .mul, .div] do out := out.push (.arith op a b)
        out := out ++ #[.lt a b, .le a b, .cmp a b, .equiv a b, .equal a b, .hashEq a b, .quot a b]
        -- `rem` with a double operand is math.cpp's `std::fmod` path (doubles, not boost).
        let isD : JV → Bool := fun | .dbl _ => true | _ => false
        if !(isD a.j || isD b.j) then out := out.push (.rem a b)
  return out.toList

def unaryQs : List Q := Id.run do
  let mut out : Array Q := #[]
  for a in operands do
    let isD : JV → Bool := fun | .dbl _ => true | _ => false
    -- Printing of doubles is round 2's R68 (string_builder's to_chars), not boost.
    if !isD a.j then out := out ++ #[.str a, .prStr a]
    out := out ++ #[.toDouble a, .toLong a, .bigdec a, .bigint a]
  return out.toList

end Jank.R3.Boost.Tables
