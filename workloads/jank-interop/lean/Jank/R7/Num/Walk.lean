import Jank.R7.Num.Dec
import Jank.R3.Boost.Tables

/-!
# Round 7, numbers: the BigDecimal walk

Every question is a Clojure form over literal values (at least one a BigDecimal), run three ways:
- on Clojure 1.12.3 (the forms are written to `.r7-scratch/num/walk/walk.clj`, run through the job
  slots, answers read back from `walk.out`);
- on the Java/Clojure model (`Dec.cAnswer`): any difference from the JVM is a model error;
- on jank's replica today (`Dec.jAnswer`) and with exact division only (`Dec.jAnswerFixed`).
Both paths are written for Clojure: the literal call and the call through a fn value (they differ
only where the compiler picks a primitive-double overload: `(/ 1M 0.0)`). In jank a BigDecimal is
always an object, and a long or double literal reaching math.hpp with it takes boost's mixed
operators, the same as its boxed form (round 3's `jArith`), so jank's answer is one per form.
-/

namespace Jank.R7.Num.Walk

open Jank.R3.Boost Jank.R3.Boost.Num Jank.R3.Boost.Java Jank.R7.Num.Dec

def decTexts : List String :=
  ["0M", "0.00M", "1M", "1.0M", "1.50M", "2.5M", "7.5M", "-7.5M", "100M", "1E+2M", "0.1M",
   "0.001M", "3M", "6M", "12345.6789M", "1E+130M", "1E-7M", "0.5M", "2M"]

def otherTexts : List String :=
  ["0", "1", "2", "3", "4", "-2", "2N", "5N", "1/2", "1/3", "1/4", "3/2", "0.5", "2.0", "0.0"]

structure Val where
  text : String
  j : JV
  c : CV

def mkVal (t : String) : Option Val :=
  match Tables.jankLiteral t, Tables.cljLiteral t with
  | .ok j, .ok c => some ⟨t, j, c⟩
  | _, _ => none

def isDec (v : Val) : Bool := match v.c with | .dec _ => true | _ => false

def vals : List Val := (decTexts ++ otherTexts).filterMap mkVal

/-- A question: an operator on two values, or a unary operator on one. -/
inductive Q where
  | bin (op : Op) (a b : Val) (static : Bool)
  | un (op : UOp) (a : Val)

def Q.form : Q → String
  | .bin op a b true => s!"({op.name} {a.text} {b.text})"
  | .bin op a b false => s!"((fn [a b] ({op.name} a b)) {a.text} {b.text})"
  | .un op a => s!"({op.name} {a.text})"

def Q.path : Q → String
  | .bin _ _ _ true => "literals" | .bin _ _ _ false => "fn" | .un _ _ => "literal"

def questions : Array Q := Id.run do
  let mut out := #[]
  for op in ops do
    for a in vals do
      for b in vals do
        if isDec a || isDec b then
          out := out.push (.bin op a b true)
          out := out.push (.bin op a b false)
  for a in vals do
    for op in uops do
      if isDec a || op == .bigdec then out := out.push (.un op a)
  return out

/-- The model's Clojure answer and jank's two answers. -/
def Q.clj : Q → Out
  | .bin op a b s => crOut (cAnswer op a.c b.c s)
  | .un op a => crOut (cUnary op a.c)

def Q.jank : Q → Out
  | .bin op a b _ => jrOut (jAnswer op a.j b.j)
  | .un op a => jrOut (jUnary op a.j)

def Q.jankFixed : Q → Out
  | .bin op a b _ => jrOut (jAnswerFixed op a.j b.j)
  | .un op a => jrOut (jUnary op a.j)

def Q.opName : Q → String
  | .bin op .. => op.name | .un op _ => op.name

/-- The JVM's encoding of an answer (written by walk.clj's `enc`). -/
def _root_.Jank.R7.Num.Dec.Out.enc : Out → String
  | .num k t _ => s!"num\t{k}\t{t}"
  | .bool b => s!"bool\t{b}"
  | .int i => s!"int\t{i}"
  | .err _ => "err"

/-- The Clojure program: one line of output per question, `id<TAB>encoding`. -/
def cljProgram (qs : Array Q) : String := Id.run do
  let header := "(defn kind [v] (cond (instance? Long v) \"long\" (instance? Double v) \"double\"
  (instance? clojure.lang.BigInt v) \"BigInt\" (instance? java.math.BigDecimal v) \"BigDecimal\"
  (instance? clojure.lang.Ratio v) \"Ratio\" :else (.getSimpleName (class v))))
(defn enc [f] (try (let [v (f)] (cond (instance? Boolean v) (str \"bool\\t\" v)
  (instance? Integer v) (str \"int\\t\" v) (string? v) (str \"num\\tString\\t\" v)
  :else (str \"num\\t\" (kind v) \"\\t\" (pr-str v))))
  (catch Throwable t (str \"err\\t\" (.getMessage t)))))
"
  let mut s := header
  let mut i := 0
  for q in qs do
    s := s ++ s!"(println \"{i}\" (enc (fn [] {q.form})))\n"
    i := i + 1
  return s

/-- `str` answers are encoded as strings by both. -/
def _root_.Jank.R7.Num.Dec.Out.encS : Out → String
  | .num "String" t _ => s!"num\tString\t{t}"
  | o => o.enc

/-- Parse walk.out: `id answer`. An error line keeps only "err". -/
def parseOut (txt : String) : Std.HashMap Nat String := Id.run do
  let mut m : Std.HashMap Nat String := {}
  for line in txt.splitOn "\n" do
    match line.splitOn " " with
    | idS :: rest =>
      match idS.toNat? with
      | some i =>
        let a := " ".intercalate rest
        m := m.insert i (if a.startsWith "err" then "err" else a)
      | none => pure ()
    | [] => pure ()
  return m

end Jank.R7.Num.Walk
