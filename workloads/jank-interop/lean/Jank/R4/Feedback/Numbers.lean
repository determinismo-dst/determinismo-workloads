import Jank.R3.Boost.Tables
import Jank.R3.Codegen.Literals

/-!
# Round 4, feedback: S2, S9 and S44 run as their round-3 tests were written

The real jank (7135b7708) passed round 3's tests for S2 (`(/ 6M 3M)`), S9 (`(bigdec 0.1)`) and
S44 (`eval` of a quoted object's metadata). This file runs each test's exact forms through the
round-3 replicas, to tell whether the replica or the test departed from jank's code:

- **S2, S9.** Each test compared with `=`. jank's `=` on two BigDecimals is `big_decimal::equal`
  (obj/big_decimal.cpp 146-155: `abs(data - o.data) < numeric_limits<f64>::epsilon()`, round 1's
  D8), reached through core/equal.cpp 19-22 (`lhs.equal(rhs)`). The replica's `jEqual` has that
  epsilon. Run on the tests' forms, the replica answers `true`: it predicted that both tests pass.
  The deviations themselves (the values) are observed through `compare` (big_decimal.cpp 182-190,
  boost's exact `<`) and `str`, which the round-4 tests use.
- **S44.** The test gave the vector the metadata `{:m 1}`. `strip_source_from_meta`
  (core/meta.cpp 229-239) dissocs `:jank/source` and turns an empty result into nil, so `{:m 1}`
  stays `{:m 1}` (round 3's own theorem `strip_changes_iff`). The prediction is about `{}` (and any
  map holding `:jank/source`); the round-4 test uses `{}` and `{:jank/source 1 :m 1}`.
-/

namespace Jank.R4.Feedback.Numbers

open Jank.R3.Boost Jank.R3.Boost.Dec Jank.R3.Boost.Java Jank.R3.Boost.Num Jank.R3.Boost.Tables

/-- A literal read by both sides (round 3's readers). -/
def lit (s : String) : Operand := mkOperand s

/-- One observation: the form, jank's answer by the replica, Clojure's answer, and whether they
agree. -/
structure Obs where
  form : String
  jank : String
  clj : String
  deriving Inhabited

def Obs.agree (o : Obs) : Bool := o.jank == o.clj

def showB : Bool → String := toString
def showOB : Option Bool → String | some b => toString b | none => "throws"
def showOI : Option Int → String | some i => toString i | none => "throws"

def jNum : JR → Option JV | .num v => some v | _ => none
def cNum : CR → Option CV | .num v => some v | _ => none

/-- `(= a (op b c))` as the round-3 test wrote it. -/
def eqOfArith (a : String) (op : AOp) (b c : String) : Obs :=
  let A := lit a; let B := lit b; let C := lit c
  let j := (jNum (jArith op B.j C.j)).map (jEqual A.j)
  let k := (cNum (cArith op B.c C.c)).bind (cEqual A.c)
  { form := s!"(= {a} ({op.sym} {b} {c}))", jank := showOB j, clj := showOB k }

/-- `(compare a (op b c))`. -/
def cmpOfArith (a : String) (op : AOp) (b c : String) : Obs :=
  let A := lit a; let B := lit b; let C := lit c
  let j := (jNum (jArith op B.j C.j)).bind (jCompare A.j)
  let k := (cNum (cArith op B.c C.c)).bind (cCompare A.c)
  { form := s!"(compare {a} ({op.sym} {b} {c}))", jank := showOI j, clj := showOI k }

/-- `(= (str a) (str (op b c)))`. -/
def strOfArith (a : String) (op : AOp) (b c : String) : Obs :=
  let A := lit a; let B := lit b; let C := lit c
  let j := (jNum (jArith op B.j C.j)).map (fun v => A.j.str == v.str)
  let k := (cNum (cArith op B.c C.c)).map (fun v => A.c.str == v.str)
  { form := s!"(= (str {a}) (str ({op.sym} {b} {c})))", jank := showOB j, clj := showOB k }

/-- `(str (op b c))` on each side, for the report. -/
def valOfArith (op : AOp) (b c : String) : Obs :=
  let B := lit b; let C := lit c
  { form := s!"(str ({op.sym} {b} {c}))"
    jank := match jArith op B.j C.j with | .num v => v.str | r => JR.show r
    clj := match cArith op B.c C.c with | .num v => v.str | r => r.show }

/-- `(= a (bigdec x))`, `(compare a (bigdec x))`, `(str (bigdec x))`. -/
def eqOfBigdec (a x : String) : Obs :=
  let A := lit a; let X := lit x
  { form := s!"(= {a} (bigdec {x}))"
    jank := showOB ((jNum (jBigdec X.j)).map (jEqual A.j))
    clj := showOB ((cNum (cBigdec X.c)).bind (cEqual A.c)) }

def cmpOfBigdec (a x : String) : Obs :=
  let A := lit a; let X := lit x
  { form := s!"(compare {a} (bigdec {x}))"
    jank := showOI ((jNum (jBigdec X.j)).bind (jCompare A.j))
    clj := showOI ((cNum (cBigdec X.c)).bind (cCompare A.c)) }

def strOfBigdec (a x : String) : Obs :=
  let A := lit a; let X := lit x
  { form := s!"(= (str {a}) (str (bigdec {x})))"
    jank := showOB ((jNum (jBigdec X.j)).map (fun v => A.j.str == v.str))
    clj := showOB ((cNum (cBigdec X.c)).map (fun v => A.c.str == v.str)) }

def valOfBigdec (x : String) : Obs :=
  let X := lit x
  { form := s!"(str (bigdec {x}))"
    jank := match jBigdec X.j with | .num v => v.str | r => JR.show r
    clj := match cBigdec X.c with | .num v => v.str | r => r.show }

/-- Round 3's S2 and S9 tests, as written (each `is` form). -/
def round3Tests : List Obs :=
  [eqOfArith "2M" .div "6M" "3M", eqOfArith "0.5M" .div "3" "6M", eqOfBigdec "0.1M" "0.1"]

/-- Round 4's observations of the same values. -/
def round4Tests : List Obs :=
  [ cmpOfArith "2M" .div "6M" "3M", strOfArith "2M" .div "6M" "3M"
  , cmpOfArith "0.5M" .div "3" "6M", strOfArith "0.5M" .div "3" "6M"
  , cmpOfArith "0.5M" .div "1.5M" "3"
  , cmpOfBigdec "0.1M" "0.1", strOfBigdec "0.1M" "0.1"
  , valOfArith .div "6M" "3M", valOfArith .div "3" "6M", valOfBigdec "0.1" ]

/-! ## S44 -/

open Jank.R3.Codegen.Literals in
/-- Round 3's S44 test gave `{:m 1}`: the replica keeps it (the test passes). -/
theorem s44_round3_test_meta_kept :
    (jankEvalQuote [(0, .keys ["m"])] 0).lookup 0 = some (.keys ["m"]) := by decide

open Jank.R3.Codegen.Literals in
/-- The cases the prediction is about: `{}` becomes nil; `{:jank/source 1 :m 1}` loses its
`:jank/source`. -/
theorem s44_round4_cases :
    (jankEvalQuote [(0, .keys [])] 0).lookup 0 = some .none
    ∧ (jankEvalQuote [(0, .keys ["jank/source", "m"])] 0).lookup 0 = some (.keys ["m"]) := by
  decide

end Jank.R4.Feedback.Numbers
