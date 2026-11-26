import Determinismo
import Std.Data.HashMap
import Std.Data.HashSet
import Jank.R3.Boost.Java

/-!
# Round 7, area G: a generated differential test driven from the round-6 models

REPORT-6 section 14's last item. Round 6's lesson (section 1): random clojure.core forms compared
with Clojure on the real jank found LG1–LG3, which no model had drawn. Here the replica draws such
forms itself, from the universes of the round-6 models, and predicts each one's verdict:

- `Jank.R7.Gen.Num`: `Jank.R6.Num.Int` (`+ - * inc dec abs rem quot (- x)` and `+' -' *' inc'
  dec'` over 23 integers × the three sources literal / literal through a fn / computed value
  through a fn);
- `Jank.R7.Gen.MinMax`: `Jank.R6.Num.MinMax` (`min max < <= compare ==` over 29 values of every kind);
- `Jank.R7.Gen.Native`: `Jank.R6.Native.Math` (`< <= > >= min max + - * /` over the native producers
  `count alength hash int bit-and aget float` and predicates, inlined and through a fn value);
- `Jank.R7.Gen.Str`: round 2's `Jank.StrModel` with round 6's exact `compare` and the R58a starts
  (`count nth get contains? subs index-of last-index-of compare` over texts of a, -, é, €, 😀).

A *draw* is one choice of operation and operands; it is emitted on every path the model
distinguishes (this file's `Path`): the call written directly ([literals]), the operands let-bound
([let]), through object parameters ([fn]: a defn wrapper, a local fn, or `apply`), and, for the
number models, a call inlined inside a local fn with one operand its parameter ([mixed]). The
draws of one operation are chosen by `choose` from a mixed seed (`Determinismo.mixSeed`): first one
draw failing on each path where the model has one (a new explaining id first), then more failing
draws up to half, then draws the model predicts pass everywhere. Each item records Clojure's value
(the model's Clojure side), the predicted jank value, the verdict the test's single assertion gets
on jank (pass, fail, or throws: an exception the assertion does not catch), and the id of the
deviation that explains a predicted failure.
-/

namespace Jank.R7.Gen

/-- The path a form takes (REPORT-6 section 3, "How a number reaches core/math.hpp"). -/
inductive Path where
  | literals | letp | fn | mixed
  deriving BEq, Repr, Inhabited, DecidableEq

def Path.slug : Path → String
  | .literals => "literals" | .letp => "let" | .fn => "fn" | .mixed => "mixed"

def Path.all : List Path := [.literals, .letp, .fn, .mixed]

/-- How the [fn] path reaches the operation: a top-level defn wrapper, a local fn, `apply`. -/
inductive Via where
  | defn | lam | app
  deriving BEq, Repr, Inhabited, DecidableEq

def Via.slug : Via → String
  | .defn => "fn:defn" | .lam => "fn:local" | .app => "fn:apply"

def Via.all : Array Via := #[.defn, .lam, .app]

def viaOf (k : Nat) : Via := Via.all[k % 3]!

inductive Verdict where
  | pass | fail | throws
  deriving BEq, Repr, Inhabited, DecidableEq

def Verdict.name : Verdict → String
  | .pass => "pass" | .fail => "fail" | .throws => "throws"

/-- One generated test. -/
structure Item where
  group : String
  /-- The operation's slug in the test name. -/
  op : String
  path : Path
  /-- The path as the TSV names it (`literals`, `let`, `fn:defn`, `fn:local`, `fn:apply`, `mixed`). -/
  detail : String
  /-- The form under test (Clojure source). -/
  form : String
  /-- The body of the test's one `is`. -/
  assertion : String
  clj : String
  jank : String
  verdict : Verdict
  /-- The deviation that explains a predicted failure ("" for a predicted pass). -/
  id : String
  deriving Inhabited

/-- A draw: one choice of operands, emitted on each of its paths. -/
structure Draw where
  key : String
  items : Array Item
  deriving Inhabited

def Draw.fails (d : Draw) : Bool := d.items.any (·.verdict != .pass)
def Draw.failsOn (d : Draw) (p : Path) : Bool := d.items.any fun i => i.path == p && i.verdict != .pass
def Draw.idOn (d : Draw) (p : Path) : String :=
  match d.items.find? (·.path == p) with
  | some i => i.id
  | none => ""
def Draw.sig (d : Draw) : String :=
  ",".intercalate (d.items.toList.map fun i => if i.verdict == .pass then "-" else i.id)

/-! ## Seeds and draws -/

/-- The generator of a stratum's seed: `mkStdGen` of the mixed seed (consecutive raw seeds give
the same first draw, `Determinismo.mixSeed`'s note). -/
def rngOf (seed : Nat) : StdGen := mkStdGen (Determinismo.mixSeed seed)

def shuffle {α : Type} [Inhabited α] (g : StdGen) (xs : Array α) : Array α × StdGen := Id.run do
  let mut a := xs
  let mut g := g
  for i in [0:xs.size] do
    let (r, g') := randNat g i (xs.size - 1)
    g := g'
    let x := a[i]!
    let y := a[r]!
    a := (a.set! i y).set! r x
  return (a, g)

/-- Choose `t` draws (see the module doc): one failing draw per path where one exists (a new
explaining id first), more failing draws (a new signature first) up to half, then passing draws;
short of passing draws, more failing ones. -/
def choose (seed : Nat) (paths : List Path) (ds : Array Draw) (t : Nat) : Array Draw := Id.run do
  let (ds, _) := shuffle (rngOf seed) ds
  let failing := ds.filter (·.fails)
  let passing := ds.filter (!·.fails)
  let half := (t + 1) / 2
  let mut chosen : Array Draw := #[]
  let mut keys : Std.HashSet String := {}
  let mut sigs : Std.HashSet String := {}
  let mut ids : Std.HashSet String := {}
  for p in paths do
    if chosen.size ≥ half then break
    let cands := failing.filter fun d => d.failsOn p && !keys.contains d.key && !sigs.contains d.sig
    let fresh := cands.filter fun d => !ids.contains (d.idOn p)
    match (if fresh.isEmpty then cands else fresh)[0]? with
    | some d =>
      chosen := chosen.push d
      keys := keys.insert d.key
      sigs := sigs.insert d.sig
      for i in d.items do ids := ids.insert i.id
    | none => pure ()
  for d in failing do
    if chosen.size ≥ half then break
    if !keys.contains d.key && !sigs.contains d.sig then
      chosen := chosen.push d
      keys := keys.insert d.key
      sigs := sigs.insert d.sig
  -- still short of half: the remaining failing draw whose signature is used least
  let mut uses : Std.HashMap String Nat := {}
  for d in chosen do uses := uses.insert d.sig (uses.getD d.sig 0 + 1)
  while chosen.size < half do
    let rest := failing.filter (!keys.contains ·.key)
    match rest.foldl (fun (best : Option Draw) d => match best with
        | none => some d
        | some b => if uses.getD d.sig 0 < uses.getD b.sig 0 then some d else some b) none with
    | none => break
    | some d =>
      chosen := chosen.push d
      keys := keys.insert d.key
      uses := uses.insert d.sig (uses.getD d.sig 0 + 1)
  for d in passing do
    if chosen.size ≥ t then break
    chosen := chosen.push d
    keys := keys.insert d.key
  for d in failing do
    if chosen.size ≥ t then break
    if !keys.contains d.key then
      chosen := chosen.push d
      keys := keys.insert d.key
  return chosen

/-! ## Clojure source text -/

def hex4 (n : Nat) : String :=
  let d := Nat.toDigits 16 n
  String.ofList (List.replicate (4 - d.length) '0' ++ d)

/-- UTF-16 code units of a code point. -/
def units (c : Nat) : List Nat :=
  if c < 0x10000 then [c] else [0xD800 + (c - 0x10000) / 1024, 0xDC00 + (c - 0x10000) % 1024]

/-- A Clojure string literal of code points: printable ASCII as is, every other code unit as a
`\uXXXX` escape (RULES 7: non-ASCII text with `\u` escapes). -/
def strLit (cps : List Nat) : String :=
  "\"" ++ String.join (cps.map fun c =>
    if c == 0x22 then "\\\"" else if c == 0x5C then "\\\\"
    else if 0x20 ≤ c && c < 0x7F then String.singleton (Char.ofNat c)
    else String.join ((units c).map fun u => "\\u" ++ hex4 u)) ++ "\""

/-- Text made ASCII for comments and the TSV (`\uXXXX` for anything else, tabs and newlines too). -/
def ascii (s : String) : String :=
  String.join (s.toList.map fun ch =>
    let c := ch.toNat
    if 0x20 ≤ c && c < 0x7F then String.singleton ch
    else String.join ((units c).map fun u => "\\u" ++ hex4 u))

/-- A double as a Clojure literal without exponent notation (both readers take plain decimals):
Java's `Double.toString` (round 3's `javaDoubleString`) with an `E` expanded. -/
def plainDouble (x : Float) : String :=
  if x.isNaN then "##NaN" else if x.isInf then (if x < 0.0 then "##-Inf" else "##Inf") else
  let s := Jank.R3.Boost.Java.javaDoubleString x
  match s.splitOn "E" with
  | [m, e] =>
    let neg := m.startsWith "-"
    let m := if neg then (m.drop 1).toString else m
    let (ip, fp) := match m.splitOn "." with
      | [a, b] => (a, b)
      | _ => (m, "")
    let digits := ip ++ fp
    let ex : Int := match e.toInt? with | some v => v | none => 0
    let pos : Int := (ip.length : Int) + ex
    let body :=
      if pos ≤ 0 then "0." ++ String.ofList (List.replicate (-pos).toNat '0') ++ digits
      else if pos.toNat ≥ digits.length then
        digits ++ String.ofList (List.replicate (pos.toNat - digits.length) '0') ++ ".0"
      else (digits.take pos.toNat).toString ++ "." ++ (digits.drop pos.toNat).toString
    -- strip trailing zeros of the fraction, keep one digit
    let body := match body.splitOn "." with
      | [a, b] =>
        let b' := String.ofList (b.toList.reverse.dropWhile (· == '0')).reverse
        a ++ "." ++ (if b'.isEmpty then "0" else b')
      | _ => body
    (if neg then "-" else "") ++ body
  | _ => s

def isNegZero (x : Float) : Bool := x == 0.0 && x.toBits >>> 63 == 1

/-! ## The test file -/

/-- The fn-path wrappers (top-level `defn-`s, as round 6's tests' `n-add`): object parameters. -/
def wrappers : List String :=
  ["(defn- g-add [a b] (+ a b))", "(defn- g-sub [a b] (- a b))", "(defn- g-mul [a b] (* a b))",
   "(defn- g-div [a b] (/ a b))", "(defn- g-addp [a b] (+' a b))", "(defn- g-subp [a b] (-' a b))",
   "(defn- g-mulp [a b] (*' a b))", "(defn- g-neg [a] (- a))", "(defn- g-inc [a] (inc a))",
   "(defn- g-dec [a] (dec a))", "(defn- g-incp [a] (inc' a))", "(defn- g-decp [a] (dec' a))",
   "(defn- g-abs [a] (abs a))", "(defn- g-rem [a b] (rem a b))", "(defn- g-quot [a b] (quot a b))",
   "(defn- g-lt [a b] (< a b))", "(defn- g-lte [a b] (<= a b))", "(defn- g-gt [a b] (> a b))",
   "(defn- g-gte [a b] (>= a b))", "(defn- g-min [a b] (min a b))", "(defn- g-max [a b] (max a b))",
   "(defn- g-compare [a b] (compare a b))", "(defn- g-equiv [a b] (== a b))",
   "(defn- g-count [s] (count s))", "(defn- g-nth [s i] (nth s i))", "(defn- g-get [s i] (get s i))",
   "(defn- g-contains [s i] (contains? s i))",
   "(defn- g-subs ([s i] (subs s i)) ([s i j] (subs s i j)))",
   "(defn- g-index-of ([s v] (string/index-of s v)) ([s v f] (string/index-of s v f)))",
   "(defn- g-last-index-of ([s v] (string/last-index-of s v)) ([s v f] (string/last-index-of s v f)))"]

def header : String :=
"; SPDX-License-Identifier: MIT
; The Lean replica of jank, round 7 (main 94d32623): generated differential tests (area G).
; Each deftest is one form drawn from the round-6 models' universes by Jank/R7/Gen (lake exe
; jank7-gen): integers (Jank/R6/Num/Int), min/max and comparisons (Jank/R6/Num/MinMax), native
; producers (Jank/R6/Native/Math) and strings (Jank/StrModel, Jank/R6/Str). A draw of operands is
; emitted on every path the model distinguishes; each test holds ONE assertion of Clojure 1.12's
; value, so a failure on jank confirms the replica's predicted failure and a pass its predicted
; pass. The comment above each test names its path, the replica's predicted jank value, the
; predicted verdict (pass, fail, or throws: an exception the assertion does not catch) and the id
; that explains a predicted failure; results/r7-gen-predictions.tsv holds the same per test.
; Paths (REPORT-6 section 3):
;   [literals]: the call written directly, its arguments literals or native producers (inlined);
;   [let]: the same arguments let-bound, then the call (the locals keep their native types);
;   [fn:defn], [fn:local], [fn:apply]: through a defn wrapper's, a local fn's or apply's object
;   parameters, so no native operand reaches the template;
;   [mixed]: the call inlined in a local fn, one operand its object parameter, the other a literal.
; Observations: longs and BigInts with pr-str (so N shows), doubles with = against an exact literal,
; NaN with NaN?, signed zeros with str, BigDecimals with decimal? and compare, ratios with =,
; characters with str, Clojure's exceptions with thrown?.
; Every form is inside a deftest body (compiled, not interpreted). Non-ASCII text is written with
; \\u escapes: run under a UTF-8 locale, each test in its own process, from tests/ with
; `--module-path .`. No test predicts a hang.
(ns jank-lean.generated-r7-test
  (:require [clojure.test :refer [deftest is]]
            [clojure.string :as string]))
"

def testName (n : Nat) (i : Item) : String := s!"g{n}-{i.op}-{i.path.slug}"

def deftestText (n : Nat) (i : Item) : String :=
  let why := if i.verdict == .pass then "pass" else s!"{i.verdict.name}, {i.id}"
  s!"; [{i.detail}] jank predicted: {ascii i.jank} ({why}); Clojure: {ascii i.clj}\n(deftest {testName n i}\n  (is {i.assertion}))\n"

def tsvLine (n : Nat) (i : Item) : String :=
  "\t".intercalate [testName n i, i.detail, ascii i.form, ascii i.clj, ascii i.jank, i.verdict.name,
    if i.verdict == .pass then "-" else i.id]

end Jank.R7.Gen
