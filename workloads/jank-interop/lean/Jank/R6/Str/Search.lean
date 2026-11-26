import Jank.StrModel
import Jank.R6.Str.Proofs
import Jank.R6.Str.Fixes
import Jank.R6.Str.SeqCount
import Jank.R6.Str.Cut

/-!
# Round 6, strings: complete walks

Plain enumeration (complete within each bound; the counts are exact):

- **A, the index functions.** Every text of at most `n` code points over `alphabet7` (ASCII `a` and
  `-`, é (2 bytes), € and Ａ (3 bytes), 😀 (4 bytes, a surrogate pair), U+0301 COMBINING ACUTE), every
  operation of round 2's `Op` that indexes, measures or walks a text, with every index in `-1..k`.
  Each case is evaluated three ways: jank (round 2's replica), Clojure, and the code-point design
  (`cpEval`, the smallest design change), and each fix model where one exists. A disagreement is
  classed *byte indexing* when the code-point design gives Clojure's answer, *code-point
  characters* when it does not and the text holds a supplementary character, and *separate* when
  neither (a defect inside jank's own model).
- **B, cut strings.** Every byte string of at most 4 bytes over the bytes of a, é, € and 😀: the
  seq walk today (R54) and with R54a.
- **C, whitespace.** Texts over ASCII and Unicode spaces: trim, triml, trimr, blank? (R59, R59a/b).
- **D, capitalize.** Texts over a, A, é, É, ß, Σ, σ: capitalize (R61, R61a), UTF-8 locale.
- **E, subs.** The 2- and 3-arity agreement conditions (`subs1_agrees_iff`, proved; the 3-arity
  condition, searched).
- **F, compare values.** Every pair of texts of at most 2 code points: Java's value, jank's
  (StrA6-1), R57a's.
-/

namespace Jank.R6.Str

open Jank.Str

def alphabet7 : List Nat := [0x61, 0x2D, 0xE9, 0x20AC, 0xFF21, 0x1F600, 0x301]

def textsOver (alpha : List Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 =>
    let shorter := textsOver alpha n
    shorter ++ ((shorter.filter (·.length == n)).flatMap fun s => alpha.map (s ++ [·]))

def hasSupp (cps : List Nat) : Bool := cps.any (· ≥ 0x10000)

/-! ## The code-point design on round 2's questions -/

def cpEval (c : Case) : Option R :=
  let cps := c.s
  match c.op with
  | .count => some (cpCount cps)
  | .nth i => some (cpNth cps i)
  | .get i => some (if i < 0 ∨ cps.length ≤ i.toNat then .nil else .chr (utf8 (cps.getD i.toNat 0)))
  | .contains i => some (.bool (decide (0 ≤ i ∧ i.toNat < cps.length)))
  | .subs1 i => some (cpSubs cps i cps.length)
  | .subs2 i j => some (cpSubs cps i j)
  | .seq => some (if cps.isEmpty then .nil else .chars (cps.map utf8))
  | .seqCount => some (.int cps.length)
  | .firstInt => some (match cps with | c :: _ => .int c | [] => .err "nil")
  | .indexOf n f => some (cIndexOf cps n (f.getD 0))
  | .lastIndexOf n f => some (cLastIndexOf cps n (f.getD cps.length))
  | .escape k => some (.str (cps.flatMap fun x => if x == k then [0x58] else utf8 x))
  | .replaceEmpty => some (.str (cps.foldr (fun x acc => [0x2D] ++ utf8 x ++ acc) [0x2D]))
  | .reverse => some (.str (cps.reverse.flatMap utf8))
  | .seqSelfEq => some (.bool true)
  | .seqEqVec => some (.bool (!cps.isEmpty))
  | .seqHashVec => some (.bool (!cps.isEmpty))
  | _ => none

/-- The fix model for a question, where a fix exists (R55a, R56a, R58a, R62a, R63a). -/
def fixedEval (c : Case) : Option R :=
  let js := jstr c.s
  match c.op with
  | .indexOf n f => some (jIndexOfFixed js (jstr n) (f.getD 0))
  | .lastIndexOf n f => some (jLastIndexOfFixed js (jstr n) (f.getD js.length))
  | .escape k => some (jEscapeFixed js (utf8 k))
  | .replaceEmpty => some (jReplaceEmptyFixed js [0x2D])
  | .seqSelfEq => some (.bool true)                       -- R55a: sequence_equal over characters
  | .seqEqVec => some (.bool (!c.s.isEmpty))             -- R55a
  | .seqHashVec => some (.bool (!c.s.isEmpty))           -- R56a: hash::ordered over characters
  | _ => none

def indexRange (len : Nat) : List Int := (List.range (len + 3)).map fun (k : Nat) => (k : Int) - 1

def needles : List (List Nat) := [[], [0x61], [0x2D], [0xE9], [0x1F600]]
def froms : List (Option Int) := [none, some (-1), some 0, some 1, some 2, some 3, some 5, some 9]

/-- Every question of walk A about one text. -/
def questionsA (s : List Nat) : List Op :=
  let bl := (jstr s).length
  let idx := indexRange bl
  [.count, .seq, .seqCount, .firstInt, .replaceEmpty, .reverse, .seqSelfEq, .seqEqVec, .seqHashVec] ++
  idx.map Op.nth ++ idx.map Op.get ++ idx.map Op.contains ++ idx.map Op.subs1 ++
  (idx.flatMap fun i => idx.map (Op.subs2 i)) ++
  (needles.flatMap fun n => froms.map (Op.indexOf n)) ++
  (needles.flatMap fun n => froms.map (Op.lastIndexOf n)) ++
  alphabet7.map Op.escape

structure Tally where
  cases : Nat := 0
  differ : Nat := 0
  byteIndexing : Nat := 0
  codePointChars : Nat := 0
  separate : Nat := 0
  cpResidual : Nat := 0
  cpResidualBmp : Nat := 0
  fixedCases : Nat := 0
  fixedDiffer : Nat := 0
  fixedDifferBmp : Nat := 0
  fixedDifferAscii : Nat := 0
  invalid : Nat := 0
  invalidFixed : Nat := 0
  firstCase : String := ""
  deriving Inhabited

/-- A result holding bytes that are not valid UTF-8 (a string, or a character not of one code point). -/
def invalidResult : R → Bool
  | .str b => (decodeUtf8 b).isNone
  | .chr b => match decodeUtf8 b with | some [_] => false | _ => true
  | .chars cs => cs.any fun b => match decodeUtf8 b with | some [_] => false | _ => true
  | _ => false

def Tally.add (t : Tally) (c : Case) : Tally := Id.run do
  let (j, cl) := c.eval
  let cp := cpEval c
  let fx := fixedEval c
  let mut t := { t with cases := t.cases + 1 }
  let cpAgrees := match cp with | some r => r.agrees cl | none => false
  if let some r := cp then
    if !r.agrees cl then
      t := { t with cpResidual := t.cpResidual + 1 }
      if !hasSupp c.s then t := { t with cpResidualBmp := t.cpResidualBmp + 1 }
  if let some r := fx then
    t := { t with fixedCases := t.fixedCases + 1 }
    if !r.agrees cl then
      t := { t with fixedDiffer := t.fixedDiffer + 1 }
      if !hasSupp c.s then t := { t with fixedDifferBmp := t.fixedDifferBmp + 1 }
      if c.s.all (· < 0x80) then t := { t with fixedDifferAscii := t.fixedDifferAscii + 1 }
  -- invalid UTF-8 handed to the program (R52's cut), today and with R52a for subs
  if invalidResult j then t := { t with invalid := t.invalid + 1 }
  let js := jstr c.s
  let subsFixed : Option R := match c.op with
    | .subs1 i => some (jSubsFixed js i js.length)
    | .subs2 i j' => some (jSubsFixed js i j')
    | _ => none
  if let some r := subsFixed then
    if invalidResult r then t := { t with invalidFixed := t.invalidFixed + 1 }
  if !j.agrees cl then
    t := { t with differ := t.differ + 1 }
    if t.firstCase.isEmpty then
      t := { t with firstCase := s!"{c.program}: Clojure {cl.show}, jank {j.show}" }
    -- the separate defects: jank's own string seq (R55, R56)
    let sep := match c.op with | .seqSelfEq | .seqEqVec | .seqHashVec => true | _ => false
    if sep then t := { t with separate := t.separate + 1 }
    else if cpAgrees then t := { t with byteIndexing := t.byteIndexing + 1 }
    else if hasSupp c.s then t := { t with codePointChars := t.codePointChars + 1 }
    else t := { t with separate := t.separate + 1 }
  return t

def opKey : Op → String
  | .subs1 _ => "subs/2" | .subs2 .. => "subs/3" | op => op.name

def walkA (n : Nat) : List (String × Tally) := Id.run do
  let keys := ["count", "nth", "get", "contains?", "subs/2", "subs/3", "seq", "count of seq",
    "int of first", "index-of", "last-index-of", "escape", "replace \"\"", "reverse",
    "(= x x) on a string seq", "(= (seq s) (vec s))", "hash of (seq s) vs (vec s)"]
  let mut acc : Std.HashMap String Tally := {}
  for s in textsOver alphabet7 n do
    for op in questionsA s do
      let k := opKey op
      acc := acc.insert k ((acc.getD k default).add { loc := .utf8, op, s })
  return keys.map fun k => (k, acc.getD k default)

/-! ## B: cut strings -/

def cutBytes : List UInt8 := [0x61, 0xC3, 0xA9, 0xE2, 0x82, 0xAC, 0xF0, 0x9F, 0x98, 0x80]

def byteStrings : Nat → List (List UInt8)
  | 0 => [[]]
  | n + 1 =>
    let shorter := byteStrings n
    shorter ++ ((shorter.filter (·.length == n)).flatMap fun s => cutBytes.map (s ++ [·]))

def isUb : R → Bool | .ub _ => true | _ => false
def isErr : R → Bool | .err _ => true | _ => false

/-! ## C: whitespace -/

def wsAlphabet : List Nat := [0x20, 0x61, 0x1F, 0x2003, 0xA0, 0x3000, 0xE9, 0x2028]

def jTrimlFixed (s : List UInt8) : R := .str ((decodeLossless s).dropWhile javaIsWhitespace |>.flatMap utf8)
def jTrimrFixed (s : List UInt8) : R := .str (((decodeLossless s).reverse.dropWhile javaIsWhitespace).reverse.flatMap utf8)

/-! ## D: capitalize -/

def capAlphabet : List Nat := [0x61, 0x41, 0xE9, 0xC9, 0xDF, 0x3A3, 0x3C3]

/-! ## E: subs conditions -/

/-- The searched 3-arity condition: both throw, or the end is within the ASCII prefix, or an empty
cut at a unit index. -/
def subs2Cond (cps : List Nat) (i j : Int) : Bool :=
  decide (i < 0 ∨ j < i ∨ ((jstr cps).length : Int) < j ∨ j ≤ asciiPrefix cps ∨ (i = j ∧ j ≤ (cstr cps).length))

def subs1Cond (cps : List Nat) (i : Int) : Bool :=
  decide (i < 0 ∨ i ≤ asciiPrefix cps ∨ ((jstr cps).length : Int) < i)

end Jank.R6.Str
