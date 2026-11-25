-- SPDX-License-Identifier: GPL-3.0-or-later WITH GCC-exception-3.1 (with round 3's regex replica; see README.md)
import Jank.R3.Regex.Java

/-!
# The spec, round 5: round 4's java.util.regex model with Java's Unicode rules

A copy of round 4's `JavaM` (namespace `Jank.R4.Regex.JM`), changed only where JDK 23's
`java.util.regex` (Pattern.java, CharPredicates.java) treats non-ASCII text in a way round 4's
model did not, because round 4's searches never drew such text:

- `Bound` (`\b`, `\B`, Pattern.java 5543–5593): a character counts as a word character when it is
  one (`[a-zA-Z0-9_]`, or `UNICODE_CHARACTER_CLASS`'s `WORD()`), **or when it is a non-spacing
  mark (`Mn`) whose base is a letter or digit** (`hasBaseCharacter` 5599–5613: walking back over
  marks to a `Character.isLetterOrDigit` code point, within the region). This holds in every mode,
  `(?U)` or not. Round 4's `boundAt` had only the first half.
- `(?U)`'s `\w` is `CharPredicates.WORD()` (159–167): `Alphabetic`, the marks `Mn`, `Me`, `Mc`,
  `Nd`, `Pc` and `Join_Control`; round 4's `uWord` had no marks, no `Nl`, no join controls.
- `\p{name}` (`family`, Pattern.java 3018–3100): POSIX names (`Alpha`, `Punct`, `Lower`, ...) are
  `CharPredicates.forPOSIXName` (Unicode) under `(?U)`, ASCII otherwise; `Is…` names are
  `forUnicodeProperty`, then general categories; general categories (`L`, `Lu`, `Mn`, `P`, ...)
  and `java…` names; `CASE_INSENSITIVE` widens `Lu`/`Ll`/`Lt`/`Lower`/`Upper`/`javaLowerCase`/...
  as `forProperty`/`getPosixPredicate` do.
- A table of `Character.getType` and the contributory properties (`Other_Lowercase`,
  `Other_Uppercase`, `Other_Alphabetic`) for the code points the round-5 searches draw
  (`gcat`), checked on a JVM (`results/r5-regex-jvm.txt`).

Two spec-side toggles classify the deviations a census finds (all off is the spec):
- `noMn`: `Bound` without the non-spacing-mark rule;
- `asciiTerm`: `.` and `$` treat only `\n` and `\r` as line terminators (not U+0085, U+2028,
  U+2029), the ECMAScript rule libstdc++ applies to `char` (regex_compiler.h `_AnyMatcher`).
-/

namespace Jank.R5.Regex.JM5

open Jank.R3.Regex

/-! ## Characters -/

def isAsciiUpper (c : Nat) : Bool := 0x41 ≤ c && c ≤ 0x5A
def isAsciiLower (c : Nat) : Bool := 0x61 ≤ c && c ≤ 0x7A
def isAsciiAlpha (c : Nat) : Bool := isAsciiUpper c || isAsciiLower c
def aLower (c : Nat) : Nat := if isAsciiUpper c then c + 32 else c
def aUpper (c : Nat) : Nat := if isAsciiLower c then c - 32 else c

/-- `Character.toLowerCase(int)` for the code points the searches draw (ASCII, Latin-1, Latin
Extended-A, Greek, the Kelvin and Angstrom signs); others map to themselves. -/
def toLowerCp (c : Nat) : Nat :=
  if isAsciiUpper c then c + 32
  else if 0xC0 ≤ c && c ≤ 0xDE && c != 0xD7 then c + 32
  else if c == 0x178 then 0xFF
  else if c == 0x130 then 0x69
  else if 0x100 ≤ c && c ≤ 0x137 && c % 2 == 0 then c + 1
  else if 0x139 ≤ c && c ≤ 0x148 && c % 2 == 1 then c + 1
  else if 0x14A ≤ c && c ≤ 0x177 && c % 2 == 0 then c + 1
  else if 0x179 ≤ c && c ≤ 0x17E && c % 2 == 1 then c + 1
  else if 0x391 ≤ c && c ≤ 0x3A9 && c != 0x3A2 then c + 32
  else if c == 0x212A then 0x6B
  else if c == 0x212B then 0xE5
  else c

/-- `Character.toUpperCase(int)` on the same code points. -/
def toUpperCp (c : Nat) : Nat :=
  if isAsciiLower c then c - 32
  else if 0xE0 ≤ c && c ≤ 0xFE && c != 0xF7 then c - 32
  else if c == 0xFF then 0x178
  else if c == 0xB5 then 0x39C
  else if c == 0x131 then 0x49
  else if c == 0x17F then 0x53
  else if 0x101 ≤ c && c ≤ 0x137 && c % 2 == 1 then c - 1
  else if 0x13A ≤ c && c ≤ 0x148 && c % 2 == 0 then c - 1
  else if 0x14B ≤ c && c ≤ 0x177 && c % 2 == 1 then c - 1
  else if 0x17A ≤ c && c ≤ 0x17E && c % 2 == 0 then c - 1
  else if c == 0x3C2 then 0x3A3
  else if 0x3B1 ≤ c && c ≤ 0x3C9 then c - 32
  else c

/-- Unicode decimal digits (`Nd`) among the drawn code points. -/
def uDigit (c : Nat) : Bool :=
  (0x30 ≤ c && c ≤ 0x39) || (0x660 ≤ c && c ≤ 0x669) || (0x6F0 ≤ c && c ≤ 0x6F9) ||
  (0x966 ≤ c && c ≤ 0x96F) || (0xFF10 ≤ c && c ≤ 0xFF19)

/-- The `White_Space` property. -/
def uSpace (c : Nat) : Bool :=
  (0x09 ≤ c && c ≤ 0x0D) || c == 0x20 || c == 0x85 || c == 0xA0 || c == 0x1680 ||
  (0x2000 ≤ c && c ≤ 0x200A) || c == 0x2028 || c == 0x2029 || c == 0x202F || c == 0x205F || c == 0x3000

/-! ## `Character.getType` and contributory properties, for the drawn code points

Java's constants: 0 UNASSIGNED, 1 Lu, 2 Ll, 3 Lt, 4 Lm, 5 Lo, 6 Mn, 7 Me, 8 Mc, 9 Nd, 10 Nl,
11 No, 12 Zs, 13 Zl, 14 Zp, 15 Cc, 16 Cf, 18 Co, 19 Cs, 20 Pd, 21 Ps, 22 Pe, 23 Pc, 24 Po, 25 Sm,
26 Sc, 27 Sk, 28 So, 29 Pi, 30 Pf. Code points outside the table are UNASSIGNED here; the
searches draw none of them. -/

def asciiGc (c : Nat) : Nat :=
  if c < 0x20 || c == 0x7F then 15
  else if c == 0x20 then 12
  else if 0x30 ≤ c && c ≤ 0x39 then 9
  else if isAsciiUpper c then 1
  else if isAsciiLower c then 2
  else if c == 0x24 then 26
  else if c == 0x28 || c == 0x5B || c == 0x7B then 21
  else if c == 0x29 || c == 0x5D || c == 0x7D then 22
  else if c == 0x2B || c == 0x3C || c == 0x3D || c == 0x3E || c == 0x7C || c == 0x7E then 25
  else if c == 0x2D then 20
  else if c == 0x5E || c == 0x60 then 27
  else if c == 0x5F then 23
  else 24

def latin1Gc (c : Nat) : Nat :=
  if c < 0xA0 then 15
  else match c with
  | 0xA0 => 12 | 0xA1 => 24 | 0xA2 => 26 | 0xA3 => 26 | 0xA4 => 26 | 0xA5 => 26 | 0xA6 => 28
  | 0xA7 => 24 | 0xA8 => 27 | 0xA9 => 28 | 0xAA => 5 | 0xAB => 29 | 0xAC => 25 | 0xAD => 16
  | 0xAE => 28 | 0xAF => 27 | 0xB0 => 28 | 0xB1 => 25 | 0xB2 => 11 | 0xB3 => 11 | 0xB4 => 27
  | 0xB5 => 2 | 0xB6 => 24 | 0xB7 => 24 | 0xB8 => 27 | 0xB9 => 11 | 0xBA => 5 | 0xBB => 30
  | 0xBC => 11 | 0xBD => 11 | 0xBE => 11 | 0xBF => 24 | 0xD7 => 25 | 0xF7 => 25
  | _ => if c ≤ 0xDE then 1 else 2

/-- `Character.getType(int)`. -/
def gcat (c : Nat) : Nat :=
  if c < 0x80 then asciiGc c
  else if c < 0x100 then latin1Gc c
  else if 0x100 ≤ c && c ≤ 0x137 then (if c % 2 == 0 then 1 else 2)
  else if 0x300 ≤ c && c ≤ 0x36F then 6
  else if 0x391 ≤ c && c ≤ 0x3A9 && c != 0x3A2 then 1
  else if 0x3B1 ≤ c && c ≤ 0x3C9 then 2
  else if 0x660 ≤ c && c ≤ 0x669 then 9
  else if 0x2000 ≤ c && c ≤ 0x200A then 12
  else if 0x200B ≤ c && c ≤ 0x200F then 16
  else if c == 0x2028 then 13
  else if c == 0x2029 then 14
  else if c == 0x202F || c == 0x205F || c == 0x3000 then 12
  else if c == 0x203F || c == 0x2040 then 23
  else if 0x2160 ≤ c && c ≤ 0x217F then 10
  else if 0xD800 ≤ c && c ≤ 0xDFFF then 19
  else if 0xFF10 ≤ c && c ≤ 0xFF19 then 9
  else if c == 0x1F600 then 28
  else 0

def isLetterGc (g : Nat) : Bool := 1 ≤ g && g ≤ 5

/-- `Other_Lowercase` / `Other_Uppercase` among the drawn code points (PropList.txt). -/
def otherLower (c : Nat) : Bool := c == 0xAA || c == 0xBA || (0x2170 ≤ c && c ≤ 0x217F)
def otherUpper (c : Nat) : Bool := 0x2160 ≤ c && c ≤ 0x216F

def jIsAlphabetic (c : Nat) : Bool := isLetterGc (gcat c) || gcat c == 10
def jIsLetter (c : Nat) : Bool := isLetterGc (gcat c)
def jIsDigit (c : Nat) : Bool := gcat c == 9
def jIsLetterOrDigit (c : Nat) : Bool := isLetterGc (gcat c) || gcat c == 9
def jIsLowerCase (c : Nat) : Bool := gcat c == 2 || otherLower c
def jIsUpperCase (c : Nat) : Bool := gcat c == 1 || otherUpper c
def jIsTitleCase (c : Nat) : Bool := gcat c == 3
def isPunctGc (g : Nat) : Bool := g == 20 || g == 21 || g == 22 || g == 23 || g == 24 || g == 29 || g == 30

/-- `CharPredicates.WHITE_SPACE()`. -/
def jWhiteSpace (c : Nat) : Bool :=
  let g := gcat c
  g == 12 || g == 13 || g == 14 || (0x09 ≤ c && c ≤ 0x0D) || c == 0x85

/-- `CharPredicates.WORD()`: alphabetic, the marks, decimal digits, connector punctuation, join
controls. -/
def jWord (c : Nat) : Bool :=
  let g := gcat c
  jIsAlphabetic c || g == 6 || g == 7 || g == 8 || g == 9 || g == 23 || c == 0x200C || c == 0x200D

/-- `CharPredicates.BLANK()`, `CONTROL()`, `GRAPH()`, `PRINT()`, `HEX_DIGIT()`. -/
def jBlank (c : Nat) : Bool := gcat c == 12 || c == 0x09
def jControl (c : Nat) : Bool := gcat c == 15
def jGraph (c : Nat) : Bool := let g := gcat c; !(g == 12 || g == 13 || g == 14 || g == 15 || g == 19 || g == 0)
def jPrint (c : Nat) : Bool := (jGraph c || jBlank c) && !jControl c
def jHexDigit (c : Nat) : Bool :=
  jIsDigit c || (0x41 ≤ c && c ≤ 0x46) || (0x61 ≤ c && c ≤ 0x66) || (0xFF21 ≤ c && c ≤ 0xFF26) ||
  (0xFF41 ≤ c && c ≤ 0xFF46)

/-- `getPosixPredicate` (CharPredicates.java 171–190), the `(?U)` meaning of a POSIX name. -/
def posixU (name : String) (ci : Bool) : Option (Nat → Bool) :=
  match name.toUpper with
  | "ALPHA" => some jIsAlphabetic
  | "LOWER" => some (if ci then fun c => jIsLowerCase c || jIsUpperCase c || jIsTitleCase c else jIsLowerCase)
  | "UPPER" => some (if ci then fun c => jIsUpperCase c || jIsLowerCase c || jIsTitleCase c else jIsUpperCase)
  | "SPACE" => some jWhiteSpace
  | "PUNCT" => some (fun c => isPunctGc (gcat c))
  | "XDIGIT" => some jHexDigit
  | "ALNUM" => some (fun c => jIsAlphabetic c || jIsDigit c)
  | "CNTRL" => some jControl
  | "DIGIT" => some jIsDigit
  | "BLANK" => some jBlank
  | "GRAPH" => some jGraph
  | "PRINT" => some jPrint
  | _ => none

/-- `getUnicodePredicate` (193–223) for the names this model knows. -/
def unicodeProp (name : String) (ci : Bool) : Option (Nat → Bool) :=
  match name.toUpper with
  | "ALPHABETIC" => some jIsAlphabetic
  | "LETTER" => some jIsLetter
  | "LOWERCASE" => some (if ci then fun c => jIsLowerCase c || jIsUpperCase c || jIsTitleCase c else jIsLowerCase)
  | "UPPERCASE" => some (if ci then fun c => jIsUpperCase c || jIsLowerCase c || jIsTitleCase c else jIsUpperCase)
  | "PUNCTUATION" => some (fun c => isPunctGc (gcat c))
  | "WHITESPACE" | "WHITE_SPACE" => some jWhiteSpace
  | "WORD" => some jWord
  | "JOINCONTROL" | "JOIN_CONTROL" => some (fun c => c == 0x200C || c == 0x200D)
  | "CONTROL" => some jControl
  | "HEXDIGIT" | "HEX_DIGIT" => some jHexDigit
  | _ => posixU name ci

/-- `forProperty` (268–390): general categories, the ASCII POSIX classes, `java…` methods. -/
def forProperty (name : String) (ci : Bool) : Option (Nat → Bool) :=
  let cat (gs : List Nat) : Option (Nat → Bool) := some fun c => gs.contains (gcat c)
  let ciCase : List Nat := [1, 2, 3]
  match name with
  | "Lu" => cat (if ci then ciCase else [1])
  | "Ll" => cat (if ci then ciCase else [2])
  | "Lt" => cat (if ci then ciCase else [3])
  | "Lm" => cat [4] | "Lo" => cat [5] | "Mn" => cat [6] | "Me" => cat [7] | "Mc" => cat [8]
  | "Nd" => cat [9] | "Nl" => cat [10] | "No" => cat [11] | "Zs" => cat [12] | "Zl" => cat [13]
  | "Zp" => cat [14] | "Cc" => cat [15] | "Cf" => cat [16] | "Pd" => cat [20] | "Ps" => cat [21]
  | "Pe" => cat [22] | "Pc" => cat [23] | "Po" => cat [24] | "Sm" => cat [25] | "Sc" => cat [26]
  | "Sk" => cat [27] | "So" => cat [28] | "Pi" => cat [29] | "Pf" => cat [30]
  | "L" => cat [1, 2, 3, 4, 5] | "M" => cat [6, 7, 8] | "N" => cat [9, 10, 11]
  | "Z" => cat [12, 13, 14] | "P" => cat [20, 21, 22, 23, 24, 29, 30] | "S" => cat [25, 26, 27, 28]
  | "LC" => cat [1, 2, 3] | "LD" => cat [1, 2, 3, 4, 5, 9]
  | "L1" => some fun c => c ≤ 0xFF
  | "ASCII" => some fun c => c ≤ 0x7F
  | "Alnum" => some J.P.alnum.eval | "Alpha" => some J.P.alpha.eval | "Blank" => some J.P.blank.eval
  | "Cntrl" => some J.P.cntrl.eval | "Digit" => some J.P.digit.eval | "Graph" => some J.P.graph.eval
  | "Lower" => some (if ci then J.P.alpha.eval else J.P.lower.eval)
  | "Print" => some J.P.print.eval | "Punct" => some J.P.punct.eval | "Space" => some J.P.space.eval
  | "Upper" => some (if ci then J.P.alpha.eval else J.P.upper.eval)
  | "XDigit" => some J.P.xdigit.eval
  | "javaLowerCase" => some (if ci then fun c => jIsLowerCase c || jIsUpperCase c || jIsTitleCase c else jIsLowerCase)
  | "javaUpperCase" => some (if ci then fun c => jIsUpperCase c || jIsLowerCase c || jIsTitleCase c else jIsUpperCase)
  | "javaAlphabetic" => some jIsAlphabetic
  | "javaDigit" => some jIsDigit
  | "javaLetter" => some jIsLetter
  | "javaLetterOrDigit" => some jIsLetterOrDigit
  | _ => none

/-- `family(singleLetter, isComplement)` (3018–3100) without `In…`, scripts and `name=value`
forms: `Is…` names, then (`UNICODE_CHARACTER_CLASS`) POSIX names, then `forProperty`. -/
def familyPred (name : String) (ucc ci : Bool) : Option (Nat → Bool) :=
  if name.startsWith "Is" then
    let short := String.ofList (name.toList.drop 2)
    unicodeProp short ci <|> forProperty short ci
  else
    (if ucc then posixU name ci else none) <|> forProperty name ci

/-- `hasBaseCharacter` (Pattern.java 5599–5613): from `i` back to the region start, over
non-spacing marks, to a letter or digit. On UTF-16 units, one unit at a time, as Java does. -/
def hasBaseCharacter (c : J.MCtx) (i : Nat) : Bool := Id.run do
  let mut x := i
  for _ in [0:i + 1] do
    let ch := (c.cpAt x).1
    if jIsLetterOrDigit ch then return true
    if gcat ch != 6 then return false
    if x == 0 then return false
    x := x - 1
  return false

/-- `UNICODE_CHARACTER_CLASS` word characters: `CharPredicates.WORD()` (round 4's `uWord` had no
marks, letter numbers or join controls; round 4's letters stand for the code points it drew). -/
def uWord (c : Nat) : Bool :=
  J.uLetterCp c || uDigit c || c == 0x5F || c == 0x203F || c == 0x2040 ||
  gcat c == 6 || gcat c == 7 || gcat c == 8 || gcat c == 10 || c == 0x200C || c == 0x200D

/-! ## Flags and character predicates -/

/-- `Pattern`'s flags as the parser holds them (`flags0`). -/
structure Fl where
  ci : Bool := false
  ml : Bool := false
  dotall : Bool := false
  comments : Bool := false
  uc : Bool := false
  unix : Bool := false
  ucc : Bool := false
  canon : Bool := false
  /-- Toggle: `Bound` without the non-spacing-mark rule. -/
  noMn : Bool := false
  /-- Toggle: `.` and `$` with only `\n` and `\r` as line terminators. -/
  asciiTerm : Bool := false
  deriving BEq, Repr, Inhabited

def Fl.ucase (f : Fl) : Bool := f.uc || f.ucc

abbrev Pred := Nat → Bool

/-- `single(ch)`: `Single`, `SingleI` (ASCII letters under `i`) or `SingleU` (under `i` with
Unicode case). -/
def singleP (fl : Fl) (ch : Nat) : Pred :=
  if fl.ci then
    if fl.ucase then
      let upper := toUpperCp ch
      let lower := toLowerCp upper
      if upper != lower then fun c => c == lower || lower == toLowerCp (toUpperCp c)
      else fun c => c == ch
    else if isAsciiAlpha ch then
      let l := aLower ch
      let u := aUpper ch
      fun c => c == l || c == u
    else fun c => c == ch
  else fun c => c == ch

/-- A single character inside a class: `bitsOrSingle` (a `BitClass` bit with its case partners
under `i`, or `single` for the code points whose case mapping leaves Latin-1). -/
def classSingle (fl : Fl) (ch : Nat) : Pred :=
  let excl := [0xFF, 0xB5, 0x49, 0x69, 0x53, 0x73, 0x4B, 0x6B, 0xC5, 0xE5]
  if ch < 256 && !(fl.ci && fl.ucase && excl.contains ch) then
    if fl.ci then
      if ch < 128 then fun c => c == ch || c == aLower ch || c == aUpper ch
      else if fl.ucase then fun c => c == ch || c == toLowerCp ch || c == toUpperCp ch
      else fun c => c == ch
    else fun c => c == ch
  else singleP fl ch

/-- `range(…)`: `Range`, `CIRange`, `CIRangeU`. -/
def rangeP (fl : Fl) (lo hi : Nat) : Pred :=
  let inR (c : Nat) : Bool := lo ≤ c && c ≤ hi
  if fl.ci then
    if fl.ucase then fun c => inR c || inR (toUpperCp c) || inR (toLowerCp (toUpperCp c))
    else fun c => inR c || (c < 128 && (inR (aUpper c) || inR (aLower c)))
  else inR

def dotP (fl : Fl) : Pred :=
  if fl.dotall then fun _ => true
  else if fl.unix then fun c => c != 0x0A
  else if fl.asciiTerm then fun c => c != 0x0A && c != 0x0D
  else fun c => !J.isTerminator c

/-- The predefined classes, with `UNICODE_CHARACTER_CLASS`. -/
def digitP (fl : Fl) : Pred := if fl.ucc then uDigit else fun c => 0x30 ≤ c && c ≤ 0x39
def wordP (fl : Fl) : Pred := if fl.ucc then uWord else J.asciiWord
def spaceP (fl : Fl) : Pred := if fl.ucc then uSpace else fun c => c == 0x20 || (0x09 ≤ c && c ≤ 0x0D)

/-! ## The compiled pattern -/

/-- Which node a quantifier becomes: `Ques` (`?`), `Curly` (over an atom, or `GroupCurly` over a
deterministic group), `Loop` (`Prolog`/`Loop` over a non-deterministic group). It decides the
lookbehind length study only; matching is the same backtracking for all three. -/
inductive QNode where
  | ques | curly | loop
  deriving BEq, Repr, Inhabited

inductive N where
  | empty
  | pred (p : Pred)
  | seq (a b : N)
  | alt (a b : N)
  | group (idx : Nat) (r : N)
  | ncgroup (r : N)
  | quant (r : N) (min max : Nat) (k : J.QK) (node : QNode)
  | begin_
  | caret (unix : Bool)
  | dollar (ml unix : Bool) (asciiT : Bool)
  | wordB (neg : Bool) (uni : Bool) (mn : Bool)
  | endz
  | lastMatch
  | look (neg : Bool) (r : N)
  | behind (neg : Bool) (r : N) (rmin rmax : Int) (supp : Bool)
  | atomic (r : N)
  | backref (n : Nat) (ci uc : Bool)
  | linebreak
  | unsupported (what : String)
  deriving Inhabited

def N.unsupportedIn : N → Option String
  | .unsupported w => some w
  | .seq a b | .alt a b => a.unsupportedIn <|> b.unsupportedIn
  | .group _ r | .ncgroup r | .quant r _ _ _ _ | .look _ r | .behind _ r _ _ _ | .atomic r => r.unsupportedIn
  | _ => none

def N.hasGroup : N → Bool
  | .group _ _ => true
  | .seq a b | .alt a b => a.hasGroup || b.hasGroup
  | .ncgroup r | .quant r _ _ _ _ | .look _ r | .behind _ r _ _ _ | .atomic r => r.hasGroup
  | _ => false

/-- A capture made inside a lookaround or an atomic group, or a possessive repeat (the places
where Java keeps a capture that the rest of the pattern did not use). -/
def N.keepsCaptures : N → Bool
  | .look _ r | .behind _ r _ _ _ | .atomic r => r.hasGroup
  | .quant r _ _ .possessive _ => r.hasGroup || r.keepsCaptures
  | .seq a b | .alt a b => a.keepsCaptures || b.keepsCaptures
  | .group _ r | .ncgroup r | .quant r _ _ _ _ => r.keepsCaptures
  | _ => false

/-! ## `TreeInfo`: the lengths a lookbehind needs -/

/-- Java `int` arithmetic. -/
def w32 (x : Int) : Int :=
  let m : Int := 4294967296
  let r := x % m
  if r ≥ 2147483648 then r - m else r

def maxReps : Nat := 0x7FFFFFFF

structure TI where
  minL : Int := 0
  maxL : Int := 0
  maxValid : Bool := true
  det : Bool := true
  deriving Repr, Inhabited

/-- `study(info)` along the node (lengths in characters). -/
partial def study : N → TI → TI
  | .empty, t => t
  | .pred _, t => { t with minL := w32 (t.minL + 1), maxL := w32 (t.maxL + 1) }
  | .linebreak, t => { t with minL := w32 (t.minL + 1), maxL := w32 (t.maxL + 2) }
  | .seq a b, t => study b (study a t)
  | .alt a b, t =>
    let ta := study a {}
    let tb := study b {}
    { minL := w32 (t.minL + min ta.minL tb.minL), maxL := w32 (t.maxL + max ta.maxL tb.maxL),
      maxValid := t.maxValid && ta.maxValid && tb.maxValid, det := false }
  | .group _ r, t | .ncgroup r, t => study r t
  | .atomic r, t => study r t
  | .backref _ _ _, t => { t with maxValid := false }
  | .quant r mn mx _ node, t =>
    match node with
    | .loop => { t with maxValid := false, det := false }
    | .ques =>
      let ta := study r {}
      { minL := t.minL, maxL := w32 (t.maxL + ta.maxL), maxValid := t.maxValid && ta.maxValid, det := false }
    | .curly =>
      let ta := study r {}
      let tmin := w32 (ta.minL * mn + t.minL)
      let minL := if tmin < t.minL then 0xFFFFFFF else tmin
      let (maxL, mv) :=
        if t.maxValid && ta.maxValid then
          let temp := w32 (ta.maxL * mx)
          let ml := w32 (t.maxL + temp)
          (ml, !(temp < t.maxL))
        else (t.maxL, false)
      let det := ta.det && mn == mx && t.det
      { minL, maxL, maxValid := mv, det }
  | _, t => t

/-! ## Parsing (`Pattern.compile`) -/

structure PS where
  pat : Array Nat
  cur : Nat := 0
  groups : Nat := 0
  names : List (List Nat × Nat) := []
  fl : Fl := {}
  /-- `hasSupplementary` set by a predicate that is not a `BmpCharPredicate` (Pattern.java
  `newCharProperty` 3101-3108, `family`'s complement 3091-3096): a negated class or escape, a Unicode
  category or property, `(?U)`'s classes. The matcher then starts with `StartS`, which never starts
  between the two halves of a surrogate pair. -/
  nonBmp : Bool := false
  deriving Inhabited

abbrev PM := StateT PS (Except J.PErr)

def perr {α : Type} (m : String) : PM α := fun _ => .error (.syntax m)

def markNonBmp : PM Unit := modify fun s => { s with nonBmp := true }

def isSpaceA (c : Nat) : Bool := c == 0x20 || c == 0x09 || c == 0x0A || c == 0x0B || c == 0x0C || c == 0x0D

def isLineSep (unix : Bool) (c : Nat) : Bool :=
  if unix then c == 0x0A else c == 0x0A || c == 0x0D || c == 0x85 || c == 0x2028 || c == 0x2029

/-- `peekPastWhitespace`: under `COMMENTS`, ASCII whitespace and `#…` up to a line separator are
skipped. -/
def skipFrom (pat : Array Nat) (unix : Bool) (cur : Nat) : Nat := Id.run do
  let mut i := cur
  for _ in [0:pat.size + 1] do
    let c := pat.getD i 0
    if i < pat.size && isSpaceA c then i := i + 1
    else if i < pat.size && c == 0x23 then
      i := i + 1
      for _ in [0:pat.size + 1] do
        if i < pat.size && !isLineSep unix (pat.getD i 0) then i := i + 1
    else break
  return i

def skipWs : PM Unit := modify fun s =>
  if s.fl.comments then { s with cur := skipFrom s.pat s.fl.unix s.cur } else s

/-- `peek()`: 0 past the end; skips whitespace first under `COMMENTS`. -/
def peek : PM Nat := do skipWs; let s ← get; return s.pat.getD s.cur 0
/-- The `k`-th character after the current one, as written. -/
def peekAt (k : Nat) : PM Nat := do let s ← get; return s.pat.getD (s.cur + k) 0
def atEnd : PM Bool := do skipWs; let s ← get; return s.cur ≥ s.pat.size
def adv : PM Unit := modify fun s => { s with cur := s.cur + 1 }
def read : PM Nat := do let c ← peek; adv; return c
/-- A character read as written (after a backslash, or the group type after `(?`). -/
def readRaw : PM Nat := do let s ← get; adv; return s.pat.getD s.cur 0
def peekRaw : PM Nat := do let s ← get; return s.pat.getD s.cur 0

def isHex (c : Nat) : Bool := J.isHex c
def hexVal (c : Nat) : Nat := J.hexVal c
def isOct (c : Nat) : Bool := J.isOct c
def isDig (c : Nat) : Bool := J.isDig c

inductive Esc where
  | ch (c : Nat)
  | pred (p : Pred)
  | node (n : N)

/-- `escape(inclass, create, isrange)` after the backslash. -/
def escape (inclass : Bool) (isrange : Bool) (groupsSoFar : Nat) : PM Esc := do
  let fl := (← get).fl
  let c ← readRaw
  let bad : PM Esc := perr "Illegal/unsupported escape sequence"
  if c == 0x30 then
    let n ← read
    if !isOct n then return ← perr "Illegal octal escape sequence"
    let m ← peek
    if !isOct m then return .ch (n - 0x30) else
    adv
    let o ← peek
    if isOct o && n ≤ 0x33 then adv; return .ch ((n - 0x30) * 64 + (m - 0x30) * 8 + (o - 0x30))
    return .ch ((n - 0x30) * 8 + (m - 0x30))
  if 0x31 ≤ c && c ≤ 0x39 then
    if inclass then return ← bad
    let rec more : Nat → Nat → PM Nat
      | 0, r => return r
      | f + 1, r => do
        let d ← peekRaw
        if isDig d then
          let r' := r * 10 + (d - 0x30)
          if groupsSoFar < r' then return r
          else adv; more f r'
        else return r
    let r ← more 8 (c - 0x30)
    return .node (.backref r fl.ci fl.ucase)
  match c with
  | 0x41 => if inclass then bad else return .node .begin_
  | 0x42 => if inclass then bad else return .node (.wordB true fl.ucc (!fl.noMn))
  | 0x44 => markNonBmp; let p := digitP fl; return .pred (fun x => !p x)
  | 0x47 => if inclass then bad else return .node .lastMatch
  | 0x48 => markNonBmp; return .pred (fun x => !(J.P.hspace.eval x))
  | 0x4E => return .node (.unsupported "\\N{…}")
  | 0x52 => if inclass then bad else return .node .linebreak
  | 0x53 => markNonBmp; let p := spaceP fl; return .pred (fun x => !p x)
  | 0x56 => markNonBmp; return .pred (fun x => !(J.P.vspace.eval x))
  | 0x57 => markNonBmp; let p := wordP fl; return .pred (fun x => !p x)
  | 0x58 => if inclass then bad else return .node (.unsupported "\\X")
  | 0x5A => if inclass then bad else return .node (.dollar false fl.unix fl.asciiTerm)
  | 0x61 => return .ch 7
  | 0x62 =>
    if inclass then bad else
    if (← peekRaw) == 0x7B && (← peekAt 1) == 0x67 then
      if (← peekAt 2) == 0x7D then adv; adv; adv; return .node (.unsupported "\\b{g}")
      else return ← bad
    return .node (.wordB false fl.ucc (!fl.noMn))
  | 0x63 =>
    if (← get).cur ≥ (← get).pat.size then perr "Illegal control escape sequence" else
    let x ← readRaw
    return .ch (x ^^^ 64)
  | 0x64 => (if fl.ucc then markNonBmp else pure ()); return .pred (digitP fl)
  | 0x65 => return .ch 0x1B
  | 0x66 => return .ch 0x0C
  | 0x68 => return .pred J.P.hspace.eval
  | 0x6B =>
    if inclass then bad else
    if (← readRaw) != 0x3C then perr "\\k is not followed by '<' for named capturing group" else
    let rec nm : Nat → List Nat → PM (List Nat)
      | 0, acc => return acc.reverse
      | g + 1, acc => do
        let x ← readRaw
        if x == 0x3E then return acc.reverse
        if isAsciiAlpha x || isDig x then nm g (x :: acc)
        else perr "named capturing group is missing trailing '>'"
    let name ← nm 64 []
    match (← get).names.find? (·.1 == name) with
    | some (_, idx) => return .node (.backref idx fl.ci fl.ucase)
    | none => perr "named capturing group does not exist"
  | 0x6E => return .ch 0x0A
  | 0x72 => return .ch 0x0D
  | 0x73 => (if fl.ucc then markNonBmp else pure ()); return .pred (spaceP fl)
  | 0x74 => return .ch 0x09
  | 0x75 =>
    let mut v := 0
    for _ in [0:4] do
      let h ← readRaw
      if !isHex h then return ← perr "Illegal Unicode escape sequence"
      v := v * 16 + hexVal h
    return .ch v
  | 0x76 => if isrange then return .ch 0x0B else return .pred J.P.vspace.eval
  | 0x77 => (if fl.ucc then markNonBmp else pure ()); return .pred (wordP fl)
  | 0x78 =>
    let n ← readRaw
    if isHex n then
      let m ← readRaw
      if isHex m then return .ch (hexVal n * 16 + hexVal m)
      perr "Illegal hexadecimal escape sequence"
    else if n == 0x7B && isHex (← peekRaw) then
      let mut v := 0
      for _ in [0:8] do
        let h ← peekRaw
        if isHex h then adv; v := v * 16 + hexVal h
      if (← readRaw) != 0x7D then return ← perr "Unclosed hexadecimal escape sequence"
      if v > 0x10FFFF then return ← perr "Hexadecimal codepoint is too big"
      return .ch v
    else perr "Illegal hexadecimal escape sequence"
  | 0x7A => if inclass then bad else return .node .endz
  | _ =>
    if isAsciiAlpha c then bad
    else if c == 0 && (← get).cur > (← get).pat.size then perr "Unexpected internal error"
    else return .ch c

/-- `\p`/`\P` after the letter (the POSIX/ASCII families of round 3's model). -/
def familyEsc (comp : Bool) : PM Pred := do
  let c ← peekRaw
  let name ← if c == 0x7B then
      adv
      let rec nm : Nat → List Nat → PM (List Nat)
        | 0, acc => return acc.reverse
        | f + 1, acc => do
          let d ← peekRaw
          if d == 0x7D then adv; return acc.reverse
          if (← get).cur ≥ (← get).pat.size then perr "Unclosed character family" else
          adv; nm f (d :: acc)
      nm 64 []
    else do adv; pure [c]
  let fl := (← get).fl
  if name.isEmpty then return ← perr "Empty character family"
  let nameS := String.ofList (name.map Char.ofNat)
  let bmpNames := ["ASCII", "Alnum", "Alpha", "Blank", "Cntrl", "Digit", "Graph", "Lower", "Print", "Punct",
    "Space", "Upper", "XDigit", "L1"]
  -- `ctype`/`range` predicates are `BmpCharPredicate`s; categories, properties, `java…` methods and
  -- `(?U)`'s POSIX names are not, nor is any complement
  if comp || !(bmpNames.contains nameS && !(fl.ucc && nameS != "ASCII" && nameS != "L1")) then markNonBmp
  match familyPred nameS fl.ucc fl.ci with
  | some p => return if comp then (fun x => !p x) else p
  | none => perr "Unknown character property name (spec model)"

mutual
/-- `clazz(consume)`: the cursor is past `[`. -/
def clazz : Nat → PM Pred
  | 0 => perr "fuel"
  | f + 1 => do
    let mut isNeg := false
    if (← peek) == 0x5E then adv; isNeg := true
    let mut prev : Option Pred := none
    for _ in [0:(← get).pat.size + 1] do
      let c ← peek
      if c == 0x5B then
        adv
        let p ← clazz f
        prev := some (match prev with | none => p | some q => fun x => q x || p x)
        continue
      if c == 0x26 && (← peekAt 1) == 0x26 then
        adv; adv
        let mut right : Option Pred := none
        for _ in [0:(← get).pat.size + 1] do
          let d ← peek
          if d == 0x5D || (d == 0x26 && (← peekAt 1) == 0x26) then break
          if ← atEnd then break
          if d == 0x5B then
            adv
            let p ← clazz f
            right := some (match right with | none => p | some q => fun x => q x || p x)
          else
            let p ← rangeTerm f
            right := some (match right with | none => p | some q => fun x => q x || p x)
        match prev, right with
        | none, none => return ← perr "Bad class syntax"
        | none, some r => prev := some r
        | some p, some r => prev := some (fun x => p x && r x)
        | some p, none => prev := some p
        continue
      if ← atEnd then return ← perr "Unclosed character class"
      if c == 0x5D && prev.isSome then
        adv
        let p := prev.getD (fun _ => false)
        if isNeg then markNonBmp
        return if isNeg then (fun x => !p x) else p
      let p ← rangeTerm f
      prev := some (match prev with | none => p | some q => fun x => q x || p x)
    perr "Unclosed character class"
/-- `range(bits)`: one member of a class. -/
def rangeTerm : Nat → PM Pred
  | 0 => perr "fuel"
  | _ + 1 => do
    let fl := (← get).fl
    let c ← peek
    let start ← if c == 0x5C then
        adv
        let e ← peekRaw
        if e == 0x70 || e == 0x50 then
          adv
          return ← familyEsc (e == 0x50)
        let isrange := (← peekAt 1) == 0x2D
        match ← escape true isrange 0 with
        | .pred p => return p
        | .ch ch => pure ch
        | .node _ => perr "Illegal/unsupported escape sequence"
      else do adv; pure c
    if (← peek) == 0x2D then
      let endRange ← peekAt 1
      if endRange == 0x5B then return classSingle fl start
      if endRange != 0x5D then
        adv
        let m ← peek
        let hi ← if m == 0x5C then
            adv
            match ← escape true true 0 with
            | .ch ch => pure ch
            | _ => perr "Illegal character range"
          else do adv; pure m
        if hi < start then perr "Illegal character range"
        else return rangeP fl start hi
    return classSingle fl start
end

/-- `closure(prev)`. -/
def closure (prev : N) (isGroup : Bool) (det : Bool) : PM N := do
  let c ← peek
  let node (mn mx : Nat) : QNode :=
    if mn == 0 && mx == 1 then .ques else if isGroup && !det then .loop else .curly
  let suffix (min max : Nat) : PM N := do
    let d ← peek
    if d == 0x3F then adv; return .quant prev min max .lazy (node min max)
    if d == 0x2B then adv; return .quant prev min max .possessive (if min == 0 && max == 1 then .ques else .curly)
    return .quant prev min max .greedy (node min max)
  if c == 0x3F then adv; suffix 0 1
  else if c == 0x2A then adv; suffix 0 maxReps
  else if c == 0x2B then adv; suffix 1 maxReps
  else if c == 0x7B then
    if !isDig (← peekAt 1) then perr "Illegal repetition" else
    adv
    let rec num : Nat → Nat → PM Nat
      | 0, v => return v
      | f + 1, v => do
        let d ← peek
        if isDig d then adv; num f (v * 10 + (d - 0x30)) else return v
    let cmin ← num 10 0
    let mut cmax := cmin
    if (← peek) == 0x2C then
      adv
      cmax := maxReps
      if (← peek) != 0x7D then cmax ← num 10 0
    if (← peek) != 0x7D then perr "Unclosed counted closure" else
    adv
    if cmax < cmin || cmin > maxReps || cmax > maxReps then perr "Illegal repetition range" else
    suffix cmin cmax
  else return prev

/-- Whether the pattern holds a supplementary character at or after `from` (`findSupplementary`). -/
def suppFrom (from_ : Nat) : PM Bool := do
  let s ← get
  return (s.pat.toList.drop from_).any (· ≥ 0x10000)

/-- `addFlag()` / `subFlag()`: flag letters (whitespace skipped under `x` as soon as it is on). -/
def flagLetters (neg : Bool) : Nat → PM Unit
  | 0 => pure ()
  | f + 1 => do
    let ch ← peek
    let set (g : Fl → Fl) : PM Unit := do modify fun s => { s with fl := g s.fl }; adv; flagLetters neg f
    match ch with
    | 0x69 => set fun l => { l with ci := !neg }
    | 0x6D => set fun l => { l with ml := !neg }
    | 0x73 => set fun l => { l with dotall := !neg }
    | 0x64 => set fun l => { l with unix := !neg }
    | 0x75 => set fun l => { l with uc := !neg }
    | 0x63 => set fun l => { l with canon := !neg }
    | 0x78 => set fun l => { l with comments := !neg }
    | 0x55 => set fun l => { l with ucc := !neg, uc := !neg }
    | 0x2D => if neg then pure () else do adv; flagLetters true f
    | _ => pure ()

mutual
def expr : Nat → PM N
  | 0 => perr "fuel"
  | f + 1 => do
    let a ← sequence f
    if (← peek) == 0x7C && !(← atEnd) then
      adv
      let b ← expr f
      return .alt a b
    return a
def sequence : Nat → PM N
  | 0 => perr "fuel"
  | f + 1 => do
    let mut acc : N := .empty
    for _ in [0:(← get).pat.size + 1] do
      if ← atEnd then break
      let c ← peek
      if c == 0x7C || c == 0x29 then break
      let fl := (← get).fl
      let node? ← (do
        if c == 0x28 then
          adv
          group0 f
        else if c == 0x5B then
          adv
          let p ← clazz f
          some <$> closure (.pred p) false true
        else if c == 0x5C then
          let e ← peekAt 1
          if e == 0x70 || e == 0x50 then
            adv; adv
            let p ← familyEsc (e == 0x50)
            some <$> closure (.pred p) false true
          else
            adv
            match ← escape false false (← get).groups with
            | .ch ch => some <$> closure (.pred (singleP fl ch)) false true
            | .pred p => some <$> closure (.pred p) false true
            | .node n => some <$> closure n false true
        else if c == 0x5E then adv; some <$> closure (if fl.ml then .caret fl.unix else .begin_) false true
        else if c == 0x24 then adv; some <$> closure (.dollar fl.ml fl.unix fl.asciiTerm) false true
        else if c == 0x2E then adv; some <$> closure (.pred (dotP fl)) false true
        else if c == 0x3F || c == 0x2A || c == 0x2B then
          perr s!"Dangling meta character '{Char.ofNat c}'"
        else if c == 0x7B then some <$> closure .empty false true
        else do adv; some <$> closure (.pred (singleP fl c)) false true : PM (Option N))
      match node? with
      | none => pure ()
      | some node =>
        acc := match acc with
          | .empty => node
          | a => .seq a node
    return acc
/-- `group0()`: the cursor is past `(`; `none` for an inline flag group `(?i)`. -/
def group0 : Nat → PM (Option N)
  | 0 => perr "fuel"
  | f + 1 => do
    let save := (← get).fl
    let start := (← get).cur
    let c ← peek
    let r ← (do
      if c == 0x3F then
        adv
        let d ← readRaw
        if d == 0x3A then
          let r ← expr f
          pure (some (N.ncgroup r, true))
        else if d == 0x3D || d == 0x21 then
          let r ← expr f
          pure (some (N.look (d == 0x21) r, true))
        else if d == 0x3E then
          let r ← expr f
          pure (some (N.atomic r, true))
        else if d == 0x3C then
          let e ← read
          if e == 0x3D || e == 0x21 then
            let r ← expr f
            let t := study r {}
            if !t.maxValid then perr "Look-behind group does not have an obvious maximum length" else
            let supp ← suppFrom start
            pure (some (N.behind (e == 0x21) r t.minL t.maxL supp, true))
          else
            if !isAsciiAlpha e then perr "capturing group name does not start with a Latin letter" else
            let rec nm : Nat → List Nat → PM (List Nat)
              | 0, acc => return acc.reverse
              | g + 1, acc => do
                let x ← read
                if x == 0x3E then return acc.reverse
                if isAsciiAlpha x || isDig x then nm g (x :: acc)
                else perr "named capturing group is missing trailing '>'"
            let name ← nm 64 [e]
            if (← get).names.any (·.1 == name) then perr "Named capturing group is already defined" else
            let idx := (← get).groups + 1
            modify fun s => { s with groups := idx, names := (name, idx) :: s.names }
            let r ← expr f
            pure (some (N.group idx r, false))
        else if d == 0x24 || d == 0x40 then perr "Unknown group type"
        else
          modify fun s => { s with cur := s.cur - 1 }
          flagLetters false 32
          let x ← read
          if x == 0x29 then pure none
          else if x != 0x3A then perr "Unknown inline modifier"
          else
            let r ← expr f
            pure (some (N.ncgroup r, true))
      else
        let idx := (← get).groups + 1
        modify fun s => { s with groups := idx }
        let r ← expr f
        pure (some (N.group idx r, false)) : PM (Option (N × Bool)))
    match r with
    | none => return none
    | some (body, _) =>
      if (← peek) != 0x29 || (← atEnd) then perr "Unclosed group" else
      adv
      modify fun s => { s with fl := save }
      match body with
      | .look _ _ | .behind _ _ _ _ _ => some <$> closure body false true
      | .atomic _ => some <$> closure body false true
      | _ =>
        -- `GroupCurly` when the group body is deterministic, else `Prolog`/`Loop`
        let inner := match body with | .group _ r | .ncgroup r => r | b => b
        let det := (study inner {}).det
        some <$> closure body true det
end

structure JPat where
  node : N
  groups : Nat
  names : List (List Nat × Nat)
  supp : Bool
  deriving Inhabited

/-- `Pattern.compile(s)` over the pattern's code points (with `\Q…\E` quoting removed first). -/
def compile (pattern : List Nat) (noMn asciiTerm : Bool := false) : Except J.PErr JPat :=
  let pat := (J.removeQE pattern).toArray
  match (expr (4 * pat.size + 8)).run { pat, fl := { noMn, asciiTerm } } with
  | .error e => .error e
  | .ok (n, s) =>
    if s.cur < pat.size then .error (.syntax "Unmatched closing ')'")
    else .ok { node := n, groups := s.groups, names := s.names, supp := pattern.any (· ≥ 0x10000) || s.nonBmp }

/-! ## Matching: one `groups` array, written and restored as Java's nodes do -/

abbrev Groups := Array (Option (Nat × Nat))

structure MS where
  groups : Groups
  steps : Nat := 0
  /-- `matcher.last` as an atomic group or a top-level accept leaves it. -/
  tmp : Nat := 0

abbrev JM := StateT MS (Except J.JAbort)

def tick (budget : Nat) : JM Unit := do
  let s ← get
  if s.steps ≥ budget then throw .steps
  set { s with steps := s.steps + 1 }

def setG (idx : Nat) (v : Option (Nat × Nat)) : JM Unit :=
  modify fun s => { s with groups := s.groups.set! idx v }

/-- `Caret` (multiline `^`): never at the end of input; after a line terminator but not between
`\r` and `\n`. `UnixCaret`: after `\n`. -/
def caretAt (c : J.MCtx) (i : Nat) (unix : Bool) : Bool :=
  if i == c.len then false
  else if i > 0 then
    let ch := c.inp.getD (i - 1) 0
    if unix then ch == 0x0A
    else if !(ch == 0x0A || ch == 0x0D || ch == 0x85 || ch == 0x2028 || ch == 0x2029) then false
    else !(ch == 0x0D && c.inp.getD i 0 == 0x0A)
  else true

/-- `Dollar`/`UnixDollar`, multiline or not. -/
def dollarAt (c : J.MCtx) (i : Nat) (ml unix : Bool) (asciiT : Bool := false) : Bool :=
  let n := c.len
  if asciiT && !ml && !unix then
    -- the toggle: `Dollar(false)` with only `\n`, `\r\n`, `\r` before the end
    if i + 2 < n then false
    else if i + 2 == n then c.inp.getD i 0 == 0x0D && c.inp.getD (i + 1) 0 == 0x0A
    else if i < n then
      let ch := c.inp.getD i 0
      if ch == 0x0A then !(i > 0 && c.inp.getD (i - 1) 0 == 0x0D) else ch == 0x0D
    else true
  else if unix then
    if i < n then
      if c.inp.getD i 0 == 0x0A then ml || i + 1 == n else false
    else true
  else if ml then
    if i < n then
      let ch := c.inp.getD i 0
      if ch == 0x0A then !(i > 0 && c.inp.getD (i - 1) 0 == 0x0D)
      else ch == 0x0D || ch == 0x85 || ch == 0x2028 || ch == 0x2029
    else true
  else c.dollar i

/-- `Bound`: ASCII word characters (JDK ≥ 19), Unicode ones under `U`. -/
def boundAt (c : J.MCtx) (i : Nat) (uni : Bool) (mn : Bool := true) : Bool :=
  let w : Nat → Bool := if uni then uWord else J.asciiWord
  -- `Bound.check`: a non-spacing mark with a base letter or digit counts as a word character
  let left := i > 0 && (w (c.cpBefore i) || (mn && gcat (c.cpBefore i) == 6 && hasBaseCharacter c (i - 1)))
  let right := i < c.len && (w (c.cpAt i).1 || (mn && gcat (c.cpAt i).1 == 6 && hasBaseCharacter c i))
  left != right

/-- `countChars(seq, i, -n)`: the units `n` code points back from `i` take (stops at 0). -/
def unitsBack (c : J.MCtx) (i : Nat) (n : Nat) : Nat := Id.run do
  let mut x := i
  for _ in [0:n] do
    if x == 0 then break
    x := x - 1
    if J.isLowS (c.inp.getD x 0) && x > 0 && J.isHighS (c.inp.getD (x - 1) 0) then x := x - 1
  return i - x

partial def m (c : J.MCtx) (budget : Nat) : Nat → N → Nat → (Nat → JM Bool) → JM Bool
  | 0, _, _, _ => throw .depth
  | f + 1, node, i, k => do
    tick budget
    match node with
    | .empty => k i
    | .pred p =>
      if i < c.len then
        let (cp, n) := c.cpAt i
        if p cp then k (i + n) else return false
      else return false
    | .seq a b => m c budget f a i (fun j => m c budget f b j k)
    | .alt a b => if ← m c budget f a i k then return true else m c budget f b i k
    | .group idx r =>
      m c budget f r i (fun j => do
        let old := (← get).groups.getD idx none
        setG idx (some (i, j))
        if ← k j then return true
        setG idx old
        return false)
    | .ncgroup r => m c budget f r i k
    | .begin_ => if i == 0 then k i else return false
    | .caret unix => if caretAt c i unix then k i else return false
    | .dollar ml unix aT => if dollarAt c i ml unix aT then k i else return false
    | .wordB neg uni mn => if boundAt c i uni mn != neg then k i else return false
    | .endz => if i == c.len then k i else return false
    | .lastMatch => if i == c.oldLast then k i else return false
    | .linebreak =>
      if i + 1 < c.len && c.inp.getD i 0 == 0x0D && c.inp.getD (i + 1) 0 == 0x0A then
        if ← k (i + 2) then return true else k (i + 1)
      else if i < c.len && J.P.vspace.eval (c.inp.getD i 0) then k (i + 1)
      else return false
    | .look neg r =>
      -- `Pos`/`Neg`: the body runs to its own end and returns; its captures stay
      let ok ← m c budget f r i (fun _ => return true)
      if ok != neg then k i else return false
    | .behind neg r rmin rmax supp =>
      -- `Behind`/`NotBehind` (`BehindS` with a supplementary character): from `i - rmin` down to
      -- `max(i - rmax, 0)`, the body ending at `i`; captures of the success stay
      let ok ← (do
        if !supp then
          let start := w32 ((i : Int) - rmin)
          let lo := max (w32 ((i : Int) - rmax)) 0
          let rec back : Nat → Int → JM Bool
            | 0, _ => return false
            | g + 1, j =>
              if j < lo then return false else do
              if ← m c budget f r j.toNat (fun e => return e == i) then return true
              back g (j - 1)
          back (i + 2) start
        else
          let rminU := unitsBack c i (if rmin < 0 then 0 else rmin.toNat)
          let rmaxU := unitsBack c i (if rmax < 0 then i else rmax.toNat)
          let start : Int := (i : Int) - rminU
          let lo : Int := (i : Int) - rmaxU
          let rec backS : Nat → Int → JM Bool
            | 0, _ => return false
            | g + 1, j =>
              if j < lo || j < 0 then return false else do
              if ← m c budget f r j.toNat (fun e => return e == i) then return true
              let step : Int := if j > lo then unitsBack c j.toNat 1 else 1
              backS g (j - step)
          backS (i + 2) start : JM Bool)
      if ok != neg then k i else return false
    | .atomic r =>
      let ok ← m c budget f r i (fun j => do modify fun s => { s with tmp := j }; return true)
      if ok then k (← get).tmp else return false
    | .backref n ci uc =>
      match (← get).groups.getD n none with
      | none => return false
      | some (s, e) =>
        let len := e - s
        if i + len > c.len then return false
        let eqU (a b : Nat) : Bool :=
          a == b || (ci && (if uc then toUpperCp a == toUpperCp b || toLowerCp (toUpperCp a) == toLowerCp (toUpperCp b)
                            else aLower a == aLower b))
        if (List.range len).all (fun t => eqU (c.inp.getD (s + t) 0) (c.inp.getD (i + t) 0)) then k (i + len)
        else return false
    | .unsupported w => throw (.unsupported w)
    | .quant r mn mx kind _ =>
      match kind with
      | .possessive =>
        -- iterations that never give back; their captures stay
        let one (j : Nat) : JM (Option Nat) := do
          if ← m c budget f r j (fun j' => do modify fun s => { s with tmp := j' }; return true) then
            return some (← get).tmp
          else return none
        let rec mins : Nat → Nat → JM (Option Nat)
          | 0, j => return some j
          | t + 1, j => do
            match ← one j with
            | some j' => mins t j'
            | none => return none
        let rec more : Nat → Nat → Nat → JM Nat
          | 0, _, j => return j
          | t + 1, cnt, j => do
            if cnt ≥ mx then return j
            match ← one j with
            | some j' => if j' == j then return j else more t (cnt + 1) j'
            | none => return j
        match ← mins mn i with
        | none => return false
        | some j =>
          let j ← more (c.len + 2) mn j
          k j
      | .greedy =>
        let rec after : Nat → Nat → Nat → Nat → JM Bool
          | 0, _, _, _ => throw .depth
          | g + 1, j, cnt, s =>
            if j > s then
              if cnt < mn then m c budget f r j (fun j' => after g j' (cnt + 1) j)
              else if cnt < mx then do
                if ← m c budget f r j (fun j' => after g j' (cnt + 1) j) then return true
                k j
              else k j
            else k j
        let fuelA := c.len + mn + 2
        if 0 < mn then m c budget f r i (fun j => after fuelA j 1 i)
        else if 0 < mx then do
          if ← m c budget f r i (fun j => after fuelA j 1 i) then return true
          k i
        else k i
      | .lazy =>
        let rec lafter : Nat → Nat → Nat → Nat → JM Bool
          | 0, _, _, _ => throw .depth
          | g + 1, j, cnt, s =>
            if j > s then
              if cnt < mn then m c budget f r j (fun j' => lafter g j' (cnt + 1) j)
              else do
                if ← k j then return true
                if cnt < mx then m c budget f r j (fun j' => lafter g j' (cnt + 1) j)
                else return false
            else k j
        let fuelA := c.len + mn + 2
        if 0 < mn then m c budget f r i (fun j => lafter fuelA j 1 i)
        else do
          if ← k i then return true
          if 0 < mx then m c budget f r i (fun j => lafter fuelA j 1 i)
          else return false

/-! ## `Matcher` -/

/-- How the start-position loop treats the groups: Java's (`resetPerStart = false`: cleared once
per `find()`), or cleared before every start position (the toggle that classifies the deviation
where libstdc++ starts each position clean). -/
structure JFix where
  resetPerStart : Bool := false
  deriving BEq, Repr, Inhabited

/-- One attempt at `i`; on success the end and the groups. -/
def matchAt (p : JPat) (c : J.MCtx) (i : Nat) (whole : Bool) (lim : J.Lim) (st : MS) :
    Except J.JAbort (Option Nat × MS) :=
  let k : Nat → JM Bool := fun j =>
    if whole && j != c.len then return false
    else do modify fun s => { s with tmp := j }; return true
  match (m c lim.budget lim.fuel p.node i k).run st with
  | .error e => .error e
  | .ok (true, st') => .ok (some st'.tmp, st')
  | .ok (false, st') => .ok (none, st')

def freshGroups (p : JPat) : Groups := Array.replicate (p.groups + 1) none

/-- `Matcher.search(from)`: groups cleared once, then `Start`/`StartS` over the positions. -/
def searchFrom (p : JPat) (c : J.MCtx) (from_ : Nat) (lim : J.Lim) (steps : Nat) (fx : JFix) :
    Except J.JAbort (Option (Nat × Nat × Groups) × Nat) :=
  let rec go : Nat → Nat → MS → Except J.JAbort (Option (Nat × Nat × Groups) × Nat)
    | 0, _, st => .ok (none, st.steps)
    | f + 1, i, st =>
      if i > c.len then .ok (none, st.steps)
      else
        let st := if fx.resetPerStart then { st with groups := freshGroups p } else st
        match matchAt p c i false lim st with
        | .error e => .error e
        | .ok (some j, st') => .ok (some (i, j, st'.groups), st'.steps)
        | .ok (none, st') =>
          let step := if p.supp && J.isHighS (c.inp.getD i 0) && i + 1 < c.len && J.isLowS (c.inp.getD (i + 1) 0) then 2 else 1
          go f (i + step) st'
  go (c.len + 2) from_ { groups := freshGroups p, steps }

/-- `Matcher.find()` (state as in round 3: `first`, `last`, `oldLast`). -/
def find (p : JPat) (inp : Array Nat) (ms : J.MState) (lim : J.Lim) (steps : Nat) (fx : JFix) :
    Except J.JAbort (Option (Nat × Nat × Groups) × J.MState × Nat) :=
  let next := if ms.first == some ms.last then ms.last + 1 else ms.last
  if next > inp.size then .ok (none, { ms with first := none }, steps)
  else
    let c : J.MCtx := { inp, oldLast := ms.oldLast.getD next }
    match searchFrom p c next lim steps fx with
    | .error e => .error e
    | .ok (none, st) => .ok (none, { ms with first := none, oldLast := some ms.last }, st)
    | .ok (some (s, e, gs), st) => .ok (some (s, e, gs), { first := some s, last := e, oldLast := some e }, st)

def findAll (p : JPat) (inp : Array Nat) (lim : J.Lim) (fx : JFix) : Except J.JAbort (List (Nat × Nat × Groups)) :=
  let rec go : Nat → J.MState → Nat → List (Nat × Nat × Groups) → Except J.JAbort (List (Nat × Nat × Groups))
    | 0, _, _, acc => .ok acc.reverse
    | f + 1, ms, st, acc =>
      match find p inp ms lim st fx with
      | .error e => .error e
      | .ok (none, _, _) => .ok acc.reverse
      | .ok (some x, ms', st') => go f ms' st' (x :: acc)
  go (2 * inp.size + 4) {} 0 []

/-- `Matcher.matches()`. -/
def matchesAll (p : JPat) (inp : Array Nat) (lim : J.Lim) : Except J.JAbort (Option (Nat × Groups)) :=
  let c : J.MCtx := { inp, oldLast := 0 }
  match matchAt p c 0 true lim { groups := freshGroups p } with
  | .error e => .error e
  | .ok (none, _) => .ok none
  | .ok (some j, st) => .ok (some (j, st.groups))

/-! ## Clojure's functions -/

def reGroups (p : JPat) (inp : Array Nat) (s e : Nat) (gs : Groups) : J.CV :=
  if p.groups == 0 then .str (J.sub inp s e)
  else .vec (some (J.sub inp s e) :: (List.range p.groups).map fun k =>
    (gs.getD (k + 1) none).map fun (a, b) => J.sub inp a b)

def reFind (p : JPat) (s : List Nat) (lim : J.Lim := {}) (fx : JFix := {}) : J.CV :=
  let inp := J.units s
  match find p inp {} lim 0 fx with
  | .error e => J.abortCV e
  | .ok (none, _, _) => .nil
  | .ok (some (a, b, gs), _, _) => reGroups p inp a b gs

def reSeq (p : JPat) (s : List Nat) (lim : J.Lim := {}) (fx : JFix := {}) : J.CV :=
  let inp := J.units s
  match findAll p inp lim fx with
  | .error e => J.abortCV e
  | .ok [] => .nil
  | .ok ms => .list (ms.map fun (a, b, gs) => reGroups p inp a b gs)

def reMatches (p : JPat) (s : List Nat) (lim : J.Lim := {}) : J.CV :=
  let inp := J.units s
  match matchesAll p inp lim with
  | .error e => J.abortCV e
  | .ok none => .nil
  | .ok (some (b, gs)) => reGroups p inp 0 b gs

/-- `appendExpandedReplacement`: `\x`, `$n` (as many digits as name a group), `${name}`. -/
def expand (p : JPat) (inp : Array Nat) (s e : Nat) (gs : Groups) (t : List Nat) :
    Except String (List Nat) :=
  let grp (n : Nat) : List Nat :=
    if n == 0 then J.sub inp s e else match gs.getD n none with
      | some (a, b) => J.sub inp a b
      | none => []
  let rec go : Nat → List Nat → Except String (List Nat)
    | 0, _ => .ok []
    | _ + 1, [] => .ok []
    | f + 1, c :: rest =>
      if c == 0x5C then
        match rest with
        | [] => .error "character to be escaped is missing"
        | d :: r => do return (J.toBytes [d]) ++ (← go f r)
      else if c == 0x24 then
        match rest with
        | [] => .error "Illegal group reference: group index is missing"
        | d :: r =>
          if d == 0x7B then
            let name := r.takeWhile (· != 0x7D)
            let r' := r.drop (name.length + 1)
            if !r.contains 0x7D then .error "named capturing group is missing trailing '}'"
            else if name.isEmpty then .error "named capturing group has 0 length name"
            else if !(isAsciiAlpha (name.headD 0)) then .error "named capturing group name must start with a letter"
            else match p.names.find? (·.1 == name) with
              | none => .error "No group with name"
              | some (_, idx) => do return grp idx ++ (← go f r')
          else if !isDig d then .error "Illegal group reference"
          else
            let rec num : Nat → Nat → List Nat → Nat × List Nat
              | 0, n, r => (n, r)
              | g + 1, n, r => match r with
                | x :: r' => if isDig x && n * 10 + (x - 0x30) ≤ p.groups then num g (n * 10 + (x - 0x30)) r' else (n, r)
                | [] => (n, r)
            let (n, r) := num 8 (d - 0x30) r
            if n > p.groups then .error s!"No group {n}"
            else do return grp n ++ (← go f r)
      else do return J.toBytes [c] ++ (← go f rest)
  go (t.length + 1) t

def replace (p : JPat) (s : List Nat) (rep : Sum (List Nat) (J.CV → J.CV)) (first : Bool)
    (lim : J.Lim := {}) (fx : JFix := {}) : J.CV :=
  let inp := J.units s
  match findAll p inp lim fx with
  | .error e => J.abortCV e
  | .ok ms =>
    let ms := if first then ms.take 1 else ms
    if ms.isEmpty then .str (J.toBytes inp.toList) else
    let rec go : List (Nat × Nat × Groups) → Nat → List Nat → J.CV
      | [], last, out => .str (out ++ J.sub inp last inp.size)
      | (a, b, gs) :: rest, last, out =>
        let piece : Except String (List Nat) := match rep with
          | .inl t => expand p inp a b gs (Jank.Str.cstr t)
          | .inr f => match f (reGroups p inp a b gs) with
            | .str r => .ok r
            | .err w => .error w
            | _ => .error "ClassCastException"
        match piece with
        | .error w => .err w
        | .ok r => go rest b (out ++ J.sub inp last a ++ r)
    go ms 0 []

def split (p : JPat) (s : List Nat) (limit : Int) (lim : J.Lim := {}) (fx : JFix := {}) : J.CV :=
  let inp := J.units s
  match findAll p inp lim fx with
  | .error e => J.abortCV e
  | .ok ms => Id.run do
    let matchLimited := limit > 0
    let mut index := 0
    let mut list : List (List Nat) := []
    for (st, en, _) in ms do
      if !matchLimited || (list.length : Int) < limit - 1 then
        if index == 0 && index == st && st == en then continue
        list := list ++ [J.sub inp index st]
        index := en
      else if (list.length : Int) == limit - 1 then
        list := list ++ [J.sub inp index inp.size]
        index := en
    if index == 0 then return .list [.str (J.sub inp 0 inp.size)]
    if !matchLimited || (list.length : Int) < limit then list := list ++ [J.sub inp index inp.size]
    if limit == 0 then list := (list.reverse.dropWhile (·.isEmpty)).reverse
    return .list (list.map .str)

end Jank.R5.Regex.JM5
