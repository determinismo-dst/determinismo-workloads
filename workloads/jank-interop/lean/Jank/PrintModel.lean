import Determinismo
import Jank.StrModel

/-!
# Printing: `str`, `pr-str` and `print-str` in jank beside Clojure's printer

jank prints with two C++ methods per object (object.hpp): `to_string` (`str`, `print`,
`println`) and `to_code_string` (`pr`, `prn`, `pr-str`). Clojure prints with `toString` (`str`)
and the `print-method` multimethod (core_print.clj; `pr` with `*print-readably*` true, `print`
with it nil).

Modeled here:

- doubles: jtl/string_builder.cpp `operator()(double)` (83): `std::to_chars(first, last, d)`
  (the shortest round-trip form, fixed or scientific, whichever is shorter, a tie going to fixed:
  [charconv.to.chars]) then `".0"` when it has neither `.` nor `e`; Clojure: `Double.toString`
  (JDK 19+: the shortest decimal; plain for 10^-3 <= |d| < 10^7, else `d.dddE±n`);
- strings in `pr-str`: util/escape.cpp `escape` (148) beside core_print.clj
  `char-escape-string`;
- collections in `str`: each element's `to_string` (core/to_string.hpp `to_string(begin, end,
  …)` 28; base_persistent_map.cpp `to_string_impl` 62) beside `RT.printString` (readable);
- regexes in `pr-str`: re_pattern.cpp `to_code_string` (23) beside print-method Pattern;
- BigDecimals: big_decimal.cpp `to_string` (157) → string_builder `operator()(native_big_decimal)`
  (240: boost `str()`, then `".0"` without a `.`) beside `BigDecimal.toString`.
-/

namespace Jank.Print

open Determinismo

/-! ## Doubles

A double is drawn as its shortest round-trip decimal: `digits` (no trailing zero) × 10^`exp`.
With at most 15 significant digits this decimal is the double's unique shortest representation
(DBL_DIG = 15: distinct decimals of ≤ 15 digits are distinct doubles), so both printers start
from the same digits. -/

structure Dbl where
  neg : Bool
  digits : Nat
  exp : Int
  deriving Repr, Inhabited, BEq

def zeros (n : Nat) : List Char := List.replicate n '0'

/-- The digits, as `List Char` (kept as lists so that `decide` can evaluate the printers). -/
def Dbl.D (d : Dbl) : List Char := Nat.toDigits 10 d.digits
def Dbl.n (d : Dbl) : Nat := d.D.length
/-- The scientific exponent: d = x.yyy × 10^sciExp. -/
def Dbl.sciExp (d : Dbl) : Int := d.exp + d.n - 1

def pad2 (n : Nat) : List Char := let s := Nat.toDigits 10 n; if s.length < 2 then '0' :: s else s

def sgn (d : Dbl) : List Char := if d.neg then ['-'] else []

/-- printf `%f` with exactly the digits needed. -/
def fixedForm (d : Dbl) : List Char :=
  if d.digits == 0 then ['0']
  else if d.exp ≥ 0 then d.D ++ zeros d.exp.toNat
  else
    let k := (-d.exp).toNat
    if d.n > k then d.D.take (d.n - k) ++ ['.'] ++ d.D.drop (d.n - k)
    else ['0', '.'] ++ zeros (k - d.n) ++ d.D

/-- printf `%e` with exactly the digits needed (exponent of at least two digits). -/
def sciForm (d : Dbl) : List Char :=
  if d.digits == 0 then "0e+00".toList
  else
    let e := d.sciExp
    d.D.take 1 ++ (if d.n > 1 then '.' :: d.D.drop 1 else []) ++ ['e'] ++
      (if e < 0 then ['-'] else ['+']) ++ pad2 e.natAbs

/-- `std::to_chars(first, last, value)` (no format): the shorter of the two, a tie to fixed. -/
def toChars (d : Dbl) : List Char :=
  let f := fixedForm d
  let s := sciForm d
  sgn d ++ (if f.length ≤ s.length then f else s)

/-- string_builder.cpp `operator()(double)` (83): `to_chars`, then `".0"` unless the text has a
`.` or an `e`. real.cpp `to_string` (291) and `to_code_string` (314) use it for finite values. -/
def jankDoubleL (d : Dbl) : List Char :=
  let r := toChars d
  if r.contains '.' || r.contains 'e' then r else r ++ ['.', '0']

/-- `Double.toString` (JDK 19+). -/
def javaDoubleL (d : Dbl) : List Char :=
  if d.digits == 0 then sgn d ++ ['0', '.', '0']
  else
    let e := d.sciExp
    if -3 ≤ e ∧ e ≤ 6 then
      if e ≥ 0 then
        let padded := d.D ++ zeros ((e.toNat + 1) - d.n)
        let intPart := padded.take (e.toNat + 1)
        let frac := padded.drop (e.toNat + 1)
        sgn d ++ intPart ++ ['.'] ++ (if frac.isEmpty then ['0'] else frac)
      else sgn d ++ ['0', '.'] ++ zeros ((-e).toNat - 1) ++ d.D
    else
      sgn d ++ d.D.take 1 ++ ['.'] ++ (if d.n > 1 then d.D.drop 1 else ['0']) ++
        ['E'] ++ (if e < 0 then ['-'] else []) ++ Nat.toDigits 10 e.natAbs

def jankDouble (d : Dbl) : String := String.ofList (jankDoubleL d)
def javaDouble (d : Dbl) : String := String.ofList (javaDoubleL d)

/-- How the double is written in a program (Clojure syntax). -/
def Dbl.code (d : Dbl) : String := javaDouble d

/-! ## Strings in `pr-str` -/

/-- util/escape.cpp `escape` (148), over the bytes: `\n \t \r \\ \" \a \v \f \b`. -/
def jankEscape (bs : List UInt8) : List UInt8 :=
  bs.flatMap fun b =>
    if b == 0x0A then "\\n".toUTF8.toList else if b == 0x09 then "\\t".toUTF8.toList
    else if b == 0x0D then "\\r".toUTF8.toList else if b == 0x5C then "\\\\".toUTF8.toList
    else if b == 0x22 then "\\\"".toUTF8.toList else if b == 0x07 then "\\a".toUTF8.toList
    else if b == 0x0B then "\\v".toUTF8.toList else if b == 0x0C then "\\f".toUTF8.toList
    else if b == 0x08 then "\\b".toUTF8.toList else [b]

/-- persistent_string.cpp `to_code_string` (52). -/
def jankPrStr (s : List Nat) : List UInt8 := ([0x22] : List UInt8) ++ jankEscape (Jank.Str.jstr s) ++ [0x22]

/-- core_print.clj `char-escape-string`: newline, tab, return, `"`, `\`, formfeed, backspace. -/
def cljEscape (u : Nat) : Option String :=
  if u == 0x0A then some "\\n" else if u == 0x09 then some "\\t" else if u == 0x0D then some "\\r"
  else if u == 0x22 then some "\\\"" else if u == 0x5C then some "\\\\"
  else if u == 0x0C then some "\\f" else if u == 0x08 then some "\\b" else none

/-- print-method String with `*print-readably*`. -/
def cljPrStr (s : List Nat) : List UInt8 :=
  ([0x22] : List UInt8) ++ ((Jank.Str.cstr s).flatMap fun u => match cljEscape u with
    | some e => e.toUTF8.toList
    | none => Jank.Str.unitsToBytes [u]) ++ [0x22]

/-! ## Values in `str`, `pr-str` and `print-str` -/

inductive PV where
  | nil
  | bool (b : Bool)
  | int (v : Int)
  | str (s : List Nat)
  | chr (c : Nat)
  | kw (name : String)
  | vec (xs : List PV)
  | list (xs : List PV)
  | map (kvs : List (PV × PV))
  | set (xs : List PV)
  deriving Inhabited

/-- Character names (character.cpp `get_literal_from_char_bytes` 12; core_print.clj
`char-name-string`: the same six). -/
def charName (c : Nat) : Option String :=
  if c == 0x0A then some "newline" else if c == 0x20 then some "space" else if c == 0x09 then some "tab"
  else if c == 0x08 then some "backspace" else if c == 0x0C then some "formfeed"
  else if c == 0x0D then some "return" else none

def charCode (c : Nat) : String :=
  match charName c with
  | some n => "\\" ++ n
  | none => "\\" ++ String.singleton (Char.ofNat c)

def bytesToString (bs : List UInt8) : String :=
  match Jank.Str.decodeUtf8 bs with
  | some cps => String.ofList (cps.map Char.ofNat)
  | none => "<invalid UTF-8>"

mutual
/-- jank `to_string` (the per-type `to_string(string_builder&)`): elements by `to_string`. -/
def jankToString : PV → String
  | .nil => "nil"
  | .bool b => toString b
  | .int v => toString v
  | .str s => String.ofList (s.map Char.ofNat)
  | .chr c => String.singleton (Char.ofNat c)
  | .kw k => ":" ++ k
  | .vec xs => "[" ++ jankJoin xs ++ "]"
  | .list xs => "(" ++ jankJoin xs ++ ")"
  | .map kvs => "{" ++ jankJoinPairs kvs ++ "}"
  | .set xs => "#{" ++ jankJoin xs ++ "}"
def jankJoin : List PV → String
  | [] => ""
  | [x] => jankToString x
  | x :: xs => jankToString x ++ " " ++ jankJoin xs
def jankJoinPairs : List (PV × PV) → String
  | [] => ""
  | [(k, v)] => jankToString k ++ " " ++ jankToString v
  | (k, v) :: kvs => jankToString k ++ " " ++ jankToString v ++ ", " ++ jankJoinPairs kvs
end

mutual
/-- jank `to_code_string`, and Clojure's readable printer (`pr`): the same on these values
(strings by their own escape, compared separately above). -/
def codeString : PV → String
  | .str s => bytesToString (cljPrStr s)
  | .chr c => charCode c
  | .vec xs => "[" ++ codeJoin xs ++ "]"
  | .list xs => "(" ++ codeJoin xs ++ ")"
  | .map kvs => "{" ++ codeJoinPairs kvs ++ "}"
  | .set xs => "#{" ++ codeJoin xs ++ "}"
  | v => jankToString v
def codeJoin : List PV → String
  | [] => ""
  | [x] => codeString x
  | x :: xs => codeString x ++ " " ++ codeJoin xs
def codeJoinPairs : List (PV × PV) → String
  | [] => ""
  | [(k, v)] => codeString k ++ " " ++ codeString v
  | (k, v) :: kvs => codeString k ++ " " ++ codeString v ++ ", " ++ codeJoinPairs kvs
end

/-- jank `str` of one value (core.jank `str`: nil → "", else `.to_string`). -/
def jankStr : PV → String
  | .nil => ""
  | v => jankToString v

/-- Clojure `str` of one value: `toString`; a collection's `toString` is `RT.printString`, the
readable printer. -/
def cljStr : PV → String
  | .nil => ""
  | .str s => String.ofList (s.map Char.ofNat)
  | .chr c => String.singleton (Char.ofNat c)
  | v => codeString v

/-- Clojure `print-str` (`print` binds `*print-readably*` to nil: nothing is readable). -/
def cljPrintStr : PV → String := jankToString

def atoms : List PV :=
  [.nil, .bool true, .int 1, .str [0x61], .str [0x61, 0x20, 0x62], .str [0x22], .chr 0x61,
   .chr 0x20, .kw "k"]

/-- Values of depth ≤ 2: atoms and collections of at most two atoms. -/
def values : List PV :=
  let pairs := atoms.flatMap fun a => atoms.map fun b => (a, b)
  atoms ++ [.vec [], .list [], .map [], .set []] ++
  atoms.map (fun a => .vec [a]) ++ pairs.map (fun (a, b) => .vec [a, b]) ++
  atoms.map (fun a => .list [a]) ++ atoms.map (fun a => .set [a]) ++
  atoms.map (fun a => .map [(.kw "k", a)])

/-! ## Regex patterns in `pr-str` -/

/-- re_pattern.cpp `to_code_string` (23): `#"` + pattern + `"`, nothing escaped. -/
def jankRegexCodeL (p : List Char) : List Char := ['#', '"'] ++ p ++ ['"']
def jankRegexCode (p : List Char) : String := String.ofList (jankRegexCodeL p)

/-- core_print.clj print-method Pattern: a backslash and the next character as they are
(`\Q` … `\E` quoting tracked), a `"` written `\"` (inside `\Q…\E`: `\E\"\Q`). -/
def cljRegexGo : List Char → Bool → List Char
  | [], _ => []
  | '\\' :: c2 :: r, q => ['\\', c2] ++ cljRegexGo r (if q then c2 != 'E' else c2 == 'Q')
  | ['\\'], _ => ['\\']
  | '"' :: r, q => (if q then "\\E\\\"\\Q".toList else ['\\', '"']) ++ cljRegexGo r q
  | c :: r, q => c :: cljRegexGo r q

def cljRegexCodeL (p : List Char) : List Char := ['#', '"'] ++ cljRegexGo p false ++ ['"']
def cljRegexCode (p : List Char) : String := String.ofList (cljRegexCodeL p)

/-- What a reader takes as a regex literal's pattern from `#"…"` text (both readers: the
characters up to the first `"` not preceded by a backslash). -/
def readRegexLiteral (text : String) : Option (List Char) :=
  match text.toList with
  | '#' :: '"' :: rest =>
    let rec scan : List Char → List Char → Option (List Char × List Char)
      | [], _ => none
      | '\\' :: c :: r, acc => scan r (acc ++ ['\\', c])
      | '"' :: r, acc => some (acc, r)
      | c :: r, acc => scan r (acc ++ [c])
    match scan rest [] with
    | some (p, []) => some p
    | _ => none
  | _ => none

/-! ## BigDecimal -/

/-- A BigDecimal: unscaled × 10^-scale (scale ≥ 0 here). -/
structure Dec where
  unscaled : Int
  scale : Nat
  deriving Repr, Inhabited

/-- BigDecimal.toString for scale ≥ 0 and an adjusted exponent ≥ -6: the plain form with
exactly `scale` fraction digits. -/
def javaDec (d : Dec) : String :=
  let neg := d.unscaled < 0
  let digits := toString d.unscaled.natAbs
  let digits := if digits.length ≤ d.scale then String.ofList (zeros (d.scale + 1 - digits.length)) ++ digits else digits
  let body := if d.scale == 0 then digits
    else (digits.take (digits.length - d.scale)).toString ++ "." ++ (digits.drop (digits.length - d.scale)).toString
  (if neg then "-" else "") ++ body

/-- big_decimal.cpp `to_string` (157): boost `cpp_dec_float<100>::str()` keeps no scale and
prints the value with no trailing zeros, in fixed notation for these magnitudes (assumption
RB7); string_builder.cpp (240) appends `".0"` when there is no `.`. `to_code_string` (169)
adds `M`. -/
def jankDec (d : Dec) : String :=
  -- The value, trailing zeros stripped.
  let rec strip (u : Nat) (s : Nat) (fuel : Nat) : Nat × Nat :=
    match fuel with
    | 0 => (u, s)
    | f + 1 => if s > 0 && u % 10 == 0 && u != 0 then strip (u / 10) (s - 1) f else (u, s)
  let (u, s) := strip d.unscaled.natAbs d.scale 20
  let s' := if u == 0 then 0 else s
  let base := javaDec { unscaled := if d.unscaled < 0 then -(u : Int) else u, scale := s' }
  if base.contains '.' then base else base ++ ".0"

/-! ## Theorems: concrete prints -/

theorem jank_100000 : jankDoubleL ⟨false, 1, 5⟩ = "1e+05".toList := by decide
theorem java_100000 : javaDoubleL ⟨false, 1, 5⟩ = "100000.0".toList := by decide
theorem jank_1e7 : jankDoubleL ⟨false, 1, 7⟩ = "1e+07".toList := by decide
theorem java_1e7 : javaDoubleL ⟨false, 1, 7⟩ = "1.0E7".toList := by decide
theorem jank_123456789 : jankDoubleL ⟨false, 123456789, 0⟩ = "123456789.0".toList := by decide
theorem java_123456789 : javaDoubleL ⟨false, 123456789, 0⟩ = "1.23456789E8".toList := by decide
theorem jank_regex_quote : jankRegexCodeL ['"'] = ['#', '"', '"', '"'] := by decide
theorem clj_regex_quote : cljRegexCodeL ['"'] = ['#', '"', '\\', '"', '"'] := by decide
/-- jank's text for the pattern `"` is read back as the empty pattern followed by a lone `"`. -/
theorem jank_regex_quote_unreadable : readRegexLiteral (jankRegexCode ['"']) ≠ some ['"'] := by
  decide

end Jank.Print
