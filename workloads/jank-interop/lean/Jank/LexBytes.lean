import Determinismo

/-!
# Bytes, code points and the C library calls jank's lexer makes

jank's lexer (read/lex.cpp, commit f3d82d654) works on the source's bytes
(`jtl::immutable_string_view file`) and decodes one code point at a time with `std::mbrtowc`
(`convert_to_codepoint`, lex.cpp:452-468). The C library's behavior is modeled here:

- `mbrtowc` under the UTF-8 locale jank installs (`jank_init_base`, c_api.cpp:1110:
  `std::locale::global(std::locale(""))`, which also sets the C locale) or under the C/POSIX
  locale (what `""` gives when LANG/LC_ALL are unset): see assumptions RA1-RA3;
- `isspace` on a `char` byte (lex.cpp:558), `iswspace` on a code point (lex.cpp:501);
- `strtoll`, `strtod`, `std::stoi`, boost `cpp_int`'s string parsing.

Clojure's side (LispReader.java) works on Java `char`s; `isWhitespace` is
`Character.isWhitespace(ch) || ch == ','` (LispReader.java:132).

All text is `List Nat` (code points or bytes): Lean's `Char` cannot hold a lone surrogate, and
Clojure strings can.
-/

namespace Jank.LexBytes

/-- The locale jank's process runs under (RA1). -/
inductive Locale where
  /-- `LANG=C.UTF-8`, `en_US.UTF-8`, ...: multibyte UTF-8. -/
  | utf8
  /-- `LANG` unset (C/POSIX locale, glibc): single-byte ASCII; bytes ≥ 0x80 are `EILSEQ`. -/
  | c
  deriving Repr, BEq, Inhabited

/-- `std::mbrtowc(&wc, s, n, &state)` with `n` = the bytes left: a code point and its length
(0 for the null character, per C11 7.29.6.3.2: "returns 0 if ... the null wide character"),
`invalid` ((size_t)-1, EILSEQ) or `incomplete` ((size_t)-2). -/
inductive Mb where
  | ok (cp : Nat) (len : Nat)
  | invalid
  | incomplete
  deriving Repr, BEq, Inhabited

def isCont (b : UInt8) : Bool := 0x80 ≤ b && b ≤ 0xBF

/-- glibc's UTF-8 `mbrtowc`: strict UTF-8 (no overlong forms, no surrogates, at most U+10FFFF). -/
def mbrtowc (loc : Locale) (f : Array UInt8) (i : Nat) : Mb :=
  if i ≥ f.size then .incomplete
  else
    let b0 := f[i]!
    if b0 == 0 then .ok 0 0
    else if b0 < 0x80 then .ok b0.toNat 1
    else match loc with
      | .c => .invalid
      | .utf8 =>
        let need : Nat := if 0xC2 ≤ b0 && b0 ≤ 0xDF then 1
          else if 0xE0 ≤ b0 && b0 ≤ 0xEF then 2
          else if 0xF0 ≤ b0 && b0 ≤ 0xF4 then 3 else 0
        if need == 0 then .invalid
        else
          -- The second byte's range depends on the first (no overlong, no surrogates, ≤ 10FFFF).
          let lo : UInt8 := if b0 == 0xE0 then 0xA0 else if b0 == 0xF0 then 0x90 else 0x80
          let hi : UInt8 := if b0 == 0xED then 0x9F else if b0 == 0xF4 then 0x8F else 0xBF
          let avail := f.size - i - 1
          let rec go (k : Nat) (acc : Nat) (fuel : Nat) : Mb :=
            match fuel with
            | 0 => .ok acc (need + 1)
            | fuel + 1 =>
              if k > need then .ok acc (need + 1)
              else if k > avail then .incomplete
              else
                let b := f[i + k]!
                let okb := if k == 1 then lo ≤ b && b ≤ hi else isCont b
                if !okb then .invalid else go (k + 1) (acc * 64 + (b.toNat % 64)) fuel
          let first : Nat := if need == 1 then b0.toNat % 32 else if need == 2 then b0.toNat % 16 else b0.toNat % 8
          go 1 first 4

/-- UTF-8 encoding of a code point (wcrtomb under a UTF-8 locale). -/
def utf8Encode (cp : Nat) : List UInt8 :=
  if cp < 0x80 then [cp.toUInt8]
  else if cp < 0x800 then [(0xC0 + cp / 64).toUInt8, (0x80 + cp % 64).toUInt8]
  else if cp < 0x10000 then
    [(0xE0 + cp / 4096).toUInt8, (0x80 + (cp / 64) % 64).toUInt8, (0x80 + cp % 64).toUInt8]
  else [(0xF0 + cp / 262144).toUInt8, (0x80 + (cp / 4096) % 64).toUInt8,
        (0x80 + (cp / 64) % 64).toUInt8, (0x80 + cp % 64).toUInt8]

/-- Decodes a byte list as UTF-8 code points; `none` when it is not valid UTF-8 (strictly). -/
def utf8Decode (bs : List UInt8) : Option (List Nat) := Id.run do
  let f := bs.toArray
  let mut i := 0
  let mut out : Array Nat := #[]
  for _ in [0:f.size + 1] do
    if i ≥ f.size then return some out.toList
    match mbrtowc .utf8 f i with
    | .ok cp len => out := out.push cp; i := i + (if len == 0 then 1 else len)
    | _ => return none
  return some out.toList

/-- `std::isspace(c)` on a `char` in the C or a UTF-8 locale (glibc): the six ASCII spaces;
bytes ≥ 0x80 (negative `char`s) are not spaces (RA2). lex.cpp:558. -/
def cIsspace (b : UInt8) : Bool := b == 32 || (9 ≤ b && b ≤ 13)

/-- glibc's `iswspace` in a UTF-8 locale (its i18n `space` class, RA2): U+0009-000D, U+0020,
U+1680, U+2000-2006, U+2008-200A, U+2028, U+2029, U+205F, U+3000. In the C locale, ASCII only. -/
def iswspace (loc : Locale) (c : Nat) : Bool :=
  c == 32 || (9 ≤ c && c ≤ 13) ||
  (loc == .utf8 && (c == 0x1680 || (0x2000 ≤ c && c ≤ 0x2006) || (0x2008 ≤ c && c ≤ 0x200A) ||
    c == 0x2028 || c == 0x2029 || c == 0x205F || c == 0x3000))

/-- Java's `Character.isWhitespace` (Character.java: SPACE_SEPARATOR, LINE_SEPARATOR or
PARAGRAPH_SEPARATOR except the non-breaking U+00A0, U+2007, U+202F; or U+0009-000D, U+001C-001F). -/
def javaIsWhitespace (c : Nat) : Bool :=
  (9 ≤ c && c ≤ 13) || (0x1C ≤ c && c ≤ 0x1F) || c == 32 || c == 0x1680 ||
  (0x2000 ≤ c && c ≤ 0x2006) || (0x2008 ≤ c && c ≤ 0x200A) || c == 0x2028 || c == 0x2029 ||
  c == 0x205F || c == 0x3000

def isDigitC (c : Nat) : Bool := 48 ≤ c && c ≤ 57
def isLowerC (c : Nat) : Bool := 97 ≤ c && c ≤ 122
def isUpperC (c : Nat) : Bool := 65 ≤ c && c ≤ 90
def chr (c : Char) : Nat := c.toNat
def byte (c : Char) : UInt8 := c.toNat.toUInt8

/-- A digit's value in bases up to 36 (Java's `Character.digit` for ASCII; `strtoll`'s). -/
def digitVal (c : Nat) : Option Nat :=
  if isDigitC c then some (c - 48)
  else if isLowerC c then some (c - 97 + 10)
  else if isUpperC c then some (c - 65 + 10)
  else none

def i64min : Int := -9223372036854775808
def i64max : Int := 9223372036854775807

/-- glibc `strtoll(s + i, nullptr, base)` (2 ≤ base ≤ 36): leading `isspace`, an optional sign,
for base 16 an optional `0x`/`0X`, then the longest run of digits below `base`. The value, and
whether `errno` was set to `ERANGE` (the value is then clamped). -/
def strtoll (f : Array UInt8) (i0 : Nat) (base : Nat) : Int × Bool := Id.run do
  let at_ := fun (k : Nat) => (f.getD k 0).toNat
  let mut i := i0
  for _ in [0:f.size + 1] do
    if i < f.size && cIsspace (f.getD i 0) then i := i + 1 else break
  let mut neg := false
  if at_ i == 45 then neg := true; i := i + 1
  else if at_ i == 43 then i := i + 1
  if base == 16 && at_ i == 48 && (at_ (i + 1) == 120 || at_ (i + 1) == 88) then i := i + 2
  let mut v : Int := 0
  for _ in [0:f.size + 1] do
    if i ≥ f.size then break
    match digitVal (at_ i) with
    | some d => if d < base then v := v * base + d; i := i + 1 else break
    | none => break
  let w := if neg then -v else v
  if w > i64max then return (i64max, true)
  if w < i64min then return (i64min, true)
  return (w, false)

/-- `std::stoi(s + i)` (decimal, `int`): `none` when it throws `std::out_of_range` (the value
leaves `int`) or `std::invalid_argument` (no digits). -/
def stoi (f : Array UInt8) (i0 : Nat) : Option Int := Id.run do
  let at_ := fun (k : Nat) => (f.getD k 0).toNat
  let mut i := i0
  let mut neg := false
  if at_ i == 45 then neg := true; i := i + 1
  else if at_ i == 43 then i := i + 1
  let mut v : Int := 0
  let mut any := false
  for _ in [0:f.size + 1] do
    if i < f.size && isDigitC (at_ i) then v := v * 10 + (at_ i - 48); i := i + 1; any := true
    else break
  if !any then return none
  let w := if neg then -v else v
  if w > 2147483647 || w < -2147483648 then return none
  return some w

/-- `static_cast<i8>(v)`: two's complement truncation. -/
def toI8 (v : Int) : Int := (BitVec.ofInt 8 v).toInt

/-- An exact decimal: (-1)^neg · mant · 10^exp, normalized (no trailing zeros in `mant`). Both
`strtod` and Java's `Double.parseDouble` round correctly, so the same decimal gives the same
double on both sides (RA4); values are compared as decimals. -/
structure Dec where
  neg : Bool
  mant : Nat
  exp : Int
  deriving Repr, BEq, Inhabited

def Dec.norm (d : Dec) : Dec := Id.run do
  if d.mant == 0 then return { d with exp := 0 }
  let mut m := d.mant
  let mut e := d.exp
  for _ in [0:400] do
    if m % 10 == 0 then m := m / 10; e := e + 1 else break
  return { d with mant := m, exp := e }

def Dec.show (d : Dec) : String :=
  s!"{if d.neg then "-" else ""}{d.mant}e{d.exp}"

/-- glibc `strtod(s + i, nullptr)` restricted to the decimal grammar the lexer lets through
(`[+-]? digits [. digits] [(e|E) [+-]? digits]`); `LC_NUMERIC` is "C" (c_api.cpp:1117). -/
def strtod (f : Array UInt8) (i0 : Nat) : Dec := Id.run do
  let at_ := fun (k : Nat) => (f.getD k 0).toNat
  let mut i := i0
  let mut neg := false
  if at_ i == 45 then neg := true; i := i + 1
  else if at_ i == 43 then i := i + 1
  let mut m : Nat := 0
  let mut e : Int := 0
  for _ in [0:f.size + 1] do
    if i < f.size && isDigitC (at_ i) then m := m * 10 + (at_ i - 48); i := i + 1 else break
  if i < f.size && at_ i == 46 then
    i := i + 1
    for _ in [0:f.size + 1] do
      if i < f.size && isDigitC (at_ i) then m := m * 10 + (at_ i - 48); e := e - 1; i := i + 1
      else break
  if i < f.size && (at_ i == 101 || at_ i == 69) then
    let mut j := i + 1
    let mut eneg := false
    if at_ j == 45 then eneg := true; j := j + 1
    else if at_ j == 43 then j := j + 1
    if j < f.size && isDigitC (at_ j) then
      let mut x : Int := 0
      for _ in [0:f.size + 1] do
        if j < f.size && isDigitC (at_ j) then x := x * 10 + (at_ j - 48); j := j + 1 else break
      e := e + (if eneg then -x else x)
  return Dec.norm { neg, mant := m, exp := e }

/-- Java `Double.parseDouble` / `new BigDecimal` of a string matching Clojure's `floatPat`
(`[-+]?[0-9]+(\.[0-9]*)?([eE][-+]?[0-9]+)?`), as an exact decimal. -/
def parseDecimal (s : List Nat) : Dec :=
  strtod (s.map (·.toUInt8)).toArray 0

/-- boost `cpp_int`'s string assignment (`do_assign_string`, RA5): an optional `-`, then a
leading `0x`/`0X` means hexadecimal and a leading `0` octal, else decimal; a digit outside the
radix throws `std::runtime_error`. -/
def boostParse (s : List UInt8) : Except String Int := Id.run do
  let mut cs := s.map (·.toNat)
  let mut neg := false
  if cs.head? == some 45 then neg := true; cs := cs.drop 1
  let mut radix := 10
  if cs.head? == some 48 then
    if cs.length > 1 && (cs[1]! == 120 || cs[1]! == 88) then radix := 16; cs := cs.drop 2
    else radix := 8; cs := cs.drop 1
  let mut v : Int := 0
  for c in cs do
    match digitVal c with
    | some d => if d < radix then v := v * radix + d else return .error "boost: unexpected content"
    | none => return .error "boost: unexpected content"
  return .ok (if neg then -v else v)

/-- Text for reports: printable ASCII as is, the rest escaped as \xNN (bytes) or \uNNNN. -/
def showCodes (cs : List Nat) : String :=
  String.join (cs.map fun c =>
    if c == 92 then "\\\\" else if c == 34 then "\\\""
    else if 32 ≤ c && c < 127 then (Char.ofNat c).toString
    else if c == 10 then "\\n" else if c == 13 then "\\r" else if c == 9 then "\\t"
    else if c < 0x10000 then
      let h := (Nat.toDigits 16 c)
      "\\u" ++ String.ofList (List.replicate (4 - h.length) '0' ++ h)
    else "\\U{" ++ String.ofList (Nat.toDigits 16 c) ++ "}")

def showBytes (bs : List UInt8) : String :=
  match utf8Decode bs with
  | some cs => showCodes cs
  | none => String.join (bs.map fun b =>
      if 32 ≤ b && b < 127 && b != 92 && b != 34 then (Char.ofNat b.toNat).toString
      else "\\x" ++ String.ofList (Nat.toDigits 16 b.toNat))

def bytesOf (s : String) : List UInt8 := s.toUTF8.toList

end Jank.LexBytes
