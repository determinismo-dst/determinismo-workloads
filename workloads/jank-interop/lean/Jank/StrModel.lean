import Std.Tactic.BVDecide
import Determinismo
import Jank.Hash

/-!
# Strings and characters: jank's UTF-8 byte strings beside Java's UTF-16 strings

jank (commit 7135b7708; citations re-read there) keeps a string as `jtl::immutable_string`, its UTF-8 bytes (book,
differences-from-clojure.md: "`persistent_string` is expected to be UTF-8"), and a character
(`obj::character`, character.hpp) as the bytes of one character (`data`, "Holds the raw form of
the character bytes"). Clojure keeps a `java.lang.String`: UTF-16 code units; `count`, `nth`,
`get`, `subs`, `seq`, `compare` and every clojure.string index are in code units, and a `char`
is one code unit.

Here each function is modeled as the C++ (or .jank) computes it, cited beside it:

- most of jank's string functions index **bytes** (`count`, `nth`, `get`, `contains?`, `subs`,
  `index-of`, `last-index-of`, `escape`, the empty-match `replace`);
- `seq` walks **code points** (persistent_string_sequence: `jtl::next_char_size`);
- the case functions, `char` and `int` go through the C library and the process locale
  (`jank_init_base` in c_api.cpp: `std::locale::global(std::locale(""))`, the environment's
  locale; `LC_NUMERIC` alone is reset to "C").

Texts are drawn as code points and encoded both ways; results are compared through one
encoding (a Clojure string's units are turned into UTF-8, a lone surrogate into its 3-byte
generalized form, which no jank string holds).
-/

namespace Jank.Str

open Determinismo

/-! ## Encodings -/

/-- UTF-8 of a code point. -/
def utf8 (c : Nat) : List UInt8 :=
  if c < 0x80 then [c.toUInt8]
  else if c < 0x800 then [(0xC0 ||| (c >>> 6)).toUInt8, (0x80 ||| (c &&& 0x3F)).toUInt8]
  else if c < 0x10000 then
    [(0xE0 ||| (c >>> 12)).toUInt8, (0x80 ||| ((c >>> 6) &&& 0x3F)).toUInt8,
     (0x80 ||| (c &&& 0x3F)).toUInt8]
  else
    [(0xF0 ||| (c >>> 18)).toUInt8, (0x80 ||| ((c >>> 12) &&& 0x3F)).toUInt8,
     (0x80 ||| ((c >>> 6) &&& 0x3F)).toUInt8, (0x80 ||| (c &&& 0x3F)).toUInt8]

/-- UTF-16 code units of a code point (java.lang.String). -/
def utf16 (c : Nat) : List Nat :=
  if c < 0x10000 then [c]
  else [0xD800 + ((c - 0x10000) >>> 10), 0xDC00 + ((c - 0x10000) &&& 0x3FF)]

/-- A text as jank holds it (bytes) and as Clojure holds it (UTF-16 units). -/
def jstr (cps : List Nat) : List UInt8 := cps.flatMap utf8
def cstr (cps : List Nat) : List Nat := cps.flatMap utf16

def isHigh (u : Nat) : Bool := 0xD800 ≤ u && u ≤ 0xDBFF
def isLow (u : Nat) : Bool := 0xDC00 ≤ u && u ≤ 0xDFFF

/-- UTF-16 units to code points: pairs combined, a lone surrogate kept as its own value. -/
def unitsToCps : List Nat → List Nat
  | [] => []
  | [u] => [u]
  | h :: l :: rest =>
    if isHigh h && isLow l then (0x10000 + (h - 0xD800) * 0x400 + (l - 0xDC00)) :: unitsToCps rest
    else h :: unitsToCps (l :: rest)
termination_by xs => xs.length

/-- A Clojure string's units as bytes (a lone surrogate: 3 bytes, never a jank string's). -/
def unitsToBytes (us : List Nat) : List UInt8 := (unitsToCps us).flatMap utf8

/-- Bytes as code points when they are valid UTF-8 (for printing results). -/
def decodeUtf8 : List UInt8 → Option (List Nat)
  | [] => some []
  | b :: rest =>
    let c := b.toNat
    if c < 0x80 then (decodeUtf8 rest).map (c :: ·)
    else
      let need := if c &&& 0xE0 == 0xC0 then 1 else if c &&& 0xF0 == 0xE0 then 2
        else if c &&& 0xF8 == 0xF0 then 3 else 0
      if need == 0 || rest.length < need then none
      else
        let conts := rest.take need
        if conts.all (fun x => x.toNat &&& 0xC0 == 0x80) then
          let lead := if need == 1 then c &&& 0x1F else if need == 2 then c &&& 0x0F else c &&& 0x07
          let cp := conts.foldl (fun acc x => acc * 64 + (x.toNat &&& 0x3F)) lead
          (decodeUtf8 (rest.drop need)).map (cp :: ·)
        else none
termination_by bs => bs.length
decreasing_by all_goals simp_all <;> omega

def hex2 (n : Nat) : String :=
  let d := Nat.toDigits 16 n
  String.ofList (List.replicate (2 - d.length) '0' ++ d)

def hex4 (n : Nat) : String :=
  let d := Nat.toDigits 16 n
  String.ofList (List.replicate (4 - d.length) '0' ++ d)

/-- A code point inside a Clojure string literal (control characters and quotes escaped). -/
def litChar (c : Nat) : String :=
  if c == 0x22 then "\\\"" else if c == 0x5C then "\\\\" else if c == 0x0A then "\\n"
  else if c < 0x20 || c == 0x7F || (0xD800 ≤ c && c ≤ 0xDFFF) then "\\u" ++ hex4 c
  else if c ≥ 0x2000 && c ≤ 0x200F then "\\u" ++ hex4 c   -- invisible spaces: escaped
  else String.singleton (Char.ofNat c)

def lit (cps : List Nat) : String := "\"" ++ String.join (cps.map litChar) ++ "\""

/-- A character literal for Clojure source. -/
def charLit (c : Nat) : String :=
  if c == 0x20 then "\\space" else if c == 0x0A then "\\newline"
  else if c < 0x20 || (c ≥ 0x2000 && c ≤ 0x200F) || (0xD800 ≤ c && c ≤ 0xDFFF) then "\\u" ++ hex4 c
  else "\\" ++ String.singleton (Char.ofNat c)

/-- Bytes shown as a string: the text when valid UTF-8, else each byte as `\xNN`. -/
def showBytes (bs : List UInt8) : String :=
  match decodeUtf8 bs with
  | some cps => lit cps
  | none => "\"" ++ String.join (bs.map fun b =>
      if b.toNat < 0x80 then litChar b.toNat else "\\x" ++ hex2 b.toNat) ++ "\" (invalid UTF-8)"

def showChar (bs : List UInt8) : String :=
  match decodeUtf8 bs with
  | some [c] => charLit c
  | _ => "\\" ++ String.join (bs.map fun b => "<byte " ++ hex2 b.toNat ++ ">")

/-! ## Results, compared across the two sides -/

inductive R where
  | nil
  | bool (b : Bool)
  | int (v : Int)
  /-- A string, as UTF-8 bytes (Clojure's units converted). -/
  | str (bytes : List UInt8)
  | chr (bytes : List UInt8)
  /-- A seq of characters. -/
  | chars (cs : List (List UInt8))
  /-- An exception. -/
  | err (what : String)
  /-- Undefined behavior: reads out of bounds, a crash or a hang. -/
  | ub (what : String)
  deriving DecidableEq, Inhabited

def R.show : R → String
  | .nil => "nil"
  | .bool b => toString b
  | .int v => toString v
  | .str b => showBytes b
  | .chr b => showChar b
  | .chars cs => "(" ++ " ".intercalate (cs.map showChar) ++ ")"
  | .err w => s!"throws ({w})"
  | .ub w => s!"undefined behavior ({w})"

instance : Repr R where reprPrec r _ := r.show

/-- Agreement: both throw, or the same value. Undefined behavior never agrees. -/
def R.agrees : R → R → Bool
  | .err _, .err _ => true
  | .ub _, _ => false
  | _, .ub _ => false
  | a, b => a == b

/-! ## The locale (jank_init_base: `std::locale::global(std::locale(""))`)

`""` names the environment's locale: "C" when `LANG`/`LC_*` are unset (a container's default),
a UTF-8 locale on a desktop. -/

inductive Locale where
  | c
  | utf8
  deriving BEq, Repr, Inhabited

def Locale.name : Locale → String
  | .c => "C locale"
  | .utf8 => "UTF-8 locale"

/-! ## jank -/

/-- persistent_string.cpp `count` (line 179): `data.size()`, the bytes. Reached by `count` →
seq.cpp `sequence_length` (842, `behavior::countable` → `count()`). -/
def jCount (s : List UInt8) : R := .int s.length

/-- seq.cpp `nth(o, idx)` (648): negative → throws; then persistent_string.cpp `nth` (107):
out of range → throws, else `make_box<character>(data[i])`: a character of **one byte**. -/
def jNth (s : List UInt8) (i : Int) : R :=
  if i < 0 then .err "index out of bounds"
  else if s.length ≤ i.toNat then .err "index out of bounds"
  else .chr [s.getD i.toNat 0]

/-- persistent_string.cpp `get(key, fallback)` (78): `data[i]`, one byte, or the fallback. -/
def jGet (s : List UInt8) (i : Int) : R :=
  if i < 0 ∨ s.length ≤ i.toNat then .nil else .chr [s.getD i.toNat 0]

/-- persistent_string.cpp `contains` (95): `0 <= i && i < data.size()`. -/
def jContains (s : List UInt8) (i : Int) : R := .bool (decide (0 ≤ i ∧ i.toNat < s.length))

/-- core.cpp `subs` (398/411) → persistent_string.cpp `substring` (133/139): byte offsets;
`data.substr(start, end - start)`. -/
def jSubs (s : List UInt8) (start stop : Int) : R :=
  if start < 0 then .err "start index is less than 0"
  else if stop < start then .err "end index is less than start"
  else if stop.toNat > s.length then .err "end index out of bounds"
  else .str ((s.drop start.toNat).take (stop - start).toNat)

/-- jtl/utf8.cpp `next_char_size` (13): the lead byte's length; throws on a continuation byte
or 0xF8..0xFF. `s[i]` is unchecked (immutable_string.hpp `operator[]`, 256). -/
def nextCharSize (s : List UInt8) (i : Nat) : Except String Nat :=
  let c := (s.getD i 0).toNat
  if c ≤ 0x7f then .ok 1
  else if c &&& 0xE0 == 0xC0 then .ok 2
  else if c &&& 0xF0 == 0xE0 then .ok 3
  else if c &&& 0xF8 == 0xF0 then .ok 4
  else .error "Invalid UTF-8 string."

/-- `(seq s)`: persistent_string.cpp `fresh_seq` (189, nil when empty), then
persistent_string_sequence.cpp `first` (122: `substr(index, next_char_size)`) and `next` (128:
`n = index + next_char_size`; **`n == size`** ends it). A last character cut short (fewer bytes
than its lead announces) makes `n > size`: `next` returns a sequence past the end, whose
`first` reads `s[index]` beyond the string. -/
def jSeq (s : List UInt8) : R :=
  if s.isEmpty then .nil else go (s.length + 1) 0 []
where
  go : Nat → Nat → List (List UInt8) → R
    | 0, _, _ => .ub "fuel"
    | fuel + 1, i, acc =>
      if s.length ≤ i then
        .ub s!"next() went past the end (index {i} of {s.length} bytes): first() reads out of bounds"
      else match nextCharSize s i with
        | .error e => .err e
        | .ok k =>
          let ch := (s.drop i).take k
          let n := i + k
          if n == s.length then .chars (acc ++ [ch]) else go fuel n (acc ++ [ch])

/-- `(count (seq s))`: persistent_string_sequence.cpp `count` (78): `i < size`, by
`next_char_size`. -/
def jSeqCount (s : List UInt8) : R :=
  if s.isEmpty then .int 0 else go (s.length + 1) 0 0
where
  go : Nat → Nat → Nat → R
    | 0, _, _ => .ub "fuel"
    | fuel + 1, i, n =>
      if s.length ≤ i then .int n
      else match nextCharSize s i with
        | .error e => .err e
        | .ok k => go fuel (i + k) (n + 1)

/-- The first byte where two byte strings differ, if any. -/
def firstDiff {α : Type} [BEq α] : List α → List α → Option (α × α)
  | a :: as, b :: bs => if a == b then firstDiff as bs else some (a, b)
  | _, _ => none

/-- `compare` → persistent_string.cpp `compare` (68) → immutable_string.hpp `compare` (576):
`traits_type::compare` over the common length (char_traits<char> compares as `unsigned char`),
else `static_cast<int>(length - s_length)` of the two `size_t`s. Only the sign is kept: the
docstring promises only negative, zero or positive. -/
def jCompareLen (a b : Nat) : Int :=
  ((BitVec.ofNat 64 a - BitVec.ofNat 64 b).truncate 32).toInt

def sign (v : Int) : Int := if v < 0 then -1 else if v > 0 then 1 else 0

def jCompare (a b : List UInt8) : R :=
  match firstDiff a b with
  | some (x, y) => .int (if x < y then -1 else 1)
  | none => .int (sign (jCompareLen a.length b.length))

/-- immutable_string.hpp `find(pattern, pos, length)` (281): an empty pattern at `pos` when
`pos <= size`; nothing when `size <= pos`; else the first occurrence at or after `pos`. -/
def find (s pat : List UInt8) (pos : Nat) : Option Nat :=
  if pat.isEmpty then (if pos ≤ s.length then some pos else none)
  else if s.length ≤ pos then none
  else ((List.range (s.length - pos)).map (· + pos)).find? fun i => (s.drop i).take pat.length == pat

/-- immutable_string.hpp `rfind(s, pos, n)` (351): `pos = min(pos, length - n)`, then down. -/
def rfind (s pat : List UInt8) (pos : Nat) : Option Nat :=
  if pat.length > s.length then none
  else
    let p := min pos (s.length - pat.length)
    if pat.isEmpty then some p
    else ((List.range (p + 1)).reverse).find? fun i => (s.drop i).take pat.length == pat

/-- An `i64` passed where the C++ takes `size_t` (string_native.cpp `index_of` passes
`from_index` to `find(…, size_type pos)`): a negative value wraps to 2^64 + v. -/
def toSizeT (v : Int) : Nat := if v < 0 then (2 ^ 64 + v).toNat else v.toNat

/-- clojure.string `index-of` (string.jank 227) → string_native.cpp `index_of` (257):
`static_cast<i64>(s.find(value, from_index))`; `npos` is -1 → nil. -/
def jIndexOf (s pat : List UInt8) (fromIndex : Int) : R :=
  match find s pat (toSizeT fromIndex) with
  | some i => .int i
  | none => .nil

/-- clojure.string `last-index-of` (string.jank 240; 2-arity passes `(count s)`, bytes) →
string_native.cpp `last_index_of` (264): `s.rfind(value, from_index)`. -/
def jLastIndexOf (s pat : List UInt8) (fromIndex : Int) : R :=
  match rfind s pat (toSizeT fromIndex) with
  | some i => .int i
  | none => .nil

/-- C `isspace` on one byte (string_native.cpp `triml_index`/`trimr_index` 271/304,
immutable_string.hpp `is_blank` 635): the six ASCII spaces, in the C and UTF-8 locales alike;
a byte ≥ 0x80 is not a space in either (assumption RB4). -/
def cIsSpace (b : UInt8) : Bool := b == 0x20 || (0x09 ≤ b && b ≤ 0x0D)

/-- string_native.cpp `triml` (287), `trimr` (320), `trim` (337). -/
def jTriml (s : List UInt8) : R := .str (s.dropWhile cIsSpace)
def jTrimr (s : List UInt8) : R := .str (s.reverse.dropWhile cIsSpace).reverse
def jTrim (s : List UInt8) : R := .str ((s.dropWhile cIsSpace).reverse.dropWhile cIsSpace).reverse

/-- clojure.string `blank?` (string.jank 201) → `is_blank` (immutable_string.hpp 635). -/
def jBlank (s : List UInt8) : R := .bool (s.all cIsSpace)

/-- glibc `towupper`/`towlower` on the code points drawn here: simple (one to one) case mapping
in a UTF-8 locale; ASCII only in the C locale (assumption RB5). -/
def towupper : Locale → Nat → Nat
  | .c, c => if 0x61 ≤ c ∧ c ≤ 0x7A then c - 32 else c
  | .utf8, c =>
    if 0x61 ≤ c ∧ c ≤ 0x7A then c - 32
    else if c == 0xE9 then 0xC9 else if c == 0x3C3 || c == 0x3C2 then 0x3A3
    else if c == 0xFF41 then 0xFF21 else c   -- ß (0xDF) has no one-character upper case

def towlower : Locale → Nat → Nat
  | .c, c => if 0x41 ≤ c ∧ c ≤ 0x5A then c + 32 else c
  | .utf8, c =>
    if 0x41 ≤ c ∧ c ≤ 0x5A then c + 32
    else if c == 0xC9 then 0xE9 else if c == 0x3A3 then 0x3C3
    else if c == 0xFF21 then 0xFF41 else c

/-- util/string.cpp `to_uppercase` (26) / `to_lowercase` (14): `wstring_convert<codecvt_utf8>`
decodes, `ctype<wchar_t>::toupper` of `std::locale("")` maps each code point, then encodes. -/
def jUpper (loc : Locale) (s : List UInt8) : R :=
  match decodeUtf8 s with
  | some cps => .str (cps.flatMap fun c => utf8 (towupper loc c))
  | none => .err "std::range_error (wstring_convert)"

def jLower (loc : Locale) (s : List UInt8) : R :=
  match decodeUtf8 s with
  | some cps => .str (cps.flatMap fun c => utf8 (towlower loc c))
  | none => .err "std::range_error (wstring_convert)"

/-- clojure.string `capitalize` (string.jank 156): `to_lowercase`, then util/string.cpp
`capitalize` (54): `std::toupper(s[0])` on the first **byte** (a byte ≥ 0x80 is left as it is:
assumption RB5), the rest unchanged. -/
def jCapitalize (loc : Locale) (s : List UInt8) : R :=
  match jLower loc s with
  | .str [] => .str []
  | .str (b :: rest) =>
    let u : UInt8 := if 0x61 ≤ b && b ≤ 0x7A then b - 32 else b
    .str (u :: rest)
  | r => r

/-- clojure.string `replace` with string/string (string.jank 54) → string_native.cpp `replace`
(164): an empty `match` inserts `replacement` around every **byte**; otherwise left-to-right
non-overlapping `find`s (the same as Java's for valid UTF-8). -/
def jReplaceEmpty (s rep : List UInt8) : R :=
  .str (s.foldr (fun b acc => rep ++ b :: acc) rep)

/-- clojure.string `escape` (string.jank 207): `(count s)` bytes, `(nth s index)` byte
characters looked up in `cmap` (here `{key "X"}`); a byte character never equals a multi-byte
key, and unmatched bytes are appended back. -/
def jEscape (s : List UInt8) (key : List UInt8) : R :=
  .str (s.flatMap fun b => if [b] == key then "X".toUTF8.toList else [b])

/-- string_native.cpp `reverse` (24): `utf8_range | views::reverse`, by code points. -/
def jReverse (s : List UInt8) : R :=
  match decodeUtf8 s with
  | some cps => .str (cps.reverse.flatMap utf8)
  | none => .err "Invalid UTF-8 string."

/-- `=` with a string seq on the left: persistent_string_sequence.cpp `equal` (34) →
seq_ext.hpp `equal(o, begin, end)` (13) over the string's **bytes** (`char`s) against `o`'s
elements (at 7135b7708 seq_ext first requires `is_sequential(o)`, line 17: `o` here is a vector
or a string seq, both sequential, so the result is unchanged), each by core/equal.cpp `equal(char, object_ref)` (8): a character of exactly that one
byte. No identity shortcut (oref.hpp `equal`, 402). -/
def jSeqEqual (s : List UInt8) (elements : List (List UInt8)) : R :=
  .bool (s.length == elements.length && (s.zip elements).all fun (b, e) => e == [b])

/-- The characters `(vec s)` holds in jank (from the string seq: code points). -/
def jSeqChars (s : List UInt8) : List (List UInt8) :=
  match jSeq s with
  | .chars cs => cs
  | _ => []

/-- `(hash (seq s))`: persistent_string_sequence.cpp `to_hash` (72) → hash.hpp
`ordered(begin, end)` over the bytes with hash.cpp `visit(char)` (151):
`static_cast<u32>(ch)`, sign-extended where `char` is signed (x86-64). `(hash (vec s))`:
`ordered` over each character's `to_hash` (character.cpp 89 → immutable_string `to_hash`). -/
def jHashSeq (s : List UInt8) : UInt32 := Jank.Hash.orderedRange (s.map (Jank.Hash.widen .signed))
def jHashVec (cs : List (List UInt8)) : UInt32 := Jank.Hash.orderedRange (cs.map Jank.Hash.immutableString)

/-- `(char n)`: core.cpp `to_char` (1311) → character.cpp `character(i64)` (57) →
jtl/utf8.cpp `to_char(ch)` (170): above 0x10FFFF throws (a signed compare: every negative `ch`
passes); then `wcrtomb` of `static_cast<wchar_t>(ch)` (line 178), the low 32 bits as a signed
32-bit `wchar_t`, whose failure (`-1`) throws. So a negative `ch` below -2^31 wraps: the low 32
bits can be a valid code point (`(char -4294967231)` is `\A`). C locale: only ASCII encodes;
UTF-8 locale: any scalar value, surrogates and negative `wchar_t`s fail (assumption RB5). -/
def jChar (loc : Locale) (n : Int) : R :=
  if n > 0x10FFFF then .err "Value out of range for char"
  else
    -- static_cast<wchar_t>(i64): modulo 2^32, signed.
    let low : Int := n % 4294967296
    let wc : Int := if low ≥ 2147483648 then low - 4294967296 else low
    -- A wrapped value past U+10FFFF: assumed rejected like a negative one (macOS/FreeBSD
    -- reject it; glibc's encoder is not modeled past U+10FFFF).
    if wc < 0 || wc > 0x10FFFF then .err "Unfinished character (wcrtomb EILSEQ)"
    else match loc with
      | .c => if wc < 0x80 then .chr (utf8 wc.toNat) else .err "Unfinished character (wcrtomb EILSEQ)"
      | .utf8 =>
        if 0xD800 ≤ wc ∧ wc ≤ 0xDFFF then .err "Unfinished character (wcrtomb EILSEQ)"
        else .chr (utf8 wc.toNat)

/-- `(int c)`: core.jank `int` → math.hpp `to_int` → character.cpp `to_integer` (104):
`mbrtowc` into `wchar_t wc{}`; its result is not checked, so a failure (an invalid or
incomplete sequence, or any byte ≥ 0x80 in the C locale) leaves `wc` = 0. -/
def jInt (loc : Locale) (ch : List UInt8) : R :=
  match loc with
  | .c => match ch with
    | [b] => if b.toNat < 0x80 then .int b.toNat else .int 0
    | _ => .int 0
  | .utf8 => match decodeUtf8 ch with
    | some [cp] => .int cp
    | _ => .int 0

/-- A `\uXXXX` string escape (util/escape.cpp `unescape`, 35): a BMP code point →
`jtl::to_char(cp, "?")` (wcrtomb, `"?"` when it fails); a surrogate pair →
`jtl::to_char(combined)` (throws when it fails). -/
def jUnescape (loc : Locale) (c : Nat) : R :=
  if c < 0x10000 then
    match jChar loc c with
    | .chr b => .str b
    | _ => .str "?".toUTF8.toList
  else match jChar loc c with
    | .chr b => .str b
    | _ => .err "Unfinished character (to_char throws)"

/-! ## Clojure (java.lang.String, clojure.string, RT) -/

def cCount (s : List Nat) : R := .int s.length

/-- RT.nthFrom on a CharSequence: `charAt(n)`, out of range throws. -/
def cNth (s : List Nat) (i : Int) : R :=
  if i < 0 ∨ s.length ≤ i.toNat then .err "StringIndexOutOfBoundsException"
  else .chr (unitsToBytes [s.getD i.toNat 0])

/-- RT.getFrom on a String: `n < length` → `charAt(n)`, else nil. -/
def cGet (s : List Nat) (i : Int) : R :=
  if i < 0 ∨ s.length ≤ i.toNat then .nil else .chr (unitsToBytes [s.getD i.toNat 0])

def cContains (s : List Nat) (i : Int) : R := .bool (decide (0 ≤ i ∧ i.toNat < s.length))

/-- String.substring(start, end). -/
def cSubs (s : List Nat) (start stop : Int) : R :=
  if start < 0 ∨ stop < start ∨ stop.toNat > s.length then .err "StringIndexOutOfBoundsException"
  else .str (unitsToBytes ((s.drop start.toNat).take (stop - start).toNat))

/-- StringSeq: one char per code unit. -/
def cSeq (s : List Nat) : R := if s.isEmpty then .nil else .chars (s.map fun u => unitsToBytes [u])

def cSeqCount (s : List Nat) : R := .int s.length

/-- String.compareTo: the first differing units' difference, else the length difference. -/
def cCompare (a b : List Nat) : R :=
  match firstDiff a b with
  | some (x, y) => .int (sign ((x : Int) - y))
  | none => .int (sign ((a.length : Int) - b.length))

/-- String.indexOf(str, fromIndex). -/
def cIndexOf (s pat : List Nat) (fromIndex : Int) : R :=
  let n := s.length
  if fromIndex ≥ n then (if pat.isEmpty then .int n else .nil)
  else
    let f := if fromIndex < 0 then 0 else fromIndex.toNat
    if pat.isEmpty then .int f
    else match ((List.range (n - f)).map (· + f)).find? (fun i => (s.drop i).take pat.length == pat) with
      | some i => .int i
      | none => .nil

/-- String.lastIndexOf(str, fromIndex). -/
def cLastIndexOf (s pat : List Nat) (fromIndex : Int) : R :=
  let right : Int := s.length - pat.length
  let f := if fromIndex > right then right else fromIndex
  if f < 0 then .nil
  else if pat.isEmpty then .int f
  else match ((List.range (f.toNat + 1)).reverse).find? (fun i => (s.drop i).take pat.length == pat) with
    | some i => .int i
    | none => .nil

/-- Character.isWhitespace on a UTF-16 unit. -/
def javaIsWhitespace (u : Nat) : Bool :=
  (0x09 ≤ u && u ≤ 0x0D) || (0x1C ≤ u && u ≤ 0x20) || u == 0x1680 ||
  (0x2000 ≤ u && u ≤ 0x2006) || (0x2008 ≤ u && u ≤ 0x200A) || u == 0x2028 || u == 0x2029 ||
  u == 0x205F || u == 0x3000

def cTriml (s : List Nat) : R := .str (unitsToBytes (s.dropWhile javaIsWhitespace))
def cTrimr (s : List Nat) : R := .str (unitsToBytes (s.reverse.dropWhile javaIsWhitespace).reverse)
def cTrim (s : List Nat) : R :=
  .str (unitsToBytes ((s.dropWhile javaIsWhitespace).reverse.dropWhile javaIsWhitespace).reverse)
def cBlank (s : List Nat) : R := .bool (s.all javaIsWhitespace)

/-- Cased letters among the drawn code points (Unicode's Cased property). -/
def cased (c : Nat) : Bool :=
  (0x41 ≤ c && c ≤ 0x5A) || (0x61 ≤ c && c ≤ 0x7A) || c == 0xC9 || c == 0xE9 || c == 0xDF ||
  c == 0x3A3 || c == 0x3C3 || c == 0x3C2 || c == 0xFF21 || c == 0xFF41

/-- String.toUpperCase (non-Turkic default locale): full case mapping (SpecialCasing:
ß → "SS"). -/
def javaUpperCp (c : Nat) : List Nat :=
  if 0x61 ≤ c ∧ c ≤ 0x7A then [c - 32]
  else if c == 0xE9 then [0xC9] else if c == 0xDF then [0x53, 0x53]
  else if c == 0x3C3 || c == 0x3C2 then [0x3A3] else if c == 0xFF41 then [0xFF21] else [c]

/-- String.toLowerCase: Σ is ς at the end of a word (Final_Sigma), σ elsewhere. -/
def javaLower (cps : List Nat) : List Nat :=
  (List.range cps.length).map fun i =>
    let c := cps.getD i 0
    if 0x41 ≤ c ∧ c ≤ 0x5A then c + 32
    else if c == 0xC9 then 0xE9 else if c == 0xFF21 then 0xFF41
    else if c == 0x3A3 then
      (if i > 0 && cased (cps.getD (i - 1) 0) && !(i + 1 < cps.length && cased (cps.getD (i + 1) 0))
       then 0x3C2 else 0x3C3)
    else c

def cUpperU (s : List Nat) : List Nat := ((unitsToCps s).flatMap javaUpperCp).flatMap utf16
def cLowerU (s : List Nat) : List Nat := (javaLower (unitsToCps s)).flatMap utf16
def cUpper (s : List Nat) : R := .str (unitsToBytes (cUpperU s))
def cLower (s : List Nat) : R := .str (unitsToBytes (cLowerU s))

/-- clojure.string/capitalize: fewer than 2 units: `toUpperCase`; else the first unit upper
cased, the rest lower cased (concatenated as units: a split surrogate pair joins again). -/
def cCapitalize (s : List Nat) : R :=
  if s.length < 2 then cUpper s
  else .str (unitsToBytes (cUpperU (s.take 1) ++ cLowerU (s.drop 1)))

/-- String.replace("", rep): `rep` around every UTF-16 unit. -/
def cReplaceEmpty (s : List Nat) (rep : List Nat) : R :=
  .str (unitsToBytes (s.foldr (fun u acc => rep ++ u :: acc) rep))

/-- clojure.string/escape: each unit looked up in `cmap`. -/
def cEscape (s : List Nat) (key : List Nat) : R :=
  .str (unitsToBytes (s.flatMap fun u => if [u] == key then [0x58] else [u]))

/-- StringBuilder.reverse: units reversed, surrogate pairs kept in order (code points). -/
def cReverse (s : List Nat) : R := .str ((unitsToCps s).reverse.flatMap utf8)

/-- RT.charCast(Object): `n < 0 || n > 0xFFFF` throws, else that unit. -/
def cChar (n : Int) : R :=
  if n < 0 ∨ n > 0xFFFF then .err "Value out of range for char" else .chr (unitsToBytes [n.toNat])

/-! ## The questions -/

inductive Op where
  | count
  | nth (i : Int)
  | get (i : Int)
  | contains (i : Int)
  | subs1 (i : Int)
  | subs2 (i j : Int)
  | seq
  | seqCount
  | firstInt
  | compare
  | indexOf (needle : List Nat) (fromIndex : Option Int)
  | lastIndexOf (needle : List Nat) (fromIndex : Option Int)
  | trim | triml | trimr | blank
  | upper | lower | capitalize
  | replaceEmpty
  | escape (key : Nat)
  | reverse
  | seqSelfEq
  | seqEqVec
  | seqHashVec
  deriving BEq, Inhabited

/-- A question: an operation on a text (and a second text for `compare`), under a locale. -/
structure Case where
  loc : Locale
  op : Op
  s : List Nat
  t : List Nat := []
  deriving Inhabited

def Op.name : Op → String
  | .count => "count" | .nth _ => "nth" | .get _ => "get" | .contains _ => "contains?"
  | .subs1 _ => "subs/2" | .subs2 .. => "subs/3" | .seq => "seq" | .seqCount => "count of seq"
  | .firstInt => "int of first" | .compare => "compare"
  | .indexOf _ _ => "index-of" | .lastIndexOf _ _ => "last-index-of"
  | .trim => "trim" | .triml => "triml" | .trimr => "trimr" | .blank => "blank?"
  | .upper => "upper-case" | .lower => "lower-case" | .capitalize => "capitalize"
  | .replaceEmpty => "replace \"\"" | .escape _ => "escape" | .reverse => "reverse"
  | .seqSelfEq => "(= x x) on a string seq" | .seqEqVec => "(= (seq s) (vec s))"
  | .seqHashVec => "hash of (seq s) vs (vec s)"

def Case.program (c : Case) : String :=
  let s := lit c.s
  match c.op with
  | .count => s!"(count {s})"
  | .nth i => s!"(nth {s} {i})"
  | .get i => s!"(get {s} {i})"
  | .contains i => s!"(contains? {s} {i})"
  | .subs1 i => s!"(subs {s} {i})"
  | .subs2 i j => s!"(subs {s} {i} {j})"
  | .seq => s!"(seq {s})"
  | .seqCount => s!"(count (seq {s}))"
  | .firstInt => s!"(int (first {s}))"
  | .compare => s!"(compare {s} {lit c.t})"
  | .indexOf n none => s!"(clojure.string/index-of {s} {lit n})"
  | .indexOf n (some f) => s!"(clojure.string/index-of {s} {lit n} {f})"
  | .lastIndexOf n none => s!"(clojure.string/last-index-of {s} {lit n})"
  | .lastIndexOf n (some f) => s!"(clojure.string/last-index-of {s} {lit n} {f})"
  | .trim => s!"(clojure.string/trim {s})"
  | .triml => s!"(clojure.string/triml {s})"
  | .trimr => s!"(clojure.string/trimr {s})"
  | .blank => s!"(clojure.string/blank? {s})"
  | .upper => s!"(clojure.string/upper-case {s})"
  | .lower => s!"(clojure.string/lower-case {s})"
  | .capitalize => s!"(clojure.string/capitalize {s})"
  | .replaceEmpty => s!"(clojure.string/replace {s} \"\" \"-\")"
  | .escape k => s!"(clojure.string/escape {s} \{{charLit k} \"X\"})"
  | .reverse => s!"(clojure.string/reverse {s})"
  | .seqSelfEq => s!"(let [x (seq {s})] (= x x))"
  | .seqEqVec => s!"(= (seq {s}) (vec {s}))"
  | .seqHashVec => s!"(= (hash (seq {s})) (hash (vec {s})))"

/-- Whether the answer can depend on the locale. -/
def Op.localeDependent : Op → Bool
  | .upper | .lower | .capitalize | .firstInt => true
  | _ => false

/-- jank's answer and Clojure's. -/
def Case.eval (c : Case) : R × R :=
  let js := jstr c.s
  let cs := cstr c.s
  match c.op with
  | .count => (jCount js, cCount cs)
  | .nth i => (jNth js i, cNth cs i)
  | .get i => (jGet js i, cGet cs i)
  | .contains i => (jContains js i, cContains cs i)
  | .subs1 i => (jSubs js i js.length, cSubs cs i cs.length)
  | .subs2 i j => (jSubs js i j, cSubs cs i j)
  | .seq => (jSeq js, cSeq cs)
  | .seqCount => (jSeqCount js, cSeqCount cs)
  | .firstInt =>
    let j := match jSeq js with
      | .chars (ch :: _) => jInt c.loc ch
      | .nil => .err "nil"
      | r => r
    let cl := match cs with
      | u :: _ => .int u
      | [] => .err "NullPointerException"
    (j, cl)
  | .compare => (jCompare js (jstr c.t), cCompare cs (cstr c.t))
  | .indexOf n f =>
    (jIndexOf js (jstr n) (f.getD 0), cIndexOf cs (cstr n) (f.getD 0))
  | .lastIndexOf n f =>
    (jLastIndexOf js (jstr n) (f.getD js.length), cLastIndexOf cs (cstr n) (f.getD cs.length))
  | .trim => (jTrim js, cTrim cs)
  | .triml => (jTriml js, cTriml cs)
  | .trimr => (jTrimr js, cTrimr cs)
  | .blank => (jBlank js, cBlank cs)
  | .upper => (jUpper c.loc js, cUpper cs)
  | .lower => (jLower c.loc js, cLower cs)
  | .capitalize => (jCapitalize c.loc js, cCapitalize cs)
  | .replaceEmpty => (jReplaceEmpty js [0x2D], cReplaceEmpty cs [0x2D])
  | .escape k => (jEscape js (utf8 k), cEscape cs (utf16 k))
  | .reverse => (jReverse js, cReverse cs)
  | .seqSelfEq =>
    -- (seq "") is nil: (= nil nil) is true on both sides.
    if c.s.isEmpty then (.bool true, .bool true) else (jSeqEqual js (jSeqChars js), .bool true)
  | .seqEqVec =>
    if c.s.isEmpty then (.bool false, .bool false)   -- (= nil []) is false in both
    else (jSeqEqual js (jSeqChars js), .bool true)
  | .seqHashVec =>
    if c.s.isEmpty then (.bool false, .bool false)   -- (hash nil) 0, (hash []) not 0, both
    else (.bool (jHashSeq js == jHashVec (jSeqChars js)), .bool true)

/-! ## Drawing questions -/

/-- The code points drawn: ASCII letter, space, U+001F (a Java whitespace C does not know),
é (2 bytes), ß (upper case "SS" in Java), Σ (final sigma), € (3 bytes), U+2003 EM SPACE,
Ａ U+FF21 (3 bytes, above the surrogates), 😀 U+1F600 (4 bytes, a surrogate pair). -/
def alphabet : List Nat := [0x61, 0x20, 0x1F, 0xE9, 0xDF, 0x3A3, 0x20AC, 0x2003, 0xFF21, 0x1F600]

def indices : List Int := [-1, 0, 1, 2, 3, 4, 5]

/-- Every text of at most `n` code points over `alphabet`. -/
def texts : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 => texts n ++ ((texts n).filter (·.length == n)).flatMap fun s => alphabet.map (s ++ [·])

def needles : List (List Nat) := [[], [0x61], [0xE9], [0x1F600]]
def froms : List (Option Int) := [none, some (-1), some 1, some 2, some 9]

/-- The operations, with their parameters drawn. -/
def opsFor (s : List Nat) : List Op :=
  let _ := s
  [.count, .seq, .seqCount, .firstInt, .trim, .triml, .trimr, .blank, .upper, .lower,
   .capitalize, .replaceEmpty, .reverse, .seqSelfEq, .seqEqVec, .seqHashVec] ++
  indices.map Op.nth ++ indices.map Op.get ++ indices.map Op.contains ++
  indices.map Op.subs1 ++ (indices.flatMap fun i => indices.map (Op.subs2 i)) ++
  (needles.flatMap fun n => froms.map (Op.indexOf n)) ++
  (needles.flatMap fun n => froms.map (Op.lastIndexOf n)) ++
  alphabet.map Op.escape

structure World where
  decisions : Decisions := {}

instance : Chaotic World where
  decisions w := w.decisions
  setDecisions w d := { w with decisions := d }

def drawText (name : String) (maxLen : Nat) : EStateM Stop World (List Nat) := do
  let n ← decide (σ := World) s!"{name}.len" (maxLen + 1)
  let mut out := []
  for k in List.range n do
    out := out ++ [alphabet.getD (← decide (σ := World) s!"{name}.char{k}" alphabet.length) 0]
  return out

def drawCase : EStateM Stop World Case := do
  let loc := if (← decide (σ := World) "env.locale" 2) == 0 then Locale.utf8 else Locale.c
  let s ← drawText "str.s" 3
  let ops := opsFor s ++ [.compare]
  let op := ops.getD (← decide (σ := World) "str.op" ops.length) .count
  let t ← if op == .compare then drawText "str.t" 2 else pure []
  return { loc, op, s, t }

def property : String := "jank's string and character functions agree with Clojure's"

def body : EStateM Stop World Unit := do
  let c ← drawCase
  let (j, cl) := c.eval
  unless j.agrees cl do
    violate (σ := World) property
      s!"{c.program} [{c.loc.name}]: Clojure {cl.show}, jank {j.show}"

def run (source : Source) : Ended :=
  match body.run { decisions := { source } } with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }
  | .error (.nodeDown _) w => { taken := w.decisions.taken, violation := none }

/-- Every question within the bounds (texts of at most `n` code points; `compare` against texts
of at most 2). -/
def allCases (n : Nat) : List Case :=
  let ts := texts n
  let ts2 := texts 2
  [Locale.utf8, Locale.c].flatMap fun loc =>
    ts.flatMap fun s =>
      ((opsFor s).filter (fun op => loc == .utf8 || op.localeDependent)).map (fun op => ({ loc, op, s } : Case)) ++
      (if loc == .utf8 && s.length ≤ 2 then ts2.map fun t => ({ loc, op := .compare, s, t } : Case) else [])

/-! ## Theorems -/

theorem utf8_length (c : Nat) :
    (utf8 c).length = if c < 0x80 then 1 else if c < 0x800 then 2 else if c < 0x10000 then 3 else 4 := by
  unfold utf8
  by_cases h1 : c < 0x80 <;> by_cases h2 : c < 0x800 <;> by_cases h3 : c < 0x10000 <;> simp [h1, h2, h3]

theorem utf16_length (c : Nat) : (utf16 c).length = if c < 0x10000 then 1 else 2 := by
  unfold utf16; split <;> simp

theorem jstr_length (cps : List Nat) : (jstr cps).length = (cps.map fun c => (utf8 c).length).sum := by
  induction cps with
  | nil => rfl
  | cons c cs ih => simp [jstr, List.flatMap_cons] at * <;> omega

theorem cstr_length (cps : List Nat) : (cstr cps).length = (cps.map fun c => (utf16 c).length).sum := by
  induction cps with
  | nil => rfl
  | cons c cs ih => simp [cstr, List.flatMap_cons] at * <;> omega

/-- Per code point, jank counts at least as many bytes as Clojure counts units, and exactly as
many only for ASCII. -/
theorem utf8_ge_utf16 (c : Nat) : (utf16 c).length ≤ (utf8 c).length ∧
    ((utf16 c).length = (utf8 c).length ↔ c < 0x80) := by
  rw [utf8_length, utf16_length]
  constructor
  · split <;> split <;> (try split) <;> (try split) <;> omega
  · split <;> split <;> (try split) <;> (try split) <;> omega

/-- `count`: jank's never undercounts Clojure's, and they agree exactly on all-ASCII texts. -/
theorem count_ge (cps : List Nat) : (cstr cps).length ≤ (jstr cps).length := by
  rw [jstr_length, cstr_length]
  induction cps with
  | nil => simp
  | cons c cs ih => simp only [List.map_cons, List.sum_cons]; have := (utf8_ge_utf16 c).1; omega

theorem count_eq_iff (cps : List Nat) :
    (cstr cps).length = (jstr cps).length ↔ ∀ c ∈ cps, c < 0x80 := by
  rw [jstr_length, cstr_length]
  induction cps with
  | nil => simp
  | cons c cs ih =>
    simp only [List.map_cons, List.sum_cons, List.mem_cons, forall_eq_or_imp]
    have h1 := utf8_ge_utf16 c
    have h2 : (cs.map fun c => (utf16 c).length).sum ≤ (cs.map fun c => (utf8 c).length).sum := by
      have := count_ge cs; rwa [jstr_length, cstr_length] at this
    constructor
    · intro h
      have e1 : (utf16 c).length = (utf8 c).length := by omega
      exact ⟨h1.2.mp e1, ih.mp (by omega)⟩
    · intro ⟨hc, hs⟩
      have := h1.2.mpr hc
      have := ih.mpr hs
      omega

/-- immutable_string `compare`'s length step: `static_cast<int>(a - b)` has the sign of
`a - b` for every pair of lengths below 2^31 … -/
theorem compare_len_sign_ok (a b : BitVec 64) (ha : a < 0x80000000#64) (hb : b < 0x80000000#64) :
    ((a - b).truncate 32).slt 0#32 = decide (a < b) := by
  bv_decide

/-- … and the wrong sign for lengths 2^31 apart (a 2 GiB string compared with its empty
prefix reads as smaller). -/
theorem compare_len_wrong : jCompareLen 0x80000000 0 < 0 := by decide

/-- A string whose last character is cut short (`(subs "aé" 0 2)`): `next()` walks past it. -/
theorem seq_walks_past_end : ∃ w, jSeq [0x61, 0xC3] = .ub w := ⟨_, rfl⟩

/-- `(= x x)` is false for the seq of "é". -/
theorem seq_not_reflexive : jSeqEqual (utf8 0xE9) (jSeqChars (utf8 0xE9)) = .bool false := by
  decide

/-- `(= (seq "a") [\a])` is true in jank but the hashes differ, even for ASCII. -/
theorem seq_hash_inconsistent :
    jSeqEqual [0x61] [[0x61]] = .bool true ∧ jHashSeq [0x61] ≠ jHashVec [[0x61]] := by
  decide

/-- `nth` and `get` on a string give a character of one byte … -/
theorem nth_is_one_byte (s : List UInt8) (i : Int) (b : List UInt8) (h : jNth s i = .chr b) :
    b.length = 1 := by
  unfold jNth at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h; rfl

/-- … so for any character outside ASCII (2 to 4 bytes) it is never that character. -/
theorem nth_never_non_ascii (s : List UInt8) (i : Int) (c : Nat) (hc : 0x80 ≤ c) :
    jNth s i ≠ .chr (utf8 c) := by
  intro h
  have h1 := nth_is_one_byte s i _ h
  rw [utf8_length] at h1
  split at h1 <;> (try split at h1) <;> (try split at h1) <;> omega

/-- `index-of` with a negative start: Java starts at 0, jank's `size_t` start is 2^64 - 1. -/
theorem index_of_negative :
    jIndexOf [0x61] [0x61] (-1) = .nil ∧ cIndexOf [0x61] [0x61] (-1) = .int 0 := by decide

/-- `compare` of Ａ (U+FF21) and 😀 (U+1F600): UTF-8 byte order is code point order; Java's is
UTF-16 unit order, where every supplementary character sorts below U+E000..U+FFFF. -/
theorem compare_fullwidth_emoji :
    jCompare (jstr [0xFF21]) (jstr [0x1F600]) = .int (-1) ∧
    cCompare (cstr [0xFF21]) (cstr [0x1F600]) = .int 1 := by decide

end Jank.Str
