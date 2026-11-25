import Determinismo

/-!
# Printing and reading back strings and characters

jank's C++, replicated function by function over UTF-8 bytes (`List UInt8`, a `std::string` /
`jtl::immutable_string`'s bytes; sizes are 64-bit `usize`, never near overflow here):

- `jtl/utf8.cpp`: `to_char(i64)`, `to_char(i64, fallback)`, `is_surrogate_high`,
  `is_surrogate_low`, `combine_surrogate_pair` (`toChar`, `toCharOr`, `isSurrogateHigh`, ...);
- `jank/util/escape.cpp`: `unescape_unicode`, `unescape`, `escape`;
- `runtime/obj/character.cpp`: `get_literal_from_char_bytes`, `character::to_code_string`;
- `runtime/obj/persistent_string.cpp`: `persistent_string::to_code_string`.

The interface the reader's model uses: `stringToCodeString`, `charToCodeString`, `unescape`.

Library behaviour assumed (not readable here):
- `std::wcrtomb` in the locale jank installs at start (`std::locale::global(std::locale(""))`,
  assumed `en_US.UTF-8`): a `wchar_t` (32-bit, signed on Linux and macOS) is written as its
  UTF-8 encoding (1 to 4 bytes; `L'\0'` as one NUL byte); a negative value or a UTF-16 surrogate
  (U+D800..U+DFFF) fails with `(size_t)-1` (EILSEQ), as glibc's and FreeBSD/macOS's UTF-8
  converters do. It never returns `(size_t)-2`.
- `std::from_chars(first, last, u16&, 16)`: the longest prefix of hex digits (either case), no
  sign, no `0x`; four hex digits always fit a `u16`.
- `std::char_traits<char>` compares as `unsigned char`.
-/

namespace Jank.Strings

/-- A byte from a character literal (ASCII). -/
@[inline] def b (c : Char) : UInt8 := c.toNat.toUInt8

/-- The bytes of an ASCII Lean string literal. -/
def bs (s : String) : List UInt8 := s.toList.map b

/-! ## jtl/utf8.cpp -/

/-- `wcrtomb` in a UTF-8 locale (assumption above): `none` is `(size_t)-1`. -/
def wcrtombUtf8 (wc : Int32) : Option (List UInt8) :=
  let v := wc.toInt
  if v < 0 then none
  else
    let n := v.toNat
    if n ≤ 0x7F then some [n.toUInt8]
    else if n ≤ 0x7FF then some [(0xC0 ||| (n >>> 6)).toUInt8, (0x80 ||| (n &&& 0x3F)).toUInt8]
    else if 0xD800 ≤ n ∧ n ≤ 0xDFFF then none
    else if n ≤ 0xFFFF then
      some [(0xE0 ||| (n >>> 12)).toUInt8, (0x80 ||| ((n >>> 6) &&& 0x3F)).toUInt8,
            (0x80 ||| (n &&& 0x3F)).toUInt8]
    else if n ≤ 0x10FFFF then
      some [(0xF0 ||| (n >>> 18)).toUInt8, (0x80 ||| ((n >>> 12) &&& 0x3F)).toUInt8,
            (0x80 ||| ((n >>> 6) &&& 0x3F)).toUInt8, (0x80 ||| (n &&& 0x3F)).toUInt8]
    else none

/-- `static_cast<wchar_t>(ch)`: the low 32 bits of the i64, as a signed 32-bit `wchar_t`
(modular since C++20). -/
def toWchar (ch : Int64) : Int32 := Int32.ofBitVec (ch.toBitVec.truncate 32)

/-- utf8.cpp `to_char(i64 const ch)` (line 170): throws past 0x10FFFF (signed compare, so a
negative `ch` passes), then `wcrtomb` of `static_cast<wchar_t>(ch)`; `(size_t)-1` throws
"Unfinished character". -/
def toChar (ch : Int64) : Except String (List UInt8) :=
  if ch > 0x10FFFF then .error s!"Value out of range for char: {ch}"
  else match wcrtombUtf8 (toWchar ch) with
    | none => .error s!"Unfinished character: {ch}"
    | some bytes => .ok bytes

/-- utf8.cpp `to_char(i64 const ch, immutable_string const &fallback)` (line 196). -/
def toCharOr (ch : Int64) (fallback : List UInt8) : List UInt8 :=
  if ch > 0x10FFFF then fallback
  else (wcrtombUtf8 (toWchar ch)).getD fallback

/-- utf8.cpp `is_surrogate_high` (line 218). -/
def isSurrogateHigh (high : UInt16) : Bool := high ≥ 0xD800 && high ≤ 0xDBFF

/-- utf8.cpp `is_surrogate_low` (line 223). -/
def isSurrogateLow (low : UInt16) : Bool := low ≥ 0xDC00 && low ≤ 0xDFFF

/-- utf8.cpp `combine_surrogate_pair` (line 228), in `u32`. -/
def combineSurrogatePair (high low : UInt16) : UInt32 :=
  0x10000 + ((high.toUInt32 - 0xD800) * 0x400) + (low.toUInt32 - 0xDC00)

/-! ## jtl/immutable_string.hpp: the substring constructor -/

/-- immutable_string.hpp `immutable_string(s, pos, count)` (line 162), what `substr` calls:
throws when `pos` is past the end, else `count` clipped to what is left. -/
def substr (s : List UInt8) (pos : Nat) (count : Option Nat := none) : Except String (List UInt8) :=
  if s.length < pos then .error "position outside of string"
  else
    let count := match count with
      | none => s.length - pos
      | some c => if s.length < pos + c then s.length - pos else c
    .ok ((s.drop pos).take count)

/-! ## jank/util/escape.cpp -/

def isHexDigit (c : UInt8) : Bool :=
  (b '0' ≤ c && c ≤ b '9') || (b 'a' ≤ c && c ≤ b 'f') || (b 'A' ≤ c && c ≤ b 'F')

def hexValue (c : UInt8) : Nat :=
  if b '0' ≤ c && c ≤ b '9' then (c - b '0').toNat
  else if b 'a' ≤ c && c ≤ b 'f' then (c - b 'a').toNat + 10
  else (c - b 'A').toNat + 10

/-- escape.cpp `unescape_unicode` (line 12): exactly four bytes, all hex digits
(`std::from_chars` into a `u16`, base 16, must stop at the end). -/
def unescapeUnicode (input : List UInt8) : Except String UInt16 :=
  if input.length != 4 then .error s!"String contains invalid unicode escape sequence '\\u{String.fromUTF8! ⟨input.toArray⟩ |>.quote}'."
  else if input.all isHexDigit then .ok (input.foldl (fun acc c => acc * 16 + hexValue c) 0).toUInt16
  else .error s!"String contains invalid unicode escape sequence."

/-- escape.cpp `unescape` (line 35): the loop over `i` with the `escape` flag, the builder `sb`.
Each turn consumes at least one byte, so `input.length + 1` turns of fuel always suffice
(`unescape_fuel_enough`). -/
def unescapeLoop (input : Array UInt8) : Nat → Nat → Bool → Array UInt8 → Except String (List UInt8)
  | 0, _, _, _ => .error "fuel"
  | fuel + 1, i, escape, sb =>
    let size := input.size
    if i < size then
      let c := input[i]!
      if !escape && c == b '\\' && i + 1 < size && input[i + 1]! == b 'u' then
        match substr input.toList (i + 2) (some 4) >>= unescapeUnicode with
        | .error e => .error e
        | .ok codepointHigh =>
          let i := i + 6
          if !isSurrogateHigh codepointHigh then
            unescapeLoop input fuel i escape (sb ++ (toCharOr codepointHigh.toNat.toInt64 (bs "?")).toArray)
          else if i + 6 > size || input[i]! != b '\\' || input[i + 1]! != b 'u' then
            unescapeLoop input fuel i escape (sb.push (b '?'))
          else
            match substr input.toList (i + 2) (some 4) >>= unescapeUnicode with
            | .error e => .error e
            | .ok codepointLow =>
              let i := i + 6
              if !isSurrogateLow codepointLow then
                let sb := sb ++ (bs "?").toArray
                unescapeLoop input fuel i escape (sb ++ (toCharOr codepointLow.toNat.toInt64 (bs "?")).toArray)
              else
                match toChar (combineSurrogatePair codepointHigh codepointLow).toNat.toInt64 with
                | .error e => .error e
                | .ok bytes => unescapeLoop input fuel i escape (sb ++ bytes.toArray)
      else if !escape then
        if c == b '\\' then unescapeLoop input fuel (i + 1) true sb
        else unescapeLoop input fuel (i + 1) escape (sb.push c)
      else
        let out : Option UInt8 :=
          if c == b 'n' then some 10 else if c == b 't' then some 9
          else if c == b 'r' then some 13 else if c == b '\\' then some (b '\\')
          else if c == b '"' then some (b '"') else if c == b 'a' then some 7
          else if c == b 'v' then some 11 else if c == b '?' then some (b '?')
          else if c == b 'f' then some 12 else if c == b 'b' then some 8
          else none
        match out with
        | none => .error s!"String contains invalid escape sequence '\\{Char.ofNat c.toNat}'."
        | some o => unescapeLoop input fuel (i + 1) false (sb.push o)
    else .ok sb.toList

/-- escape.cpp `unescape(immutable_string const &input)` (line 35). -/
def unescape (s : List UInt8) : Except String (List UInt8) :=
  unescapeLoop s.toArray (s.length + 1) 0 false #[]

/-- escape.cpp `escape(immutable_string const &input)` (line 148): byte by byte. -/
def escape (input : List UInt8) : List UInt8 :=
  input.flatMap fun c =>
    if c == 10 then bs "\\n"
    else if c == 9 then bs "\\t"
    else if c == 13 then bs "\\r"
    else if c == b '\\' then bs "\\\\"
    else if c == b '"' then bs "\\\""
    else if c == 7 then bs "\\a"
    else if c == 11 then bs "\\v"
    else if c == 12 then bs "\\f"
    else if c == 8 then bs "\\b"
    else [c]

/-! ## Code strings -/

/-- character.cpp `get_literal_from_char_bytes` (line 12): one byte is looked up among the six
names, else `\` and the byte (`util::format(R"(\{})", bytes[0])` appends the `char`); more bytes
(or none) are `\` and the bytes. -/
def getLiteralFromCharBytes (bytes : List UInt8) : List UInt8 :=
  match bytes with
  | [c] =>
    if c == 10 then bs "\\newline"
    else if c == b ' ' then bs "\\space"
    else if c == 9 then bs "\\tab"
    else if c == 8 then bs "\\backspace"
    else if c == 12 then bs "\\formfeed"
    else if c == 13 then bs "\\return"
    else [b '\\', c]
  | _ => b '\\' :: bytes

/-- character.cpp `character::to_code_string` (line 84). -/
def charToCodeString (data : List UInt8) : List UInt8 := getLiteralFromCharBytes data

/-- persistent_string.cpp `persistent_string::to_code_string` (line 52):
`"` + `util::escape(data)` + `"`. -/
def stringToCodeString (s : List UInt8) : List UInt8 := b '"' :: (escape s ++ [b '"'])

end Jank.Strings


-- READY
