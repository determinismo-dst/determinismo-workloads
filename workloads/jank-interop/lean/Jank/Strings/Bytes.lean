import Jank.Strings.Print
import Jank.Hash

/-!
# Bytes: jtl/utf8.cpp, jtl/immutable_string.hpp, jtl/string_builder.cpp

A `jtl::immutable_string` is its bytes (`List UInt8`) and a cached hash (`store.hash`, 0 = not
computed). Its small/large layout (23 bytes inline, else a GC buffer, shared or owned) does not
change any result jank code can observe, with two exceptions modeled where they matter:
`init_large_fill` takes its size as `u8` (no caller passes more than 1: latent), and the cached
hash is written in place while it is computed (`Jank.Strings.HashRace`).

Indices are `usize` (64-bit); an `i64` converted to `usize` is taken modulo 2^64 (`toUsize`).
`char` comparisons are byte comparisons; where signedness changes a value (`hash::visit(char)`),
`Jank.Hash.CharSign` gives both platforms.
-/

namespace Jank.Strings

abbrev Bytes := List UInt8

/-- `npos` (`std::numeric_limits<usize>::max()`). -/
def npos : Nat := 2 ^ 64 - 1

/-- `static_cast<usize>(i64)` / an `i64` passed where a `size_type` is expected. -/
def toUsize (i : Int) : Nat := (i % (2 ^ 64)).toNat

/-- `static_cast<i64>(usize)`. -/
def usizeToI64 (n : Nat) : Int := if n < 2 ^ 63 then n else (n : Int) - 2 ^ 64

/-- Reading `s[i]` (`operator[]`, no bounds check): `none` past the end (undefined behaviour). -/
def at? (s : Bytes) (i : Nat) : Option UInt8 := s[i]?

/-! ## jtl/utf8.cpp -/

/-- utf8.cpp `next_char_size` (line 13): from the lead byte (`static_cast<u8>`); a continuation
byte or 0xF8.. throws "Invalid UTF-8 string.". Reading past the end is `.error "UB: ..."`. -/
def nextCharSize (s : Bytes) (i : Nat) : Except String Nat :=
  match at? s i with
  | none => .error "UB: next_char_size reads past the end"
  | some c =>
    if c ≤ 0x7f then .ok 1
    else if c &&& 0xE0 == 0xC0 then .ok 2
    else if c &&& 0xF0 == 0xE0 then .ok 3
    else if c &&& 0xF8 == 0xF0 then .ok 4
    else .error "Invalid UTF-8 string."

/-- utf8.cpp `is_continuation_byte` (line 38): `i == npos` throws. Here `i` is already a
`usize` (a wrapped `i - 1` from index 0 is `npos`). -/
def isContinuationByte (s : Bytes) (i : Nat) : Except String Bool :=
  if i == npos then .error "Invalid UTF-8 string."
  else match at? s i with
    | none => .error "UB: is_continuation_byte reads past the end"
    | some c => .ok (c &&& 0xC0 == 0x80)

/-- `i - k` in `usize`. -/
def usub (i k : Nat) : Nat := (i + 2 ^ 64 - k) % 2 ^ 64

/-- utf8.cpp `prev_char_size` (line 48). -/
def prevCharSize (data : Bytes) (i : Nat) : Except String Nat := do
  if !(← isContinuationByte data (usub i 1)) then return 1
  if !(← isContinuationByte data (usub i 2)) then return 2
  if !(← isContinuationByte data (usub i 3)) then return 3
  if !(← isContinuationByte data (usub i 4)) then return 4
  throw "Invalid UTF-8 string."

/-- utf8.hpp `utf8_iterator`: its string, position `i` (`npos`: past the end) and the size `n`
of the character at `i`. -/
structure Utf8Iterator where
  data : Bytes
  i : Nat
  n : Nat
  deriving BEq, Repr

/-- utf8.cpp `utf8_iterator(s, position)` (line 79) (and `utf8_iterator(s)`, line 72, at 0). -/
def Utf8Iterator.mk' (s : Bytes) (position : Nat) : Except String Utf8Iterator := do
  let i := if s.isEmpty then npos else position
  let n ← if i == npos then pure 0 else nextCharSize s i
  return { data := s, i, n }

/-- utf8.cpp `operator*` (line 86): `data.substr(i, n)`. -/
def Utf8Iterator.deref (it : Utf8Iterator) : Except String Bytes := substr it.data it.i (some it.n)

/-- utf8.cpp `operator++` (line 91). -/
def Utf8Iterator.inc (it : Utf8Iterator) : Except String Utf8Iterator := do
  if it.i == npos then
    return { it with i := 0, n := ← nextCharSize it.data 0 }
  let i := it.i + it.n
  if i ≥ it.data.length then return { it with i := npos, n := 0 }
  return { it with i, n := ← nextCharSize it.data i }

/-- utf8.cpp `operator--` (line 122). -/
def Utf8Iterator.dec (it : Utf8Iterator) : Except String Utf8Iterator := do
  if it.i == 0 then return { it with i := npos, n := 0 }
  if it.i == npos then
    let size := it.data.length
    let n ← prevCharSize it.data size
    return { it with n, i := size - n }
  let n ← prevCharSize it.data it.i
  return { it with n, i := it.i - n }

/-- utf8.cpp `operator==` (line 150): same position and the same bytes. -/
def Utf8Iterator.eq (a b : Utf8Iterator) : Bool := a.i == b.i && a.data == b.data

/-- utf8.cpp `utf8_range::begin` / `end` (lines 160, 165). -/
def utf8Begin (s : Bytes) : Except String Utf8Iterator := Utf8Iterator.mk' s 0
def utf8End (s : Bytes) : Except String Utf8Iterator := Utf8Iterator.mk' s npos

/-- Iterating a `utf8_range` forward (`for(auto i(begin); i != end; ++i)`): its characters. The
iterator only moves forward and stops at `npos`, so `s.length + 1` steps suffice. -/
def utf8Chars (s : Bytes) : Except String (List Bytes) := do
  let e ← utf8End s
  let rec go (fuel : Nat) (it : Utf8Iterator) (acc : List Bytes) : Except String (List Bytes) := do
    match fuel with
    | 0 => throw "fuel"
    | fuel + 1 =>
      if it.eq e then return acc.reverse
      go fuel (← it.inc) ((← it.deref) :: acc)
  go (s.length + 2) (← utf8Begin s) []

/-- Iterating a `utf8_range | std::views::reverse`: from `end`, `--` then `*`, until `begin`. -/
def utf8CharsReversed (s : Bytes) : Except String (List Bytes) := do
  let b ← utf8Begin s
  let rec go (fuel : Nat) (it : Utf8Iterator) (acc : List Bytes) : Except String (List Bytes) := do
    match fuel with
    | 0 => throw "fuel"
    | fuel + 1 =>
      if it.eq b then return acc.reverse
      let it ← it.dec
      go fuel it ((← it.deref) :: acc)
  go (s.length + 2) (← utf8End s) []

/-! ## jtl/immutable_string.hpp: the operations jank's string code uses -/

/-- `traits_type::compare(a, b, n)` (memcmp: bytes as `unsigned char`): its sign. -/
def memcmpSign (a b : Bytes) (n : Nat) : Int :=
  let rec go : List UInt8 → List UInt8 → Nat → Int
    | x :: xs, y :: ys, n + 1 => if x < y then -1 else if y < x then 1 else go xs ys n
    | _, _, _ => 0
  go a b n

/-- immutable_string.hpp `compare` (line 576): memcmp over the common length, else
`static_cast<int>(length - s_length)` (the `usize` difference, cast to `int`). Its sign. -/
def compare (a b : Bytes) : Int :=
  let r := memcmpSign a b (min a.length b.length)
  if r != 0 then r
  else
    -- (int)(usize difference): the low 32 bits, signed.
    let d := usub a.length b.length
    let low := d % 2 ^ 32
    if low == 0 then 0 else if low < 2 ^ 31 then 1 else -1

/-- immutable_string.hpp `operator==` (line 546): same size and memcmp 0. -/
def eqBytes (a b : Bytes) : Bool := a.length == b.length && memcmpSign a b a.length == 0

/-- immutable_string.hpp `find(pattern, pos, pattern_length)` (line 281). The loop: find the
pattern's first byte in the remaining window (`char_traits::find`), compare the whole pattern
there, else continue one past it. -/
def find (corpus pattern : Bytes) (pos : Nat) : Nat :=
  let corpusLength := corpus.length
  let patternLength := pattern.length
  if patternLength == 0 then (if pos ≤ corpusLength then pos else npos)
  else if corpusLength ≤ pos then npos
  else
    let patternStart := pattern.headD 0
    let rec loop (fuel : Nat) (corpusPos : Nat) : Nat :=
      match fuel with
      | 0 => npos
      | fuel + 1 =>
        let remainingLen := corpusLength - corpusPos
        if remainingLen ≥ patternLength then
          -- char_traits::find(corpus_pos, remaining_len - pattern_length + 1, pattern_start)
          let window := ((corpus.drop corpusPos).take (remainingLen - patternLength + 1))
          match window.findIdx? (· == patternStart) with
          | none => npos
          | some k =>
            let p := corpusPos + k
            if memcmpSign (corpus.drop p) pattern patternLength == 0 then p
            else loop fuel (p + 1)
        else npos
    loop (corpusLength + 1) pos

/-- immutable_string.hpp `rfind(s, pos, n)` (line 353). -/
def rfind (corpus s : Bytes) (pos : Nat) : Nat :=
  let length := corpus.length
  let n := s.length
  if n > length then npos
  else
    let pos := min pos (length - n)
    if n == 0 then pos
    else
      let rec loop (fuel : Nat) (it : Nat) : Nat :=
        match fuel with
        | 0 => npos
        | fuel + 1 =>
          if at? corpus it == s.head? && memcmpSign (corpus.drop it) s n == 0 then it
          else if it == 0 then npos
          else loop fuel (it - 1)
      loop (pos + 1) pos

/-- immutable_string.hpp `starts_with(immutable_string_view)` (line 420). -/
def startsWith (s p : Bytes) : Bool := if s.length < p.length then false else memcmpSign s p p.length == 0

/-- immutable_string.hpp `ends_with(immutable_string_view)` (line 449). -/
def endsWith (s p : Bytes) : Bool :=
  if s.length < p.length then false else memcmpSign (s.drop (s.length - p.length)) p p.length == 0

/-- immutable_string.hpp `contains(immutable_string_view)` (line 473): `find(s) != npos`. -/
def contains (s p : Bytes) : Bool := find s p 0 != npos

/-- `std::isspace` of a `char` in the C locale jank installs (en_US.UTF-8): the six ASCII
whitespace bytes; a byte ≥ 0x80 passed as a negative `char` is not space on glibc or macOS
(assumption; passing a negative `char` other than EOF is undefined). -/
def isspaceChar (c : UInt8) : Bool := c == 32 || (9 ≤ c && c ≤ 13)

/-- immutable_string.hpp `is_blank` (line 635). -/
def isBlank (s : Bytes) : Bool := s.all isspaceChar

/-- The value `to_hash` computes: Java's `String.hashCode` over the bytes (`ptr[i] & 0xff`),
then `hash::integer(u32)` (Murmur3 hashInt). -/
def toHashValue (s : Bytes) : UInt32 :=
  Jank.Hash.integer32 (s.foldl (fun h c => 31 * h + c.toUInt32) 0)

/-- immutable_string.hpp `to_hash` (line 648), with its cache: `store.hash != 0` returns it. -/
def toHash (s : Bytes) (cached : UInt32) : UInt32 × UInt32 :=
  if cached != 0 then (cached, cached) else let h := toHashValue s; (h, h)

/-- immutable_string.hpp `init_large_fill(value_type fill, u8 size)` (line 851) as reached from
`immutable_string(size_type size, value_type fill)` (line 140): the size is truncated to `u8`.
Only `character(char)` calls this constructor, with size 1 (latent). -/
def fill (size : Nat) (c : UInt8) : Bytes :=
  if size ≤ 23 then List.replicate size c else List.replicate (size % 256) c

/-! ## hash.cpp on bytes -/

/-- hash.cpp `visit(char)` (line 151): `static_cast<u32>(ch)` (sign-extended where `char` is
signed). -/
def visitChar (cs : Jank.Hash.CharSign) (c : UInt8) : UInt32 := Jank.Hash.widen cs c

/-- hash.hpp `ordered(It begin, It end)` over a byte range (persistent_string_sequence). -/
def orderedBytes (cs : Jank.Hash.CharSign) (bs : Bytes) : UInt32 :=
  Jank.Hash.mixCollectionHash (bs.foldl (fun h c => 31 * h + visitChar cs c) 1) bs.length.toUInt32

/-! ## jtl/string_builder.cpp

A builder is its bytes: every `operator()` appends (`maybe_realloc` keeps `pos + size + 1 ≤
capacity`, so nothing is lost). The double overload is modeled on the decimal it prints. -/

/-- A finite double as `std::to_chars` sees it: its shortest round-trip decimal digits `d` (no
leading or trailing zeros; "0" for zero) and the exponent `e` of the first digit (value =
0.d × 10^(e+1), i.e. d[0].d[1..] × 10^e), and its sign. -/
structure Dec where
  neg : Bool
  digits : List Char
  exp : Int
  deriving BEq, Repr

/-- The fixed (`%f`-style) text of a shortest decimal. -/
def Dec.fixed (d : Dec) : String :=
  let sign := if d.neg then "-" else ""
  let ds := d.digits
  let n := ds.length
  if d.exp ≥ 0 then
    let intLen := d.exp.toNat + 1
    if n ≤ intLen then sign ++ String.ofList (ds ++ List.replicate (intLen - n) '0')
    else sign ++ String.ofList (ds.take intLen) ++ "." ++ String.ofList (ds.drop intLen)
  else
    sign ++ "0." ++ String.ofList (List.replicate ((-d.exp).toNat - 1) '0') ++ String.ofList ds

/-- `%e`-style text of a shortest decimal (`d.ddde±XX`, at least two exponent digits). -/
def Dec.sci (d : Dec) : String :=
  let sign := if d.neg then "-" else ""
  let ds := d.digits
  let mant := match ds with
    | [c] => String.singleton c
    | c :: rest => String.singleton c ++ "." ++ String.ofList rest
    | [] => "0"
  let e := d.exp
  let eabs := toString e.natAbs
  let eabs := if eabs.length < 2 then "0" ++ eabs else eabs
  sign ++ mant ++ "e" ++ (if e < 0 then "-" else "+") ++ eabs

/-- `std::to_chars(first, last, double)` (shortest): the fixed or scientific text, whichever is
shorter, a tie going to fixed ([charconv.to.chars]). -/
def toChars (d : Dec) : String :=
  let f := d.fixed
  let s := d.sci
  if s.length < f.length then s else f

/-- string_builder.cpp `operator()(double)` (line 83) for a finite value: `to_chars`, then ".0"
when the text has neither '.' nor 'e'. (Infinities and NaN print `INFINITY`/`NAN` here, but
`real::to_string` prints those itself: number.cpp line 291.) -/
def builderDouble (d : Dec) : String :=
  let t := toChars d
  if t.contains '.' || t.contains 'e' then t else t ++ ".0"

/-- Java's `Double.toString` (JDK 19+, what Clojure's `str` gives) on the same shortest digits:
plain for 10^-3 ≤ |d| < 10^7 with at least one fractional digit, else `d.dddE±n`. -/
def javaDoubleToString (d : Dec) : String :=
  let sign := if d.neg then "-" else ""
  if d.digits == ['0'] then sign ++ "0.0"
  else if -3 ≤ d.exp ∧ d.exp < 7 then
    let f := ({ d with neg := false } : Dec).fixed
    sign ++ (if f.contains '.' then f else f ++ ".0")
  else
    let mant := match d.digits with
      | [c] => String.singleton c ++ ".0"
      | c :: rest => String.singleton c ++ "." ++ String.ofList rest
      | [] => "0.0"
    sign ++ mant ++ "E" ++ toString d.exp

end Jank.Strings
