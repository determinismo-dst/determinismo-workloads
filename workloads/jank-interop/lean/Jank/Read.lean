import Jank.Lex
import Jank.ReadValue

/-!
# jank's parser, `read::parse::processor` (read/parse.cpp, commit f3d82d654), as written

The parser pulls tokens from the lexer iterator (`token_current`; `*token_current` is the latest
token, `++token_current` lexes the next, parse.cpp:149-163) and builds objects. Modeled here:
`next` (204-335), `parse_upto` (337-368), lists, vectors, maps (421-511, duplicate keys found
through `std::unordered_map<object_ref>` with jank's `hash::visit` and `equal`, object.cpp:369-385),
quote, characters (541-588, with `get_char_from_literal` 105-137 and `parse_character_in_base`
63-103), meta hints (590-674), reader macros (676-709): sets (711-750), `#()` (752-805 with the
`%` handling of `parse_symbol` 1853-1894), `#'` (807-838), `##` (840-886), regexes (888-913, the
string token's raw text), tagged literals (1008-1124, no readers installed: an error), `#_`
(1126-1143), `#?` (1145-1318, read-string's default `allow_reader_conditional = false`), unquote
(1761-1784), deref (1786-1808), symbols (1824-1901), keywords (1903-1938), numbers (1940-1994)
and strings (1996-2021, `util::unescape`, escape.cpp:35-145).

Syntax quote is modeled on its own (`Jank.ReadSyntaxQuote`); here a backquote is an error
"unmodeled". jank's `{:jank/source ...}` metadata on lists, vectors, maps, sets and symbols is
left out (see ReadValue).

Recursion and loops run under fuel: recursion deeper than the input allows (every level of a
real parse consumes a token of at least one byte) is a stack overflow, reported as `crash`.
-/

namespace Jank.Read

open Jank.LexBytes Jank.Lex Jank.ReadValue

/-! ## Escapes, characters, numbers -/

/-- `std::from_chars(buf, buf + 4, u16, 16)` on exactly four characters: hex digits only (no
sign, no `0x`), all consumed. -/
def fromChars4 (bs : List UInt8) : Option Nat :=
  if bs.length != 4 then none
  else bs.foldl (fun acc b => acc.bind fun a =>
    match digitVal b.toNat with
    | some d => if d < 16 then some (a * 16 + d) else none
    | none => none) (some 0)

/-- `jtl::to_char(cp, fallback)` (utf8.cpp:196-216): `wcrtomb` in the locale; a code point it
cannot encode (a surrogate; anything ≥ 0x80 in the C locale) gives the fallback (RA3). -/
def toCharFallback (loc : Locale) (cp : Nat) (fallback : List UInt8) : List UInt8 :=
  if cp > 0x10FFFF then fallback
  else if 0xD800 ≤ cp && cp ≤ 0xDFFF then fallback
  else if loc == .c && cp ≥ 0x80 then fallback
  else utf8Encode cp

/-- `util::unescape` (escape.cpp:35-145), on the raw bytes between the quotes. -/
def unescape (loc : Locale) (input : List UInt8) : Except String (List UInt8) := Id.run do
  let a := input.toArray
  let size := a.size
  let mut sb : Array UInt8 := #[]
  let mut escape := false
  let mut i := 0
  let q : List UInt8 := [63]
  for _ in [0:size + 1] do
    if i ≥ size then break
    let c := a[i]!
    if !escape && c == 92 && i + 1 < size && a[i + 1]! == 117 then
      let high := fromChars4 (a.extract (i + 2) (i + 6)).toList
      i := i + 6
      match high with
      | none => return .error "invalid unicode escape"
      | some h =>
        if !(0xD800 ≤ h && h ≤ 0xDBFF) then
          sb := sb ++ (toCharFallback loc h q).toArray
          continue
        if i + 6 > size || a[i]! != 92 || a[i + 1]! != 117 then
          sb := sb.push 63
          continue
        let low := fromChars4 (a.extract (i + 2) (i + 6)).toList
        i := i + 6
        match low with
        | none => return .error "invalid unicode escape"
        | some l =>
          if !(0xDC00 ≤ l && l ≤ 0xDFFF) then
            sb := sb.push 63
            sb := sb ++ (toCharFallback loc l q).toArray
            continue
          let cp := 0x10000 + (h - 0xD800) * 0x400 + (l - 0xDC00)
          sb := sb ++ (toCharFallback loc cp q).toArray
    else if !escape then
      if c == 92 then escape := true else sb := sb.push c
      i := i + 1
    else
      let mapped : Option UInt8 :=
        if c == 110 then some 10 else if c == 116 then some 9 else if c == 114 then some 13
        else if c == 92 then some 92 else if c == 34 then some 34 else if c == 97 then some 7
        else if c == 118 then some 11 else if c == 63 then some 63 else if c == 102 then some 12
        else if c == 98 then some 8 else none
      match mapped with
      | none => return .error s!"invalid escape sequence \\{showBytes [c]}"
      | some m => sb := sb.push m
      escape := false
      i := i + 1
  return .ok sb.toList

def textVal (bs : List UInt8) : Val :=
  match utf8Decode bs with
  | some cs => .str cs
  | none => .bytes bs

def codes (bs : List UInt8) : List Nat :=
  (utf8Decode bs).getD (bs.map (·.toNat))

/-- `std::stol(s, &processed, base)` then `processed == size`: an optional sign, for base 16 an
optional `0x`, at least one digit, all characters consumed (RA6). -/
def stolAll (s : List UInt8) (base : Nat) : Option Int := Id.run do
  let mut cs := s.map (·.toNat)
  let mut neg := false
  if cs.head? == some 45 then neg := true; cs := cs.drop 1
  else if cs.head? == some 43 then cs := cs.drop 1
  if base == 16 && cs.length ≥ 2 && cs[0]! == 48 && (cs[1]! == 120 || cs[1]! == 88) then cs := cs.drop 2
  if cs.isEmpty then return none
  let mut v : Int := 0
  for c in cs do
    match digitVal c with
    | some d => if d < base then v := v * base + d else return none
    | none => return none
  return some (if neg then -v else v)

/-- `is_utf8_char(immutable_string)` (parse.cpp:24-61): a byte-pattern check by length. -/
def isUtf8Str (s : List UInt8) : Bool :=
  let cont := fun (b : UInt8) => 0x80 ≤ b && b ≤ 0xBF
  match s with
  | [a] => a ≤ 0x7F
  | [a, b] => 0xC0 ≤ a && a ≤ 0xDF && cont b
  | [a, b, c] => 0xE0 ≤ a && a ≤ 0xEF && cont b && cont c
  | [a, b, c, d] => 0xF0 ≤ a && a ≤ 0xF7 && cont b && cont c && cont d
  | _ => false

/-- `parse_character` (parse.cpp:541-588) on the token's text (`\` included). -/
def parseCharacter (sv : List UInt8) : Except String Val :=
  let named : List (String × Nat) :=
    [("\\newline", 10), ("\\space", 32), ("\\tab", 9), ("\\backspace", 8), ("\\formfeed", 12), ("\\return", 13)]
  if sv.length == 2 then .ok (.char sv[1]!.toNat)
  else match named.find? (fun (n, _) => bytesOf n == sv) with
  | some (_, c) => .ok (.char c)
  | none =>
    if sv[0]? == some 92 && (sv[1]? == some 117 || sv[1]? == some 111) then
      let base := if sv[1]? == some 117 then 16 else 8
      match stolAll (sv.drop 2) base with
      | none => .error "Unable to parse Unicode codepoint."
      | some cp =>
        -- codecvt_utf8<char32_t>::to_bytes: code points above 0x10FFFF and surrogates fail (RA6).
        let u := cp % 4294967296
        if u > 0x10FFFF || (0xD800 ≤ u && u ≤ 0xDFFF) then .error "Unicode character is out of range."
        else .ok (.char u.toNat)
    else if sv[0]? == some 92 && 3 ≤ sv.length && sv.length ≤ 5 then
      let str := sv.drop 1
      if !isUtf8Str str then .error "This Unicode character literal is invalid."
      else match utf8Decode str with
        | some [c] => .ok (.char c)
        | _ => .error "invalid"
    else .error "invalid character"

/-- `big_integer(s, radix, is_negative)` (big_integer.cpp:66-108): radix 10, 8 and 16 through
boost's string parsing (with a "0" or "0x" prefix), other radixes digit by digit (an empty
literal is 0). -/
def bigIntegerCreate (lit : List UInt8) (radix : Int) (neg : Bool) : Except String Int := do
  let v ← if radix == 10 then
      (if lit.isEmpty then .error "The `big_integer` constructor requires a non-empty string."
       else boostParse lit)
    else if radix == 8 then boostParse (48 :: lit)
    else if radix == 16 then boostParse (48 :: 120 :: lit)
    else
      pure (lit.foldl (fun (acc : Int) b =>
        let c := if isUpperC b.toNat then b.toNat + 32 else b.toNat
        let d : Int := if isDigitC c then c - 48 else (c : Int) - 97 + 10
        acc * radix + d) 0)
  return if neg then -v else v

/-- `ratio::create` (ratio.cpp:46-62, 88-101): gcd-normalized, sign on the numerator; an integer
when the denominator is 1. -/
def ratioCreate (n d : Int) : Except String Val :=
  if d == 0 then .error "Ratio denominator cannot be zero."
  else
    let g : Int := Int.ofNat (Int.gcd n d)
    let n' := n / g
    let d' := d / g
    let (n', d') := if d < 0 then (-n', -d') else (n', d')
    if d' == 1 then
      (if i64min ≤ n' && n' ≤ i64max then .ok (.long n') else .ok (.big n'))
    else .ok (.ratio n' d'.toNat)

/-- `big_decimal(string)` (big_decimal.cpp:128-132): boost `cpp_dec_float<100>` from the literal.
An empty literal (only from `36rM`-like tokens) is taken to be an error (RA7). -/
def bigDecimalCreate (lit : List UInt8) : Except String Val :=
  if lit.isEmpty || !(lit.any fun b => isDigitC b.toNat) then .error "cpp_dec_float: no digits"
  else .ok (.bigdec (strtod lit.toArray 0))

/-- `std::regex{ s.c_str(), ECMAScript }` (re_pattern.cpp:6-10) throws `regex_error` for Java
syntax outside C++'s ECMAScript grammar (RA8): a group opened by `(?` not followed by `:`, `=`
or `!` (inline flags `(?i)`, named groups `(?<n>...)`, lookbehind `(?<=...)`), and possessive
quantifiers (`*+`, `++`, `?+`: "nothing to repeat"). -/
def ecmaRejects (raw : List Nat) : Bool :=
  let a := raw.toArray
  (List.range a.size).any fun i =>
    let c := a[i]!
    let prevBackslash := i > 0 && a[i - 1]! == 92 && !(i > 1 && a[i - 2]! == 92)
    if prevBackslash then false
    else if c == 40 && a.getD (i + 1) 0 == 63 then
      let d := a.getD (i + 2) 0
      !(d == 58 || d == 61 || d == 33)
    else (c == 42 || c == 43 || c == 63) && a.getD (i + 1) 0 == 43 && i > 0 && a[i - 1]! != 40

/-! ## Keys: what jank's duplicate check and its collections treat as the same key -/

/-- jank's `equal` on read values (round 1's model, Jank/Equality.lean, restricted): integers of
any width by value, doubles with `==`, sequential collections elementwise. -/
def jankEqual : Val → Val → Bool
  | .long a, .long b | .long a, .big b | .big a, .long b | .big a, .big b => a == b
  | .dbl a, .dbl b => a.mant == b.mant && a.exp == b.exp
  | .withMeta _ a, b => jankEqual a b
  | a, .withMeta _ b => jankEqual a b
  | .list xs, .list ys | .list xs, .vec ys | .vec xs, .list ys | .vec xs, .vec ys =>
    xs.length == ys.length && (xs.zip ys).attach.all fun ⟨(x, y), _⟩ => jankEqual x y
  | a, b => a == b
termination_by a b => sizeOf a + sizeOf b
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (rename_i hm
       have hz := List.of_mem_zip hm
       have h1 := List.sizeOf_lt_of_mem hz.1
       have h2 := List.sizeOf_lt_of_mem hz.2
       omega)

/-- Equal and equal hashes: what `std::unordered_map<object_ref>` (and immer's hash set) treat as
one key. A long and a BigInt of one value, and 0.0 and -0.0, are equal with different hashes
(round 1, D12). -/
def jankSameKey : Val → Val → Bool
  | .long _, .big _ | .big _, .long _ => false
  | .dbl a, .dbl b => a == b
  | .withMeta _ a, b => jankSameKey a b
  | a, .withMeta _ b => jankSameKey a b
  | .list xs, .list ys | .list xs, .vec ys | .vec xs, .list ys | .vec xs, .vec ys =>
    xs.length == ys.length && (xs.zip ys).attach.all fun ⟨(x, y), _⟩ => jankSameKey x y
  | a, b => jankEqual a b
termination_by a b => sizeOf a + sizeOf b
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (rename_i hm
       have hz := List.of_mem_zip hm
       have h1 := List.sizeOf_lt_of_mem hz.1
       have h2 := List.sizeOf_lt_of_mem hz.2
       omega)

/-! ## The parser -/

inductive R where
  | ok (v : Option Val)
  | err (msg : String)
  | hang (w : String)
  | crash (w : String)
  deriving Repr, Inhabited

structure Shorthand where
  maxArity : Option Nat := none
  variadic : Bool := false
  deriving Repr, Inhabited

/-- `parse::processor`'s state (parse.hpp:145-182). -/
structure S where
  lex : P
  /-- `token_current.latest`. -/
  cur : Out
  expectedCloser : Option Kind := none
  shorthand : Option Shorthand := none
  /-- `allow_reader_conditional` (false for `read-string` by default). -/
  allowCond : Bool := false
  pending : List Val := []
  deriving Inhabited

def S.advance (s : S) : S :=
  let (o, l) := next 4 s.lex
  { s with lex := l, cur := o }

def S.start (file : Array UInt8) (loc : Locale) (allowCond : Bool := false) : S :=
  let l : P := { file, loc }
  let (o, l') := next 4 l
  { lex := l', cur := o, allowCond }

def outR : Out → R
  | .err m => .err m
  | .hang w => .hang w
  | .tok _ => .err "unexpected token"

abbrev PM := StateM S

def sym (n : String) : Val := .sym [] (n.toList.map Char.toNat)
def kwv (n : String) : Val := .kw [] (n.toList.map Char.toNat)

/-- `parse_symbol` (parse.cpp:1824-1901): ns/name at the first `/`; inside `#()` a `%`-symbol
is checked and renamed (`%` → `%1`, kept here without the trailing `#`). -/
def parseSymbol (sv : List UInt8) : PM R := do
  let s ← get
  let slash := sv.findIdx? (· == 47)
  match slash with
  | some k =>
    if sv.length == 1 then return .ok (some (.sym [] (codes sv)))
    return .ok (some (.sym (codes (sv.take k)) (codes (sv.drop (k + 1)))))
  | none =>
    match s.shorthand with
    | some sh =>
      if sv.head? == some 37 then
        let after := sv.drop 1
        let allDigits := after.all fun c => isDigitC c.toNat && c != 48
        if allDigits then
          let name := if after.isEmpty then bytesOf "%1" else sv
          let num := ((name.drop 1).foldl (fun a c => a * 10 + (c.toNat - 48)) 0) % 256  -- u8
          let mx := match sh.maxArity with
            | some m => if m < num then num else m
            | none => num
          set { s with shorthand := some { sh with maxArity := some mx } }
          return .ok (some (.sym [] (codes name)))
        else if after == [38] then
          set { s with shorthand := some { sh with variadic := true } }
          return .ok (some (.sym [] (codes sv)))
        else return .err "invalid shorthand function parameter"
      return .ok (some (.sym [] (codes sv)))
    | none => return .ok (some (.sym [] (codes sv)))

/-- `parse_keyword` (parse.cpp:1903-1938) and `context::intern_keyword` (context.cpp:561-585),
current namespace `user`, no aliases. -/
def parseKeyword (sv : List UInt8) : R :=
  let resolved := sv.head? != some 58
  match sv.findIdx? (· == 47) with
  | some k =>
    let ns := if resolved then sv.take k else (sv.take k).drop 1
    let name := sv.drop (k + 1)
    if !resolved then
      if ns.isEmpty then .ok (some (.kw (codes (bytesOf "user")) (codes name)))
      else .err s!"Unable to resolve namespace alias"
    else if ns.isEmpty then .ok (some (.kw [] (codes name)))
    else .ok (some (.kw (codes ns) (codes name)))
  | none =>
    let name := if resolved then sv else sv.drop 1
    if resolved then .ok (some (.kw [] (codes name)))
    else .ok (some (.kw (codes (bytesOf "user")) (codes name)))

/-- Metadata a `^` value stands for (parse.cpp:605-635). -/
def metaOf : Val → Option Val
  | .kw ns n => some (.map [(.kw ns n, .bool true)])
  | .sym ns n => some (.map [(kwv "tag", .list [sym "quote", .sym ns n])])
  | .withMeta _ (.sym ns n) => some (.map [(kwv "tag", .list [sym "quote", .sym ns n])])
  | .list xs => some (.map [(kwv "tag", .list [sym "quote", .list xs])])
  | .map kvs => some (.map kvs)
  | _ => none

def isMetadatable : Val → Bool
  | .sym .. | .list _ | .vec _ | .map _ | .set _ | .withMeta .. => true
  | _ => false

/-- `merge(old, new)`: the new entries win. -/
def mergeMeta (old new_ : List (Val × Val)) : List (Val × Val) :=
  old.filter (fun (k, _) => !new_.any fun (k', _) => k == k') ++ new_

def withMeta (m : Val) (v : Val) : Val :=
  match m, v with
  | .map new_, .withMeta (.map old) inner => .withMeta (.map (mergeMeta old new_)) inner
  | _, _ => .withMeta m v

mutual

/-- `nextForm (depth - 1)`, written so that the recursion is seen to terminate (round 3): at depth
0 it is what `nextForm 0` returns (the crash), without any state change. -/
def nextFormBelow (depth : Nat) : PM R :=
  match depth with
  | 0 => pure (.crash "parser recursion never ends (stack overflow)")
  | d + 1 => nextForm d
termination_by (depth, 0)

/-- `processor::next()` (parse.cpp:204-335). -/
def nextForm (depth : Nat) : PM R := do
  if depth == 0 then return .crash "parser recursion never ends (stack overflow)"
  let s ← get
  if let .tok t := s.cur then
    if t.kind == .eof then return .ok none
  for _ in [0:s.lex.file.size + 4] do
    let s ← get
    match s.pending with
    | v :: rest => set { s with pending := rest }; return .ok (some v)
    | [] => pure ()
    match s.cur with
    | .err m => return .err m
    | .hang w => return .hang w
    | .tok t =>
      match t.kind with
      | .comment => set s.advance; continue
      | .openParen => return ← parseColl depth .closeParen
      | .openSquare => return ← parseColl depth .closeSquare
      | .openCurly => return ← parseColl depth .closeCurly
      | .closeParen | .closeSquare | .closeCurly =>
        set s.advance
        if s.expectedCloser != some t.kind then return .err "unexpected closing character"
        modify fun s => { s with expectedCloser := none }
        return .ok none
      | .singleQuote => return ← wrap depth "quote" []
      | .character =>
        set s.advance
        match t.data with
        | .text sv => return (match parseCharacter sv with | .ok v => .ok (some v) | .error e => .err e)
        | _ => return .err "character data"
      | .metaHint => return ← parseMeta depth
      | .readerMacro =>
        let r ← parseReaderMacro depth
        match r with
        | .ok none => continue
        | other => return other
      | .readerMacroComment =>
        set s.advance
        let r ← nextFormBelow depth
        match r with
        | .ok none => return .err "A value after `#_` must be present."
        | .ok (some _) => continue
        | other => return other
      | .readerMacroConditional | .readerMacroConditionalSplice =>
        set s.advance
        if !s.allowCond then return .err "Reader conditionals are not allowed by default."
        return .err "reader conditional (unmodeled)"
      | .syntaxQuote => return .err "syntax quote (modeled in ReadSyntaxQuote)"
      | .unquote => return ← wrap depth "unquote" ("clojure.core".toList.map Char.toNat)
      | .unquoteSplice => return ← wrap depth "unquote-splicing" ("clojure.core".toList.map Char.toNat)
      | .deref => return ← wrap depth "deref" []
      | .nil => set s.advance; return .ok (some .nil)
      | .boolean =>
        set s.advance
        match t.data with | .bool b => return .ok (some (.bool b)) | _ => return .err "bool"
      | .symbol =>
        set s.advance
        match t.data with | .text sv => return ← parseSymbol sv | _ => return .err "symbol"
      | .keyword =>
        set s.advance
        match t.data with | .text sv => return parseKeyword sv | _ => return .err "keyword"
      | .integer =>
        set s.advance
        match t.data with | .int v => return .ok (some (.long v)) | _ => return .err "int"
      | .real =>
        set s.advance
        match t.data with | .real d => return .ok (some (.dbl d)) | _ => return .err "real"
      | .ratio =>
        set s.advance
        match t.data with
        | .ratio n d =>
          if d == 0 then return .err "A ratio may not have a denominator of zero."
          return (match ratioCreate n d with | .ok v => .ok (some v) | .error e => .err e)
        | _ => return .err "ratio"
      | .bigInteger =>
        set s.advance
        match t.data with
        | .big lit radix neg =>
          return (match bigIntegerCreate lit radix neg with | .ok v => .ok (some (.big v)) | .error e => .err e)
        | _ => return .err "big"
      | .bigDecimal =>
        set s.advance
        match t.data with
        | .bigdec lit => return (match bigDecimalCreate lit with | .ok v => .ok (some v) | .error e => .err e)
        | _ => return .err "bigdec"
      | .string =>
        set s.advance
        match t.data with | .text sv => return .ok (some (textVal sv)) | _ => return .err "string"
      | .escapedString =>
        set s.advance
        match t.data with
        | .text sv =>
          return (match unescape s.lex.loc sv with | .ok bs => .ok (some (textVal bs)) | .error e => .err e)
        | _ => return .err "string"
      | .eof => return .ok none
  return .hang "parser loop over zero-width tokens"
termination_by (depth, 3)

/-- `(name form)`: quote, unquote, unquote-splicing, deref (parse.cpp:513-539, 1761-1808). -/
def wrap (depth : Nat) (name : String) (ns : List Nat) : PM R := do
  modify S.advance
  let r ← nextFormBelow depth
  match r with
  | .ok none => return .err s!"A {name} form is missing its value."
  | .ok (some v) => return .ok (some (.list [.sym ns (name.toList.map Char.toNat), v]))
  | other => return other
termination_by (depth, 1)

/-- `parse_upto` (parse.cpp:337-368): forms until the expected closer. -/
def parseUpto (depth : Nat) (upto : Kind) : PM (Except R (List Val)) := do
  modify S.advance
  let prev := (← get).expectedCloser
  modify fun s => { s with expectedCloser := some upto }
  let mut items : Array Val := #[]
  for _ in [0:(← get).lex.file.size + 4] do
    let r ← nextFormBelow depth
    match r with
    | .ok none =>
      if (← get).expectedCloser.isSome then return .error (.err "unterminated form")
      modify fun s => { s with expectedCloser := prev }
      return .ok items.toList
    | .ok (some v) => items := items.push v
    | other => return .error other
  return .error (.hang "parse_upto loop")
termination_by (depth, 1)

/-- Lists, vectors, maps (parse.cpp:370-511). -/
def parseColl (depth : Nat) (closer : Kind) : PM R := do
  match ← parseUpto depth closer with
  | .error r => return r
  | .ok items =>
    match closer with
    | .closeParen => return .ok (some (.list items))
    | .closeSquare => return .ok (some (.vec items))
    | _ =>
      -- parse_map: odd entries; duplicates by hash + equal; insert_or_assign by `equal`.
      if items.length % 2 == 1 then return .err "odd number of entries in map"
      let mut seen : List Val := []
      let mut kvs : Array (Val × Val) := #[]
      for k in [0:items.length / 2] do
        let key := items[2 * k]!
        let val := items[2 * k + 1]!
        if seen.any (jankSameKey key ·) then return .err "duplicate keys in map"
        seen := key :: seen
        match kvs.findIdx? (fun (k', _) => jankEqual k' key) with
        | some i => kvs := kvs.set! i (kvs[i]!.1, val)
        | none => kvs := kvs.push (key, val)
      return .ok (some (.map kvs.toList))
termination_by (depth, 2)

/-- `parse_meta_hint` (parse.cpp:590-674). -/
def parseMeta (depth : Nat) : PM R := do
  modify S.advance
  match ← nextFormBelow depth with
  | .ok none => return .err "invalid meta hint value"
  | .ok (some mv) =>
    match metaOf mv with
    | none => return .err "invalid meta hint value"
    | some m =>
      match ← nextFormBelow depth with
      | .ok none => return .err "A value after the meta hint is missing."
      | .ok (some target) =>
        if isMetadatable target then return .ok (some (withMeta m target))
        return .err "The target value for a meta hint must support metadata."
      | other => return other
  | other => return other
termination_by (depth, 1)

/-- `parse_reader_macro` (parse.cpp:676-709) and the dispatch it does. -/
def parseReaderMacro (depth : Nat) : PM R := do
  modify S.advance
  let s ← get
  match s.cur with
  | .err m => return .err m
  | .hang w => return .hang w
  | .tok t =>
    match t.kind with
    | .openCurly =>
      -- parse_reader_macro_set (711-750)
      match ← parseUpto depth .closeCurly with
      | .error r => return r
      | .ok items =>
        let mut seen : List Val := []
        for it in items do
          if seen.any (jankSameKey it ·) then return .err "duplicate items in set"
          seen := seen ++ [it]
        return .ok (some (.set seen))
    | .openParen =>
      -- parse_reader_macro_fn (752-805)
      if s.shorthand.isSome then return .err "nested #()"
      set { s with shorthand := some {} }
      match ← nextFormBelow depth with
      | .ok (some (.list body)) =>
        let sh := ((← get).shorthand).getD {}
        let fixed := (List.range (sh.maxArity.getD 0)).map fun i => sym s!"%{i + 1}"
        let params := fixed ++ (if sh.variadic then [sym "&", sym "%&"] else [])
        modify fun s => { s with shorthand := none }
        return .ok (some (.list [sym "fn*", .vec params, .list body]))
      | .ok _ => return .err "A value after `#(` must be present."
      | other => return other
    | .singleQuote =>
      modify S.advance
      match ← nextFormBelow depth with
      | .ok (some (.sym ns n)) => return .ok (some (.list [sym "var", .sym ns n]))
      | .ok (some (.withMeta m (.sym ns n))) => return .ok (some (.list [sym "var", .withMeta m (.sym ns n)]))
      | .ok _ => return .err "A value after `#'` must be a symbol."
      | other => return other
    | .readerMacro =>
      modify S.advance
      match ← nextFormBelow depth with
      | .ok (some (.sym [] n)) =>
        if n == "Inf".toList.map Char.toNat then return .ok (some (.inf false))
        if n == "-Inf".toList.map Char.toNat then return .ok (some (.inf true))
        if n == "NaN".toList.map Char.toNat then return .ok (some .nan)
        return .err "This symbolic value is invalid."
      | .ok (some (.sym _ _)) => return .err "This symbolic value is invalid."
      | .ok _ => return .err "A value after `##` must be a symbol."
      | other => return other
    | .symbol =>
      -- parse_reader_macro_tagged (1008-1124): no reader for the tag here.
      let _ ← nextFormBelow depth
      match ← nextFormBelow depth with
      | .ok none => return .err "There must be a form after the tagged literal."
      | .ok (some _) => return .err "This reader tag is not supported."
      | other => return other
    | .string | .escapedString =>
      -- parse_regex (888-913): parse_string's raw text, for both token kinds.
      modify S.advance
      match t.data with
      | .text sv =>
        if ecmaRejects (codes sv) then return .err "invalid regex (std::regex_error)"
        return .ok (some (.regex (codes sv)))
      | _ => return .err "regex"
    | _ => return .err "unsupported reader macro"
termination_by (depth, 2)

end

/-- Reading a whole input as jank's loaders do (forms until eof; the first error stops it). -/
def readAll (file : Array UInt8) (loc : Locale := .utf8) (maxForms : Nat := 64) : Outcome := Id.run do
  let mut s := S.start file loc
  let mut out : Array Val := #[]
  for _ in [0:maxForms] do
    let (r, s') := (nextForm (file.size + 8)).run s
    s := s'
    match r with
    | .ok none => return .ok out.toList
    | .ok (some v) => out := out.push v
    | .err m => return .err m
    | .hang w => return .hang w
    | .crash w => return .crash w
  return .hang "too many forms"

/-- `context::read_string` (context.cpp:166-298) with `nth_form = 1` (core.jank `read-string`):
the range-for over the parser reads the first form, `++` parses the SECOND form, and only then
the loop breaks (`nth_form <= count`). The value, and what parsing the second form did. -/
def readString (file : Array UInt8) (loc : Locale := .utf8) : Outcome × R := Id.run do
  let s := S.start file loc
  let (r1, s1) := (nextForm (file.size + 8)).run s
  match r1 with
  | .ok none => return (.err "EOF was reached while reading.", r1)
  | .ok (some v) =>
    let (r2, _) := (nextForm (file.size + 8)).run s1
    match r2 with
    | .hang w => return (.hang s!"{w} (while parsing the second form)", r2)
    | .crash w => return (.crash s!"{w} (while parsing the second form)", r2)
    | _ => return (.ok [v], r2)
  | .err m => return (.err m, r1)
  | .hang w => return (.hang w, r1)
  | .crash w => return (.crash w, r1)

end Jank.Read
