import Jank.LexBytes

/-!
# jank's lexer, `read::lex::processor::next` (read/lex.cpp, commit f3d82d654), as written

The processor holds `pos` (a `movable_position`; only its byte `offset` matters here),
`require_space` and `found_slash_after_number` (lex.hpp:268-274). `next()` (lex.cpp:547-1526)
skips whitespace, decodes the first code point with `mbrtowc`, and switches on it. Inside a
token, `pos` points at the LAST byte of the last character consumed and `peek()` (lex.cpp:1528)
decodes the character at `pos + 1`; a token ends with a final `++pos`. Loops advance by the
peeked character's `len`, which `mbrtowc` reports as 0 for a NUL byte.

Every loop runs under fuel (`file.size + 2` iterations, more than any loop that advances can
take); running out of fuel is reported as `hang`: the C++ loop never ends.
-/

namespace Jank.Lex

open Jank.LexBytes

inductive Kind where
  | openParen | closeParen | openSquare | closeSquare | openCurly | closeCurly
  | singleQuote | metaHint | readerMacro | readerMacroComment | readerMacroConditional
  | readerMacroConditionalSplice | syntaxQuote | unquote | unquoteSplice | deref | comment
  | nil | boolean | character | symbol | keyword | integer | bigInteger | bigDecimal | real
  | ratio | string | escapedString | eof
  deriving Repr, BEq, Inhabited

/-- `token::data` (lex.hpp:225): the variant's alternatives that matter. -/
inductive Data where
  | none
  | int (v : Int)
  | real (d : Dec)
  | text (bytes : List UInt8)
  | bool (b : Bool)
  | ratio (num : Int) (den : Int)
  | big (literal : List UInt8) (radix : Int) (neg : Bool)
  | bigdec (literal : List UInt8)
  deriving Repr, BEq, Inhabited

structure Token where
  kind : Kind
  start : Nat
  stop : Nat
  data : Data := .none
  deriving Repr, BEq, Inhabited

/-- What `next()` gives: a token, an error (`jtl::result` err or a C++ exception thrown out of
the lexer), or a loop that never ends. -/
inductive Out where
  | tok (t : Token)
  | err (msg : String)
  | hang (where_ : String)
  deriving Repr, BEq, Inhabited

/-- `lex::processor` (lex.hpp:237-275). -/
structure P where
  file : Array UInt8
  loc : Locale := .utf8
  pos : Nat := 0
  requireSpace : Bool := false
  foundSlash : Bool := false
  deriving Repr, Inhabited

structure CP where
  c : Nat
  len : Nat

def P.at (p : P) (i : Nat) : Nat := (p.file.getD i 0).toNat

/-- `convert_to_codepoint(file.substr(i))` (lex.cpp:452): none for an error. -/
def P.decode (p : P) (i : Nat) : Option CP :=
  match mbrtowc p.loc p.file i with
  | .ok c l => some ⟨c, l⟩
  | _ => none

/-- `processor::peek(ahead)` (lex.cpp:1528-1537): an error past the end, else the decode. -/
def P.peek (p : P) (ahead : Nat := 1) : Option CP :=
  if p.pos + ahead ≥ p.file.size then none else p.decode (p.pos + ahead)

def unwrapSpace : Option CP → CP
  | some cp => cp
  | none => ⟨32, 1⟩

def P.slice (p : P) (a b : Nat) : List UInt8 := (p.file.extract a b).toList

/-- `is_utf8_char` (lex.cpp:470-491). -/
def isUtf8Char (c : Nat) : Bool :=
  if c ≤ 0x7FF then true else if c ≤ 0xFFFF then c < 0xD800 || c > 0xDFFF else c ≤ 0x10FFFF

/-- `is_special_char` (lex.cpp:493-497). -/
def isSpecialChar (c : Nat) : Bool :=
  [40, 41, 123, 125, 91, 93, 34, 94, 92, 96, 126, 44, 59].contains c

/-- `is_symbol_char` (lex.cpp:499-505): every valid code point that is neither `iswspace` nor
special (`is_utf8_char` makes the rest of the disjunction irrelevant). -/
def isSymbolChar (loc : Locale) (c : Nat) : Bool :=
  !iswspace loc c && !isSpecialChar c &&
  (isDigitC c || isLowerC c || isUpperC c || [95, 45, 47, 63, 33, 43, 42, 61, 46, 38, 60, 62, 35, 37].contains c
   || isUtf8Char c)

def isLetter (c : Nat) : Bool := isLowerC c || isUpperC c

/-- `is_valid_num_char` (lex.cpp:522-545). -/
def isValidNumChar (c : Nat) (radix : Int) : Bool :=
  if c == 45 || c == 43 || c == 46 then radix == 10
  else if radix == 10 && (c == 101 || c == 69) then true
  else if radix ≤ 10 then 48 ≤ c && (c : Int) < 48 + radix
  else if isUpperC c then (c : Int) < 65 + radix - 10
  else if isLowerC c then (c : Int) < 97 + radix - 10
  else 48 ≤ c && c ≤ 57

/-- `check_whitespace` (lex.cpp:442-450): the error resets `require_space`. -/
def P.checkWs (p : P) (foundSpace : Bool) : Option P :=
  if p.requireSpace && !foundSpace then some { p with requireSpace := false } else none

def mk (k : Kind) (s e : Nat) (d : Data := .none) : Out := .tok { kind := k, start := s, stop := e, data := d }

/-! ## One iteration of the loops that advance by `len` -/

/-- How one loop iteration ended: the loop goes on with this state, or stops. -/
inductive Step (α : Type) where
  | next (s : α)
  | stop (s : α)

/-- One iteration of the symbol and keyword loops (lex.cpp:1183-1197, 1282-1296) and of the
character loop (612-620): peek, stop at an error or a non-symbol character, else
`pos += len`. -/
def symbolStep (p : P) : Step P :=
  match p.peek with
  | none => .stop p
  | some oc => if !isSymbolChar p.loc oc.c then .stop p else .next { p with pos := p.pos + oc.len }

/-- One iteration of the string loop (lex.cpp:1325-1349); the state carries `escaped`.
`none`: the unterminated-string error. -/
def stringStep (st : P × Bool) : Option (Step (P × Bool)) :=
  let (p, escaped) := st
  match p.peek with
  | none => none
  | some oc =>
    if !escaped && oc.c == 34 then some (.stop ({ p with pos := p.pos + 1 }, escaped))
    else
      let escaped' := if escaped then false else oc.c == 92
      some (.next ({ p with pos := p.pos + oc.len }, escaped'))

/-- One iteration of the comment loops (lex.cpp:635-657, 1411-1425). -/
def commentStep (p : P) : Step P :=
  match p.peek with
  | none => .stop p
  | some oc => if oc.c == 10 then .stop p else .next { p with pos := p.pos + oc.len }

/-- The symbol case (lex.cpp:1163-1218), entered at `tokenStart = pos` (also the fall-through
from a lone `-`). -/
def lexSymbol (p0 : P) (foundSpace : Bool) : Out × P := Id.run do
  let mut p := p0
  let tokenStart := p.pos
  if let some p' := p.checkWs foundSpace then return (.err "expected whitespace", p')
  let mut done := false
  for _ in [0:p.file.size + 2] do
    match symbolStep p with
    | .stop _ => done := true; break
    | .next p' => p := p'
  if !done then return (.hang "symbol loop (lex.cpp:1183)", p)
  p := { p with requireSpace := true, pos := p.pos + 1 }
  let name := p.slice tokenStart p.pos
  if name.head? == some 47 && name.length > 1 then return (.err "A symbol may not start with `/`.", p)
  if name == bytesOf "nil" then return (mk .nil tokenStart p.pos, p)
  if name == bytesOf "true" then return (mk .boolean tokenStart p.pos (.bool true), p)
  if name == bytesOf "false" then return (mk .boolean tokenStart p.pos (.bool false), p)
  return (mk .symbol tokenStart p.pos (.text name), p)


/-- `processor::next()` (lex.cpp:547-1526), its body: `lexNum` is the number case at this depth
(round 3: the recursion through `lexNumber` is passed in, so that `next` is structural in
`depth`). -/
def nextCore (lexNum : P → Nat → Option (Out × P)) (p0 : P) : Out × P := Id.run do
  let mut p := p0
  -- Skip whitespace (lex.cpp:549-565).
  let mut foundSpace := false
  for _ in [0:p.file.size + 2] do
    if p.pos ≥ p.file.size then return (mk .eof p.pos p.pos, p)
    let c := p.file[p.pos]!
    if !cIsspace c && c != 44 then break
    foundSpace := true
    p := { p with pos := p.pos + 1 }
  let tokenStart := p.pos
  match p.decode tokenStart with
  | none => return (.err "invalid unicode (lex.cpp:571)", { p with pos := p.pos + 1 })
  | some oc =>
  let c := oc.c
  if c == 40 then return (mk .openParen tokenStart (p.pos + 1), { p with requireSpace := false, pos := p.pos + 1 })
  if c == 41 then return (mk .closeParen tokenStart (p.pos + 1), { p with requireSpace := false, pos := p.pos + 1 })
  if c == 91 then return (mk .openSquare tokenStart (p.pos + 1), { p with requireSpace := false, pos := p.pos + 1 })
  if c == 93 then return (mk .closeSquare tokenStart (p.pos + 1), { p with requireSpace := false, pos := p.pos + 1 })
  if c == 123 then return (mk .openCurly tokenStart (p.pos + 1), { p with requireSpace := false, pos := p.pos + 1 })
  if c == 125 then return (mk .closeCurly tokenStart (p.pos + 1), { p with requireSpace := false, pos := p.pos + 1 })
  if c == 39 then return (mk .singleQuote tokenStart (p.pos + 1), { p with requireSpace := false, pos := p.pos + 1 })
  -- Characters (lex.cpp:599-630).
  if c == 92 then
    p := { p with requireSpace := false }
    match p.peek with
    | none => return (.err "unexpected eof after \\", { p with pos := p.pos + 1 })
    | some ch =>
      p := { p with pos := p.pos + ch.len }
      let mut done := false
      for _ in [0:p.file.size + 2] do
        if p.pos > p.file.size then done := true; break
        match symbolStep p with
        | .stop _ => done := true; break
        | .next p' => p := p'
      if !done then return (.hang "character loop (lex.cpp:612)", p)
      p := { p with pos := p.pos + 1 }
      let data := p.slice tokenStart p.pos
      if data == [92, 32] then return (mk .character tokenStart p.pos (.text (bytesOf "\\space")), p)
      return (mk .character tokenStart p.pos (.text data), p)
  -- Comments (lex.cpp:631-669): to the next '\n' only.
  if c == 59 then
    let mut done := false
    for _ in [0:p.file.size + 2] do
      match commentStep p with
      | .stop _ => done := true; break
      | .next p' => p := p'
    if !done then return (.hang "comment loop (lex.cpp:635)", p)
    return (mk .comment tokenStart (p.pos + 1), { p with pos := p.pos + 1 })
  -- Numbers (lex.cpp:671-1161); a '-' not followed by a number falls through to symbols.
  if c == 45 || isDigitC c then
    if let some p' := p.checkWs foundSpace then return (.err "expected whitespace", p')
    match lexNum p tokenStart with
    | some r => return r
    | none => return lexSymbol p foundSpace
  if isLetter c || [95, 47, 63, 43, 61, 42, 33, 38, 60, 62, 37, 46].contains c then
    return lexSymbol p foundSpace
  -- Keywords (lex.cpp:1220-1315).
  if c == 58 then
    if let some p' := p.checkWs foundSpace then return (.err "expected whitespace", p')
    match p.peek with
    | none => return (.err "A keyword must contain a valid symbol after `:`.", { p with pos := p.pos + 1 })
    | some oc2 =>
      if iswspace p.loc oc2.c || isSpecialChar oc2.c then
        return (.err "A keyword must contain a valid symbol after `:`.", { p with pos := p.pos + 1 })
      if oc2.c == 58 then
        p := { p with pos := p.pos + 1 }
        match p.peek with
        | none => return (.err "auto-resolved keyword without symbol", { p with pos := p.pos + 1 })
        | some a =>
          if iswspace p.loc a.c || isSpecialChar a.c then
            return (.err "auto-resolved keyword without symbol", { p with pos := p.pos + 1 })
          if a.c == 47 then return (.err "The namespace symbol before `/` is missing.", p)
      let mut done := false
      for _ in [0:p.file.size + 2] do
        match symbolStep p with
        | .stop _ => done := true; break
        | .next p' => p := p'
      if !done then return (.hang "keyword loop (lex.cpp:1282)", p)
      p := { p with requireSpace := true, pos := p.pos + 1 }
      let name := p.slice (tokenStart + 1) p.pos
      if name.head? == some 47 && name.length > 1 then return (.err "A keyword may not start with `:/`.", p)
      if name.head? == some 58 && name[1]? == some 58 then return (.err "more than two `:`", p)
      return (mk .keyword tokenStart p.pos (.text name), p)
  -- Strings (lex.cpp:1317-1362).
  if c == 34 then
    if let some p' := p.checkWs foundSpace then return (.err "expected whitespace", p')
    let mut st : P × Bool := (p, false)
    let mut containsEscape := false
    let mut closed := false
    for _ in [0:p.file.size + 2] do
      match stringStep st with
      | none => return (.err "unterminated string", { st.1 with pos := st.1.pos + 1 })
      | some (.stop st') => st := st'; closed := true; break
      | some (.next st') => st := st'; if st'.2 then containsEscape := true
    p := st.1
    if !closed then return (.hang "string loop (lex.cpp:1325)", p)
    p := { p with requireSpace := true, pos := p.pos + 1 }
    let body := p.slice (tokenStart + 1) (p.pos - 1)
    return (mk (if containsEscape then .escapedString else .string) tokenStart p.pos (.text body), p)
  -- Meta hints (lex.cpp:1364-1375).
  if c == 94 then
    if let some p' := p.checkWs foundSpace then return (.err "expected whitespace", p')
    return (mk .metaHint tokenStart (p.pos + 1), { p with pos := p.pos + 1, requireSpace := false })
  -- Reader macros (lex.cpp:1377-1443).
  if c == 35 then
    if let some p' := p.checkWs foundSpace then return (.err "expected whitespace", p')
    p := { p with requireSpace := false }
    let cl := unwrapSpace p.peek
    p := { p with pos := p.pos + cl.len }
    if cl.c == 95 then
      return (mk .readerMacroComment tokenStart (p.pos + 1), { p with pos := p.pos + 1 })
    if cl.c == 63 then
      let ms := unwrapSpace p.peek
      p := { p with pos := p.pos + ms.len }
      if ms.c == 64 then
        return (mk .readerMacroConditionalSplice tokenStart (p.pos + 1), { p with pos := p.pos + 1 })
      return (mk .readerMacroConditional tokenStart p.pos, p)
    if cl.c == 33 then
      let mut done := false
      for _ in [0:p.file.size + 2] do
        match commentStep p with
        | .stop _ => done := true; break
        | .next p' => p := p'
      if !done then return (.hang "#! comment loop (lex.cpp:1411)", p)
      return (mk .comment tokenStart (p.pos + 1), { p with pos := p.pos + 1 })
    return (mk .readerMacro tokenStart p.pos, p)
  -- Syntax quote, unquote, deref (lex.cpp:1445-1491).
  if c == 96 then
    if let some p' := p.checkWs foundSpace then return (.err "expected whitespace", p')
    return (mk .syntaxQuote tokenStart (p.pos + 1), { p with pos := p.pos + 1, requireSpace := false })
  if c == 126 then
    if let some p' := p.checkWs foundSpace then return (.err "expected whitespace", p')
    p := { p with requireSpace := false }
    let r := unwrapSpace p.peek
    p := { p with pos := p.pos + r.len }
    if r.c == 64 then return (mk .unquoteSplice tokenStart (p.pos + 1), { p with pos := p.pos + 1 })
    return (mk .unquote tokenStart p.pos, p)
  if c == 64 then
    if let some p' := p.checkWs foundSpace then return (.err "expected whitespace", p')
    return (mk .deref tokenStart (p.pos + 1), { p with pos := p.pos + 1, requireSpace := false })
  -- Default (lex.cpp:1492-1524): any other code point starts a symbol.
  if c != 46 && isUtf8Char c then
    if let some p' := p.checkWs foundSpace then return (.err "expected whitespace", p')
    p := { p with pos := p.pos + oc.len }
    let mut done := false
    for _ in [0:p.file.size + 2] do
      if p.pos > p.file.size then done := true; break
      match p.decode p.pos with
      | none => done := true; break
      | some r =>
        if !isSymbolChar p.loc r.c || r.len == 0 then done := true; break
        p := { p with pos := p.pos + r.len }
    if !done then return (.hang "symbol loop (lex.cpp:1502)", p)
    p := { p with requireSpace := true }
    return (mk .symbol tokenStart p.pos (.text (p.slice tokenStart p.pos)), p)
  return (.err "unexpected character", { p with pos := p.pos + 1 })

/-- The number case (lex.cpp:673-1159). `none`: a lone `-`, which falls through to symbols
(lex.cpp:1160). -/
def lexNumberCore (den : Option (P → Out × P)) (p0 : P) (tokenStart : Nat) : Option (Out × P) := Id.run do
  let mut p := p0
  let fileAt := p.at
  let mut foundR := false
  let mut containsLeadingDigit := fileAt tokenStart != 45
  let mut containsDot := false
  let mut isScientific := false
  let mut foundExponentSign := false
  let mut expectingExponent := false
  let mut expectingMoreDigits := false
  let mut foundN := false
  let mut foundM := false
  let mut radix : Int := 10
  let mut rPos := p.pos
  let mut foundBeginningNegative := false
  let c1 := (unwrapSpace p.peek).c
  if fileAt tokenStart == 45 && c1 == 48 && !p.foundSlash then
    containsLeadingDigit := true
    let f := (unwrapSpace (p.peek 2)).c
    if f != 32 then
      if f != 120 && f != 88 then radix := 8; p := { p with pos := p.pos + 1 }
      else radix := 16; p := { p with pos := p.pos + 2 }
  else if fileAt tokenStart == 48 && !p.foundSlash then
    containsLeadingDigit := true
    let f := (unwrapSpace p.peek).c
    if f != 32 then
      if f != 120 && f != 88 then radix := 8
      if f == 120 || f == 88 then radix := 16; p := { p with pos := p.pos + 1 }
  if radix == 8 || radix == 16 then expectingMoreDigits := true
  let err := fun (msg : String) (q : P) => some (Out.err msg, q)
  for _ in [0:p.file.size + 2] do
    let some r := p.peek | break
    let c := r.c
    let isDigit := isDigitC c
    if !containsLeadingDigit && !isDigit then break
    if c == 46 then
      if containsDot || isScientific || !containsLeadingDigit || foundN then
        return err "A number literal cannot contain a `.` in this position." { p with pos := p.pos + 1 }
      if foundR then return err "An arbitrary-radix number must be an integer." { p with pos := p.pos + 1 }
      containsDot := true
      if radix != 10 && radix != 8 then
        p := { p with pos := p.pos + 1 }
        continue
      radix := 10
    else if c == 101 || c == 69 then
      if foundR then
        p := { p with pos := p.pos + 1 }
        continue
      if foundN then return err "unexpected N" { p with pos := p.pos + 1 }
      if radix < 15 then
        radix := 10
        if isScientific || !containsLeadingDigit then return err "unexpected e" { p with pos := p.pos + 1 }
        if p.foundSlash then return err "A ratio cannot use scientific notation." { p with pos := p.pos + 1, foundSlash := false }
        isScientific := true
        expectingExponent := true
    else if c == 43 || c == 45 then
      if radix == 10 && !foundR then
        if !expectingExponent then break
        if foundExponentSign || !isScientific then return err "unexpected sign" { p with pos := p.pos + 1 }
        foundExponentSign := true
    -- 7135b7708 lex.cpp:828-836: a denominator written `0x…` is rejected at once.
    else if p.foundSlash && (c == 120 || c == 88) && p.pos == tokenStart && fileAt tokenStart == 48 then
      return err "A ratio denominator must be a base-10 integer." { p with pos := p.pos + 1 }
    else if c == 114 || c == 82 then
      p := { p with pos := p.pos + 1 }
      -- 7135b7708 lex.cpp:840-844: no radix in a denominator.
      if p.foundSlash then return err "A ratio denominator must be a base-10 integer." p
      if foundR then continue
      if foundN then return err "unexpected N" p
      foundR := true
      expectingMoreDigits := true
      rPos := p.pos
      if p.foundSlash || containsDot || foundExponentSign || expectingExponent then
        return err "An arbitrary-radix number must be an integer." p
      continue
    else if c == 47 then
      p := { p with requireSpace := false, pos := p.pos + 1 }
      let slashPos := p.pos
      if foundExponentSign || isScientific || expectingExponent || containsDot || p.foundSlash
         || (radix != 10 && radix != 8) then
        return err "A ratio numerator must be an integer." p
      if foundN then return err "unexpected N" p
      p := { p with foundSlash := true, pos := p.pos + 1 }
      -- `depth == 0` (`den = none`): the recursion bound; else the denominator one level lower.
      let some lexDen := den | return some (.hang "lexer recursion", p)
      let (den, p') := lexDen p
      p := { p' with foundSlash := false }
      match den with
      | .tok t =>
        if t.kind != .integer && t.kind != .bigInteger then
          return err "A ratio denominator must be an integer." p
        let numText := if radix == 8 && fileAt tokenStart == 48
          then p.slice (tokenStart + 1) slashPos else p.slice tokenStart slashPos
        match boostParse numText with
        | .error e => return err e p
        | .ok num =>
          match t.data with
          | .int d => return some (mk .ratio tokenStart p.pos (.ratio num d), p)
          | .big lit _ _ =>
            match boostParse lit with
            | .error e => return err e p
            | .ok d => return some (mk .ratio tokenStart p.pos (.ratio num d), p)
          | _ => return err "ratio data" p
      | other => return some (other, p)
    else if !isDigit then
      if expectingExponent then return err "The decimal exponent is missing." { p with pos := p.pos + 1 }
      if !containsLeadingDigit then break
      if c == 78 then
        if containsDot then break
        p := { p with pos := p.pos + 1 }
        if foundN then return err "unexpected N" p
        if p.foundSlash then return err "unexpected N" { p with foundSlash := false }
        if foundM then return err "unexpected M" p
        foundN := true
        expectingMoreDigits := false
        break
      if c == 77 then
        p := { p with pos := p.pos + 1 }
        if foundM then return err "unexpected M" p
        if p.foundSlash then return err "unexpected M" { p with foundSlash := false }
        if foundN then return err "unexpected N" p
        foundM := true
        expectingMoreDigits := false
        break
      if containsDot then break
      if !isLetter c then
        if foundR && expectingMoreDigits then return err "This integer literal ended unexpectedly." { p with pos := p.pos + 1 }
        if p.pos == tokenStart && fileAt tokenStart == 48 then
          radix := 10
          expectingMoreDigits := false
        break
    else if expectingExponent then
      expectingExponent := false
    containsLeadingDigit := true
    expectingMoreDigits := false
    p := { p with pos := p.pos + 1 }
  if expectingExponent then return err "This decimal number literal ended unexpectedly." { p with pos := p.pos + 1 }
  if expectingMoreDigits then
    if foundR then return err "This integer literal ended unexpectedly." { p with pos := p.pos + 1 }
    return err s!"This base-{radix} number literal ended unexpectedly." { p with pos := p.pos + 1 }
  if fileAt tokenStart != 45 || p.pos - tokenStart ≥ 1 then
    p := { p with requireSpace := true, pos := p.pos + 1 }
    let mut numberStart := tokenStart
    if fileAt tokenStart == 45 || fileAt tokenStart == 43 then
      numberStart := tokenStart + 1
      foundBeginningNegative := fileAt tokenStart == 45
    if foundR then
      match stoi p.file tokenStart with
      | none => return err "std::stoi threw (out of range)" p
      | some v =>
        radix := toI8 v
        if radix < 0 then
          radix := toI8 (-radix)
          foundBeginningNegative := true
        if radix < 2 || radix > 36 then return err s!"The base `{radix}` is out of range." p
        numberStart := rPos + 1
    else if radix == 16 then numberStart := numberStart + 2
    let numberEnd := if foundN || foundM then p.pos - 1 else p.pos
    let invalid := (List.range (numberEnd - numberStart)).any fun k =>
      !isValidNumChar (fileAt (numberStart + k)) radix
    if invalid then return err s!"invalid characters for a base-{radix} number literal" p
    if foundM then
      let lit := if foundBeginningNegative then p.slice (numberStart - 1) numberEnd
        else p.slice numberStart numberEnd
      return some (mk .bigDecimal tokenStart p.pos (.bigdec lit), p)
    if containsDot || isScientific || foundExponentSign then
      return some (mk .real tokenStart p.pos (.real (strtod p.file tokenStart)), p)
    let (v, erange) := strtoll p.file numberStart radix.toNat
    -- `strtoll(...) * (found_beginning_negative ? -1 : 1)` in i64.
    let parsed := (BitVec.ofInt 64 (if foundBeginningNegative then -v else v)).toInt
    if erange || foundN then
      return some (mk .bigInteger tokenStart p.pos (.big (p.slice numberStart numberEnd) radix foundBeginningNegative), p)
    return some (mk .integer tokenStart p.pos (.int parsed), p)
  return none

/-- `processor::next()` (lex.cpp:547-1526). `depth` bounds the one recursive call (a ratio's
denominator, lex.cpp:888). Structural in `depth` (round 3). -/
def next : Nat → P → Out × P
  | 0, p0 => nextCore (lexNumberCore none) p0
  | d + 1, p0 => nextCore (lexNumberCore (some (next d))) p0

/-- The number case (lex.cpp:673-1159) at `depth`. `none`: a lone `-`, which falls through to
symbols (lex.cpp:1160). -/
def lexNumber (depth : Nat) (p0 : P) (tokenStart : Nat) : Option (Out × P) :=
  match depth with
  | 0 => lexNumberCore none p0 tokenStart
  | d + 1 => lexNumberCore (some (next d)) p0 tokenStart

theorem next_eq (depth : Nat) (p0 : P) : next depth p0 = nextCore (lexNumber depth) p0 := by
  cases depth <;> rfl

/-- Every token of a file until eof, the first error, or a hang (at most `max` tokens; a
lexer that keeps returning zero-width tokens is reported as `hang`). -/
def tokens (file : Array UInt8) (loc : Locale := .utf8) (max : Nat := 200) : List Out := Id.run do
  let mut p : P := { file, loc }
  let mut out : Array Out := #[]
  for _ in [0:max] do
    let (o, p') := next 4 p
    out := out.push o
    match o with
    | .tok t => if t.kind == .eof then return out.toList
    | _ => return out.toList
    p := p'
  return (out.push (.hang "token stream does not end")).toList

end Jank.Lex
