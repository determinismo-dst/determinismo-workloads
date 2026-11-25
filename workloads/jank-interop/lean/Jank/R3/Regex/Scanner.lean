import Jank.R3.Regex.Traits

/-!
# `std::__detail::_Scanner<char>` in ECMAScript mode

libstdc++ 15.3.0 `regex_scanner.h` / `regex_scanner.tcc`, replicated for the flags jank passes
(`std::regex_constants::ECMAScript` only: re_pattern.cpp 9). Every branch of `_M_scan_normal`
(85), `_M_scan_in_bracket` (196), `_M_scan_in_brace` (253), `_M_eat_escape_ecma` (289) and
`_M_eat_class` (503) is here; the POSIX/awk branches are unreachable with ECMAScript.

The pattern is `s.c_str()` of a `jtl::immutable_string` (`basic_regex(const char*, flag)` takes
`char_traits::length`), so it never holds a NUL, and `*_M_end` reads the terminating NUL: `peek`
past the end gives 0, as the C++ dereference does. Bytes are `Nat` (0–255). Loops are structural
recursion on the pattern's length so that the kernel can run concrete patterns.
-/

namespace Jank.R3.Regex

/-- `_ScannerBase::_TokenT`. -/
inductive Tok where
  | anychar | ordChar | octNum | hexNum | backref | subexprBegin | subexprNoGroupBegin
  | subexprLookaheadBegin | subexprEnd | bracketBegin | bracketNegBegin | bracketEnd
  | intervalBegin | intervalEnd | quotedClass | charClassName | collsymbol | equivClassName
  | opt | or_ | closure0 | closure1 | lineBegin | lineEnd | wordBound | comma | dupCount | eof
  | bracketDash | unknown
  deriving BEq, DecidableEq, Repr, Inhabited

/-- `regex_constants::error_type` (regex_error.h), and `_S_null`/`_S_grammar`. -/
inductive ErrCode where
  | collate | ctype | escape | backref | brack | paren | brace | badbrace | range | space
  | badrepeat | complexity | stack | null | grammar
  deriving BEq, DecidableEq, Repr, Inhabited

/-- A `std::regex_error`: its code and `what()`. -/
structure RxErr where
  code : ErrCode
  what : String
  deriving BEq, Repr, Inhabited

/-- regex.cc `desc` (the one-argument `__throw_regex_error`). -/
def ErrCode.desc : ErrCode → String
  | .collate => "Invalid collating element in regular expression"
  | .ctype => "Invalid character class in regular expression"
  | .escape => "Invalid escape in regular expression"
  | .backref => "Invalid back reference in regular expression"
  | .brack => "Mismatched '[' and ']' in regular expression"
  | .paren => "Mismatched '(' and ')' in regular expression"
  | .brace => "Mismatched '{' and '}' in regular expression"
  | .badbrace => "Invalid range in '{}' in regular expression"
  | .range => "Invalid character range in regular expression"
  | .space => "Insufficient memory to compile regular expression"
  | .badrepeat => "Invalid '?', '*', or '+' in regular expression"
  | .complexity => "Complexity of regex match exceeded implementation limits"
  | .stack => "Insufficient memory to determine regex match"
  | .null => "Unexpected null character in regular expression"
  | .grammar => "Conflicting regex grammar options"

def rxErr (c : ErrCode) (what : String := c.desc) : RxErr := { code := c, what }

/-- `_ScannerBase::_StateT`. -/
inductive SState where
  | normal | inBrace | inBracket
  deriving BEq, DecidableEq, Repr, Inhabited

structure Scanner where
  pat : Array Nat
  cur : Nat
  loc : Loc
  state : SState := .normal
  token : Tok := .unknown
  value : List Nat := []
  atBracketStart : Bool := false
  deriving Inhabited

namespace Scanner

def atEnd (s : Scanner) : Bool := s.cur ≥ s.pat.size

/-- `*_M_current` (0 at `_M_end`: the C string's terminator). -/
def peek (s : Scanner) : Nat := s.pat.getD s.cur 0

/-- `_M_ecma_spec_char` = "^$\\.*+?()[]{}|"; `strchr` also finds the terminating NUL. -/
def ecmaSpec (c : Nat) : Bool :=
  c == 0 || [0x5E, 0x24, 0x5C, 0x2E, 0x2A, 0x2B, 0x3F, 0x28, 0x29, 0x5B, 0x5D, 0x7B, 0x7D,
    0x7C].contains c

/-- `_M_ecma_escape_tbl` (`_M_find_escape`): '0'→NUL, b f n r t v; a NUL argument stops at the
sentinel and finds nothing. -/
def findEscape (c : Nat) : Option Nat :=
  if c == 0x30 then some 0 else if c == 0x62 then some 8 else if c == 0x66 then some 12
  else if c == 0x6E then some 10 else if c == 0x72 then some 13 else if c == 0x74 then some 9
  else if c == 0x76 then some 11 else none

def isDigit (s : Scanner) (c : Nat) : Bool := ctypeIs s.loc mDigit c
def isXdigit (s : Scanner) (c : Nat) : Bool := ctypeIs s.loc mXdigit c

/-- `while (_M_current != _M_end && digit(*_M_current)) _M_value += *_M_current++;` -/
def takeDigits (s : Scanner) : Nat → Scanner
  | 0 => s
  | f + 1 =>
    if !s.atEnd && s.isDigit s.peek then
      takeDigits { s with value := s.value ++ [s.peek], cur := s.cur + 1 } f
    else s

/-- The `\xNN`/`\uNNNN` loop: `n` hex digits, else `error_escape`. -/
def takeHex (s : Scanner) (wide : Bool) : Nat → Except RxErr Scanner
  | 0 => .ok s
  | k + 1 =>
    if s.atEnd || !s.isXdigit s.peek then
      .error (rxErr .escape (if !wide then "Invalid '\\xNN' control character in regular expression"
        else "Invalid '\\uNNNN' control character in regular expression"))
    else takeHex { s with value := s.value ++ [s.peek], cur := s.cur + 1 } wide k

/-- regex_scanner.tcc `_M_eat_escape_ecma` (289). -/
def eatEscapeEcma (s : Scanner) : Except RxErr Scanner :=
  if s.atEnd then .error (rxErr .escape) else
  let c := s.peek
  let s := { s with cur := s.cur + 1 }
  match findEscape c with
  | some e =>
    if c != 0x62 || s.state == .inBracket then .ok { s with token := .ordChar, value := [e] }
    -- `\b` outside a bracket: a word boundary
    else .ok { s with token := .wordBound, value := [0x70] }
  | none =>
    if c == 0x42 then .ok { s with token := .wordBound, value := [0x6E] }
    else if c == 0x64 || c == 0x44 || c == 0x73 || c == 0x53 || c == 0x77 || c == 0x57 then
      .ok { s with token := .quotedClass, value := [c] }
    else if c == 0x63 then
      if s.atEnd then .error (rxErr .escape "invalid '\\cX' control character in regular expression")
      -- `\cX` is the character X itself
      else .ok { s with token := .ordChar, value := [s.peek], cur := s.cur + 1 }
    else if c == 0x78 || c == 0x75 then
      match takeHex { s with value := [] } (c == 0x75) (if c == 0x78 then 2 else 4) with
      | .ok s => .ok { s with token := .hexNum }
      | .error e => .error e
    else if s.isDigit c then
      -- ECMAScript recognizes multi-digit back-references.
      let s := takeDigits { s with value := [c] } s.pat.size
      .ok { s with token := .backref }
    else .ok { s with token := .ordChar, value := [c] }

/-- The name loop of `_M_eat_class`: up to `ch`. -/
def takeUntil (s : Scanner) (ch : Nat) : Nat → Scanner
  | 0 => s
  | f + 1 =>
    if !s.atEnd && s.peek != ch then takeUntil { s with value := s.value ++ [s.peek], cur := s.cur + 1 } ch f
    else s

/-- regex_scanner.tcc `_M_eat_class` (503): the name up to `ch`, then `ch` `]`, else
`error_ctype` (for ':') or `error_collate`. -/
def eatClass (s : Scanner) (ch : Nat) : Except RxErr Scanner :=
  let s := takeUntil { s with value := [] } ch s.pat.size
  let err := rxErr (if ch == 0x3A then .ctype else .collate)
  if s.atEnd then .error err else
  let s := { s with cur := s.cur + 1 }
  if s.atEnd then .error err
  else if s.peek != 0x5D then .error err
  else .ok { s with cur := s.cur + 1 }

/-- regex_scanner.tcc `_M_scan_normal` (85). -/
def scanNormal (s : Scanner) : Except RxErr Scanner :=
  let c := s.peek
  let s := { s with cur := s.cur + 1 }
  if !ecmaSpec c then .ok { s with token := .ordChar, value := [c] }
  else if c == 0x5C then
    if s.atEnd then .error (rxErr .escape "Invalid escape at end of regular expression")
    -- ECMAScript is not basic: always `_M_eat_escape`
    else eatEscapeEcma s
  else if c == 0x28 then
    if s.peek == 0x3F then
      let s := { s with cur := s.cur + 1 }
      if s.atEnd then .error (rxErr .paren)
      else if s.peek == 0x3A then .ok { s with cur := s.cur + 1, token := .subexprNoGroupBegin }
      else if s.peek == 0x3D then
        .ok { s with cur := s.cur + 1, token := .subexprLookaheadBegin, value := [0x70] }
      else if s.peek == 0x21 then
        .ok { s with cur := s.cur + 1, token := .subexprLookaheadBegin, value := [0x6E] }
      else .error (rxErr .paren "Invalid '(?...)' zero-width assertion in regular expression")
    -- no nosubs flag
    else .ok { s with token := .subexprBegin }
  else if c == 0x29 then .ok { s with token := .subexprEnd }
  else if c == 0x5B then
    let s := { s with state := .inBracket, atBracketStart := true }
    if !s.atEnd && s.peek == 0x5E then .ok { s with token := .bracketNegBegin, cur := s.cur + 1 }
    else .ok { s with token := .bracketBegin }
  else if c == 0x7B then .ok { s with state := .inBrace, token := .intervalBegin }
  -- ECMAScript: a NUL is an ordinary character (unreachable from jank: C strings)
  else if c == 0 then .ok { s with token := .ordChar, value := [c] }
  else if c != 0x5D && c != 0x7D then
    -- `_M_token_tbl`: ^ $ . * + ? |
    let tok := if c == 0x5E then Tok.lineBegin else if c == 0x24 then .lineEnd
      else if c == 0x2E then .anychar else if c == 0x2A then .closure0
      else if c == 0x2B then .closure1 else if c == 0x3F then .opt else .or_
    .ok { s with token := tok }
  else .ok { s with token := .ordChar, value := [c] }

/-- regex_scanner.tcc `_M_scan_in_bracket` (196). -/
def scanInBracket (s : Scanner) : Except RxErr Scanner :=
  if s.atEnd then .error (rxErr .brack) else
  let c := s.peek
  let s := { s with cur := s.cur + 1 }
  let r : Except RxErr Scanner :=
    if c == 0x2D then .ok { s with token := .bracketDash }
    else if c == 0x5B then
      if s.atEnd then .error (rxErr .brack "Incomplete '[[' character class in regular expression")
      else if s.peek == 0x2E then eatClass { s with token := .collsymbol, cur := s.cur + 1 } 0x2E
      else if s.peek == 0x3A then eatClass { s with token := .charClassName, cur := s.cur + 1 } 0x3A
      else if s.peek == 0x3D then eatClass { s with token := .equivClassName, cur := s.cur + 1 } 0x3D
      else .ok { s with token := .ordChar, value := [c] }
    -- ECMAScript: ']' always ends the bracket, even first ("[]" is empty, "[^]" is anything)
    else if c == 0x5D then .ok { s with token := .bracketEnd, state := .normal }
    else if c == 0x5C then eatEscapeEcma s
    else .ok { s with token := .ordChar, value := [c] }
  match r with
  | .ok s => .ok { s with atBracketStart := false }
  | .error e => .error e

/-- regex_scanner.tcc `_M_scan_in_brace` (253). -/
def scanInBrace (s : Scanner) : Except RxErr Scanner :=
  if s.atEnd then .error (rxErr .brace) else
  let c := s.peek
  let s := { s with cur := s.cur + 1 }
  if s.isDigit c then .ok (takeDigits { s with token := .dupCount, value := [c] } s.pat.size)
  else if c == 0x2C then .ok { s with token := .comma }
  else if c == 0x7D then .ok { s with state := .normal, token := .intervalEnd }
  else .error (rxErr .badbrace)

/-- regex_scanner.tcc `_M_advance` (66). -/
def advance (s : Scanner) : Except RxErr Scanner :=
  if s.atEnd then .ok { s with token := .eof }
  else match s.state with
    | .normal => s.scanNormal
    | .inBracket => s.scanInBracket
    | .inBrace => s.scanInBrace

/-- `_Scanner(__begin, __end, __flags, __loc)` (regex_scanner.tcc 55): `_M_advance()`. -/
def init (pat : Array Nat) (loc : Loc) : Except RxErr Scanner :=
  advance { pat, cur := 0, loc }

end Scanner

end Jank.R3.Regex
