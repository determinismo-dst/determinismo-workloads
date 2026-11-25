import Jank.StrModel

/-!
# The spec: java.util.regex as Clojure 1.12 uses it

Clojure (`clojure-ref` core.clj 4892–4962, string.clj): `re-pattern` = `Pattern.compile`,
`re-find`/`re-seq` = successive `Matcher.find()`, `re-matches` = `Matcher.matches()`,
`re-groups` (a string without groups, else a vector with nil for a group that did not
participate), `clojure.string/replace`/`replace-first` = `Matcher.replaceAll`/`replaceFirst`
(the `appendReplacement` template rules) or, with a function, `(f (re-groups m))` quoted
(`Matcher/quoteReplacement`), `split` = `Pattern.split`.

Semantics are the `Pattern`/`Matcher` javadoc's (JDK ≥ 19, assumption RXJ1): the input is UTF-16
units; `.` excludes `\n \r \u0085    `; `^`/`$` without MULTILINE (`$` also before a
final line terminator); `\b` with ASCII word characters (JDK ≥ 19); `\d \w \s` ASCII; `\v`/`\h`
vertical/horizontal whitespace; backreferences fail for a group that has not matched; captures are
the most recent iteration's; `find()` after an empty match starts one unit later; a quantified
group whose iteration matches empty stops iterating (RXJ2, the engine's loop rule); possessive and
atomic constructs never backtrack. Parsing follows the documented grammar; corner cases the
javadoc does not settle (dangling `]`/`}` literal, a leading `]` in a class, `{n}` after nothing)
follow `Pattern`'s known behaviour and are marked "spec-corner" by the searches (RXJ3). Lookbehind,
flags, named groups and Unicode properties other than a few are parsed (to know Java accepts
them) but not matched: such patterns are reported as accepted by Java, never compared on matches.
-/

namespace Jank.R3.Regex.J

/-- A character predicate over code points. -/
inductive P where
  | single (c : Nat)
  | range (lo hi : Nat)
  | digit | word | space | hspace | vspace
  | lower | upper | alpha | alnum | punct | graph | print | blank | cntrl | xdigit | ascii
  | uLetter | uLower | uUpper | uNumber
  | union (a b : P)
  | inter (a b : P)
  | neg (a : P)
  | none_
  deriving BEq, Repr, Inhabited

def isTerminator (c : Nat) : Bool := c == 0x0A || c == 0x0D || c == 0x85 || c == 0x2028 || c == 0x2029

def asciiWord (c : Nat) : Bool :=
  (0x30 ≤ c && c ≤ 0x39) || (0x41 ≤ c && c ≤ 0x5A) || (0x61 ≤ c && c ≤ 0x7A) || c == 0x5F

/-- Unicode letters/digits for the code points the searches draw (ASCII, U+00C0–U+024F Latin,
Greek letters): enough for `\p{L}` on that alphabet. -/
def uLetterCp (c : Nat) : Bool :=
  (0x41 ≤ c && c ≤ 0x5A) || (0x61 ≤ c && c ≤ 0x7A) || c == 0xAA || c == 0xB5 || c == 0xBA ||
  (0xC0 ≤ c && c ≤ 0x24F && c != 0xD7 && c != 0xF7) || (0x391 ≤ c && c ≤ 0x3C9 && c != 0x3A2)
def uUpperCp (c : Nat) : Bool := (0x41 ≤ c && c ≤ 0x5A) || (0xC0 ≤ c && c ≤ 0xDE && c != 0xD7) || (0x391 ≤ c && c ≤ 0x3A9)
def uLowerCp (c : Nat) : Bool := uLetterCp c && !uUpperCp c

def P.eval : P → Nat → Bool
  | .single c, x => c == x
  | .range lo hi, x => lo ≤ x && x ≤ hi
  | .digit, x => 0x30 ≤ x && x ≤ 0x39
  | .word, x => asciiWord x
  | .space, x => x == 0x20 || (0x09 ≤ x && x ≤ 0x0D)
  | .hspace, x => x == 0x20 || x == 0x09 || x == 0xA0 || x == 0x1680 || x == 0x180E ||
      (0x2000 ≤ x && x ≤ 0x200A) || x == 0x202F || x == 0x205F || x == 0x3000
  | .vspace, x => (0x0A ≤ x && x ≤ 0x0D) || x == 0x85 || x == 0x2028 || x == 0x2029
  | .lower, x => 0x61 ≤ x && x ≤ 0x7A
  | .upper, x => 0x41 ≤ x && x ≤ 0x5A
  | .alpha, x => (0x61 ≤ x && x ≤ 0x7A) || (0x41 ≤ x && x ≤ 0x5A)
  | .alnum, x => (0x61 ≤ x && x ≤ 0x7A) || (0x41 ≤ x && x ≤ 0x5A) || (0x30 ≤ x && x ≤ 0x39)
  | .punct, x => (0x21 ≤ x && x ≤ 0x2F) || (0x3A ≤ x && x ≤ 0x40) || (0x5B ≤ x && x ≤ 0x60) || (0x7B ≤ x && x ≤ 0x7E)
  | .graph, x => 0x21 ≤ x && x ≤ 0x7E
  | .print, x => 0x20 ≤ x && x ≤ 0x7E
  | .blank, x => x == 0x20 || x == 0x09
  | .cntrl, x => x < 0x20 || x == 0x7F
  | .xdigit, x => (0x30 ≤ x && x ≤ 0x39) || (0x41 ≤ x && x ≤ 0x46) || (0x61 ≤ x && x ≤ 0x66)
  | .ascii, x => x < 0x80
  | .uLetter, x => uLetterCp x
  | .uLower, x => uLowerCp x
  | .uUpper, x => uUpperCp x
  | .uNumber, x => 0x30 ≤ x && x ≤ 0x39
  | .union a b, x => a.eval x || b.eval x
  | .inter a b, x => a.eval x && b.eval x
  | .neg a, x => !a.eval x
  | .none_, _ => false

inductive QK where
  | greedy | lazy | possessive
  deriving BEq, DecidableEq, Repr, Inhabited

/-- A compiled pattern. -/
inductive N where
  | empty
  | pred (p : P)
  | dot
  | seq (a b : N)
  | alt (a b : N)
  | group (idx : Nat) (r : N)
  | ncgroup (r : N)
  | quant (r : N) (min : Nat) (max : Nat) (k : QK)
  | bol | eol | wordB (neg : Bool) | beginA | endZ | endz | lastMatch
  | look (neg : Bool) (r : N)
  | atomic (r : N)
  | backref (n : Nat)
  /-- `\R`: `\r\n` or one of `[\n\x0B\f\r\x85  ]`. -/
  | linebreak
  /-- A construct parsed but not matched by this model (lookbehind, flags, named groups,
  `\X`, `\b{g}`, unknown properties). -/
  | unsupported (what : String)
  deriving BEq, Repr, Inhabited

def maxReps : Nat := 0x7FFFFFFF

def N.unsupportedIn : N → Option String
  | .unsupported w => some w
  | .seq a b | .alt a b => a.unsupportedIn <|> b.unsupportedIn
  | .group _ r | .ncgroup r | .quant r _ _ _ | .look _ r | .atomic r => r.unsupportedIn
  | _ => none

def N.hasGroup : N → Bool
  | .group _ _ => true
  | .seq a b | .alt a b => a.hasGroup || b.hasGroup
  | .ncgroup r | .quant r _ _ _ | .look _ r | .atomic r => r.hasGroup
  | _ => false

/-- Whether a group occurs inside a lookahead (captures there are compared only through the
whole match: RXJ4). -/
def N.groupInLook : N → Bool
  | .look _ r => r.hasGroup
  | .seq a b | .alt a b => a.groupInLook || b.groupInLook
  | .group _ r | .ncgroup r | .quant r _ _ _ | .atomic r => r.groupInLook
  | _ => false

/-! ## Parsing (`Pattern.compile`) -/

structure PS where
  pat : Array Nat
  cur : Nat := 0
  groups : Nat := 0
  /-- Named groups: name ↦ number. -/
  names : List (List Nat × Nat) := []
  deriving Inhabited

inductive PErr where
  | syntax (msg : String)
  deriving BEq, Repr, Inhabited

abbrev PM := StateT PS (Except PErr)

def perr {α : Type} (m : String) : PM α := fun _ => .error (.syntax m)

/-- `peek()`: 0 past the end (Pattern pads its buffer with zeros). -/
def peek : PM Nat := do let s ← get; return s.pat.getD s.cur 0
def peekAt (k : Nat) : PM Nat := do let s ← get; return s.pat.getD (s.cur + k) 0
def atEnd : PM Bool := do let s ← get; return s.cur ≥ s.pat.size
def adv : PM Unit := modify fun s => { s with cur := s.cur + 1 }
def read : PM Nat := do let c ← peek; adv; return c

def isHex (c : Nat) : Bool := (0x30 ≤ c && c ≤ 0x39) || (0x41 ≤ c && c ≤ 0x46) || (0x61 ≤ c && c ≤ 0x66)
def hexVal (c : Nat) : Nat := if c ≤ 0x39 then c - 0x30 else if c ≤ 0x46 then c - 0x41 + 10 else c - 0x61 + 10
def isOct (c : Nat) : Bool := 0x30 ≤ c && c ≤ 0x37
def isDig (c : Nat) : Bool := 0x30 ≤ c && c ≤ 0x39

/-- What an escape gives: a character, a predicate, or a node (anchors, backrefs). -/
inductive Esc where
  | ch (c : Nat)
  | pred (p : P)
  | node (n : N)
  deriving Inhabited

/-- `\p{…}`/`\pX` (family). -/
def family (name : List Nat) : Option P :=
  let s := String.ofList (name.map Char.ofNat)
  match s with
  | "Lower" => some .lower | "Upper" => some .upper | "ASCII" => some .ascii
  | "Alpha" => some .alpha | "Digit" => some .digit | "Alnum" => some .alnum
  | "Punct" => some .punct | "Graph" => some .graph | "Print" => some .print
  | "Blank" => some .blank | "Cntrl" => some .cntrl | "XDigit" => some .xdigit
  | "Space" => some .space | "L" => some .uLetter | "Lu" => some .uUpper | "Ll" => some .uLower
  | "N" | "Nd" => some .uNumber
  | _ => none

/-- `Pattern.escape(inclass, create, isrange)` after the backslash. -/
def escape (inclass : Bool) (isrange : Bool) (groupsSoFar : Nat) : PM Esc := do
  let c ← read
  let bad : PM Esc := perr "Illegal/unsupported escape sequence"
  if c == 0x30 then
    -- `o()`: one to three octal digits
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
    -- `ref()`: 1–9 always; further digits while the number names an existing group
    let rec more : Nat → Nat → PM Nat
      | 0, r => return r
      | f + 1, r => do
        let d ← peek
        if isDig d then
          let r' := r * 10 + (d - 0x30)
          if groupsSoFar < r' then return r
          else adv; more f r'
        else return r
    let r ← more 8 (c - 0x30)
    return .node (.backref r)
  match c with
  | 0x41 => if inclass then bad else return .node .beginA
  | 0x42 => if inclass then bad else return .node (.wordB true)
  | 0x44 => return .pred (.neg .digit)
  | 0x47 => if inclass then bad else return .node .lastMatch
  | 0x48 => return .pred (.neg .hspace)
  | 0x4E => return .node (.unsupported "\\N{…}")
  | 0x52 => if inclass then bad else return .node .linebreak
  | 0x53 => return .pred (.neg .space)
  | 0x56 => return .pred (.neg .vspace)
  | 0x57 => return .pred (.neg .word)
  | 0x58 => if inclass then bad else return .node (.unsupported "\\X")
  | 0x5A => if inclass then bad else return .node .endZ
  | 0x61 => return .ch 7
  | 0x62 =>
    if inclass then bad else
    -- `\b{g}` (a grapheme boundary); `\b{` + anything else is a `\b` before a `{`
    if (← peek) == 0x7B && (← peekAt 1) == 0x67 then
      if (← peekAt 2) == 0x7D then adv; adv; adv; return .node (.unsupported "\\b{g}")
      else return ← bad
    return .node (.wordB false)
  | 0x63 =>
    if ← atEnd then perr "Illegal control escape sequence" else
    let x ← read
    return .ch (x ^^^ 64)
  | 0x64 => return .pred .digit
  | 0x65 => return .ch 0x1B
  | 0x66 => return .ch 0x0C
  | 0x68 => return .pred .hspace
  | 0x6B =>
    if inclass then bad else
    if (← read) != 0x3C then perr "\\k is not followed by '<' for named capturing group" else
    return .node (.unsupported "\\k<name>")
  | 0x6E => return .ch 0x0A
  | 0x72 => return .ch 0x0D
  | 0x73 => return .pred .space
  | 0x74 => return .ch 0x09
  | 0x75 =>
    let mut v := 0
    for _ in [0:4] do
      let h ← read
      if !isHex h then return ← perr "Illegal Unicode escape sequence"
      v := v * 16 + hexVal h
    return .ch v
  | 0x76 => if isrange then return .ch 0x0B else return .pred .vspace
  | 0x77 => return .pred .word
  | 0x78 =>
    let n ← read
    if isHex n then
      let m ← read
      if isHex m then return .ch (hexVal n * 16 + hexVal m)
      perr "Illegal hexadecimal escape sequence"
    else if n == 0x7B && isHex (← peek) then
      let mut v := 0
      for _ in [0:8] do
        let h ← peek
        if isHex h then adv; v := v * 16 + hexVal h
      if (← read) != 0x7D then return ← perr "Unclosed hexadecimal escape sequence"
      if v > 0x10FFFF then return ← perr "Hexadecimal codepoint is too big"
      return .ch v
    else perr "Illegal hexadecimal escape sequence"
  | 0x7A => if inclass then bad else return .node .endz
  | _ =>
    -- C E F I J K L M O P Q T U Y g i j l m o p q y: unsupported letters
    if (0x41 ≤ c && c ≤ 0x5A) || (0x61 ≤ c && c ≤ 0x7A) then bad
    else if c == 0 && (← get).cur > (← get).pat.size then perr "Unexpected internal error"
    else return .ch c

/-- `\p`/`\P` after the letter: `{name}` or one letter. -/
def familyEsc (comp : Bool) : PM P := do
  let c ← peek
  let name ← if c == 0x7B then
      adv
      let rec nm : Nat → List Nat → PM (List Nat)
        | 0, acc => return acc.reverse
        | f + 1, acc => do
          let d ← peek
          if d == 0x7D then adv; return acc.reverse
          if ← atEnd then perr "Unclosed character family" else
          adv; nm f (d :: acc)
      nm 64 []
    else do adv; pure [c]
  match family name with
  | some p => return if comp then .neg p else p
  | none => perr s!"Unknown character property name (spec model)"

mutual
/-- `clazz(consume)`: a `[…]` class; the cursor is past `[`. -/
def clazz : Nat → PM P
  | 0 => perr "fuel"
  | f + 1 => do
    let mut isNeg := false
    if (← peek) == 0x5E then adv; isNeg := true
    let mut prev : Option P := none
    let mut first := true
    -- the loop of `clazz`, bounded by the pattern length
    for _ in [0:(← get).pat.size + 1] do
      let c ← peek
      if c == 0x5B then
        adv
        let p ← clazz f
        prev := some (match prev with | none => p | some q => .union q p)
        first := false
        continue
      if c == 0x26 && (← peekAt 1) == 0x26 then
        adv; adv
        -- `&&`: the right operand is the rest up to `]` or the next `&&`
        let mut right : Option P := none
        for _ in [0:(← get).pat.size + 1] do
          let d ← peek
          if d == 0x5D || (d == 0x26 && (← peekAt 1) == 0x26) then break
          if ← atEnd then break
          if d == 0x5B then
            adv
            let p ← clazz f
            right := some (match right with | none => p | some q => .union q p)
          else
            let p ← rangeTerm f
            right := some (match right with | none => p | some q => .union q p)
        match prev, right with
        | none, none => return ← perr "Bad class syntax"
        | none, some r => prev := some r
        | some p, some r => prev := some (.inter p r)
        | some p, none => prev := some p
        first := false
        continue
      if ← atEnd then return ← perr "Unclosed character class"
      if c == 0x5D && prev.isSome then
        adv
        let p := prev.getD .none_
        return if isNeg then .neg p else p
      -- a ']' first in the class is a literal (RXJ3)
      let p ← rangeTerm f
      prev := some (match prev with | none => p | some q => .union q p)
      first := false
    perr "Unclosed character class"
/-- `range(bits)`: one member of a class (a char, a range, an escape class). -/
def rangeTerm : Nat → PM P
  | 0 => perr "fuel"
  | _ + 1 => do
    let c ← peek
    let start ← if c == 0x5C then
        adv
        let e ← peek
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
      if endRange == 0x5B then return .single start
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
        else return .range start hi
    return .single start
end

/-- `closure(prev)`: a quantifier after an atom, with `?`/`+` suffixes. -/
def closure (prev : N) : PM N := do
  let c ← peek
  let suffix (min max : Nat) : PM N := do
    let d ← peek
    if d == 0x3F then adv; return .quant prev min max .lazy
    if d == 0x2B then adv; return .quant prev min max .possessive
    return .quant prev min max .greedy
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

def isMeta (c : Nat) : Bool := [0x2A, 0x2B, 0x3F, 0x7B, 0x24, 0x2E, 0x5E, 0x28, 0x5B, 0x7C, 0x29, 0x5C].contains c

mutual
/-- `expr()`: alternatives. -/
def expr : Nat → PM N
  | 0 => perr "fuel"
  | f + 1 => do
    let a ← sequence f
    if (← peek) == 0x7C && !(← atEnd) then
      adv
      let b ← expr f
      return .alt a b
    return a
/-- `sequence()`: atoms with their closures, up to `|` or `)`. -/
def sequence : Nat → PM N
  | 0 => perr "fuel"
  | f + 1 => do
    let mut acc : N := .empty
    for _ in [0:(← get).pat.size + 1] do
      if ← atEnd then break
      let c ← peek
      if c == 0x7C || c == 0x29 then break
      let node ← (do
        if c == 0x28 then
          adv
          group0 f
        else if c == 0x5B then
          adv
          let p ← clazz f
          closure (.pred p)
        else if c == 0x5C then
          let e ← peekAt 1
          if e == 0x70 || e == 0x50 then
            adv; adv
            let p ← familyEsc (e == 0x50)
            closure (.pred p)
          else
            adv
            match ← escape false false (← get).groups with
            | .ch ch => closure (.pred (.single ch))
            | .pred p => closure (.pred p)
            | .node n => closure n
        else if c == 0x5E then adv; closure .bol
        else if c == 0x24 then adv; closure .eol
        else if c == 0x2E then adv; closure .dot
        else if c == 0x3F || c == 0x2A || c == 0x2B then
          perr s!"Dangling meta character '{Char.ofNat c}'"
        else if c == 0x7B then
          -- `atom()` with '{' first: an empty slice, then `closure` (RXJ3)
          closure .empty
        else adv; closure (.pred (.single c)) : PM N)
      acc := match acc with
        | .empty => node
        | a => .seq a node
    return acc
/-- `group0()`: the cursor is past `(`. -/
def group0 : Nat → PM N
  | 0 => perr "fuel"
  | f + 1 => do
    let c ← peek
    let (body, closed) ← (do
      if c == 0x3F then
        adv
        let d ← read
        if d == 0x3A then
          let r ← expr f
          pure (N.ncgroup r, false)
        else if d == 0x3D || d == 0x21 then
          let r ← expr f
          pure (N.look (d == 0x21) r, false)
        else if d == 0x3E then
          let r ← expr f
          pure (N.atomic r, false)
        else if d == 0x3C then
          let e ← read
          if e == 0x3D || e == 0x21 then
            let _ ← expr f
            pure (N.unsupported "lookbehind", false)
          else
            -- a named group: a letter then letters/digits
            let isL (x : Nat) := (0x41 ≤ x && x ≤ 0x5A) || (0x61 ≤ x && x ≤ 0x7A)
            if !isL e then perr "capturing group name does not start with a Latin letter" else
            let rec nm : Nat → List Nat → PM (List Nat)
              | 0, acc => return acc.reverse
              | g + 1, acc => do
                let x ← read
                if x == 0x3E then return acc.reverse
                if isL x || isDig x then nm g (x :: acc)
                else perr "named capturing group is missing trailing '>'"
            let name ← nm 64 [e]
            if (← get).names.any (·.1 == name) then perr "Named capturing group is already defined" else
            let idx := (← get).groups + 1
            modify fun s => { s with groups := idx, names := (name, idx) :: s.names }
            let r ← expr f
            pure (N.group idx r, false)
        else if d == 0x24 || d == 0x40 then perr "Unknown group type"
        else
          -- inline flags `(?idmsuxU-idmsuxU)` / `(?…:X)`
          let isFlag (x : Nat) := [0x69, 0x64, 0x6D, 0x73, 0x75, 0x78, 0x55, 0x63, 0x2D].contains x
          if !isFlag d then perr "Unknown inline modifier" else
          let rec fl : Nat → PM Nat
            | 0 => return 0
            | g + 1 => do
              let x ← read
              if isFlag x then fl g else return x
          let x ← fl 16
          if x == 0x29 then return (N.unsupported "flags", true)
          if x != 0x3A then perr "Unknown inline modifier" else
          let _ ← expr f
          pure (N.unsupported "flags", false)
      else
        let idx := (← get).groups + 1
        modify fun s => { s with groups := idx }
        let r ← expr f
        pure (N.group idx r, false) : PM (N × Bool))
    if closed then return body
    if (← peek) != 0x29 || (← atEnd) then perr "Unclosed group" else
    adv
    closure body
end

/-- A compiled Java pattern: its node, group count, and whether it holds a supplementary
character (`StartS` vs `Start`). -/
structure JPat where
  node : N
  groups : Nat
  supp : Bool
  deriving Inhabited

/-- `RemoveQEQuoting`: `\Q…\E` becomes escaped literals (letters/digits as themselves). -/
def removeQE (p : List Nat) : List Nat :=
  let rec go : Nat → List Nat → Bool → List Nat
    | 0, _, _ => []
    | _ + 1, [], _ => []
    | f + 1, c :: rest, inQ =>
      if inQ then
        if c == 0x5C && rest.head? == some 0x45 then go f (rest.drop 1) false
        else
          let isAlnum := (0x30 ≤ c && c ≤ 0x39) || (0x41 ≤ c && c ≤ 0x5A) || (0x61 ≤ c && c ≤ 0x7A)
          (if isAlnum || c ≥ 0x80 then [c] else [0x5C, c]) ++ go f rest true
      else if c == 0x5C then
        match rest with
        | 0x51 :: r => go f r true
        | d :: r => [c, d] ++ go f r false
        | [] => [c]
      else c :: go f rest false
  go (p.length + 1) p false

/-- `Pattern.compile(s)` over the pattern's code points. -/
def compile (pattern : List Nat) : Except PErr JPat :=
  let pat := (removeQE pattern).toArray
  match (expr (4 * pat.size + 8)).run { pat } with
  | .error e => .error e
  | .ok (n, s) =>
    if s.cur < pat.size then
      -- `expr` stopped at a ')' with no group open
      .error (.syntax "Unmatched closing ')'")
    else .ok { node := n, groups := s.groups, supp := pattern.any (· ≥ 0x10000) }

/-! ## Matching (backtracking, continuation passing) -/

abbrev Caps := Array (Option (Nat × Nat))

structure MCtx where
  inp : Array Nat
  /-- `\G`: the end of the previous match (`oldLast`). -/
  oldLast : Nat

def MCtx.len (c : MCtx) : Nat := c.inp.size

def isHighS (u : Nat) : Bool := 0xD800 ≤ u && u ≤ 0xDBFF
def isLowS (u : Nat) : Bool := 0xDC00 ≤ u && u ≤ 0xDFFF

/-- `Character.codePointAt` and its length in units. -/
def MCtx.cpAt (c : MCtx) (i : Nat) : Nat × Nat :=
  let u := c.inp.getD i 0
  if isHighS u && i + 1 < c.len && isLowS (c.inp.getD (i + 1) 0) then
    (0x10000 + ((u - 0xD800) <<< 10) + (c.inp.getD (i + 1) 0 - 0xDC00), 2)
  else (u, 1)

/-- `Character.codePointBefore`. -/
def MCtx.cpBefore (c : MCtx) (i : Nat) : Nat :=
  let u := c.inp.getD (i - 1) 0
  if isLowS u && i ≥ 2 && isHighS (c.inp.getD (i - 2) 0) then
    0x10000 + ((c.inp.getD (i - 2) 0 - 0xD800) <<< 10) + (u - 0xDC00)
  else u

/-- `Dollar(multiline=false)`. -/
def MCtx.dollar (c : MCtx) (i : Nat) : Bool :=
  let n := c.len
  if i + 2 < n then false
  else if i + 2 == n then c.inp.getD i 0 == 0x0D && c.inp.getD (i + 1) 0 == 0x0A
  else if i < n then
    let ch := c.inp.getD i 0
    if ch == 0x0A then !(i > 0 && c.inp.getD (i - 1) 0 == 0x0D)
    else ch == 0x0D || ch == 0x85 || ch == 0x2028 || ch == 0x2029
  else true

/-- `Bound` (ASCII word characters, JDK ≥ 19). -/
def MCtx.bound (c : MCtx) (i : Nat) : Bool :=
  let left := i > 0 && asciiWord (c.cpBefore i)
  let right := i < c.len && asciiWord (c.cpAt i).1
  left != right

inductive JAbort where
  | steps | depth | unsupported (w : String)
  deriving BEq, Repr, Inhabited

abbrev JM := StateT Nat (Except JAbort)
abbrev Res := Option (Nat × Caps)

def tick (budget : Nat) : JM Unit := do
  let n ← get
  if n ≥ budget then throw .steps
  set (n + 1)

/-- The matcher: `node` at `i` with captures, then the continuation (`partial`: the Java side
is run, never reduced in the kernel). -/
partial def m (c : MCtx) (budget : Nat) : Nat → N → Nat → Caps → (Nat → Caps → JM Res) → JM Res
  | 0, _, _, _, _ => throw .depth
  | f + 1, node, i, caps, k => do
    tick budget
    match node with
    | .empty => k i caps
    | .pred p =>
      if i < c.len then
        let (cp, n) := c.cpAt i
        if p.eval cp then k (i + n) caps else return none
      else return none
    | .dot =>
      if i < c.len then
        let (cp, n) := c.cpAt i
        if !isTerminator cp then k (i + n) caps else return none
      else return none
    | .seq a b => m c budget f a i caps (fun j cs => m c budget f b j cs k)
    | .alt a b =>
      match ← m c budget f a i caps k with
      | some r => return some r
      | none => m c budget f b i caps k
    | .group idx r => m c budget f r i caps (fun j cs => k j (cs.set! idx (some (i, j))))
    | .ncgroup r => m c budget f r i caps k
    | .bol => if i == 0 then k i caps else return none
    | .eol => if c.dollar i then k i caps else return none
    | .wordB neg => if c.bound i != neg then k i caps else return none
    | .beginA => if i == 0 then k i caps else return none
    | .endz => if i == c.len then k i caps else return none
    | .endZ => if c.dollar i then k i caps else return none
    | .lastMatch => if i == c.oldLast then k i caps else return none
    | .linebreak =>
      if i + 1 < c.len && c.inp.getD i 0 == 0x0D && c.inp.getD (i + 1) 0 == 0x0A then
        match ← k (i + 2) caps with
        | some r => return some r
        | none => k (i + 1) caps
      else if i < c.len && P.vspace.eval (c.inp.getD i 0) then k (i + 1) caps
      else return none
    | .look neg r =>
      match ← m c budget f r i caps (fun j cs => return some (j, cs)) with
      | some (_, cs) => if neg then return none else k i cs
      | none => if neg then k i caps else return none
    | .atomic r =>
      match ← m c budget f r i caps (fun j cs => return some (j, cs)) with
      | some (j, cs) => k j cs
      | none => return none
    | .backref n =>
      match caps.getD n none with
      | none => return none
      | some (s, e) =>
        let len := e - s
        if i + len > c.len then return none
        else if (List.range len).all (fun t => c.inp.getD (s + t) 0 == c.inp.getD (i + t) 0) then k (i + len) caps
        else return none
    | .unsupported w => throw (.unsupported w)
    | .quant r mn mx kind =>
      match kind with
      | .possessive =>
        -- `Curly` POSSESSIVE (`match2`): first-way iterations, no backtracking
        let one (j : Nat) (cs : Caps) : JM Res := m c budget f r j cs (fun j' cs' => return some (j', cs'))
        let rec mins : Nat → Nat → Caps → JM Res
          | 0, j, cs => return some (j, cs)
          | t + 1, j, cs => do
            match ← one j cs with
            | some (j', cs') => mins t j' cs'
            | none => return none
        let rec more : Nat → Nat → Nat → Caps → JM (Nat × Caps)
          | 0, _, j, cs => return (j, cs)
          | t + 1, cnt, j, cs => do
            if cnt ≥ mx then return (j, cs)
            match ← one j cs with
            | some (j', cs') => if j' == j then return (j, cs) else more t (cnt + 1) j' cs'
            | none => return (j, cs)
        match ← mins mn i caps with
        | none => return none
        | some (j, cs) =>
          let (j, cs) ← more (c.len + 2) mn j cs
          k j cs
      | .greedy =>
        -- `Loop` (and `Curly`/`GroupCurly`, equal for their bodies): an iteration that ends
        -- where it began ends the loop
        let rec after : Nat → Nat → Nat → Caps → Nat → JM Res
          | 0, _, _, _, _ => throw .depth
          | g + 1, j, cnt, cs, s =>
            if j > s then
              if cnt < mn then m c budget f r j cs (fun j' cs' => after g j' (cnt + 1) cs' j)
              else if cnt < mx then do
                match ← m c budget f r j cs (fun j' cs' => after g j' (cnt + 1) cs' j) with
                | some x => return some x
                | none => k j cs
              else k j cs
            else k j cs
        let fuelA := c.len + mn + 2
        if 0 < mn then m c budget f r i caps (fun j cs => after fuelA j 1 cs i)
        else if 0 < mx then
          match ← m c budget f r i caps (fun j cs => after fuelA j 1 cs i) with
          | some x => return some x
          | none => k i caps
        else k i caps
      | .lazy =>
        -- `LazyLoop` / `Curly.match1`
        let rec lafter : Nat → Nat → Nat → Caps → Nat → JM Res
          | 0, _, _, _, _ => throw .depth
          | g + 1, j, cnt, cs, s =>
            if j > s then
              if cnt < mn then m c budget f r j cs (fun j' cs' => lafter g j' (cnt + 1) cs' j)
              else do
                match ← k j cs with
                | some x => return some x
                | none =>
                  if cnt < mx then m c budget f r j cs (fun j' cs' => lafter g j' (cnt + 1) cs' j)
                  else return none
            else k j cs
        let fuelA := c.len + mn + 2
        if 0 < mn then m c budget f r i caps (fun j cs => lafter fuelA j 1 cs i)
        else
          match ← k i caps with
          | some x => return some x
          | none =>
            if 0 < mx then m c budget f r i caps (fun j cs => lafter fuelA j 1 cs i)
            else return none

structure Lim where
  budget : Nat := 400000
  fuel : Nat := 2000
  deriving Inhabited

/-- One match attempt at `i` (`matches()` when `whole`). -/
def matchAt (p : JPat) (c : MCtx) (i : Nat) (whole : Bool) (lim : Lim) (steps : Nat) :
    Except JAbort (Res × Nat) :=
  let caps : Caps := Array.replicate (p.groups + 1) none
  let k : Nat → Caps → JM Res := fun j cs =>
    if whole && j != c.len then return none else return some (j, cs)
  (m c lim.budget lim.fuel p.node i caps k).run steps

/-- `Matcher.search(from)`: `Start` (unit steps) or `StartS` (code-point steps when the pattern
has a supplementary character). -/
def searchFrom (p : JPat) (c : MCtx) (from_ : Nat) (lim : Lim) (steps : Nat) :
    Except JAbort (Option (Nat × Nat × Caps) × Nat) :=
  let rec go : Nat → Nat → Nat → Except JAbort (Option (Nat × Nat × Caps) × Nat)
    | 0, _, st => .ok (none, st)
    | f + 1, i, st =>
      if i > c.len then .ok (none, st)
      else match matchAt p c i false lim st with
        | .error e => .error e
        | .ok (some (j, cs), st) => .ok (some (i, j, cs), st)
        | .ok (none, st) =>
          let step := if p.supp && isHighS (c.inp.getD i 0) && i + 1 < c.len && isLowS (c.inp.getD (i + 1) 0) then 2 else 1
          go f (i + step) st
  go (c.len + 2) from_ steps

/-- A `Matcher`'s find state: `first`, `last` (of the last match; `first = none` after reset or a
failure), `oldLast`. -/
structure MState where
  first : Option Nat := none
  last : Nat := 0
  oldLast : Option Nat := none
  deriving Inhabited

/-- `Matcher.find()`. -/
def find (p : JPat) (inp : Array Nat) (ms : MState) (lim : Lim) (steps : Nat) :
    Except JAbort (Option (Nat × Nat × Caps) × MState × Nat) :=
  let next := if ms.first == some ms.last then ms.last + 1 else ms.last
  if next > inp.size then .ok (none, { ms with first := none }, steps)
  else
    let c : MCtx := { inp, oldLast := ms.oldLast.getD next }
    match searchFrom p c next lim steps with
    | .error e => .error e
    | .ok (none, st) => .ok (none, { ms with first := none, oldLast := some ms.last }, st)
    | .ok (some (s, e, cs), st) => .ok (some (s, e, cs), { first := some s, last := e, oldLast := some e }, st)

/-- Every match of successive `find()`s. -/
def findAll (p : JPat) (inp : Array Nat) (lim : Lim) : Except JAbort (List (Nat × Nat × Caps)) :=
  let rec go : Nat → MState → Nat → List (Nat × Nat × Caps) → Except JAbort (List (Nat × Nat × Caps))
    | 0, _, _, acc => .ok acc.reverse
    | f + 1, ms, st, acc =>
      match find p inp ms lim st with
      | .error e => .error e
      | .ok (none, _, _) => .ok acc.reverse
      | .ok (some x, ms', st') => go f ms' st' (x :: acc)
  go (2 * inp.size + 4) {} 0 []

/-- `Matcher.matches()`. -/
def matchesAll (p : JPat) (inp : Array Nat) (lim : Lim) : Except JAbort (Option (Nat × Caps)) :=
  let c : MCtx := { inp, oldLast := 0 }
  match matchAt p c 0 true lim 0 with
  | .error e => .error e
  | .ok (r, _) => .ok r

end Jank.R3.Regex.J

namespace Jank.R3.Regex.J

/-! ## Clojure's functions on the model -/

/-- A Clojure value as bytes (UTF-16 results re-encoded as UTF-8; a lone surrogate gives its own
3-byte form, which no jank string holds). -/
inductive CV where
  | nil
  | str (b : List Nat)
  | vec (xs : List (Option (List Nat)))
  | list (xs : List CV)
  | err (what : String)
  /-- The model does not decide this one (an unsupported construct, or its limits). -/
  | unknown (why : String)
  deriving BEq, Repr, Inhabited

def toBytes (units : List Nat) : List Nat := (Jank.Str.unitsToBytes units).map (·.toNat)

def sub (inp : Array Nat) (s e : Nat) : List Nat := toBytes (inp.extract s e).toList

/-- `re-groups`. -/
def reGroups (p : JPat) (inp : Array Nat) (s e : Nat) (caps : Caps) : CV :=
  if p.groups == 0 then .str (sub inp s e)
  else .vec (some (sub inp s e) :: (List.range p.groups).map fun k =>
    (caps.getD (k + 1) none).map fun (a, b) => sub inp a b)

def abortCV : JAbort → CV
  | .steps => .unknown "steps"
  | .depth => .unknown "depth"
  | .unsupported w => .unknown w

/-- Clojure's string: UTF-16 units of the code points. -/
def units (cps : List Nat) : Array Nat := (Jank.Str.cstr cps).toArray

def reFind (p : JPat) (s : List Nat) (lim : Lim := {}) : CV :=
  let inp := units s
  match find p inp {} lim 0 with
  | .error e => abortCV e
  | .ok (none, _, _) => .nil
  | .ok (some (a, b, cs), _, _) => reGroups p inp a b cs

def reSeq (p : JPat) (s : List Nat) (lim : Lim := {}) : CV :=
  let inp := units s
  match findAll p inp lim with
  | .error e => abortCV e
  | .ok [] => .nil
  | .ok ms => .list (ms.map fun (a, b, cs) => reGroups p inp a b cs)

def reMatches (p : JPat) (s : List Nat) (lim : Lim := {}) : CV :=
  let inp := units s
  match matchesAll p inp lim with
  | .error e => abortCV e
  | .ok none => .nil
  | .ok (some (b, cs)) => reGroups p inp 0 b cs

/-- A replacement template, expanded for one match (`appendExpandedReplacement`). -/
def expand (p : JPat) (inp : Array Nat) (s e : Nat) (caps : Caps) (t : List Nat) :
    Except String (List Nat) :=
  let grp (n : Nat) : List Nat :=
    if n == 0 then sub inp s e else match caps.getD n none with
      | some (a, b) => sub inp a b
      | none => []
  let rec go : Nat → List Nat → Except String (List Nat)
    | 0, _ => .ok []
    | _ + 1, [] => .ok []
    | f + 1, c :: rest =>
      if c == 0x5C then
        match rest with
        | [] => .error "character to be escaped is missing"
        | d :: r => do return (toBytes [d]) ++ (← go f r)
      else if c == 0x24 then
        match rest with
        | [] => .error "Illegal group reference: group index is missing"
        | d :: r =>
          if d == 0x7B then .error "named group reference (spec model: no named groups drawn)"
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
      else do return toBytes [c] ++ (← go f rest)
  go (t.length + 1) t

/-- `Matcher.replaceAll(t)` / `replaceFirst(t)` (`first`); with `f`, `(f (re-groups m))` quoted. -/
def replace (p : JPat) (s : List Nat) (rep : Sum (List Nat) (CV → CV)) (first : Bool) (lim : Lim := {}) : CV :=
  let inp := units s
  match findAll p inp lim with
  | .error e => abortCV e
  | .ok ms =>
    let ms := if first then ms.take 1 else ms
    if ms.isEmpty then .str (toBytes inp.toList) else
    let rec go : List (Nat × Nat × Caps) → Nat → List Nat → CV
      | [], last, out => .str (out ++ sub inp last inp.size)
      | (a, b, cs) :: rest, last, out =>
        let piece : Except String (List Nat) := match rep with
          | .inl t => expand p inp a b cs (Jank.Str.cstr t)
          | .inr f => match f (reGroups p inp a b cs) with
            | .str r => .ok r
            | .err w => .error w
            | _ => .error "ClassCastException"
        match piece with
        | .error w => .err w
        | .ok r => go rest b (out ++ sub inp last a ++ r)
    go ms 0 []

/-- `Pattern.split(s, limit)`. -/
def split (p : JPat) (s : List Nat) (limit : Int) (lim : Lim := {}) : CV :=
  let inp := units s
  match findAll p inp lim with
  | .error e => abortCV e
  | .ok ms => Id.run do
    let matchLimited := limit > 0
    let mut index := 0
    let mut list : List (List Nat) := []
    for (st, en, _) in ms do
      if !matchLimited || (list.length : Int) < limit - 1 then
        if index == 0 && index == st && st == en then continue
        list := list ++ [sub inp index st]
        index := en
      else if (list.length : Int) == limit - 1 then
        list := list ++ [sub inp index inp.size]
        index := en
    if index == 0 then return .list [.str (sub inp 0 inp.size)]
    if !matchLimited || (list.length : Int) < limit then list := list ++ [sub inp index inp.size]
    if limit == 0 then list := (list.reverse.dropWhile (·.isEmpty)).reverse
    return .list (list.map .str)

end Jank.R3.Regex.J
