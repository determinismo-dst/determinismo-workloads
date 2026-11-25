/-!
# Round 5, native loading: jank's GNU ld script reader, replicated

`upstream-r5/compiler+runtime/src/cpp/jank/jit/parse_ld_script.cpp` (jank 94d32623), line by line:

- `is_identifier_character` 20–24, `is_separator` 26–30 (`std::isalnum`/`std::isspace` on
  `unsigned char`; jank sets `LC_NUMERIC` to "C" and `LC_CTYPE` from the environment, c_api.cpp
  1110–1117; for the ASCII bytes these scripts hold every glibc locale agrees with "C");
- `matches_directive` 32–50 (word boundaries on both sides);
- `strip_comments` 52–81 (`/* … */` removed everywhere, an unterminated comment runs to the end);
- `find_input_directive` 83–149 (the first `GROUP`/`INPUT` at parenthesis depth 0, its parenthesis
  matched without regard to quotes; unbalanced ⇒ none);
- `read_token` 154–191 (`"` and `'` quotes with backslash escapes; bare tokens end at a separator or
  a parenthesis);
- `parse_ld_script` 234–324 (the first path outside `AS_NEEDED`, else the first path at all).

`is_elf_file` 211–222 is `Libs.isElf` (it reads the file system).

Every loop is written with explicit fuel so the kernel can evaluate it (`decide`, `rfl`); the
theorems in `LdTheorems.lean` prove the fuel the callers pass never runs out, so the fuel is not
a behavior of the replica. A loop that runs out returns `none` at the outer `Option`.
-/

namespace Jank.R5.Native.LdScript

abbrev Src := List Char

/-- `source[i]` (in range at every call site; `'\x00'` outside). -/
def chr (s : Src) (i : Nat) : Char := (s[i]?).getD '\x00'

/-- `std::isalnum((unsigned char)c)` in the "C" locale. -/
def isAlnum (c : Char) : Bool :=
  ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')

/-- `std::isspace((unsigned char)c)` in the "C" locale. -/
def isSpace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\x0B' || c == '\x0C' || c == '\r'

/-- `is_identifier_character` (20–24). -/
def isIdent (c : Char) : Bool := isAlnum c || c == '_'

/-- `is_separator` (26–30): whitespace or a comma. -/
def isSep (c : Char) : Bool := isSpace c || c == ','

/-- `matches_directive` (32–50). -/
def matchesDirective (s : Src) (pos : Nat) (d : Src) : Bool :=
  if pos + d.length > s.length || (s.drop pos).take d.length != d then false
  else
    let before := pos > 0 && isIdent (chr s (pos - 1))
    let e := pos + d.length
    let after := e < s.length && isIdent (chr s e)
    !before && !after

/-- `strip_comments` (52–81), as a walk over the characters with `in_comment`. -/
def stripComments : Src → Bool → Src
  | [], _ => []
  | '*' :: '/' :: r, true => stripComments r false
  | _ :: r, true => stripComments r true
  | '/' :: '*' :: r, false => stripComments r true
  | c :: r, false => c :: stripComments r false

/-- `while(open_paren < size && is_separator(source[open_paren])) ++open_paren;` (105–108). -/
def skipSeps (s : Src) (i : Nat) : Nat → Nat
  | 0 => i
  | f + 1 => if i < s.length && isSep (chr s i) then skipSeps s (i + 1) f else i

/-- The matching close parenthesis (116–131): `some (some j)` found at `j`, `some none` at the end
of the source (unbalanced), `none` out of fuel. `depth ≥ 1` on entry. -/
def findClose (s : Src) (j depth : Nat) : Nat → Option (Option Nat)
  | 0 => none
  | f + 1 =>
    if j < s.length then
      let c := chr s j
      if c == '(' then findClose s (j + 1) (depth + 1) f
      else if c == ')' then
        if depth - 1 == 0 then some (some j) else findClose s (j + 1) (depth - 1) f
      else findClose s (j + 1) depth f
    else some none

/-- What one position of `find_input_directive`'s outer loop decides. -/
inductive DirStep where
  | found (b e : Nat)   -- `return directive_range{ open + 1, close }`
  | unbalanced          -- `return none` (133–134)
  | next                -- go on to the depth update
  deriving Repr, DecidableEq

/-- The inner `for(auto const directive : directives)` (97–135) at position `i`. -/
def tryDirectives (s : Src) (i : Nat) (ds : List Src) : Option DirStep :=
  match ds with
  | [] => some .next
  | d :: rest =>
    if !matchesDirective s i d then tryDirectives s i rest
    else
      let o := skipSeps s (i + d.length) (s.length + 1)
      if o ≥ s.length || chr s o != '(' then tryDirectives s i rest
      else match findClose s (o + 1) 1 (s.length + 1) with
        | none => none
        | some none => some .unbalanced
        | some (some c) => some (.found (o + 1) c)

def directives : List Src := ["GROUP".toList, "INPUT".toList]

/-- `find_input_directive` (83–149): `some (some (b, e))` the argument range `[b, e)`, `some none`
no directive (or unbalanced), `none` out of fuel. -/
def findInputDirective (s : Src) : Nat → Nat → Nat → Option (Option (Nat × Nat))
  | 0, _, _ => none
  | f + 1, i, depth =>
    if i < s.length then
      let step := if depth == 0 then tryDirectives s i directives else some .next
      match step with
      | none => none
      | some (.found b e) => some (some (b, e))
      | some .unbalanced => some none
      | some .next =>
        let c := chr s i
        let depth' := if c == '(' then depth + 1 else if c == ')' && depth > 0 then depth - 1 else depth
        findInputDirective s f (i + 1) depth'
    else some none

/-- The quoted branch of `read_token` (161–182), from just after the opening quote. -/
def readQuoted (s : Src) (q : Char) (p e : Nat) (acc : Src) : Nat → Option (Src × Nat)
  | 0 => none
  | f + 1 =>
    if p < e && chr s p != q then
      if chr s p == '\\' && p + 1 < e then readQuoted s q (p + 2) e (acc ++ [chr s (p + 1)]) f
      else readQuoted s q (p + 1) e (acc ++ [chr s p]) f
    else some (acc, if p < e then p + 1 else p)

/-- The bare branch of `read_token` (184–190). -/
def readBare (s : Src) (p e : Nat) : Nat → Option Nat
  | 0 => none
  | f + 1 =>
    if p < e && !isSep (chr s p) && chr s p != '(' && chr s p != ')' then readBare s (p + 1) e f
    else some p

/-- `read_token` (154–191): the token and the new position. -/
def readToken (s : Src) (p e : Nat) : Option (Src × Nat) :=
  if p ≥ e then some ([], p)
  else if chr s p == '"' || chr s p == '\'' then readQuoted s (chr s p) (p + 1) e [] (e + 1)
  else match readBare s p e (e + 1) with
    | none => none
    | some p' => some ((s.drop p).take (p' - p), p')

/-- The state of `parse_ld_script`'s scan (250–313). -/
structure Scan where
  pos : Nat
  asNeeded : Nat := 0
  firstPath : Option Src := none
  firstRequired : Option Src := none
  deriving Repr, DecidableEq

/-- `parse_ld_script`'s `while(position < range.end)` (259–313). -/
def scan (s : Src) (e : Nat) : Nat → Scan → Option Scan
  | 0, _ => none
  | f + 1, st =>
    if st.pos < e then
      let c := chr s st.pos
      if isSep c then scan s e f { st with pos := st.pos + 1 }
      else if c == '(' then scan s e f { st with pos := st.pos + 1 }
      else if c == ')' then
        scan s e f { st with pos := st.pos + 1, asNeeded := if st.asNeeded > 0 then st.asNeeded - 1 else 0 }
      else match readToken s st.pos e with
        | none => none
        | some (tok, p) =>
          let st := { st with pos := p }
          if tok.isEmpty then scan s e f st
          else if tok == "AS_NEEDED".toList then
            let p2 := skipSeps s p (s.length + 1)
            -- `while(position < range.end && is_separator(...))`: the skip stops at `range.end`.
            let p2 := if p2 > e then e else p2
            if p2 < e && chr s p2 == '(' then scan s e f { st with pos := p2 + 1, asNeeded := st.asNeeded + 1 }
            else scan s e f { st with pos := p2 }
          else
            let st := if st.firstPath.isNone then { st with firstPath := some tok } else st
            let st := if st.asNeeded == 0 && st.firstRequired.isNone then { st with firstRequired := some tok } else st
            scan s e f st
    else some st

/-- What `parse_ld_script` returns for a script's text (234–324): the path jank loads instead
of the script, or `none` (jank then hands the script itself to the dynamic loader). The outer
`Option` is fuel; `parseText` below never runs out (`parseText_fuel`). -/
def parseTextF (text : Src) : Option (Option Src) :=
  let s := stripComments text false
  match findInputDirective s (s.length + 1) 0 0 with
  | none => none
  | some none => some none
  | some (some (b, e)) =>
    match scan s e (e + 1) { pos := b } with
    | none => none
    | some st => some (match st.firstRequired with
      | some r => some r
      | none => st.firstPath)

/-- `parse_ld_script` on a script's text: the path it names, or none. -/
def parseText (text : Src) : Option Src := (parseTextF text).getD none

def parseStr (t : String) : Option String := (parseText t.toList).map String.ofList

end Jank.R5.Native.LdScript
