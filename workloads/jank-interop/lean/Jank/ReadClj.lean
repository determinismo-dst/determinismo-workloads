import Jank.ReadValue

/-!
# Clojure's reader, the spec: `clojure.lang.LispReader` (Clojure 1.12) on `read-string`

`read-string` reads from a `PushbackReader` over a Java `String` (UTF-16 code units), with
`*read-eval*` true and no reader conditionals allowed. Modeled: `read` (LispReader.java:236-306),
`readToken` (308-322), `readNumber` (324-344), `interpretToken`/`matchSymbol` (395-472, the
patterns at 66-74 as hand-written matchers), `matchNumber` (475-533), the macros (`"` 563-623,
`;` and `#!` 625-636 ending at `\n` or `\r`, `'` and `@` wrapping, `^` 944-990, `~` 1171-1191,
`(`/`[`/`{` with `createWithCheck`, `\` 1193-1239, `%` 928-942) and the dispatch macros (`#{`,
`#_`, `##`, `#'`, `#"` (raw text), `#(` 869-927, `#:` 650-745, `#?` not allowed by default,
tagged literals with no reader: an error). Syntax quote is modeled separately.
-/

namespace Jank.ReadClj

open Jank.LexBytes Jank.ReadValue

/-- Code points to UTF-16 code units (Java's `String`). -/
def toUtf16 (cs : List Nat) : List Nat :=
  cs.flatMap fun c =>
    if c < 0x10000 then [c]
    else let v := c - 0x10000; [0xD800 + v / 1024, 0xDC00 + v % 1024]

/-- UTF-16 code units back to code points (pairs combined, lone surrogates kept). -/
def fromUtf16 : List Nat → List Nat
  | h :: l :: rest =>
    if 0xD800 ≤ h && h ≤ 0xDBFF && 0xDC00 ≤ l && l ≤ 0xDFFF then
      (0x10000 + (h - 0xD800) * 1024 + (l - 0xDC00)) :: fromUtf16 rest
    else h :: fromUtf16 (l :: rest)
  | xs => xs

def isWhitespace (c : Nat) : Bool := javaIsWhitespace c || c == 44

def macroChars : List Nat := [34, 59, 39, 64, 94, 96, 126, 40, 41, 91, 93, 123, 125, 92, 37, 35]
def isMacro (c : Nat) : Bool := macroChars.contains c
def isTerminatingMacro (c : Nat) : Bool := c != 35 && c != 39 && c != 37 && isMacro c

structure R where
  s : Array Nat
  pos : Nat := 0
  deriving Inhabited

def R.read1 (r : R) : Option Nat × R :=
  if r.pos < r.s.size then (some r.s[r.pos]!, { r with pos := r.pos + 1 }) else (none, r)

def R.unread (r : R) (c : Option Nat) : R :=
  match c with | some _ => { r with pos := r.pos - 1 } | none => r

def str (s : String) : List Nat := s.toList.map Char.toNat
def symv (ns n : String) : Val := .sym (str ns) (str n)

/-- `readToken` (LispReader.java:308): until EOF, whitespace or a terminating macro. -/
def readToken (r0 : R) (init : Nat) : List Nat × R := Id.run do
  let mut r := r0
  let mut out := #[init]
  for _ in [0:r.s.size + 1] do
    let (c, r') := r.read1
    match c with
    | none => return (out.toList, r)
    | some ch =>
      if isWhitespace ch || isTerminatingMacro ch then return (out.toList, r)
      out := out.push ch
      r := r'
  return (out.toList, r)

/-- `readNumber`'s token (LispReader.java:324): until EOF, whitespace or ANY macro character. -/
def numberToken (r0 : R) (init : Nat) : List Nat × R := Id.run do
  let mut r := r0
  let mut out := #[init]
  for _ in [0:r.s.size + 1] do
    let (c, r') := r.read1
    match c with
    | none => return (out.toList, r)
    | some ch =>
      if isWhitespace ch || isMacro ch then return (out.toList, r)
      out := out.push ch
      r := r'
  return (out.toList, r)

def digitsIn (cs : List Nat) (radix : Nat) : Option Int :=
  if cs.isEmpty then none
  else cs.foldl (fun acc c => acc.bind fun a => match digitVal c with
    | some d => if d < radix then some (a * radix + d) else none
    | none => none) (some 0)

/-- `Numbers.reduceBigInt` / `bitLength() < 64`: a long when it fits. -/
def fitsLong (v : Int) : Bool := i64min ≤ v && v ≤ i64max

/-- `matchNumber` (LispReader.java:475-533). -/
def matchNumber (s : List Nat) : Option Val := Id.run do
  -- intPat
  let (sign, body) := match s with
    | 45 :: rest => (true, rest)
    | 43 :: rest => (false, rest)
    | _ => (false, s)
  let (core, bigN) := if body.getLast? == some 78 then (body.dropLast, true) else (body, false)
  let tryInt (cs : List Nat) (nflag : Bool) : Option (Option Val) :=
    -- one of the alternatives of intPat matching `cs` entirely (none: no alternative matches)
    if cs == [48] then some (some (if nflag then .big 0 else .long 0))
    else match cs with
    | c :: rest =>
      if 49 ≤ c && c ≤ 57 && rest.all isDigitC then
        let v : Int := (digitsIn cs 10).getD 0
        let v := if sign then -v else v
        some (some (if nflag || !fitsLong v then .big v else .long v))
      else if c == 48 && (rest.head? == some 120 || rest.head? == some 88) && rest.length ≥ 2
              && (rest.drop 1).all (fun d => (digitVal d).any (· < 16)) then
        let v : Int := (digitsIn (rest.drop 1) 16).getD 0
        let v := if sign then -v else v
        some (some (if nflag || !fitsLong v then .big v else .long v))
      else if c == 48 && !rest.isEmpty && rest.all (fun d => 48 ≤ d && d ≤ 55) then
        let v : Int := (digitsIn rest 8).getD 0
        let v := if sign then -v else v
        some (some (if nflag || !fitsLong v then .big v else .long v))
      else
        -- ([1-9][0-9]?)[rR]([0-9A-Za-z]+): radix of one or two digits, greedy digits.
        let radixLen := if rest.head?.any isDigitC then 2 else 1
        let rdx := cs.take radixLen
        let after := cs.drop radixLen
        if 49 ≤ c && c ≤ 57 && rdx.all isDigitC && (after.head? == some 114 || after.head? == some 82)
           && after.length ≥ 2 && (after.drop 1).all (fun d => isDigitC d || isLowerC d || isUpperC d) then
          let radix := (digitsIn rdx 10).getD 0
          -- new BigInteger(n, radix): radix outside 2..36 or a bad digit throws.
          if radix < 2 || radix > 36 then some none
          else match digitsIn (after.drop 1) radix.toNat with
            | none => some none
            | some v =>
              let v := if sign then -v else v
              some (some (if nflag || !fitsLong v then .big v else .long v))
        else if c == 48 && rest.all isDigitC && !rest.isEmpty then some none  -- 0[0-9]+: null
        else none
    | [] => none
  -- (N)? : the alternatives first try to match everything (an N as a radix digit), then
  -- without a trailing N.
  match tryInt body false with
  | some r => return r
  | none =>
    if bigN then
      match tryInt core true with
      | some r => return r
      | none => pure ()
  -- floatPat: ([-+]?[0-9]+(\.[0-9]*)?([eE][-+]?[0-9]+)?)(M)?
  let (fbody, mflag) := if body.getLast? == some 77 then (body.dropLast, true) else (body, false)
  let intPart := fbody.takeWhile isDigitC
  let rest1 := fbody.drop intPart.length
  let (fracOk, rest2) := match rest1 with
    | 46 :: r => (true, r.drop (r.takeWhile isDigitC).length)
    | r => (true, r)
  let expOk := match rest2 with
    | [] => true
    | e :: r =>
      (e == 101 || e == 69) &&
      (let r' := match r with | 45 :: x => x | 43 :: x => x | x => x
       !r'.isEmpty && r'.all isDigitC)
  if !intPart.isEmpty && fracOk && expOk then
    let d := parseDecimal ((if sign then [45] else []) ++ fbody)
    return some (if mflag then .bigdec d else .dbl d)
  -- ratioPat: ([-+]?[0-9]+)/([0-9]+)
  match body.findIdx? (· == 47) with
  | some k =>
    let num := body.take k
    let den := body.drop (k + 1)
    if !num.isEmpty && num.all isDigitC && !den.isEmpty && den.all isDigitC then
      let n : Int := (digitsIn num 10).getD 0
      let n := if sign then -n else n
      let d : Int := (digitsIn den 10).getD 0
      if d == 0 then return none  -- ArithmeticException: Divide by zero
      let g : Int := Int.ofNat (Int.gcd n d)
      let (n', d') := if g == 0 then (0, 1) else (n / g, d / g)
      -- reduceBigInt, then LongOps (both fit) or BigIntOps: an integral BigIntOps result is a BigInt.
      let bigOps := !(fitsLong n && fitsLong d)
      if d' == 1 then return some (if bigOps then .big n' else .long n')
      return some (.ratio n' d'.toNat)
    return none
  | none => return none

/-- `matchSymbol` (LispReader.java:410-472) and `interpretToken`. `user` is the current
namespace; no aliases. -/
def interpretToken (s : List Nat) : Except String Val := Id.run do
  if s == str "nil" then return .ok .nil
  if s == str "true" then return .ok (.bool true)
  if s == str "false" then return .ok (.bool false)
  let isKw := s.head? == some 58
  let t := if isKw then s.drop 1 else s
  let nondigit := fun (c : Nat) => !isDigitC c
  -- symbolPat on t: ns group `[\D&&[^/]].*/` (to the last usable '/'), name `/` or `[\D&&[^/]][^/]*`.
  let nameOk := fun (n : List Nat) => n == [47] || (match n with
    | c :: rest => nondigit c && c != 47 && !rest.contains 47
    | [] => false)
  let nsOk := fun (ns : List Nat) => match ns with
    | c :: _ => nondigit c && c != 47
    | [] => false
  let matchRest := fun (t : List Nat) =>
    let slashes := (List.range t.length).filter fun i => t[i]! == 47
    let candidates : List (Option (List Nat) × List Nat) :=
      (none, t) :: (slashes.reverse.map fun i => (some (t.take (i + 1)), t.drop (i + 1)))
    candidates.find? fun (ns, name) =>
      nameOk name && (match ns with | none => true | some n => nsOk n)
  -- `[:]?` takes the colon first, then backtracks to leave it to the groups (`:1` matches).
  let found := match matchRest t with
    | some m => some m
    | none => if isKw then matchRest s else none
  match found with
  | none =>
    -- arraySymbolPat ([\D&&[^/:]].*)/([1-9])
    match t.reverse with
    | d :: 47 :: revNs =>
      let ns := revNs.reverse
      if !isKw && 49 ≤ d && d ≤ 57 && (match ns with | c :: _ => nondigit c && c != 47 && c != 58 | [] => false)
      then return .ok (.sym ns [d])
      return .error s!"Invalid token: {showCodes s}"
    | _ => return .error s!"Invalid token: {showCodes s}"
  | some (ns, name) =>
    let nsEndsColonSlash := match ns with
      | some n => n.length ≥ 2 && n.drop (n.length - 2) == [58, 47]
      | none => false
    let hasDoubleColon := (List.range (s.length - 1)).any fun i => i ≥ 1 && s[i]! == 58 && s[i + 1]! == 58
    if nsEndsColonSlash || name.getLast? == some 58 || hasDoubleColon then
      return .error s!"Invalid token: {showCodes s}"
    -- Symbol.intern(String): split at the FIRST '/' unless the whole is "/".
    let split := fun (x : List Nat) =>
      match x.findIdx? (· == 47) with
      | some i => if x == [47] then ([], x) else (x.take i, x.drop (i + 1))
      | none => ([], x)
    if s.take 2 == [58, 58] then
      let (kns, kname) := split (s.drop 2)
      if kns.isEmpty then return .ok (.kw (str "user") kname)
      return .error "unknown alias"
    let (sns, sname) := split t
    return .ok (if isKw then .kw sns sname else .sym sns sname)

inductive O where
  | ok (v : Val)
  /-- A reader that returns the reader: nothing read (comment, discard). -/
  | none_
  | closer (c : Nat)
  | err (m : String)
  | eof
  deriving Inhabited

structure St where
  r : R
  /-- ARG_ENV: inside `#()`, the highest `%n` and whether `%&` was seen. -/
  argEnv : Option (Nat × Bool) := none

abbrev CM := StateM St

def readChar : CM (Option Nat) := do
  let s ← get
  let (c, r') := s.r.read1
  set { s with r := r' }
  return c

def unreadChar (c : Option Nat) : CM Unit := modify fun s => { s with r := s.r.unread c }

def tokenFrom (init : Nat) (number : Bool) : CM (List Nat) := do
  let s ← get
  let (t, r') := if number then numberToken s.r init else readToken s.r init
  set { s with r := r' }
  return t

/-- The string reader (LispReader.java:563-623). -/
def readString : CM (Except String Val) := do
  let mut out : Array Nat := #[]
  for _ in [0:(← get).r.s.size + 2] do
    let some ch ← readChar | return .error "EOF while reading string"
    if ch == 34 then return .ok (.str (fromUtf16 out.toList))
    if ch != 92 then out := out.push ch; continue
    let some e ← readChar | return .error "EOF while reading string"
    if e == 116 then out := out.push 9
    else if e == 114 then out := out.push 13
    else if e == 110 then out := out.push 10
    else if e == 92 || e == 34 then out := out.push e
    else if e == 98 then out := out.push 8
    else if e == 102 then out := out.push 12
    else if e == 117 then
      let some c0 ← readChar | return .error "Invalid unicode escape: \\u"
      if !(digitVal c0).any (· < 16) then return .error "Invalid unicode escape"
      let mut uc := (digitVal c0).getD 0
      let mut i := 1
      for _ in [0:3] do
        let c ← readChar
        match c with
        | none => break
        | some ch =>
          if isWhitespace ch || isMacro ch then unreadChar c; break
          match digitVal ch with
          | some d => if d < 16 then uc := uc * 16 + d; i := i + 1 else return .error "Invalid digit"
          | none => return .error "Invalid digit"
      if i != 4 then return .error "Invalid character length"
      out := out.push uc
    else if isDigitC e then
      let mut uc := (digitVal e).getD 0
      if uc ≥ 8 then return .error "Invalid digit"
      for _ in [0:2] do
        let c ← readChar
        match c with
        | none => break
        | some ch =>
          if isWhitespace ch || isMacro ch then unreadChar c; break
          match digitVal ch with
          | some d => if d < 8 then uc := uc * 8 + d else return .error "Invalid digit"
          | none => return .error "Invalid digit"
      if uc > 255 then return .error "Octal escape sequence must be in range [0, 377]."
      out := out.push uc
    else return .error s!"Unsupported escape character: \\{showCodes [e]}"
  return .error "EOF while reading string"

/-- The character reader (LispReader.java:1193-1239). -/
def readCharacter : CM (Except String Val) := do
  let some ch ← readChar | return .error "EOF while reading character"
  let token ← tokenFrom ch false
  if token.length == 1 then return .ok (.char token[0]!)
  let named : List (String × Nat) :=
    [("newline", 10), ("space", 32), ("tab", 9), ("backspace", 8), ("formfeed", 12), ("return", 13)]
  if let some (_, c) := named.find? (fun (n, _) => str n == token) then return .ok (.char c)
  if token.head? == some 117 then
    if token.length != 5 then return .error "Invalid unicode character"
    match digitsIn (token.drop 1) 16 with
    | none => return .error "Invalid digit"
    | some v =>
      if 0xD800 ≤ v && v ≤ 0xDFFF then return .error "Invalid character constant"
      return .ok (.char v.toNat)
  if token.head? == some 111 then
    let len := token.length - 1
    if len > 3 then return .error "Invalid octal escape sequence length"
    match digitsIn (token.drop 1) 8 with
    | none => return .error "Invalid digit"
    | some v => if v > 255 then return .error "Octal escape sequence must be in range [0, 377]."
                else return .ok (.char v.toNat)
  return .error s!"Unsupported character: \\{showCodes token}"

def comment : CM Unit := do
  for _ in [0:(← get).r.s.size + 2] do
    let c ← readChar
    match c with
    | none => return
    | some ch => if ch == 10 || ch == 13 then return

/-- Clojure's `^` metadata (LispReader.java:955-962). -/
def cljMetaOf : Val → Option Val
  | .sym ns n => some (.map [(.kw [] (str "tag"), .sym ns n)])
  | .str s => some (.map [(.kw [] (str "tag"), .str s)])
  | .kw ns n => some (.map [(.kw ns n, .bool true)])
  | .vec xs => some (.map [(.kw [] (str "param-tags"), .vec xs)])
  | .map kvs => some (.map kvs)
  | _ => none

def isIMeta : Val → Bool
  | .sym .. | .list _ | .vec _ | .map _ | .set _ | .withMeta .. => true
  | _ => false

def cljWithMeta (m : Val) (v : Val) : Val :=
  match m, v with
  | .map new_, .withMeta (.map old) inner =>
    .withMeta (.map (old.filter (fun (k, _) => !new_.any fun (k', _) => k == k') ++ new_)) inner
  | _, _ => .withMeta m v

mutual

/-- `LispReader.read` (236-306) with `returnOn` for delimited lists. -/
partial def read (depth : Nat) : CM O := do
  if depth == 0 then return .err "StackOverflowError"
  for _ in [0:(← get).r.s.size + 2] do
    let mut c ← readChar
    for _ in [0:(← get).r.s.size + 2] do
      match c with
      | some ch => if isWhitespace ch then c ← readChar else break
      | none => break
    let some ch := c | return .eof
    if isDigitC ch then
      let t ← tokenFrom ch true
      return match matchNumber t with
        | some v => .ok v
        | none => .err s!"Invalid number: {showCodes t}"
    if isMacro ch then
      let o ← readMacro depth ch
      match o with
      | .none_ => continue
      | other => return other
    if ch == 43 || ch == 45 then
      let c2 ← readChar
      unreadChar c2
      if c2.any isDigitC then
        let t ← tokenFrom ch true
        return match matchNumber t with
          | some v => .ok v
          | none => .err s!"Invalid number: {showCodes t}"
    let t ← tokenFrom ch false
    match interpretToken t with
    | .ok v => return .ok v
    | .error e => return .err e
  return .err "reader loop"

partial def readDelimited (depth : Nat) (delim : Nat) : CM (Except String (List Val)) := do
  let mut out : Array Val := #[]
  for _ in [0:(← get).r.s.size + 2] do
    match ← read (depth - 1) with
    | .ok v => out := out.push v
    | .closer c => if c == delim then return .ok out.toList else return .error "Unmatched delimiter"
    | .eof => return .error "EOF while reading"
    | .err e => return .error e
    | .none_ => pure ()
  return .error "reader loop"

partial def wrapping (depth : Nat) (ns name : String) : CM O := do
  match ← read (depth - 1) with
  | .ok v => return .ok (.list [symv ns name, v])
  | .eof => return .err "EOF while reading"
  | .closer _ => return .err "Unmatched delimiter"
  | other => return other

partial def readMacro (depth : Nat) (ch : Nat) : CM O := do
  if ch == 34 then return match ← readString with | .ok v => .ok v | .error e => .err e
  if ch == 59 then comment; return .none_
  if ch == 39 then return ← wrapping depth "" "quote"
  if ch == 64 then return ← wrapping depth "clojure.core" "deref"
  if ch == 94 then
    match ← read (depth - 1) with
    | .ok m =>
      match cljMetaOf m with
      | none => return .err "Metadata must be Symbol,Keyword,String,Vector or Map"
      | some mt =>
        match ← read (depth - 1) with
        | .ok o => if isIMeta o then return .ok (cljWithMeta mt o)
                   else return .err "Metadata can only be applied to IMetas"
        | .eof => return .err "EOF while reading"
        | .closer _ => return .err "Unmatched delimiter"
        | other => return other
    | .eof => return .err "EOF while reading"
    | .closer _ => return .err "Unmatched delimiter"
    | other => return other
  if ch == 96 then return .err "syntax quote (modeled in ReadSyntaxQuote)"
  if ch == 126 then
    let c2 ← readChar
    if c2 == some 64 then return ← wrapping depth "clojure.core" "unquote-splicing"
    unreadChar c2
    return ← wrapping depth "clojure.core" "unquote"
  if ch == 40 || ch == 91 || ch == 123 then
    let close := if ch == 40 then 41 else if ch == 91 then 93 else 125
    match ← readDelimited depth close with
    | .error e => return .err e
    | .ok items =>
      if ch == 40 then return .ok (.list items)
      if ch == 91 then return .ok (.vec items)
      if items.length % 2 == 1 then return .err "Map literal must contain an even number of forms"
      let kvs := (List.range (items.length / 2)).map fun k => (items[2 * k]!, items[2 * k + 1]!)
      let dup := (List.range kvs.length).any fun i => (List.range i).any fun j => kvs[i]!.1.equiv kvs[j]!.1
      if dup then return .err "Duplicate key"
      return .ok (.map kvs)
  if ch == 41 || ch == 93 || ch == 125 then return .closer ch
  if ch == 92 then return match ← readCharacter with | .ok v => .ok v | .error e => .err e
  if ch == 37 then
    let t ← tokenFrom 37 false
    let s ← get
    match s.argEnv with
    | none => return match interpretToken t with | .ok v => .ok v | .error e => .err e
    | some (hi, rest) =>
      let after := t.drop 1
      if after == [38] then set { s with argEnv := some (hi, true) }; return .ok (symv "" "%&")
      if after.isEmpty then
        set { s with argEnv := some (max hi 1, rest) }; return .ok (symv "" "%1")
      match after with
      | c :: _ =>
        if 49 ≤ c && c ≤ 57 && after.all isDigitC then
          let n := ((digitsIn after 10).getD 0).toNat
          set { s with argEnv := some (max hi n, rest) }
          return .ok (.sym [] (37 :: after))
        return .err "arg literal must be %, %& or %integer"
      | [] => return .err "arg literal"
  if ch == 35 then return ← dispatch depth
  return .err "macro"

/-- The dispatch macros (LispReader.java:116-128, 779-804). -/
partial def dispatch (depth : Nat) : CM O := do
  let some ch ← readChar | return .err "EOF while reading character"
  if ch == 123 then
    match ← readDelimited depth 125 with
    | .error e => return .err e
    | .ok items =>
      let dup := (List.range items.length).any fun i => (List.range i).any fun j => items[i]!.equiv items[j]!
      if dup then return .err "Duplicate key"
      return .ok (.set items)
  if ch == 95 then
    match ← read (depth - 1) with
    | .ok _ => return .none_
    | .eof => return .err "EOF while reading"
    | .closer _ => return .err "Unmatched delimiter"
    | other => return other
  if ch == 35 then
    match ← read (depth - 1) with
    | .ok (.sym [] n) =>
      if n == str "Inf" then return .ok (.inf false)
      if n == str "-Inf" then return .ok (.inf true)
      if n == str "NaN" then return .ok .nan
      return .err "Unknown symbolic value"
    | .ok _ => return .err "Invalid token"
    | .eof => return .err "EOF while reading"
    | .closer _ => return .err "Unmatched delimiter"
    | other => return other
  if ch == 39 then
    match ← read (depth - 1) with
    | .ok v => return .ok (.list [symv "" "var", v])
    | .eof => return .err "EOF while reading"
    | .closer _ => return .err "Unmatched delimiter"
    | other => return other
  if ch == 34 then
    -- RegexReader: the raw text, a backslash keeping the next character.
    let mut out : Array Nat := #[]
    for _ in [0:(← get).r.s.size + 2] do
      let some c ← readChar | return .err "EOF while reading regex"
      if c == 34 then return .ok (.regex (fromUtf16 out.toList))
      out := out.push c
      if c == 92 then
        let some c2 ← readChar | return .err "EOF while reading regex"
        out := out.push c2
    return .err "regex"
  if ch == 40 then
    let s ← get
    if s.argEnv.isSome then return .err "Nested #()s are not allowed"
    set { s with argEnv := some (0, false) }
    unreadChar (some 40)
    let o ← read (depth - 1)
    let env := ((← get).argEnv).getD (0, false)
    modify fun s => { s with argEnv := none }
    match o with
    | .ok form =>
      let fixed := (List.range env.1).map fun i => symv "" s!"%{i + 1}"
      let params := fixed ++ (if env.2 then [symv "" "&", symv "" "%&"] else [])
      return .ok (.list [symv "" "fn*", .vec params, form])
    | .eof => return .err "EOF while reading"
    | .closer _ => return .err "Unmatched delimiter"
    | other => return other
  if ch == 33 then comment; return .none_
  if ch == 94 then return ← readMacro depth 94
  if ch == 60 then return .err "Unreadable form"
  if ch == 61 then return .err "#= (read-eval, unmodeled)"
  if ch == 63 then return .err "Conditional read not allowed"
  if ch == 58 then
    -- NamespaceMapReader (LispReader.java:650-745): `#:ns{...}` / `#::{...}`, no aliases.
    let c1 ← readChar
    let auto := c1 == some 58
    if !auto then unreadChar c1
    let c2 ← readChar
    let mut ns : List Nat := []
    let mut nc := c2
    if c2.any isWhitespace then
      if !auto then return .err "Namespaced map must specify a namespace"
      for _ in [0:(← get).r.s.size + 2] do
        if nc.any isWhitespace then nc ← readChar else break
      if nc != some 123 then return .err "Namespaced map must specify a namespace"
      ns := str "user"
    else if c2 != some 123 then
      unreadChar c2
      match ← read (depth - 1) with
      | .ok (.sym [] n) =>
        if auto then return .err "Unknown auto-resolved namespace alias"
        ns := n
      | .ok _ => return .err "Namespaced map must specify a valid namespace"
      | _ => return .err "Namespaced map must specify a namespace"
      nc ← readChar
      for _ in [0:(← get).r.s.size + 2] do
        if nc.any isWhitespace then nc ← readChar else break
    else
      if !auto then return .err "Namespaced map must specify a namespace"
      ns := str "user"
    if nc != some 123 then return .err "Namespaced map must specify a map"
    match ← readDelimited depth 125 with
    | .error e => return .err e
    | .ok items =>
      if items.length % 2 == 1 then return .err "odd forms"
      let qual := fun (k : Val) => match k with
        | .kw [] n => Val.kw ns n
        | .kw kns n => if kns == [95] then .kw [] n else .kw kns n
        | .sym [] n => Val.sym ns n
        | .sym sns n => if sns == [95] then .sym [] n else .sym sns n
        | other => other
      let kvs := (List.range (items.length / 2)).map fun k => (qual items[2 * k]!, items[2 * k + 1]!)
      let dup := (List.range kvs.length).any fun i => (List.range i).any fun j => kvs[i]!.1.equiv kvs[j]!.1
      if dup then return .err "Duplicate key"
      return .ok (.map kvs)
  -- CtorReader: a tag symbol, then no reader for it.
  unreadChar (some ch)
  match ← read (depth - 1) with
  | .ok (.sym _ _) =>
    match ← read (depth - 1) with
    | .ok _ => return .err "No reader function for tag"
    | .eof => return .err "EOF while reading"
    | _ => return .err "tagged"
  | .ok _ => return .err "Reader tag must be a symbol"
  | .eof => return .err "EOF while reading"
  | _ => return .err "No dispatch macro"

end

/-- Every form of the input until EOF; the first error stops it. -/
def readAll (cs : List Nat) (maxForms : Nat := 64) : Outcome := Id.run do
  let units := toUtf16 cs
  let mut st : St := { r := { s := units.toArray } }
  let mut out : Array Val := #[]
  for _ in [0:maxForms] do
    let (o, st') := (read (units.length + 8)).run st
    st := st'
    match o with
    | .eof => return .ok out.toList
    | .ok v => out := out.push v
    | .none_ => pure ()
    | .closer _ => return .err "Unmatched delimiter"
    | .err e => return .err e
  return .err "too many forms"

/-- `read-string`: the first form. -/
def readString1 (cs : List Nat) : Outcome :=
  let units := toUtf16 cs
  let st : St := { r := { s := units.toArray } }
  match (read (units.length + 8)).run' st with
  | .eof => .err "EOF while reading"
  | .ok v => .ok [v]
  | .closer _ => .err "Unmatched delimiter"
  | .err e => .err e
  | .none_ => .err "nothing"

end Jank.ReadClj
