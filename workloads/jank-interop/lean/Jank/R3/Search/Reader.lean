import Jank.R3.Search.Common
import Jank.ReaderSearch

/-!
# Round 3: the reader's residual searches

Round 2 removed each found trigger from the alphabet and searched again; most of its residual
searches still ended in a finding. Here each disagreement is first put to `explain`, which names
the round-2 class (R1–R22) it belongs to, or none:

- by the input (narrow textual triggers, each the condition the code path in REPORT-2 needs:
  R1 a NUL byte; R3 `-0` before a character other than a space; R4 a `+` starting a number;
  R6 a radix `r`; R7 a number starting `0`/`-0` before a digit; R8 a backslash-digit escape in a
  string; R9 a `\r` after `;`; R11 `^`; R12 `%` and two digits; R14 `@` after a symbol character
  or `~` before a non-ASCII character; R15 Unicode-only whitespace; R16 `:/`; R17 `#:`/`#^`);
- by the outputs: R10 when jank's value equals Clojure's after renaming jank's `deref` heads to
  `clojure.core/deref`; R13 when Clojure rejects a duplicate key/element;
- by repair: R2 when jank's error is `expected whitespace` and inserting one or two spaces gives
  agreement (or another known class) without changing what Clojure reads.

Inputs jank accepts and Clojure rejects are counted, never violations (round 2's verdict).
-/

namespace Jank.R3.Search.Reader

open Determinismo Jank.LexBytes Jank.ReadValue Jank.ReaderSearch

def isDigitN (c : Nat) : Bool := 48 ≤ c && c ≤ 57

/-- Java `Character.isWhitespace` or `,` (LispReader.isWhitespace) without ASCII `isspace`. -/
def unicodeOnlyWs (c : Nat) : Bool :=
  (0x1C ≤ c && c ≤ 0x1F) || c == 0x1680 || (0x2000 ≤ c && c ≤ 0x2006) || (0x2008 ≤ c && c ≤ 0x200A)
  || c == 0x2028 || c == 0x2029 || c == 0x205F || c == 0x3000

/-- Characters that end a token in both readers (whitespace, delimiters, `"`, `;`). -/
def terminator (c : Nat) : Bool :=
  c == 32 || c == 10 || c == 13 || c == 9 || c == 44 || c == 40 || c == 41 || c == 91 || c == 93
  || c == 123 || c == 125 || c == 34 || c == 59 || c == 12 || c == 11

/-- A token starts at `i`: after a terminator, a prefix macro character (`' @ ^ \` ~`), or a `#`
that itself starts a token (a dispatch); a `#` inside a token is a constituent. -/
def tokenStartAt (cs : List Nat) : Nat → Bool
  | 0 => true
  | i + 1 => match cs[i]? with
    | some p => terminator p || p == 64 || p == 94 || p == 96 || p == 126
                || ((p == 35 || p == 39) && tokenStartAt cs i)
                -- `#_` (discard) is a prefix too
                || (p == 95 && i > 0 && cs[i - 1]? == some 35 && tokenStartAt cs (i - 1))
    | none => true



def substr (cs : List Nat) (pat : List Nat) : Bool :=
  (List.range (cs.length + 1)).any fun i => (cs.drop i).take pat.length == pat

/-- A scan of the input as both readers see its lexical regions: for each position, whether it
lies in a string literal, in a `;` comment, and whether it is a backslash starting an escape in
a string. Outside strings and comments a backslash starts a character literal, whose next
character is taken as it is. -/
structure Scan where
  inStr : Array Bool
  inCom : Array Bool
  escStart : Array Bool

def scan (cs : List Nat) : Scan := Id.run do
  let n := cs.length
  let mut inStr := Array.replicate n false
  let mut inCom := Array.replicate n false
  let mut escStart := Array.replicate n false
  let mut k := 0
  let mut mode := 0  -- 0 normal, 1 string, 2 comment
  for _ in [0:n + 1] do
    if k ≥ n then break
    let c := cs.getD k 0
    if mode == 1 then
      inStr := inStr.set! k true
      if c == 92 then
        escStart := escStart.set! k true
        if k + 1 < n then inStr := inStr.set! (k + 1) true
        k := k + 2
      else
        if c == 34 then mode := 0
        k := k + 1
    else if mode == 2 then
      inCom := inCom.set! k true
      if c == 10 then mode := 0
      k := k + 1
    else
      if c == 34 then mode := 1; k := k + 1
      else if c == 59 then mode := 2; inCom := inCom.set! k true; k := k + 1
      else if c == 92 then k := k + 2
      else k := k + 1
  return { inStr, inCom, escStart }

/-- Inside a string literal at position `i`. -/
def inString (cs : List Nat) (i : Nat) : Bool := (scan cs).inStr.getD i false

/-- Inside a `;` comment at position `i`. -/
def inComment (cs : List Nat) (i : Nat) : Bool := (scan cs).inCom.getD i false

/-- The input-only explanations. -/
def byInput (cs : List Nat) : Option String := Id.run do
  let n := cs.length
  if cs.contains 0 then return some "R1"
  if cs.any unicodeOnlyWs then return some "R15"
  -- R9: a `\r` after a `;` (outside strings).
  let sc := scan cs
  for i in [0:n] do
    if cs.getD i 0 == 13 && sc.inCom.getD i false then return some "R9"
  for i in [0:n] do
    let c := cs.getD i 0
    let nx := cs.getD (i + 1) 32
    if sc.inCom.getD i false then continue
    let st := sc.inStr.getD i false
    if st then
      if c == 92 && isDigitN nx && sc.escStart.getD i false then return some "R8"
      continue
    if c == 43 && isDigitN nx && (tokenStartAt cs i || (i > 0 && (cs.getD (i - 1) 0 == 39 || cs.getD (i - 1) 0 == 35))) then return some "R4"
    if c == 45 && nx == 48 && tokenStartAt cs i && cs.getD (i + 2) 32 != 32 then return some "R3"
    if c == 48 && isDigitN nx && tokenStartAt cs i then return some "R7"
    if (c == 45 || c == 43) && nx == 48 && isDigitN (cs.getD (i + 2) 32) && tokenStartAt cs i then return some "R7"
    if (c == 114 || c == 82) && i > 0 && isDigitN (cs.getD (i - 1) 0) then return some "R6"
    if c == 94 then return some "R11"
    if c == 37 && isDigitN nx && isDigitN (cs.getD (i + 2) 32) then return some "R12"
    if c == 64 && i > 0 && !tokenStartAt cs i then return some "R14"
    if c == 126 && nx ≥ 128 then return some "R14"
    if c == 58 && nx == 47 then return some "R16"
    if c == 35 && (nx == 58 || nx == 94) then return some "R17"
  return none

/-- jank's `(deref x)` renamed to Clojure's `(clojure.core/deref x)`. -/
partial def derefFix : Val → Val
  | .list (.sym [] n :: xs) =>
    -- (outCanon flattens names: Clojure's head reads `.sym [] "clojure.core/deref"`.)
    if n == codesOf "deref" then .list (.sym [] (codesOf "clojure.core/deref") :: xs.map derefFix)
    else .list (.sym [] n :: xs.map derefFix)
  | .list xs => .list (xs.map derefFix)
  | .vec xs => .vec (xs.map derefFix)
  | .set xs => .set (xs.map derefFix)
  | .map kvs => .map (kvs.map fun (k, v) => (derefFix k, derefFix v))
  | .withMeta m v => .withMeta (derefFix m) (derefFix v)
  | v => v

def bad (v : Verdict) : Bool := v == .notTotal || v == .wrongValue || v == .rejectsValid

mutual
/-- The round-2 class of a disagreement, or none (`repair`: R2's repair allowed, at the top only). -/
partial def explain (cs : List Nat) (j c : Outcome) (repair : Bool := true) : Option String :=
  if cs.contains 0 then some "R1" else if cs.any unicodeOnlyWs then some "R15" else
  let j' := match j with | .ok vs => .ok (vs.map (Jank.ReadRoundtrip.canon ∘ derefFix)) | o => o
  if !bad (verdict j' c) then some "R10"
  -- Round 3's own classes, set aside once found.
  else if j == .err "A value after `#'` must be a symbol." then some "W1"
  -- Regex literals are the Regex agent's area (R18): ReadClj keeps a pattern's source without
  -- compiling it, so validity is not judged here.
  else if j == .err "invalid regex (std::regex_error)" then some "R18 (regex area)"
  else match byInput cs with
  | some r => some r
  | none =>
    match c with
    | .err m => if (m.splitOn "Duplicate").length > 1 then some "R13" else if repair then repairR2 cs j c else none
    | _ => if repair then repairR2 cs j c else none

/-- R2's repair: spaces inserted at some set of inner positions (every subset, smallest first),
leaving what Clojure reads unchanged. -/
partial def repairR2 (cs : List Nat) (j c : Outcome) : Option String :=
  match j with
  | .err "expected whitespace" =>
    let n := cs.length
    let inner := (List.range n).filter (· > 0)
    -- Subsets of inner positions, by size.
    let subsets : List (List Nat) := (inner.foldr (fun i acc => acc ++ acc.map (i :: ·)) [[]]).filter (!·.isEmpty)
    let subsets := (subsets.toArray.qsort (fun a b => a.length < b.length)).toList
    let insAll := fun (ps : List Nat) => (ps.toArray.qsort (· > ·)).toList.foldl
      (fun xs i => xs.take i ++ [32] ++ xs.drop i) cs
    let ok := subsets.any fun ps =>
      let t := insAll ps
      let ct := cljRead t
      ct == c && (let jt := jankRead t
                  !bad (verdict jt ct) || (match explain t jt ct false with | some _ => true | none => false))
    if ok then some "R2" else none
  | _ => none
end

/-- The residual property: jank reads what Clojure reads, unless a round-2 class explains it. -/
def residualBody (alphabet : List Nat) (maxLen : Nat) : WM Unit := do
  let cs ← drawString alphabet maxLen
  let j := jankRead cs
  let c := cljRead cs
  let v := verdict j c
  if bad v then
    match explain cs j c with
    | some r => violate (σ := World) r s!"{showCodes cs}: Clojure {c.show}, jank {j.show}"
    | none => violate (σ := World) "unexplained" s!"{showCodes cs}: Clojure {c.show}, jank {j.show}"
  else if v == .acceptsInvalid then
    violate (σ := World) "accepts invalid (counted)" s!"{showCodes cs}: Clojure {c.show}, jank {j.show}"

/-- A census world: classes are properties; `exhaustUnder` on `strict` stops only at the
unexplained. -/
def strict (alphabet : List Nat) (maxLen : Nat) (source : Source) : Ended :=
  let e := runW (residualBody alphabet maxLen) source
  match e.violation with
  | some ("unexplained", _) => e
  | _ => { e with violation := none }

def censusWorld (alphabet : List Nat) (maxLen : Nat) : Source → Ended := runW (residualBody alphabet maxLen)

/-! ## Totality without NUL, by length-5 partitions -/

def totalNoNul (maxLen : Nat) : WM Unit := do
  let bs ← drawBytes (totalBytes.filter (· != 0)) maxLen
  match jankReadB bs with
  | .hang w => violate (σ := World) "read is total" s!"{showBytes bs}: hangs in {w}"
  | .crash w => violate (σ := World) "read is total" s!"{showBytes bs}: {w}"
  | _ => pure ()
  match (Jank.Read.readString bs.toArray).1 with
  | .hang w => violate (σ := World) "read is total" s!"(read-string {showBytes bs}): hangs in {w}"
  | .crash w => violate (σ := World) "read is total" s!"(read-string {showBytes bs}): {w}"
  | _ => pure ()

/-! ## Syntax quote, widened: depth 3, the found classes removable -/

section
open Jank.ReadSyntaxQuote

structure SQOpts where
  depth : Nat := 3
  /-- R19 (second part): `~@` of a literal set form. -/
  setSplice : Bool := true
  syms : List (String × String) := symbols

def drawU3 (o : SQOpts) : Jank.ReaderSearch.WM F := do
  let kinds := if o.setSplice then 3 else 2
  match ← decide (σ := Jank.ReaderSearch.World) "sq.unquoted" kinds with
  | 0 => pure (.sym "" (if (← decide (σ := Jank.ReaderSearch.World) "sq.local" 2) == 0 then "a" else "b"))
  | 1 => do
    let n ← decide (σ := Jank.ReaderSearch.World) "sq.lit.size" 3
    let mut xs := #[]
    for _ in [0:n] do xs := xs.push (.sym "" (if (← decide (σ := Jank.ReaderSearch.World) "sq.local" 2) == 0 then "a" else "b"))
    pure (.vec xs.toList)
  | _ => do
    match ← decide (σ := Jank.ReaderSearch.World) "sq.lit.set" 3 with
    | 0 => pure (.set [.sym "" "a"])
    | 1 => pure (.set [.sym "" "b"])
    | _ => pure (.set [.sym "" "a", .sym "" "b"])

partial def drawF3 (o : SQOpts) (depth : Nat) : Jank.ReaderSearch.WM F := do
  let k ← decide (σ := Jank.ReaderSearch.World) "sq.kind" (if depth == 0 then 3 else 6)
  match k with
  | 0 => do
    let s ← pick (σ := Jank.ReaderSearch.World) "sq.symbol" o.syms
    let (ns, n) := s.getD ("", "a")
    pure (.sym ns n)
  | 1 => pure (.num 1)
  | 2 => pure (.unq (← drawU3 o))
  | _ => do
    let n ← decide (σ := Jank.ReaderSearch.World) "sq.size" 3
    let mut xs := #[]
    for _ in [0:n] do
      if (← decide (σ := Jank.ReaderSearch.World) "sq.splice" 2) == 1 then xs := xs.push (.unqs (← drawU3 o))
      else xs := xs.push (← drawF3 o (depth - 1))
    match k with
    | 3 => pure (.list xs.toList)
    | 4 => pure (.vec xs.toList)
    | _ => pure (.set xs.toList)

def sqBody (o : SQOpts) : Jank.ReaderSearch.WM Unit := do
  let f ← drawF3 o o.depth
  let a ← decide (σ := Jank.ReaderSearch.World) "sq.a" 2
  let b ← decide (σ := Jank.ReaderSearch.World) "sq.b" 2
  let env : Env := { locals := [("a", .num (Int.ofNat a + 1)), ("b", .num (Int.ofNat b + 1))] }
  let j := jankSQ env f
  let c := cljSQ env f
  let sh := fun (r : Except String V) => match r with | .ok v => v.show | .error e => s!"error ({e})"
  if sh j != sh c then
    violate (σ := Jank.ReaderSearch.World) "syntax quote evaluates as Clojure's"
      s!"(let [a {a + 1} b {b + 1}] `{f.show}): Clojure {sh c}, jank {sh j}"

def sqResidualSyms : List (String × String) :=
  symbols.filter fun (_, n) => (!(n.contains '.') || n.startsWith ".") && n != "new"
end

/-! ## Round trips, widened: generated values -/

/-- Every string of ≤ 2 code points over `cps`, every character in `chars`, longs at the edges,
doubles on a grid, ratios, names. -/
def rtValues3 : List Val :=
  let cps : List Nat := (List.range 128) ++ [0xA0, 0xE9, 0x2003, 0x2028, 0xFEFF, 0x1F600]
  let strs := [[]] ++ cps.map (fun c => [c]) ++ cps.flatMap fun a => [0x61, 0x22, 0x5C, 0x0A, 0xE9].map fun b => [a, b]
  let chars := cps
  let longs : List Int := [0, 1, -1, 7, -7, 2147483647, -2147483648, 2147483648, 9223372036854775807,
    -9223372036854775807, -9223372036854775808, 4611686018427387904]
  let bigs : List Int := [9223372036854775808, -9223372036854775809, 0, 1, -1]
  let ratios : List (Int × Nat) := [(1, 2), (-1, 2), (7, 3), (9223372036854775807, 2), (-9223372036854775808, 3), (1, 9223372036854775808)]
  -- (a zero mantissa only with exponent 0: the canonical zero)
  let dbls : List Dec := ([false, true].flatMap fun neg => [0, 1, 15, 123456789].flatMap fun m =>
    ([(-20 : Int), -8, -5, -4, -3, -1, 0, 1, 5, 6, 7, 15, 16, 20, 21, 22].filter (fun e => m != 0 || e == 0)).map
      fun e => ({ neg, mant := m, exp := e } : Dec))
  let names : List (List Nat × List Nat) := [([], codesOf "a"), (codesOf "a", codesOf "b"), ([], codesOf "a.b"),
    ([], codesOf "é"), ([], codesOf "+"), ([], codesOf "-a"), ([], codesOf "a:b"), ([], codesOf "/"),
    (codesOf "a", codesOf "/"), ([], codesOf "a#")]
  strs.map Val.str ++ chars.map Val.char ++ longs.map Val.long ++ bigs.map Val.big
  ++ ratios.map (fun (n, d) => Val.ratio n d) ++ dbls.map Val.dbl
  ++ names.map (fun (n, m) => Val.sym n m) ++ names.map (fun (n, m) => Val.kw n m)
  ++ [.inf false, .inf true, .nan, .nil, .bool true, .bool false]

/-- The round-2 class of a value that does not round-trip, or none. -/
def rtExplain (v : Val) : Option String :=
  match v with
  | .str s => if s.contains 0 then some "R1 (NUL printed raw, read hangs)"
    else if s.contains 7 || s.contains 11 then some "R70 (\\a \\v)"
    else if s.any unicodeOnlyWs then some "R15" else none
  | .char c => if c == 0 then some "R1" else if c == 7 || c == 11 then some "R70"
    else if unicodeOnlyWs c then some "R15" else none
  | .long v => if v == -9223372036854775808 then some "R5" else none
  | .ratio n _ => if n == -9223372036854775808 then some "R5" else none
  | .sym _ n | .kw _ n => if n == codesOf "/" then some "R16" else none
  | _ => none

end Jank.R3.Search.Reader
