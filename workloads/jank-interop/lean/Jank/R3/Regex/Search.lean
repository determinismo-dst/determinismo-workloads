import Jank.R3.Regex.Compare
import Determinismo

/-!
# Searches: census tables, residual walks and a Determinismo world

- `census`: every question of a table, its verdict on the replica, each deviation's class (the
  first toggle of `fixOrder` that removes it; else its trigger: non-ASCII text, a construct whose
  syntax differs, or "unexplained"), counted per class with the shortest examples.
- `residual`: the same table with every toggle on; a complete walk with nothing left means every
  deviation of the table belongs to a reported class.
- The Determinismo world draws the same questions decision by decision, so `exhaust` and
  `explore` search them as round 2 did; set-aside classes are skipped by the property.
-/

namespace Jank.R3.Regex

open Determinismo

def cpsOf (s : String) : List Nat := s.toList.map Char.toNat

/-- Pattern tokens whose meaning is meant to be the same in ECMAScript and Java. -/
def coreTokens : List String :=
  ["a", "b", ".", "*", "+", "?", "|", "(", ")", "(?:", "(?=", "(?!", "[", "]", "^", "$", "-",
   "\\b", "\\B", "\\d", "\\w", "\\s", "\\1", "{2}", "{1,}", "{0,1}"]

/-- Tokens of constructs whose syntax differs (or may): measured in the syntax table. -/
def extraTokens : List String :=
  ["\\v", "\\cJ", "\\A", "\\z", "\\Z", "\\G", "\\Q", "\\E", "\\e", "\\a", "\\h", "\\R", "\\pL",
   "\\p{L}", "\\x41", "\\xe9", "\\u00e9", "\\u0141", "\\0", "\\01", "\\012", "[:", ":]", "[[:alpha:]]",
   "[[.a.]]", "[[=a=]]", "&&", "é", "\\x{41}", "(?<=", "(?<!", "(?<n>", "(?>", "(?i)", "\\k<n>",
   "{", "}", "\\10", "\\2", "*+", "++", "?+", "{2}+", "**", "\\-", "\\/", "\\y", "\\i", "\\N",
   "\\H", "\\V", "\\X", "\\S", "\\W", "\\D", "[^]", "[]", "[]a]", "[a-]", "[-a]", "[\\w-a]",
   "[a-\\d]", "[\\b]", "[\\B]", "[\\1]", "[a-é]", "[é-a]", "[\\x80-\\xff]", "\\x80", "😀", "{,2}",
   "{2,1}", "{99999}", "a{100000}"]

def tokensToPat (ts : List String) : List Nat := (String.join ts).toList.map Char.toNat

/-- All concatenations of exactly `k` tokens. -/
def tupleOf (toks : List String) : Nat → List (List String)
  | 0 => [[]]
  | k + 1 => (tupleOf toks k).flatMap fun t => toks.map fun x => t ++ [x]

def upTo (toks : List String) (k : Nat) : List (List String) :=
  (List.range (k + 1)).flatMap fun n => if n == 0 then [] else tupleOf toks n

/-- Inputs: every string over `alpha` of length ≤ `n`. -/
def inputsOver (alpha : List Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 => inputsOver alpha n ++ ((inputsOver alpha n).filter (·.length == n)).flatMap fun s => alpha.map (s ++ [·])

/-- ASCII inputs: a, b, newline. -/
def asciiInputs (n : Nat) : List (List Nat) := inputsOver [0x61, 0x62, 0x0A] n

/-- Inputs with a 2-byte, a 4-byte character, a NUL and U+0085. -/
def extInputs : List (List Nat) :=
  [[0xE9], [0x61, 0xE9], [0xE9, 0x61], [0x1F600], [0x61, 0x1F600], [0, 0x61], [0x61, 0, 0x62],
   [0x85], [0x0D, 0x0A], [0x61, 0x0D, 0x0A]]

def apisFull : List Api :=
  [.find, .seq, .matches, .replace (cpsOf "-"), .replace (cpsOf "<$0>"), .replace (cpsOf "$1"),
   .replace (cpsOf "$$"), .replace (cpsOf "\\$"), .replaceFn, .replaceFirst (cpsOf "-"),
   .replaceFirstFn, .split 0, .split (-1), .split 2]

def apisSmall : List Api := [.find, .seq, .matches, .replace (cpsOf "-"), .split 0]

/-- Whether a pattern or input holds a non-ASCII character. -/
def nonAscii (q : Q) : Bool := q.pat.any (· ≥ 0x80) || q.inp.any (· ≥ 0x80)

/-- Java's tree has a node satisfying `p`. -/
partial def jHas (p : J.N → Bool) (n : J.N) : Bool :=
  p n || match n with
    | .seq a b | .alt a b => jHas p a || jHas p b
    | .group _ r | .ncgroup r | .quant r _ _ _ | .look _ r | .atomic r => jHas p r
    | _ => false

def isAssertion : J.N → Bool
  | .bol | .eol | .wordB _ | .beginA | .endZ | .endz | .lastMatch | .look _ _ => true
  | _ => false

def subList (xs ys : List Nat) : Bool :=
  (List.range (xs.length + 1)).any fun i => (xs.drop i).take ys.length == ys

/-- The syntax a pattern holds whose meaning differs between the two grammars (from the pattern
text and Java's tree). -/
def syntaxShape (pat : List Nat) : Option String :=
  let has (s : String) := subList pat (cpsOf s)
  let esc (c : Char) := has ("\\" ++ String.singleton c)
  match J.compile pat with
  | .error _ => none
  | .ok jp =>
    if jHas (fun n => match n with | .quant _ _ _ .possessive => true | _ => false) jp.node then some "possessive quantifier read as a nested repeat"
    else if jHas (fun n => match n with | .quant r _ _ _ => isAssertion r | _ => false) jp.node then some "quantifier on an assertion"
    else if jHas (fun n => match n with | .quant .empty _ _ _ => true | _ => false) jp.node then some "{n} after nothing"
    else if has "[[" || has "&&" then some "nested class / intersection / POSIX bracket"
    else if has "[]" || has "[^]" then some "] first in a class"
    else if ['v', 'c', 'A', 'z', 'Z', 'G', 'Q', 'E', 'e', 'a', 'h', 'H', 'R', 'p', 'P', 'V', 'X', 'N', '0', 'x', 'u', 'k'].any esc then
      some "escape with another meaning"
    else none

/-- The class of a deviation no toggle removes. -/
def trigger (q : Q) : String :=
  match syntaxShape q.pat with
  | some s => s!"syntax: {s}"
  | none =>
    if nonAscii q then "bytes (R78)"
    else if q.inp.contains 0 then "nul (R83)"
    else "unexplained"

/-- The class of a pattern jank rejects and Java compiles. -/
def rejectShape (pat : List Nat) (jankErr : String) : String :=
  let has (s : String) := subList pat (cpsOf s)
  match J.compile pat with
  | .error _ => jankErr
  | .ok jp =>
    match jp.node.unsupportedIn with
    | some w => s!"{w} (R18)"
    | none =>
      if has "(?>" then "atomic group (R18)"
      else if jHas (fun n => match n with | .quant r _ _ _ => isAssertion r | _ => false) jp.node then "quantifier on an assertion"
      else if jHas (fun n => match n with | .quant .empty _ _ _ => true | _ => false) jp.node then "{n} after nothing"
      else if jHas (fun n => match n with | .backref _ => true | _ => false) jp.node then s!"backreference: {jankErr}"
      else jankErr

structure Tally where
  total : Nat := 0
  agree : Nat := 0
  skipped : Nat := 0
  skipReasons : List (String × Nat) := []
  rejects : List (String × Nat × List Q) := []
  acceptsInvalid : List (String × Nat × List Q) := []
  differ : List (String × Nat × List Q) := []
  deriving Inhabited

def bump (xs : List (String × Nat × List Q)) (k : String) (q : Q) (keep : Nat := 3) : List (String × Nat × List Q) :=
  match xs.find? (·.1 == k) with
  | some _ => xs.map fun (k', n, qs) =>
      if k' == k then
        let qs := if qs.length < keep then qs ++ [q]
          else if (q.program.length < (qs.map (·.program.length)).foldl max 0) then
            (qs ++ [q]).mergeSort (fun a b => a.program.length ≤ b.program.length) |>.take keep
          else qs
        (k', n + 1, qs)
      else (k', n, qs)
  | none => xs ++ [(k, 1, [q])]

def bumpN (xs : List (String × Nat)) (k : String) : List (String × Nat) :=
  match xs.find? (·.1 == k) with
  | some _ => xs.map fun (k', n) => if k' == k then (k', n + 1) else (k', n)
  | none => xs ++ [(k, 1)]

/-- Census of a list of questions under `fx` (classify only when `fx` is all off). -/
def census (loc : Loc) (fx : Fix) (qs : List Q) (classifyOn : Bool := true) : Tally := Id.run do
  let mut t : Tally := {}
  for q in qs do
    t := { t with total := t.total + 1 }
    let (v, _, _) := verdict loc fx q
    match v with
    | .agree => t := { t with agree := t.agree + 1 }
    | .skip w => t := { t with skipped := t.skipped + 1, skipReasons := bumpN t.skipReasons w }
    | .rejects w => t := { t with rejects := bump t.rejects (rejectShape q.pat w) q }
    | .acceptsInvalid w => t := { t with acceptsInvalid := bump t.acceptsInvalid w q }
    | .differ =>
      let cls := if classifyOn then (classify loc q).getD (trigger q) else trigger q
      t := { t with differ := bump t.differ cls q }
  return t

def showQ (loc : Loc) (fx : Fix) (q : Q) : String :=
  let (_, j, c) := verdict loc fx q
  s!"{q.program}: Clojure {CV.show c}, jank {V.show j}"

def printTally (loc : Loc) (fx : Fix) (name : String) (t : Tally) : IO Unit := do
  let nd := t.differ.foldl (fun a (_, n, _) => a + n) 0
  let nr := t.rejects.foldl (fun a (_, n, _) => a + n) 0
  let na := t.acceptsInvalid.foldl (fun a (_, n, _) => a + n) 0
  IO.println s!"  {name}: {t.total} questions: {t.agree} agree, {nd} differ, {nr} jank rejects a valid pattern, {na} jank accepts an invalid one, {t.skipped} not compared"
  for (k, n) in t.skipReasons do IO.println s!"    not compared ({k}): {n}"
  for (k, n, qs) in t.differ do
    IO.println s!"    differ [{k}]: {n}"
    for q in qs do IO.println s!"      {showQ loc fx q}"
  for (k, n, qs) in t.rejects do
    IO.println s!"    jank rejects [{k}]: {n}"
    for q in qs.take 2 do IO.println s!"      {showQ loc fx q}"
  for (k, n, qs) in t.acceptsInvalid do
    IO.println s!"    jank accepts, Java rejects [{k}]: {n}"
    for q in qs.take 2 do IO.println s!"      {showQ loc fx q}"

/-! ## The Determinismo world -/

structure World where
  decisions : Decisions := {}

instance : Chaotic World where
  decisions w := w.decisions
  setDecisions w d := { w with decisions := d }

/-- A world: an API, `maxTok` tokens, an input over `alpha` of length ≤ `maxLen`; a deviation is a
violation unless its class is set aside. -/
structure WSpec where
  loc : Loc
  toks : List String
  maxTok : Nat
  alpha : List Nat
  maxLen : Nat
  apis : List Api
  setAside : List String
  /-- Also report patterns jank rejects that Java accepts. -/
  rejectsCount : Bool := false

def drawQ (w : WSpec) : EStateM Stop World Q := do
  let api := w.apis.getD (← decide (σ := World) "rx.api" w.apis.length) .find
  let n ← decide (σ := World) "rx.tokens" w.maxTok
  let mut ts : List String := []
  for k in List.range (n + 1) do
    ts := ts ++ [w.toks.getD (← decide (σ := World) s!"rx.tok{k}" w.toks.length) ""]
  let len ← decide (σ := World) "rx.input.len" (w.maxLen + 1)
  let mut inp : List Nat := []
  for k in List.range len do
    inp := inp ++ [w.alpha.getD (← decide (σ := World) s!"rx.input{k}" w.alpha.length) 0x61]
  return { api, pat := tokensToPat ts, inp }

def property : String := "jank's regex functions agree with Clojure's"

def body (w : WSpec) : EStateM Stop World Unit := do
  let q ← drawQ w
  match verdict w.loc {} q with
  | (.differ, j, c) =>
    let cls := (classify w.loc q).getD (trigger q)
    unless w.setAside.contains cls do
      violate (σ := World) s!"{property} [{cls}]" s!"{q.program}: Clojure {CV.show c}, jank {V.show j}"
  | (.rejects e, _, _) =>
    let sh := rejectShape q.pat e
    if w.rejectsCount && !w.setAside.contains s!"rejects:{sh}" then
      violate (σ := World) s!"{property} [rejects:{sh}]" s!"{q.program}: Java compiles it, jank throws ({e})"
  | _ => pure ()

def run (w : WSpec) (source : Source) : Ended :=
  match (body w).run { decisions := { source } } with
  | .ok _ s => { taken := s.decisions.taken, violation := none }
  | .error (.violation p d) s => { taken := s.decisions.taken, violation := some (p, d) }
  | .error .limit s => { taken := s.decisions.taken, violation := none }

/-- `exhaust` with residual restarts: each found class is set aside and the walk restarts, until
a complete walk finds nothing (or `maxRounds`). -/
def residualExhaust (w : WSpec) (maxRuns : Nat) (maxRounds : Nat := 24) : IO (List String) := do
  let mut w := w
  let mut found : List String := []
  for _ in List.range maxRounds do
    match exhaust (run w) maxRuns with
    | .found c =>
      let raw := ((c.property.splitOn "[").getD 1 "").toList
      let cls := String.ofList (raw.take (raw.length - 1))
      IO.println s!"    found after {c.runs} timelines [{cls}]: {c.detail}"
      found := found ++ [cls]
      w := { w with setAside := w.setAside ++ [cls] }
    | .complete n =>
      IO.println s!"    complete: {n} timelines, nothing (set aside: {w.setAside})"
      return found
    | .stopped n =>
      IO.println s!"    stopped at {n} timelines, nothing (set aside: {w.setAside})"
      return found
  return found

end Jank.R3.Regex
