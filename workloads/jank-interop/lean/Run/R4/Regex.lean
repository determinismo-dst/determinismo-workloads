-- SPDX-License-Identifier: GPL-3.0-or-later WITH GCC-exception-3.1 (replicates libstdc++; see Jank/R4/Regex/README.md)
import Jank.R4.Regex.Matcher
import Jank.R4.Regex.Theorems4

/-! Round 4 driver: Regex (round 3's libstdc++ replica against the round-4 java.util.regex model).

`lake exe jank4-regex <command> [args]`; each command prints one section of
`results/r4-regex*.txt`. -/

open Jank.R3.Regex
open Jank.R4.Regex

def locOf (s : String) : Loc := if s == "c" then .c else .utf8

/-- Tokens for captures inside lookaheads (whole lookaheads, so three tokens reach them). -/
def lookTokens : List String :=
  ["(?=(a))", "(?=(b))", "(?!(a))", "(?!(a)b)", "(?=(a)b)", "(?=(a|b))", "(?=(a?))", "(?=(a*))",
   "(?=a(b))", "a", "b", "|", "(", ")", "(?:", "*", "?", "\\1", "\\2", "^", "$", "\\b", "."]

/-- Tokens for lookbehind, inline flags, named groups, atomic groups. -/
def flagTokens : List String :=
  ["(?i)", "(?-i)", "(?i:", "(?m)", "(?s)", "(?x)", "(?d)", "(?u)", "(?U)", "(?iu)", "(?<=", "(?<!",
   "(?<n>", "\\k<n>", "(?>", "a", "A", "b", " ", "#", "^", "$", ".", "(", ")", "|", "*", "\\w",
   "\\b", "[a]", "é", "É"]

def lookApis : List Api :=
  [.find, .seq, .matches, .replace (cpsOf "-"), .replace (cpsOf "[$1]"), .replaceFirst (cpsOf "[$1]"),
   .replaceFn, .replaceFirstFn, .split 0]

def flagInputs : List (List Nat) :=
  [[], cpsOf "a", cpsOf "A", cpsOf "b", cpsOf "é", cpsOf "É", cpsOf "\n", cpsOf " ", cpsOf "aA",
   cpsOf "Aa", cpsOf "a\nb", cpsOf "b\na", cpsOf "\r\n", cpsOf "ab", cpsOf "ba", cpsOf "a b", cpsOf "#a"]

def partOf {α : Type} (xs : List α) (part parts : Nat) : List α :=
  ((List.range xs.length).zip xs).filterMap fun (i, p) => if i % parts == part then some p else none

/-- `look <maxTok> <part> <parts>`: every pattern of ≤ maxTok lookahead tokens. -/
def lookCensus (args : List String) : IO Unit := do
  let k := (args.getD 0 "3").toNat!
  let part := (args.getD 1 "0").toNat!
  let parts := (args.getD 2 "1").toNat!
  let pats := partOf (upTo lookTokens k) part parts
  let inps := inputsOver [0x61, 0x62] 3
  IO.println s!"== look: lookahead tokens ≤ {k} ({pats.length} patterns in part {part}/{parts}), inputs ≤ 3 over a b ({inps.length}), {lookApis.length} calls, locale UTF-8"
  let qs := pats.flatMap fun p => inps.flatMap fun i => lookApis.map fun a => ({ api := a, pat := tokensToPat p, inp := i } : Q)
  printTally4 .utf8 "census" (census4 .utf8 {} qs)

/-- `flags <maxTok> <part> <parts>`: lookbehind, inline flags, named and atomic groups. -/
def flagCensus (args : List String) : IO Unit := do
  let k := (args.getD 0 "2").toNat!
  let part := (args.getD 1 "0").toNat!
  let parts := (args.getD 2 "1").toNat!
  let pats := partOf (upTo flagTokens k) part parts
  let apis : List Api := [.find, .seq, .matches, .replace (cpsOf "<$0>")]
  IO.println s!"== flags: tokens ≤ {k} ({pats.length} patterns in part {part}/{parts}), {flagInputs.length} inputs, {apis.length} calls, locale UTF-8"
  let qs := pats.flatMap fun p => flagInputs.flatMap fun i => apis.map fun a => ({ api := a, pat := tokensToPat p, inp := i } : Q)
  printTally4 .utf8 "census" (census4 .utf8 {} qs)

/-- `core <maxTok> <part> <parts>`: round 3's core census on the round-4 verdict, only the
patterns whose Java tree keeps captures (a group in a lookaround) — the ones round 3 compared
through the whole match only. -/
def coreCensus (args : List String) : IO Unit := do
  let k := (args.getD 0 "3").toNat!
  let part := (args.getD 1 "0").toNat!
  let parts := (args.getD 2 "1").toNat!
  let pats := (partOf (upTo coreTokens k) part parts).filter fun p =>
    match JM.compile (tokensToPat p) with
    | .ok jp => jp.node.keepsCaptures
    | .error _ => false
  let inps := asciiInputs 3 ++ extInputs
  IO.println s!"== core (round 3's tokens) ≤ {k}, part {part}/{parts}: {pats.length} patterns keeping captures, {inps.length} inputs, {apisFull.length} calls"
  let qs := pats.flatMap fun p => inps.flatMap fun i => apisFull.map fun a => ({ api := a, pat := tokensToPat p, inp := i } : Q)
  printTally4 .utf8 "census" (census4 .utf8 {} qs)

/-- `regress <maxTok> <part> <parts>`: round 3's Java model against round 4's on every question
of the core census where round 4 changes nothing (no capture kept, no lookbehind or flag): the
two must give the same answer. -/
def regress (args : List String) : IO Unit := do
  let k := (args.getD 0 "3").toNat!
  let part := (args.getD 1 "0").toNat!
  let parts := (args.getD 2 "1").toNat!
  let pats := partOf (upTo coreTokens k) part parts
  let inps := asciiInputs 3 ++ extInputs
  let mut total := 0
  let mut same := 0
  let mut diff : List String := []
  let mut skipped := 0
  for p in pats do
    let pat := tokensToPat p
    let keeps := match JM.compile pat with | .ok jp => jp.node.keepsCaptures | .error _ => false
    if keeps then skipped := skipped + 1; continue
    for i in inps do
      for a in apisFull do
        let q : Q := { api := a, pat, inp := i }
        total := total + 1
        let c3 := cljEval q
        let c4 := cljEval4 q
        let ok := match c3, c4 with
          | .unknown _, _ => true
          | _, .unknown _ => true
          | .err _, .err _ => true
          | x, y => x == y
        if ok then same := same + 1
        else if diff.length < 20 then diff := diff ++ [s!"{q.program}: round 3 {CV.show c3}, round 4 {CV.show c4}"]
        else pure ()
  IO.println s!"== regress: core tokens ≤ {k}, part {part}/{parts}: {total} questions, {same} identical, {total - same} differ ({skipped} patterns keeping captures left out)"
  for d in diff do IO.println s!"    {d}"

/-- `nul`: patterns with a NUL (only `re-pattern` can build them; a `#"…"` literal cannot hold one). -/
def nulCensus : IO Unit := do
  let toks : List String := ["a", "b", "\u0000", "*", "|", "(", ")", "$", "^", ".", "?"]
  let pats := (upTo toks 3).filter fun p => p.contains "\u0000"
  let inps := inputsOver [0x61, 0x62, 0] 3
  let apis : List Api := [.find, .seq, .matches, .replace (cpsOf "-"), .split 0]
  IO.println s!"== nul: {pats.length} patterns with a NUL (≤ 3 tokens), {inps.length} inputs over a b NUL, {apis.length} calls"
  let qs := pats.flatMap fun p => inps.flatMap fun i => apis.map fun a => ({ api := a, pat := tokensToPat p, inp := i } : Q)
  printTally4 .utf8 "census" (census4 .utf8 {} qs)

/-- `matcher`: scripts of `re-find`/`re-groups`/`nth` on one `re-matcher`. -/
def matcherCensus : IO Unit := do
  let pats := ["a", "ab", "a|b", "(a)", "(a)|b", "a(b)?", "(a)(b)", "", "é", "x", "(é)", "a*"].map cpsOf
  let inps := (inputsOver [0x61, 0x62] 3) ++ [cpsOf "é", cpsOf "aé"]
  let opsPool : List MOp := [.find, .groups, .nth 0, .nth 1, .nth 2, .nth (-1), .nthNf 0, .nthNf 1, .nthNf 2, .nthNf (-1)]
  let scripts : List (List MOp) :=
    (opsPool.map fun o => [o]) ++ (opsPool.flatMap fun o => [[.find, o], [.find, .find, o]])
  let mut total := 0
  let mut agree := 0
  let mut classes : List (String × Nat × List String) := []
  for p in pats do
    for i in inps do
      for sc in scripts do
        total := total + 1
        let j := jankScript .utf8 p i sc
        let c := cljScript p i sc
        if j.length == c.length && (j.zip c).all fun (x, y) => MV.agree x y then agree := agree + 1
        else
          let last := (j.zip c).find? fun (x, y) => !MV.agree x y
          let cls := match last with
            | some (.ch _, .str _) => "nth reads a character of the match (no groups)"
            | some (.ch _, .err _) => "nth past group 0 reads a character (no groups)"
            | some (.ch _, .notFound) => "nth with not-found reads a character (no groups)"
            | some (.nil, .err _) => "nth without a match is nil"
            | some (.notFound, .err _) => "nth with not-found without a match is not-found"
            | some (.str [], .nil) => "unmatched group is \"\" (R80)"
            | some (.vec _, .vec _) => "unmatched group is \"\" (R80)"
            | _ => "other"
          let ex := s!"{scriptProgram p i sc}: Clojure {" ".intercalate (c.map MV.show)}, jank {" ".intercalate (j.map MV.show)}"
          classes := match classes.find? (·.1 == cls) with
            | some _ => classes.map fun (k, n, es) => if k == cls then (k, n + 1, if es.length < 3 && ex.length < 140 then es ++ [ex] else es) else (k, n, es)
            | none => classes ++ [(cls, 1, [ex])]
  IO.println s!"== matcher: {pats.length} patterns × {inps.length} inputs × {scripts.length} scripts = {total} scripts: {agree} agree, {total - agree} differ"
  for (k, n, es) in classes do
    IO.println s!"    [{k}]: {n}"
    for e in es do IO.println s!"      {e}"
  -- printing
  let printPats := ["a", "a\"b", "\\Q\"\\E", "(a)|b", ""].map cpsOf
  IO.println "  print-str of a pattern (Clojure: print-method's #\"…\"; jank: to_string):"
  for p in printPats do
    IO.println s!"    (print-str (re-pattern {Jank.Str.lit p})): Clojure {Jank.Str.lit (cljPrintPattern p)}, jank {Jank.Str.lit (jankPrintPattern p)}"

/-- `examples`: the report's programs with both answers and their class. -/
def examples : IO Unit := do
  let q (api : Api) (p : String) (i : String) : Q := { api, pat := cpsOf p, inp := cpsOf i }
  let qs : List Q := [
    q .find "(?=(a))x|b" "ab", q .find "(?!(a))x|b" "ab", q .seq "(?=(a))x|b" "abab",
    q (.replace (cpsOf "[$1]")) "(?=(a))x|b" "ab", q .replaceFn "(?=(a))x|b" "ab",
    q .find "(?:(?=(a))x|a)" "a", q .matches "(?=(a))x|ab" "ab", q .find "(?=(a))b|(?=(b))" "ab",
    q .find "a(?=(b))\\1" "abb", q .find "(?=(a)b)|b" "ab",
    { api := .find, pat := [0x78, 0], inp := cpsOf "x" }, { api := .find, pat := [0x61, 0, 0x62], inp := cpsOf "a" },
    { api := .matches, pat := [0], inp := [] }, { api := .seq, pat := [0x61, 0], inp := cpsOf "aa" },
    q .find "(?<=a)b" "ab", q .find "(?i)a" "A", q .find "(?<=(a|ab))c" "abc", q .find "(?<=(?:ab)*)c" "abc"]
  IO.println "== examples: Clojure's answer, the replica's, the class"
  for x in qs do
    let (v, _, _) := verdict4 .utf8 {} x
    let cls := match v with
      | .differ => (classify4 .utf8 x).getD (trigger x)
      | .rejects e => s!"jank rejects: {rejectShape4 x.pat e}"
      | .acceptsInvalid e => s!"Java rejects ({e})"
      | .agree => "agree"
      | .skip w => s!"not compared ({w})"
    IO.println s!"  {showQ4 .utf8 x}  [{cls}]"

/-- `dump <table> <part> <parts>`: one EDN vector per question whose pattern Java compiles, with
the round-4 model's answer, for `.r4-scratch/regex/clj/validate.clj` to rerun on a JVM. Tables:
`look` (≤ 3 lookahead tokens), `flags` (≤ 2 flag tokens), `core` (round 3's ≤ 3 core tokens),
`syntax` (round 3's extra tokens in six contexts). -/
def dump (args : List String) : IO Unit := do
  let table := args.getD 0 "look"
  let part := (args.getD 1 "0").toNat!
  let parts := (args.getD 2 "1").toNat!
  let qs : List Q :=
    if table == "look" then
      (partOf (upTo lookTokens 3) part parts).flatMap fun p => (inputsOver [0x61, 0x62] 3).flatMap fun i =>
        lookApis.map fun a => ({ api := a, pat := tokensToPat p, inp := i } : Q)
    else if table == "flags" then
      (partOf (upTo flagTokens 2) part parts).flatMap fun p => flagInputs.flatMap fun i =>
        [Api.find, .seq, .matches, .replace (cpsOf "<$0>")].map fun a => ({ api := a, pat := tokensToPat p, inp := i } : Q)
    else if table == "core" then
      (partOf (upTo coreTokens 3) part parts).flatMap fun p => (asciiInputs 3 ++ extInputs).flatMap fun i =>
        apisSmall.map fun a => ({ api := a, pat := tokensToPat p, inp := i } : Q)
    else
      let ctxs : List (String → List String) := [fun t => [t], fun t => ["a", t], fun t => [t, "a"],
        fun t => ["(", t, ")"], fun t => [t, "*"], fun t => ["[", t, "]"]]
      let pats := (extraTokens ++ coreTokens).flatMap fun t => ctxs.map fun c => c t
      (partOf pats part parts).flatMap fun p => (asciiInputs 2 ++ extInputs).flatMap fun i =>
        [Api.find, .matches].map fun a => ({ api := a, pat := tokensToPat p, inp := i } : Q)
  let mut n := 0
  let mut lastBad : List Nat := [0x110000]
  for q in qs do
    if javaAccepts4 q.pat then
      match cljEval4 q with
      | .unknown _ => pure ()
      | _ => IO.println (ednLine n q); n := n + 1
    else if q.pat != lastBad then
      IO.println s!"[{n} :compile-error {ednNats q.pat}]"; n := n + 1
      lastBad := q.pat

def main (args : List String) : IO UInt32 := do
  match args with
  | "look" :: rest => lookCensus rest
  | "flags" :: rest => flagCensus rest
  | "core" :: rest => coreCensus rest
  | "regress" :: rest => regress rest
  | ["nul"] => nulCensus
  | ["matcher"] => matcherCensus
  | ["examples"] => examples
  | "dump" :: rest => dump rest
  | _ => IO.println "usage: jank4-regex look|flags|core|regress|nul|matcher|examples|dump …"
  return 0
