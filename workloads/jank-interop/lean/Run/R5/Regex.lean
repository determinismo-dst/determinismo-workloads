-- SPDX-License-Identifier: GPL-3.0-or-later WITH GCC-exception-3.1 (with round 3's regex replica; see Jank/R5/Regex/README.md)
import Jank.R5.Regex.ExecInv
import Jank.R5.Regex.Compare5

/-!
Round 5 driver, regex (`jank5-regex <part> …`):
- `uni2 [k n]`: patterns of ≤ 2 tokens (Unicode classes, `(?U)`, `\p{…}`, `\b`, `.`, `$`, …) ×
  every input of ≤ 2 code points over 13 code points (ASCII, Latin-1, a combining mark, an
  Arabic-Indic digit, a letter number, a join control, U+2028, an emoji) × 4 calls; part `k` of `n`
  (patterns split round-robin).
- `mn3 [k n]`: `\b`-centred patterns of ≤ 3 tokens × inputs of ≤ 3 code points over 7 × 4 calls.
- `dump uni2|mn3 [every]`: the questions with the spec's answers as EDN lines for the JVM check
  (`every`: one question in `every`).
- `table`: `Character.getType` and the properties the spec reads, per drawn code point (diffed
  against the JVM's).
- `examples`: the report's programs.
-/

open Jank.R3.Regex Jank.R4.Regex Jank.R5.Regex

def uniTokens : List String :=
  ["a", "é", "́", ".", "\\w", "\\W", "\\b", "\\B", "\\s", "\\S", "\\d", "+", "*", "$", "[^a]",
   "(?U)", "\\p{L}", "\\p{Alpha}", "\\p{Punct}", "\\p{IsAlphabetic}", "\\p{javaLowerCase}",
   "\\p{Mn}", "\\p{IsWhite_Space}", "[[:alpha:]]", "(?i)"]

/-- a, e, é, U+0301, ١ (U+0661), ¡, NBSP, U+2028, _, space, Ⅰ (U+2160), ZWJ, 😀. -/
def uniAlpha : List Nat :=
  [0x61, 0x65, 0xE9, 0x301, 0x661, 0xA1, 0xA0, 0x2028, 0x5F, 0x20, 0x2160, 0x200D, 0x1F600]

def mnTokens : List String := ["a", "e", "́", "\\w", "\\b", "\\B", "+", ".", "(?U)"]

def mnAlpha : List Nat := [0x61, 0x65, 0x301, 0xE9, 0x661, 0x2028, 0x20]

def apis5 : List Api := [.find, .seq, .matches, .replace (cpsOf "<$0>")]

def questions (toks : List String) (maxTok : Nat) (alpha : List Nat) (maxLen : Nat)
    (part parts : Nat) : List Q :=
  let all := upTo toks maxTok
  let pats := (all.zip (List.range all.length)).filterMap fun (p, i) =>
    if parts == 0 || i % parts == part then some p else none
  pats.flatMap fun p => (inputsOver alpha maxLen).flatMap fun i =>
    apis5.map fun a => ({ api := a, pat := tokensToPat p, inp := i } : Q)

def worldQs (name : String) (part parts : Nat) : List Q :=
  if name == "uni2" then questions uniTokens 2 uniAlpha 2 part parts
  else if name == "mn3" then questions mnTokens 3 mnAlpha 3 part parts
  else []

def runCensus (name : String) (part parts : Nat) : IO Unit := do
  let t0 ← IO.monoMsNow
  let qs := worldQs name part parts
  let t := census5 .utf8 qs
  printTally5 .utf8 s!"{name} part {part}/{parts} (UTF-8 locale)" t
  let t1 ← IO.monoMsNow
  IO.println s!"  ({(t1 - t0) / 1000} s)"

def tableLine (c : Nat) : String :=
  s!"{c} {JM5.gcat c} {JM5.jIsAlphabetic c} {JM5.jIsLetterOrDigit c} {JM5.jIsLowerCase c} {JM5.jIsUpperCase c} {JM5.jIsDigit c} {JM5.jWhiteSpace c} {JM5.jWord c}"

def examples : List Q :=
  let q (api : Api) (p : String) (i : String) : Q := { api, pat := cpsOf p, inp := cpsOf i }
  [q .find "e\\b" "é", q .seq "\\b\\w+\\b" "café x", q (.replace (cpsOf "|")) "\\b" "naïve",
   q (.replace (cpsOf "|")) "\\B" "é", q .find "\\b" "é́", q .find "\\b" "١́",
   q (.replace (cpsOf "|")) "\\b" "naïve", q .seq "\\w+" "naïve",
   q .find ".+" " ", q .matches ".*" " ", q .find ".+" "a ", q .find "a$" "a ", q .find "a$" "a",
   q .find "(?U)\\w" "é", q .find "\\p{Alpha}" "é", q .find "(?U)\\p{Alpha}" "é",
   q .find "[[:alpha:]]" "é", q .find "\\W" "é"]

def main (args : List String) : IO Unit := do
  match args with
  | ["dump", w] => do
    let mut i := 0
    for q in worldQs w 0 0 do
      IO.println (ednLine5 i q)
      i := i + 1
  | ["dump", w, every] => do
    let e := every.toNat!
    let mut i := 0
    for q in worldQs w 0 0 do
      if i % e == 0 then IO.println (ednLine5 i q)
      i := i + 1
  | ["table"] => for c in (uniAlpha ++ mnAlpha).eraseDups do IO.println (tableLine c)
  | ["examples"] => for q in examples do
      let (v, _, _) := verdict5 .utf8 {} q
      let cls := match v with
        | .differ => (classify5 .utf8 q).getD (trigger q)
        | .agree => "agree"
        | .rejects w => s!"jank rejects: {rejectShape5 q.pat w}"
        | .acceptsInvalid _ => "jank accepts an invalid pattern"
        | .skip w => s!"not compared: {w}"
      IO.println s!"{showQ5 .utf8 q}   [{cls}]"
  | [w] => runCensus w 0 0
  | [w, k, n] => runCensus w k.toNat! n.toNat!
  | _ => IO.println "usage: jank5-regex uni2|mn3 [k n] | dump uni2|mn3 [every] | table | examples"
