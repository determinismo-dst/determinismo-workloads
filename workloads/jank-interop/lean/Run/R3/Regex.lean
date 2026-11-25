-- SPDX-License-Identifier: GPL-3.0-or-later WITH GCC-exception-3.1 (replicates libstdc++; see Jank/R3/Regex/README.md)
import Jank.R3.Regex.Search
import Jank.R3.Regex.Round2
import Jank.R3.Regex.Theorems

/-! Round 3 driver: Regex (std::regex as libstdc++ 15.3.0 implements it, against java.util.regex).

`lake exe jank3-regex <command> [args]`; each command prints one section of
`results/r3-regex*.txt`. -/

open Jank.R3.Regex

def locOf (s : String) : Loc := if s == "c" then .c else .utf8

def inputsNamed (name : String) : List (List Nat) :=
  if name == "ascii3" then asciiInputs 3 ++ extInputs
  else if name == "ab3" then inputsOver [0x61, 0x62] 3
  else if name == "abn3" then inputsOver [0x61, 0x62, 0x0A] 3
  else if name == "ab4" then inputsOver [0x61, 0x62] 4
  else asciiInputs 2

/-- `grammar <loc> <maxTok> <part> <parts> <inputs> [fix]`: every pattern of ≤ maxTok core
tokens (`fix` = all: every toggle on, the residual walk). -/
def grammar (args : List String) : IO Unit := do
  let loc := locOf (args.getD 0 "utf8")
  let k := (args.getD 1 "2").toNat!
  let part := (args.getD 2 "0").toNat!
  let parts := (args.getD 3 "1").toNat!
  let inputs := args.getD 4 "ascii3"
  let fx : Fix := if args.getD 5 "" == "all" then Fix.all else {}
  let pats := upTo coreTokens k
  let pats := ((List.range pats.length).zip pats).filterMap fun (i, p) => if i % parts == part then some p else none
  let inps := inputsNamed inputs
  let apis := if inputs == "ascii3" then apisFull else apisSmall
  IO.println s!"== grammar: core tokens ≤ {k} ({pats.length} patterns in part {part}/{parts}), inputs {inputs} ({inps.length}), {apis.length} calls, locale {loc.name}{if fx == {} then "" else ", every toggle on (residual)"}"
  let qs := pats.flatMap fun p => inps.flatMap fun i => apis.map fun a => ({ api := a, pat := tokensToPat p, inp := i } : Q)
  let t := census loc fx qs (fx == {})
  printTally loc fx "census" t

/-- Inputs for the syntax table: single characters an escape may denote, and a few words. -/
def syntaxInputs : List (List Nat) :=
  [[], [0x61], [0x62], [0x0A], [0x0B], [0x4A], [0x41], [0x5A], [0x7A], [0x1B], [0x07], [0x01], [0x2D],
   [0x3A], [0x141], [0x7B], [0x7D], [0x26], [0x5D], [0x5B], [0x08], [0x5C], [0x51], [0x45], [0x2E],
   [0x20], [0x09], [0x65], [0x68], [0x76], [0x63], [0x6C], [0x70], [0x4C], [0x30], [0x31], [0x32],
   [0xE9], [0x1F600], [0x85], [0x61, 0x61], [0x61, 0x62], [0x61, 0x0A], [0x0D, 0x0A], [0x51, 0x2E, 0x45],
   [0x61, 0x31, 0x30], [0x61, 0x61, 0x30], [0x61, 0x2D], [0x2D, 0x61]]

/-- `syntax <loc>`: every extra token alone and in five contexts. -/
def syntaxTable (loc : Loc) : IO Unit := do
  let ctxs : List (String → List String) := [fun t => [t], fun t => ["a", t], fun t => [t, "a"],
    fun t => ["(", t, ")"], fun t => [t, "*"], fun t => ["[", t, "]"]]
  let pats := (extraTokens ++ coreTokens).flatMap fun t => ctxs.map fun c => c t
  IO.println s!"== syntax: {extraTokens.length + coreTokens.length} tokens × {ctxs.length} contexts = {pats.length} patterns, {syntaxInputs.length} inputs, re-find and re-matches, locale {loc.name}"
  let qs := pats.flatMap fun p => syntaxInputs.flatMap fun i => [Api.find, .matches].map fun a => ({ api := a, pat := tokensToPat p, inp := i } : Q)
  let t := census loc {} qs
  printTally loc {} "census" t
  -- per token: how each side treats the token alone
  IO.println "  per token (alone): jank / Java"
  for tok in extraTokens do
    let p := tokensToPat [tok]
    let j := match compile loc (utf8s p) with | .ok _ => "compiles" | .error e => s!"throws ({e.what})"
    let c := match J.compile p with | .ok _ => "compiles" | .error (.syntax e) => s!"throws ({e})"
    IO.println s!"    {patLit p}: jank {j}; Java {c}"

/-- `depth`: the deepest `_M_dfs` recursion of one search as a function of the input. -/
def depthTable : IO Unit := do
  IO.println "== stack depth: `_M_dfs` frames of one regex_search (re-find), input of n characters"
  IO.println "   D = all `_M_dfs` frames (no sibling calls); NT = frames left when every tail call is a sibling call"
  let cases : List (String × (Nat → List Nat)) := [
    ("a*", fun n => List.replicate n 0x61), (".*", fun n => List.replicate n 0x61),
    ("[^,]*", fun n => List.replicate n 0x61), ("\\w+", fun n => List.replicate n 0x61),
    ("a*?$", fun n => List.replicate n 0x61), ("(a|b)*", fun n => List.replicate n 0x61),
    ("(?:ab)*", fun n => (List.replicate (n / 2) [0x61, 0x62]).flatten), ("(a)*", fun n => List.replicate n 0x61),
    ("[a-z]+@", fun n => List.replicate n 0x61), ("(?:a|b)*?c", fun n => List.replicate n 0x61 ++ [0x63])]
  for (p, mk) in cases do
    match compile .utf8 (utf8s (cpsOf p)) with
    | .error e => IO.println s!"  {p}: {e.what}"
    | .ok nfa =>
      let mut line := s!"  #\"{p}\":"
      let mut pts : List (Nat × Nat × Nat) := []
      for n in [10, 100, 1000, 3000] do
        let inp := (mk n).toArray
        match search nfa inp 0 inp.size {} { budget := 200000000, fuel := 40 * n + 200 } {} with
        | .error a => line := line ++ s!" n={n}: {repr a};"
        | .ok (_, _, st) =>
          line := line ++ s!" n={n}: D={st.maxDepth} NT={st.maxNT} steps={st.steps};"
          pts := pts ++ [(n, st.maxDepth, st.maxNT)]
      IO.println line
      match pts.getLast?, pts[2]? with
      | some (n2, d2, t2), some (n1, d1, t1) =>
        if n2 > n1 then
          let sd : Nat := (d2 - d1) / (n2 - n1)
          let st : Nat := (t2 - t1) / (n2 - n1)
          IO.println s!"      slope per character (n {n1}→{n2}): D {d2 - d1}/{n2 - n1} ≈ {sd}, NT {t2 - t1}/{n2 - n1} ≈ {st}"
      | _, _ => pure ()

/-- `exhaust <loc> <maxTok> <alpha> <maxLen> <maxRuns>`: Determinismo `exhaust` over the world,
restarting with each found class set aside until a walk completes. -/
def exhaustCmd (args : List String) : IO Unit := do
  let loc := locOf (args.getD 0 "utf8")
  let k := (args.getD 1 "3").toNat!
  let alpha := if args.getD 2 "abn" == "abn" then [0x61, 0x62, 0x0A] else if args.getD 2 "" == "ab" then [0x61, 0x62]
    else [0x61, 0x62, 0x0A, 0xE9, 0x1F600, 0]
  let n := (args.getD 3 "3").toNat!
  let maxRuns := (args.getD 4 "10000000").toNat!
  let rej := args.getD 5 "" == "rejects"
  let w : WSpec := { loc, toks := coreTokens, maxTok := k, alpha, maxLen := n, apis := apisSmall,
                     setAside := [], rejectsCount := rej }
  IO.println s!"== exhaust: core tokens ≤ {k}, inputs ≤ {n} over {alpha}, calls {apisSmall.length}, locale {loc.name}{if rej then ", rejected patterns reported" else ""}"
  let _ ← residualExhaust w maxRuns 40
  pure ()

/-- `explore <loc> <maxTok> <maxLen> <seeds> <first>`: random timelines (SplitMix-mixed seeds). -/
def exploreCmd (args : List String) : IO Unit := do
  let loc := locOf (args.getD 0 "utf8")
  let k := (args.getD 1 "7").toNat!
  let n := (args.getD 2 "6").toNat!
  let seeds := (args.getD 3 "10000").toNat!
  let first := (args.getD 4 "0").toNat!
  let setAside := (args.drop 5)
  let w : WSpec := { loc, toks := coreTokens, maxTok := k, alpha := [0x61, 0x62, 0x0A], maxLen := n,
                     apis := apisFull, setAside }
  IO.println s!"== explore: core tokens ≤ {k}, inputs ≤ {n} over a b newline, {apisFull.length} calls, seeds {first}..{first + seeds - 1}, locale {loc.name}, set aside {setAside}"
  let mut found : List (String × Nat × String) := []
  let mut runs := 0
  for i in List.range seeds do
    runs := runs + 1
    -- SplitMix64 finalizer on the seed (consecutive seeds give unrelated first draws)
    let z0 := (first + i + 0x9E3779B97F4A7C15) % 2^64
    let z1 := ((z0 ^^^ (z0 >>> 30)) * 0xBF58476D1CE4E5B9) % 2^64
    let z2 := ((z1 ^^^ (z1 >>> 27)) * 0x94D049BB133111EB) % 2^64
    let z := z2 ^^^ (z2 >>> 31)
    let o := run w (Determinismo.Source.seeded z)
    if let some (p, d) := o.violation then
      let raw := ((p.splitOn "[").getD 1 "").toList
      let cls := String.ofList (raw.take (raw.length - 1))
      match found.find? (·.1 == cls) with
      | some _ => found := found.map fun (c, m, e) => if c == cls then (c, m + 1, if d.length < e.length then d else e) else (c, m, e)
      | none => found := found ++ [(cls, 1, d)]
  IO.println s!"  {runs} timelines"
  for (c, m, e) in found do IO.println s!"    [{c}] {m} timelines; shortest: {e}"
  if found.isEmpty then IO.println "    nothing"

/-- The report's programs: each deviation's examples, with both answers and its class. -/
def exampleQs : List (String × List Q) :=
  let q (api : Api) (p : String) (i : List Nat) : Q := { api, pat := cpsOf p, inp := i }
  let s := cpsOf
  [("R78 bytes", [q .find "." (s "é"), q .matches "é*" [], q .find "é+" (s "éé"), q .find "\\u00e9" (s "é"),
      q .find "\\xe9" (s "é"), q .seq "." [0x1F600], q .find "[^a]" (s "é"), q .find "." [0x85],
      q (.split 0) "" (s "é")]),
   ("RX range", [q .find "[a-é]" (s "b"), q .find "[ -\\xff]" (s "b"), q .find "[\\x80-\\xff]" (s "é")]),
   ("RX \\u", [q .find "\\u0141" (s "A"), q .find "\\u0100" [0]]),
   ("R79", [q .find "a$" (s "a\n"), q (.split 0) "$" (s "a\n")]),
   ("R80", [q .find "(a)?b" (s "b"), q .find "(a)|b" (s "b")]),
   ("R81", [q .seq "^a" (s "aa"), q .seq "a*" (s "b"), q .seq "\\b\\w" (s "ab cd"), q .seq "\\Ba" (s "aaa")]),
   ("R82", [q .matches "a|ab" (s "ab"), q .matches "a*?" (s "a")]),
   ("R83", [q .find "b" (s "a\u0000b"), q (.replace (s "y")) "x" (s "a\u0000b"),
      q (.replaceFirst (s "y")) "x" (s "a\u0000b"), q .replaceFn "a" (s "a\u0000b"), q (.split 0) "b" (s "a\u0000b")]),
   ("R84", [q (.replace (s "$12")) "(a)" (s "a"), q (.replace (s "$$")) "a" (s "a"), q (.replace (s "\\$")) "a" (s "a"),
      q (.replace (s "$&")) "a" (s "a"), q (.replace (s "$")) "a" (s "x"), q .replaceFn "(a)(b)" (s "ab"),
      q (.replace (s "$01")) "a" (s "a"), q (.replace (s "$2")) "(a)" (s "a")]),
   ("R85", [q (.replace (s "-")) "a*?" (s "aa"), q (.split 0) "b?|a" (s "ab")]),
   ("R18", [q .find "(?i)a" (s "A"), q .find "(?<=a)b" (s "ab"), q .find "(?<n>a)" (s "a"), q .find "(?>a)" (s "a"),
      q .find "a*+" (s "aa")]),
   ("RX possessive", [q .find "a++a" (s "aaa"), q .find "a{2}+" (s "aaaa"), q .find "a?+a" (s "a"),
      q .matches "\\d*+\\d" (s "12")]),
   ("RX quantified assertion", [q .find "^*a" (s "a"), q .find "\\b+a" (s "a"), q .find "(?=a)*a" (s "a"), q .find "a$?" (s "a")]),
   ("RX backref", [q .find "\\1" (s "a"), q .find "(a)\\10" (s "aa0"), q .find "\\1(a)" (s "a"), q .find "(a\\1)" (s "a")]),
   ("RX posix bracket", [q .find "[[:alpha:]]" (s "x"), q .find "[[:alpha:]]" (s ":"), q .find "[[a]]" (s "a"),
      q .find "[a-z&&[^b]]" (s "c"), q .find "[[:foo:]]" (s "f"), q .find "[[.a.]]" (s ".")]),
   ("RX ] first", [q .find "[]a]" (s "a"), q .find "[^]" (s "\n"), q .find "[]" (s "a")]),
   ("RX escapes", [q .find "\\cJ" (s "\n"), q .find "\\cJ" (s "J"), q .find "\\v" (s "\n"), q .find "\\Aa" (s "a"),
      q .find "a\\z" (s "a"), q .find "a\\Z" (s "a"), q .find "\\Q.\\E" (s "."), q .find "\\e" (s "e"),
      q .find "\\a" (s "a"), q .find "\\h" (s " "), q .find "\\R" (s "\n"), q .find "\\pL" (s "x"),
      q .find "\\p{L}" (s "x"), q .find "\\0" (s "a"), q .find "\\01" [1], q .find "[\\b]" (s "a"),
      q .find "\\y" (s "y"), q .find "\\x{41}" (s "A"), q .find "\\G" (s "G")]),
   ("RX class range", [q .find "[\\w-a]" (s "-"), q .find "[\\s-]" (s "-")]),
   ("RX brace", [q .find "{2}" (s "x"), q .find "a{,2}" (s "a{,2}")]),
   ("RX lookahead at start", [q .find "a(?=\\b)" (s "ab"), q .find "foo(?=\\bbar)" (s "foobar"), q .find "a(?=^b)" (s "ab"),
      q .find "a(?!\\B)" (s "ab"), q .seq "a(?=\\b)" (s "abab")]),
   ("RX lookahead not-null (inside R85)", [q (.replace (s "-")) "|b(?=a*)" (s "bc")]),
   ("RX limits and leniency", [q .find "a{99999}" (s "a"), q .find "[é-a]" (s "a"), q .find "a{2}{3}" (s "aaaaaa"), q .find "a**" (s "aa")])]

def examples (loc : Loc) : IO Unit := do
  IO.println s!"== the report's programs (locale {loc.name}): Clojure's answer, the replica's, the class"
  for (name, qs) in exampleQs do
    IO.println s!"  {name}"
    for q in qs do
      let (v, j, c) := verdict loc {} q
      let cls := match v with
        | .differ => (classify loc q).getD (trigger q)
        | .rejects e => s!"jank rejects: {rejectShape q.pat e}"
        | .acceptsInvalid e => s!"Java rejects ({e})"
        | .agree => "agree"
        | .skip w => s!"not compared ({w})"
      IO.println s!"    {q.program}: Clojure {CV.show c}, jank {V.show j}  [{cls}]"

def main (args : List String) : IO UInt32 := do
  match args with
  | "grammar" :: rest => grammar rest
  | ["round2", l] => R2.rerun (locOf l)
  | ["syntax", l] => syntaxTable (locOf l)
  | ["depth"] => depthTable
  | ["examples", l] => examples (locOf l)
  | "exhaust" :: rest => exhaustCmd rest
  | "explore" :: rest => exploreCmd rest
  | _ => IO.println "usage: jank3-regex grammar|round2|syntax|depth …"
  return 0
