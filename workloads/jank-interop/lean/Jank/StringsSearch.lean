import Determinismo
import Jank.StrModel
import Jank.PrintModel
import Jank.RegexModel
import Jank.Strings.Object

/-! Round 2, strings, characters, printing and regexes: the searches of this area. -/

namespace Jank.StringsSearch

open Determinismo

def describe (c : Counterexample) : String :=
  s!"{c.property} after {c.runs} timelines, {c.taken.size} decisions: {c.detail}"

def indent (s : String) : String := (s.splitOn "\n").map ("    " ++ ·) |> "\n".intercalate

/-- explore, shrink, exhaust, shrink: as the first round's `report`. -/
def report (name : String) (run : Source → Ended) (seeds : Nat) (maxRuns : Nat) : IO Unit := do
  IO.println s!"== {name}"
  match explore run seeds with
  | some c =>
    IO.println s!"  explore ({seeds} seeds): {describe c}"
    let s := shrink run c
    IO.println s!"  shrunk to {s.taken.size} decisions: {s.detail}"
    IO.println s!"  tape:\n{indent (tape s.taken)}"
  | none => IO.println s!"  explore ({seeds} seeds): nothing"
  match exhaust run maxRuns with
  | .found c =>
    IO.println s!"  exhaust: found after {c.runs} timelines: {c.detail}"
    let s := shrink run c
    IO.println s!"  exhaust's counterexample shrunk to {s.taken.size} decisions: {s.detail}"
    IO.println s!"  tape:\n{indent (tape s.taken)}"
  | .complete n => IO.println s!"  exhaust: complete, {n} timelines, nothing"
  | .stopped n => IO.println s!"  exhaust: stopped at {n} timelines, nothing"

section
open Jank.Str

def strings : IO Unit := do
  report "strings: every operation, texts ≤ 3 code points, both locales" Jank.Str.run 3000 200000
  -- The full table: per operation, how many questions deviate, and the shortest ones.
  let cases := allCases 3
  IO.println s!"  table: {cases.length} questions (texts ≤ 3 code points over {alphabet.length} code points; compare: ≤ 2 × ≤ 2)"
  let names := (cases.map (·.op.name)).eraseDups
  let mut total := 0
  for name in names do
    for loc in [Locale.utf8, Locale.c] do
      let qs := cases.filter fun c => c.op.name == name && c.loc == loc
      if qs.isEmpty then continue
      let bad := qs.filter fun c => let (j, cl) := c.eval; !j.agrees cl
      total := total + bad.length
      IO.println s!"  {name} [{loc.name}]: {bad.length} of {qs.length} deviate"
      let sorted := (bad.toArray.qsort fun a b => a.program.length < b.program.length).toList
      for c in sorted.take 3 do
        let (j, cl) := c.eval
        IO.println s!"      {c.program}: Clojure {cl.show}, jank {j.show}"
  IO.println s!"  total: {total} deviating questions"
  -- Written by hand.
  IO.println "  by hand:"
  let hand : List Case := [
    { loc := .utf8, op := .count, s := [0xE9] },
    { loc := .utf8, op := .subs2 0 1, s := [0x61, 0xE9] },
    { loc := .utf8, op := .seq, s := [0x61, 0xE9] },
    { loc := .utf8, op := .compare, s := [0xFF21], t := [0x1F600] },
    { loc := .utf8, op := .upper, s := [0xDF] },
    { loc := .c, op := .upper, s := [0xE9] },
    { loc := .utf8, op := .lower, s := [0x61, 0x3A3] },
    { loc := .utf8, op := .trim, s := [0x2003, 0x61] },
    { loc := .utf8, op := .blank, s := [0x1F] },
    { loc := .utf8, op := .seqSelfEq, s := [0xE9] },
    { loc := .utf8, op := .seqHashVec, s := [0x61] },
    { loc := .utf8, op := .indexOf [0x61] none, s := [0xE9, 0x61] },
    { loc := .utf8, op := .indexOf [0x61] (some (-1)), s := [0x61] },
    { loc := .utf8, op := .lastIndexOf [0x61] (some (-1)), s := [0x61, 0x61] },
    { loc := .utf8, op := .capitalize, s := [0xC9, 0x61] },
    { loc := .c, op := .capitalize, s := [0xC9, 0x61] } ]
  for c in hand do
    let (j, cl) := c.eval
    IO.println s!"    {c.program} [{c.loc.name}]: Clojure {cl.show}, jank {j.show}"
  -- A seq whose last character is cut short.
  IO.println s!"    (seq (subs \"aé\" 0 2)): jank {(jSeq [0x61, 0xC3]).show}"
  -- (char n) and "\uXXXX" under both locales.
  for n in [(-1 : Int), 0x61, 0xE9, 0xD800, 0xFFFF, 0x10000, 0x1F600, 0x110000, -2147483648, -4294967296, -4294967231] do
    IO.println s!"    (char {n}): Clojure {(cChar n).show}, jank UTF-8 {(jChar .utf8 n).show}, jank C {(jChar .c n).show}"
  for cp in [0x61, 0xE9, 0x20AC, 0x1F600] do
    let lit := if cp < 0x10000 then s!"\"\\u{hex4 cp}\"" else
      s!"\"\\u{hex4 (utf16 cp).head!}\\u{hex4 (utf16 cp).getLast!}\""
    IO.println s!"    {lit}: Clojure {showBytes (utf8 cp)}, jank UTF-8 {(jUnescape .utf8 cp).show}, jank C {(jUnescape .c cp).show}"
  for (ch, label) in [(utf8 0x61, "\\a"), (utf8 0xE9, "\\é"), ([0xC3], "(nth \"é\" 0)")] do
    IO.println s!"    (int {label}): jank UTF-8 {(jInt .utf8 ch).show}, jank C {(jInt .c ch).show}"

end

section
open Jank.Print

def printing : IO Unit := do
  IO.println "== printing: doubles (str and pr-str)"
  let digitsSet : List Nat := [1, 2, 15, 123, 1234567, 12345678, 123456789012345]
  let exps : List Int := (List.range 41).map fun (i : Nat) => (i : Int) - 18
  let ds := [false, true].flatMap fun neg => digitsSet.flatMap fun dg => exps.map fun e => ({ neg, digits := dg, exp := e } : Dbl)
  let bad := ds.filter fun d => jankDouble d != javaDouble d
  IO.println s!"  {bad.length} of {ds.length} doubles print differently (digits {digitsSet}, exponents -18..22, both signs)"
  let pos := ds.filter (!·.neg)
  -- Where they agree: by scientific exponent.
  for e in (List.range 30).map (fun (i : Nat) => (i : Int) - 8) do
    let at_ := pos.filter (·.sciExp == e)
    let agree := at_.filter fun d => jankDouble d == javaDouble d
    if !at_.isEmpty then
      IO.println s!"    magnitude 1e{e}: {agree.length} of {at_.length} agree, e.g. {at_.head!.code}: Clojure \"{javaDouble at_.head!}\", jank \"{jankDouble at_.head!}\""
  for d in [({ neg := false, digits := 1, exp := 5 } : Dbl), ⟨false, 3, 6⟩, ⟨false, 1, 7⟩, ⟨false, 123456789, 0⟩,
            ⟨false, 1, -4⟩, ⟨false, 15, -5⟩, ⟨false, 1, 21⟩, ⟨false, 1, 0⟩, ⟨false, 12345, -2⟩, ⟨false, 0, 0⟩, ⟨true, 0, 0⟩] do
    IO.println s!"    (str {d.code}): Clojure \"{javaDouble d}\", jank \"{jankDouble d}\""
  -- Readability: every jank double text reads back as the same decimal (both readers accept
  -- `1e+05`), so only the text differs.
  IO.println "== printing: strings in pr-str (each code point 0..127 and é, € alone)"
  let cps := (List.range 128) ++ [0xE9, 0x20AC]
  let sbad := cps.filter fun c => jankPrStr [c] != cljPrStr [c]
  IO.println s!"  {sbad.length} of {cps.length} differ:"
  for c in sbad do
    IO.println s!"    (pr-str (str (char {c}))): Clojure {repr (bytesToString (cljPrStr [c]))}, jank {repr (bytesToString (jankPrStr [c]))}"
  IO.println "== printing: str, pr-str, print-str of values of depth ≤ 2"
  let vs := values
  let strBad := vs.filter fun v => jankStr v != cljStr v
  IO.println s!"  str: {strBad.length} of {vs.length} values differ, e.g.:"
  for v in (strBad.toArray.qsort (fun a b => (codeString a).length < (codeString b).length)).toList.take 6 do
    IO.println s!"    (str {codeString v}): Clojure {repr (cljStr v)}, jank {repr (jankStr v)}"
  let printBad := vs.filter fun v => jankStr v != cljPrintStr v && !(match v with | .nil => true | _ => false)
  IO.println s!"  print-str: {printBad.length} of {vs.length} values differ"
  IO.println "== printing: regex patterns in pr-str (patterns over a, \", \\, Q, E up to 3 characters)"
  let chars := ['a', '"', '\\', 'Q', 'E']
  let rec pats : Nat → List (List Char)
    | 0 => [[]]
    | n + 1 => pats n ++ ((pats n).filter (·.length == n)).flatMap fun p => chars.map (p ++ [·])
  let ps := pats 3
  let rbad := ps.filter fun p => jankRegexCode p != cljRegexCode p
  -- A pattern ending in an odd backslash is invalid in both engines: left out.
  let valid := ps.filter fun p => (p.reverse.takeWhile (· == '\\')).length % 2 == 0
  let rtrip := valid.filter fun p => (readRegexLiteral (jankRegexCode p)).isNone
  let ctrip := valid.filter fun p => (readRegexLiteral (cljRegexCode p)).isNone
  IO.println s!"  {rbad.length} of {ps.length} print differently; of the {valid.length} valid patterns, jank's text is not one regex literal for {rtrip.length}, Clojure's for {ctrip.length}"
  for p in (rbad.toArray.qsort (fun a b => a.length < b.length)).toList.take 3 do
    IO.println s!"    (pr-str (re-pattern {repr (String.ofList p)})): Clojure {cljRegexCode p}, jank {jankRegexCode p}"
  IO.println "== printing: BigDecimal (str; pr-str adds M on both sides)"
  for d in [({ unscaled := 1, scale := 0 } : Dec), ⟨150, 2⟩, ⟨10, 1⟩, ⟨-5, 0⟩, ⟨15, 1⟩, ⟨0, 2⟩] do
    IO.println s!"    BigDecimal {d.unscaled}×10^-{d.scale}: Clojure \"{javaDec d}\", jank \"{jankDec d}\""

end

section
open Jank.Regex

def regexes : IO Unit := do
  report "regex: re-find, re-seq, re-matches (patterns of depth ≤ 2, inputs ≤ 3)" Jank.Regex.run 3000 300000
  let cases := allCases
  IO.println s!"  table: {cases.length} questions ({patterns1.length + patterns2.length} patterns × {(inputs 3).length} inputs × 3 functions)"
  for api in [Api.find, .seq, .matches] do
    let qs := cases.filter (·.api == api)
    let bad := qs.filter fun c => let (j, cl) := c.eval; !j.agrees cl
    IO.println s!"  {api.name}: {bad.length} of {qs.length} deviate"
    let sorted := (bad.toArray.qsort fun a b => a.program.length < b.program.length).toList
    for c in sorted.take 4 do
      let (j, cl) := c.eval
      IO.println s!"      {c.program}: Clojure {cl.show}, jank {j.show}"
  -- One shortest example per cause.
  IO.println "  by cause:"
  let hand : List Case := [
    { api := .find, re := .any, input := [0xE9] },
    { api := .matches, re := .cls false [0xE9], input := [0xE9] },
    { api := .find, re := .cat (.lit 0x61) .eol, input := [0x61, 0x0A] },
    { api := .find, re := .cat (.opt (.group (.lit 0x61))) (.lit 0x62), input := [0x62] },
    { api := .seq, re := .cat .bol (.lit 0x61), input := [0x61, 0x61] },
    { api := .seq, re := .star (.lit 0x61) false, input := [0x62] },
    { api := .matches, re := .alt (.lit 0x61) (.cat (.lit 0x61) (.lit 0x62)), input := [0x61, 0x62] },
    { api := .matches, re := .star (.lit 0x61) true, input := [0x61] },
    { api := .find, re := .lit 0x62, input := [0x61, 0x00, 0x62] },
    { api := .matches, re := .lit 0x61, input := [0x61, 0x00, 0x62] } ]
  for c in hand do
    let (j, cl) := c.eval
    IO.println s!"    {c.program}: Clojure {cl.show}, jank {j.show}"
  IO.println "== regex: replacement templates (clojure.string/replace s #\"(a)\" template), one match, 1 group"
  for t in ["$1", "$0", "$&", "$$", "\\$", "$12", "$x", "$", "x\\y", "$1$1"] do
    let e := ecmaTemplate 1 t.toList
    let j := javaTemplate 1 t.toList
    IO.println s!"    {repr t}: Clojure {match j with | .ok p => repr (expand p) | .error w => s!"throws ({w})"}, jank {repr (expand e)}"

end


section
open Jank.Strings

def bytesStr (b : Bytes) : String := (String.fromUTF8? ⟨b.toArray⟩).map (·.quote) |>.getD s!"<bytes {b}>"

def objShow : Except String Obj → String
  | .error e => s!"throws ({e})"
  | .ok .nil => "nil"
  | .ok (.str b) => bytesStr b
  | .ok (.kw ns n) => if ns.isEmpty then s!":{bytesStr n}" else s!":{bytesStr ns}/{bytesStr n}"
  | .ok (.sym ns n) => if ns.isEmpty then s!"sym {bytesStr n}" else s!"sym {bytesStr ns}/{bytesStr n}"
  | .ok (.chr b) => s!"\\{bytesStr b}"
  | .ok o => reprStr o

def optStr : Option (List Nat) → String
  | none => "nil"
  | some cps => bytesStr (encodeAll cps)

def argCode : Option Obj → String
  | none => ""
  | some .nil => "nil "
  | some (.str b) => bytesStr b ++ " "
  | some _ => "? "

/-- B32–B34: keywords and symbols built from strings; `char` past its range check; `=` on
string seqs at 7135b7708 (`is_sequential`). -/
def extras : IO Unit := do
  IO.println "== keywords from a namespace and a name (core.cpp keyword 521 → context.cpp intern_keyword 561/584/588 → symbol.cpp separate 8)"
  let nss : List (Option Obj) := [some .nil, some (.str []), some (.str (bs "a")), some (.str (bs "a/b"))]
  let names : List Bytes := [bs "c", bs "b/c", bs "a/"]
  let cljKw (ns : Option Obj) (n : Bytes) : Option Clj.V :=
    match ns with
    | some (.str nb) => do pure (.kw (some (← decodeUtf8 nb)) (← decodeUtf8 n))
    | _ => do pure (.kw none (← decodeUtf8 n))
  let kws := nss.flatMap fun ns => names.map fun n => (ns, n)
  let mut nsBad := 0
  for (ns, n) in kws do
    let j := jankKeyword ns (.str n)
    let jns := (j >>= coreNamespace) |> objShow
    let cns := match cljKw ns n with
      | some (.kw o _) => optStr o
      | _ => "?"
    let jname := match j with | .ok (.kw _ nm) => bytesStr nm | _ => "?"
    let cname := bytesStr n
    if jns != cns || jname != cname then
      nsBad := nsBad + 1
      IO.println s!"    (keyword {argCode ns}{bytesStr n}): namespace Clojure {cns}, jank {jns}; name Clojure {cname}, jank {jname}"
  IO.println s!"  {nsBad} of {kws.length} keywords have another namespace or name than Clojure's"
  let mut eqBad := 0
  let mut shown := 0
  for (ns1, n1) in kws do
    for (ns2, n2) in kws do
      let j := match jankKeyword ns1 (.str n1), jankKeyword ns2 (.str n2) with
        | .ok a, .ok b => jankEqual a b |>.toOption |>.getD false
        | _, _ => false
      let c := match cljKw ns1 n1, cljKw ns2 n2 with
        | some a, some b => Clj.equiv a b
        | _, _ => false
      if j != c then
        eqBad := eqBad + 1
        if shown < 4 then
          shown := shown + 1
          IO.println s!"    (= (keyword {argCode ns1}{bytesStr n1}) (keyword {argCode ns2}{bytesStr n2})): Clojure {c}, jank {j}"
  IO.println s!"  {eqBad} of {kws.length * kws.length} keyword pairs: `=` differs from Clojure's"
  IO.println "== symbols from strings (core.jank symbol 517 → core.cpp to_unqualified_symbol 84 / to_qualified_symbol 118 → symbol.cpp separate 8)"
  let mut symBad := 0
  let mut symAll := 0
  for (ns, n) in kws do
    symAll := symAll + 1
    let j := jankSymbol ns (.str n)
    let jns := (j >>= coreNamespace) |> objShow
    -- Clojure: (symbol ns name) = Symbol.intern(ns, name), no splitting; ns nil → no namespace.
    let cns := match ns with | some (.str nb) => bytesStr nb | _ => "nil"
    let jname := match j with | .ok (.sym _ nm) => bytesStr nm | _ => "?"
    if jns != cns || jname != bytesStr n then
      symBad := symBad + 1
      IO.println s!"    (symbol {argCode ns}{bytesStr n}): namespace Clojure {cns}, jank {jns}; name Clojure {bytesStr n}, jank {jname}"
  for n in [bs "a/b", bs "/a", bs "/", bs "a/", bs "a"] do
    symAll := symAll + 1
    let j := jankSymbol none (.str n)
    let jns := (j >>= coreNamespace) |> objShow
    let cv := Clj.symbolIntern ((decodeUtf8 n).getD [])
    let (cns, cname) := match cv with
      | .sym o nm => (optStr o, bytesStr (encodeAll nm))
      | _ => ("?", "?")
    let jname := match j with | .ok (.sym _ nm) => bytesStr nm | _ => "?"
    if jns != cns || jname != cname then
      symBad := symBad + 1
      IO.println s!"    (symbol {bytesStr n}): namespace Clojure {cns}, jank {jns}; name Clojure {cname}, jank {jname}"
  IO.println s!"  {symBad} of {symAll} symbols differ"
  IO.println "== (char n) past the range check (core.cpp to_char 1311 → character.cpp 57 → utf8.cpp to_char 170/178)"
  for n in [(-1 : Int), -2147483648, -4294967296, -4294967295, -4294967231, -4294967296 + 0xE9, -8589934592 + 0x1F600] do
    let j := characterOfI64 n |> objShow
    IO.println s!"    (char {n}): Clojure throws (Value out of range for char), jank (UTF-8 locale) {j}"
  IO.println "== = on string seqs, lists, strings and nil (seq_ext.hpp equal 13; seq.cpp sequence_equal 881; 7135b7708 requires is_sequential)"
  let e := encodeAll [0xE9]
  let pairs : List (String × Obj × Obj) := [
    ("(= (seq \"a\") \"a\")", .sseq (bs "a") 0, .str (bs "a")),
    ("(= '(\\a) \"a\")", .list [.chr (bs "a")], .str (bs "a")),
    ("(= [] nil)", .vec [], .nil),
    ("(= [\\a] \"a\")", .vec [.chr (bs "a")], .str (bs "a")),
    ("(let [x (seq \"é\")] (= x x))", .sseq e 0, .sseq e 0),
    ("(= (seq \"é\") [\\é])", .sseq e 0, .vec [.chr e]),
    ("(= [\\é] (seq \"é\"))", .vec [.chr e], .sseq e 0),
    ("(= (seq \"a\") [\\a])", .sseq (bs "a") 0, .vec [.chr (bs "a")]) ]
  for (prog, a, b) in pairs do
    let j := (jankEqual a b).toOption
    let c := match Clj.ofObj a, Clj.ofObj b with
      | some x, some y => some (Clj.equiv x y)
      | _, _ => none
    let hashes := if j == some true then s!"; jank hashes {jankHash .signed a} vs {jankHash .signed b}" else ""
    IO.println s!"    {prog}: Clojure {c.map toString |>.getD "?"}, jank {j.map toString |>.getD "throws"}{hashes}"
  IO.println s!"    (empty (seq \"ab\")): jank {reprStr sseqEmpty} (persistent_string_sequence.cpp empty 157, new); Clojure ()"

end

section
open Jank.Regex

/-- B35: `clojure.string/replace` and `split` with a pattern: std::regex_iterator after an
empty match. -/
def iteration : IO Unit := do
  report "regex: clojure.string/replace and split with a pattern (std::regex_iterator vs Matcher.find)" Jank.Regex.iterRun 3000 300000
  let cases := iterCases
  let bad := cases.filter fun c => let (j, cl) := c.eval; !j.agrees cl
  IO.println s!"  table: {bad.length} of {cases.length} questions deviate (patterns of depth ≤ 2 without ^, inputs ≤ 3 over a b \\n é; replace \"-\", split 0/-1/2)"
  let ascii := cases.filter asciiOnly
  let abad := ascii.filter fun c => let (j, cl) := c.eval; !j.agrees cl
  IO.println s!"  ASCII letters only, no $ (only the iteration rule left): {abad.length} of {ascii.length} deviate"
  let sorted := (abad.toArray.qsort fun a b => a.program.length < b.program.length).toList
  for c in sorted.take 6 do
    let (j, cl) := c.eval
    IO.println s!"    {c.program}: Clojure {cl.show}, jank {j.show}"
  -- With Java's rule (one past an empty match, no not-null retry) jank's replace would agree.
  let reps := ascii.filter fun c => match c.api with | .replace _ => true | _ => false
  let fixed := reps.filter fun c => match c.api with
    | .replace t => jankReplaceJavaIter c.re t c.input != cljReplace c.re t c.input
    | _ => false
  IO.println s!"  replace with Matcher.find's rule instead of regex_iterator's, ASCII: {fixed.length} of {reps.length} still differ"
  for c in [({ api := .replace "-", re := .star (.lit 0x61) true, input := [0x61, 0x61] } : IterCase),
            { api := .split 0, re := .alt (.opt (.lit 0x62)) (.lit 0x61), input := [0x61, 0x62] },
            { api := .replace "-", re := .star (.lit 0x61) false, input := [0x62, 0x61, 0x61] }] do
    let (j, cl) := c.eval
    IO.println s!"    {c.program}: Clojure {cl.show}, jank {j.show}"

end

def searches (args : List String) : IO Unit := do
  let only := args.head?
  if only.isNone || only == some "strings" then strings
  if only.isNone || only == some "printing" then printing
  if only.isNone || only == some "regex" then regexes
  if only.isNone || only == some "extras" then extras
  if only.isNone || only == some "iteration" then iteration

end Jank.StringsSearch
