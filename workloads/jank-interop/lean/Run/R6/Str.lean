import Jank.R6.Str.Search

/-! Round 6, strings (area W): the complete walks of `Jank.R6.Str.Search`.

`lake exe jank6-str [n]`: walk A over texts of at most `n` code points (default 3; 4 is the recorded
run), then walks B–F at their fixed bounds. -/

open Jank.Str Jank.R6.Str

def pct (a b : Nat) : String := if b == 0 then "-" else s!"{a * 1000 / b / 10}.{a * 1000 / b % 10}%"

def runA (n : Nat) : IO Unit := do
  let texts := (textsOver alphabet7 n).length
  IO.println s!"== A. index functions: every text of at most {n} code points over a - é € Ａ 😀 U+0301 ({texts} texts), complete"
  IO.println "   op | cases | jank≠Clojure | byte indexing | code-point chars | separate | code-point design ≠ Clojure (BMP-only texts) | fix model: cases, ≠ Clojure (BMP-only, ASCII-only) | invalid UTF-8 results today, with R52a"
  for (k, t) in walkA n do
    IO.println s!"   {k} | {t.cases} | {t.differ} ({pct t.differ t.cases}) | {t.byteIndexing} | {t.codePointChars} | {t.separate} | {t.cpResidual} ({t.cpResidualBmp}) | {t.fixedCases}, {t.fixedDiffer} ({t.fixedDifferBmp}, {t.fixedDifferAscii}) | {t.invalid}, {if k.startsWith "subs" then toString t.invalidFixed else "-"}"
    unless t.firstCase.isEmpty do IO.println s!"      first: {t.firstCase}"

def runB : IO Unit := do
  let all := byteStrings 4
  let mut ubOld := 0
  let mut errOld := 0
  let mut ubNew := 0
  let mut errNew := 0
  let mut first := ""
  for s in all do
    let o := jSeq s
    let f := jSeqFixed s
    if isUb o then
      ubOld := ubOld + 1
      if first.isEmpty then first := s!"{s}: today {o.show}, R54a {f.show}"
    if isErr o then errOld := errOld + 1
    if isUb f then ubNew := ubNew + 1
    if isErr f then errNew := errNew + 1
  IO.println s!"== B. cut strings: every byte string of at most 4 bytes over {cutBytes.length} bytes ({all.length} strings), complete"
  IO.println s!"   seq walk past the end (UB): today {ubOld}, with R54a {ubNew}; \"Invalid UTF-8 string.\": today {errOld}, with R54a {errNew}"
  IO.println s!"   first: {first}"

def runC : IO Unit := do
  let ts := textsOver wsAlphabet 4
  let mut n := 0
  let mut old := 0
  let mut new := 0
  let mut first := ""
  for s in ts do
    let js := jstr s
    let cs := cstr s
    for (name, j, f, cl) in [("trim", jTrim js, jTrimFixed js, cTrim cs), ("triml", jTriml js, jTrimlFixed js, cTriml cs),
        ("trimr", jTrimr js, jTrimrFixed js, cTrimr cs), ("blank?", jBlank js, jBlankFixed js, cBlank cs)] do
      n := n + 1
      if !j.agrees cl then
        old := old + 1
        if first.isEmpty then first := s!"({name} {lit s}): Clojure {cl.show}, jank {j.show}"
      if !f.agrees cl then new := new + 1
  IO.println s!"== C. whitespace: trim/triml/trimr/blank? on every text of at most 4 code points over space a U+001F U+2003 U+00A0 U+3000 é U+2028 ({ts.length} texts), complete"
  IO.println s!"   {n} cases: jank ≠ Clojure {old}; R59a/R59b ≠ Clojure {new}"
  IO.println s!"   first: {first}"

def runD : IO Unit := do
  let ts := textsOver capAlphabet 3
  let mut old := 0
  let mut new := 0
  let mut firstOld := ""
  let mut residual : List String := []
  for s in ts do
    let js := jstr s
    let cl := cCapitalize (cstr s)
    let j := jCapitalize .utf8 js
    let f := jCapitalizeFixed .utf8 js
    if !j.agrees cl then
      old := old + 1
      if firstOld.isEmpty then firstOld := s!"(capitalize {lit s}): Clojure {cl.show}, jank {j.show}"
    if !f.agrees cl then
      new := new + 1
      if residual.length < 4 then residual := residual ++ [s!"(capitalize {lit s}): Clojure {cl.show}, R61a {f.show}"]
  let residualBad := ts.filter fun s =>
    !(jCapitalizeFixed .utf8 (jstr s)).agrees (cCapitalize (cstr s)) && !(s.contains 0xDF || s.contains 0x3A3)
  IO.println s!"== D. capitalize: every text of at most 3 code points over a A é É ß Σ σ ({ts.length} texts), UTF-8 locale, complete"
  IO.println s!"   jank ≠ Clojure {old}; R61a ≠ Clojure {new}, all holding ß or Σ (R60's case mapping): {residualBad.isEmpty}"
  IO.println s!"   first: {firstOld}"
  for r in residual do IO.println s!"   R61a residual: {r}"

def runE (n : Nat) : IO Unit := do
  let ts := textsOver alphabet7 n
  let mut c1 := 0
  let mut bad1 := 0
  let mut c2 := 0
  let mut bad2 := 0
  let mut firstBad := ""
  for s in ts do
    let idx := indexRange (jstr s).length
    for i in idx do
      c1 := c1 + 1
      if (jSubs1 s i).agrees (cSubs1 s i) != subs1Cond s i then bad1 := bad1 + 1
      for j in idx do
        c2 := c2 + 1
        let ag := (jSubs (jstr s) i j).agrees (cSubs (cstr s) i j)
        if ag != subs2Cond s i j then
          bad2 := bad2 + 1
          if firstBad.isEmpty then firstBad := s!"(subs {lit s} {i} {j}) agrees={ag}"
  IO.println s!"== E. subs agreement conditions over walk A's texts (at most {n} code points), complete"
  IO.println s!"   (subs s i): {c1} cases, {bad1} where agreement ≠ (i < 0 ∨ i ≤ asciiPrefix ∨ i > bytes) [proved: subs1_agrees_iff]"
  IO.println s!"   (subs s i j): {c2} cases, {bad2} where agreement ≠ (i < 0 ∨ j < i ∨ j > bytes ∨ j ≤ asciiPrefix ∨ (i = j ∧ j ≤ units)) {firstBad}"

def runF : IO Unit := do
  let ts := textsOver alphabet7 2
  let mut n := 0
  let mut signOld := 0
  let mut valOld := 0
  let mut valNew := 0
  let mut firstSign := ""
  for a in ts do
    for b in ts do
      n := n + 1
      let cl := javaCompare (cstr a) (cstr b)
      let j := jankCompare (jstr a) (jstr b)
      let f := jankCompareFixed (jstr a) (jstr b)
      if sign cl != sign j then
        signOld := signOld + 1
        if firstSign.isEmpty then firstSign := s!"(compare {lit a} {lit b}): Clojure {cl}, jank {j}"
      if cl != j then valOld := valOld + 1
      if cl != f then valNew := valNew + 1
  let mut cn := 0
  let mut cOld := 0
  let mut cNew := 0
  for a in alphabet7.filter (· < 0x10000) do
    for b in alphabet7.filter (· < 0x10000) do
      cn := cn + 1
      if jankCompare (utf8 a) (utf8 b) != (a : Int) - b then cOld := cOld + 1
      if jankCharCompareFixed (utf8 a) (utf8 b) != (a : Int) - b then cNew := cNew + 1
  IO.println s!"== F. compare: every pair of texts of at most 2 code points over walk A's alphabet ({ts.length}² = {n} pairs), complete"
  IO.println s!"   strings: sign differs {signOld}, value differs {valOld} (StrA6-1), R57a value differs {valNew}"
  IO.println s!"   first sign difference: {firstSign}"
  IO.println s!"   characters (BMP pairs, {cn}): value differs {cOld}, R57b value differs {cNew}"

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  runA n
  runB
  runC
  runD
  runE n
  runF
