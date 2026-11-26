import Jank.R7.Native.Brief
import Jank.R7.Native.Unary
import Jank.R7.Native.Nan
import Jank.R7.Native.Loop
import Jank.R7.Native.StrCase
import Jank.R7.Native.StrAbbrev
import Jank.R5.Regex.Compare5

/-! Round 7 driver, native values and strings (`jank7-native <part>`): `brief`, `unary`, `nan`,
`case`, `abbrev`, `regex`, or `all`. -/

open Jank.R6.Native Jank.R7.Native

def tally (l : List (String × Nat)) (k : String) : List (String × Nat) :=
  if l.any (·.1 == k) then l.map (fun (a, n) => if a == k then (a, n + 1) else (a, n)) else l ++ [(k, 1)]

open Jank.Str in
def briefPart : IO Unit := do
  IO.println "== brief: the real jank's observations on round 6's string model"
  IO.println s!"  (index-of \"a\" \"a\" -1): model {(jIndexOf [0x61] [0x61] (-1)).show}, Clojure {(Jank.R6.Str.cIndexOf' [0x61] [0x61] (-1)).show}; real jank nil"
  IO.println s!"  (index-of \"a\" \"\" 5): model {(jIndexOf [0x61] [] 5).show}, Clojure {(Jank.R6.Str.cIndexOf' [0x61] [] 5).show}; real jank nil"
  IO.println s!"  (last-index-of \"aa\" \"a\" -1): model {(jLastIndexOf [0x61, 0x61] [0x61] (-1)).show}, Clojure {(Jank.R6.Str.cLastIndexOf' [0x61, 0x61] [0x61] (-1)).show}; real jank 1"
  IO.println s!"  (upper-case (subs \"é\" 1)): round 6 {(Jank.R6.Str.jUpper6 .utf8 [0xA9]).show}, round 7 {(Brief.jUpper7 .utf8 [0xA9]).show}; real jank throws \"wstring_convert::from_bytes\""
  let q : Jank.R3.Regex.Q := { api := .split 0, pat := [], inp := [0x61, 0xE9, 0x62] }
  let (_, j, c) := Jank.R5.Regex.verdict5 .utf8 {} q
  IO.println s!"  (split \"aéb\" #\"\"): round 3's replica {Jank.R3.Regex.V.show j}, Clojure {Jank.R3.Regex.CV.show c}; real jank: é split into its two bytes"
  let q2 : Jank.R3.Regex.Q := { api := .split 0, pat := [], inp := [0xE9] }
  let (_, j2, c2) := Jank.R5.Regex.verdict5 .utf8 {} q2
  IO.println s!"  (split \"é\" #\"\"): replica {Jank.R3.Regex.V.show j2}, Clojure {Jank.R3.Regex.CV.show c2}"

def unaryPart : IO Unit := do
  IO.println "== unary: zero? abs inc dec × round 6's 45 sources × {inlined, fn value}, complete"
  let cases := unaryCases
  let mut total := 0
  let mut devs := 0
  let mut byCause : List (String × Nat) := []
  let mut examples : Array String := #[]
  for c in cases do
    total := total + 1
    if c.deviates {} then
      devs := devs + 1
      let j := (c.jank {}).seen
      let srcFixed := !c.deviates srcSw
      let cause :=
        if srcFixed then "the source's own value (P6 hash, P7 float, R122 bytes)"
        else match c.a with
          | .charA _ => s!"char native is a number to math.hpp (V64's cause) [{c.op.sym}]"
          | .pred _ => s!"bool native is a number to math.hpp (R33) [{c.op.sym}]"
          | .floatA _ => s!"float element computes in binary32 (V63's cause) [{c.op.sym}]"
          | .dparam _ | .dlit _ => s!"abs keeps -0.0 / NaN (D6) [{c.op.sym}]"
          | _ => s!"other [{c.op.sym}{if c.fnValue then " fn" else ""}]"
      byCause := tally byCause cause
      if examples.size < 40 && (examples.all fun e => !e.startsWith s!"[{cause}]") then
        examples := examples.push s!"[{cause}] {c.form}: Clojure {c.clj.show}, jank {j.show}"
  IO.println s!"  {total} cases, {devs} differ from Clojure 1.12"
  for (k, n) in byCause do IO.println s!"    {k}: {n}"
  for e in examples do IO.println s!"    e.g. {e}"

open Jank.R7.Native.Nan in
def nanPart : IO Unit := do
  IO.println "== nan: producers of x86-64's default NaN, every path, runtime -O0 and -O1"
  for p in [Prog.divZeroZero, .subInfInf, .mulZeroInf, .addInfNegInf, .parseNegNaN, .mathSqrtNeg, .mathPowNegHalf, .mathTanInf] do
    for path in [Path.literals, .letBound, .fnValue] do
      let bits := jankBits 0 p path
      IO.println s!"  {p.code path}: bits 0x{(Nat.toDigits 16 bits).asString}, jank -O0 {repr (jankOutcome 0 p path)}, -O1 {repr (jankOutcome 1 p path)}, Clojure {repr (cljOutcome p path)}"

open Jank.R7.Native.StrCase in
def casePart : IO Unit := do
  IO.println s!"== case (R60): JDK 23's special upper-case table has {jdkSpecialUpper.length} entries, lower {jdkSpecialLower.length} (+ Final_Sigma)"
  let lens := jdkSpecialUpper.map (·.2.length)
  IO.println s!"  entries mapping to 2 code points: {(lens.filter (· == 2)).length}, to 3: {(lens.filter (· == 3)).length}"
  for (c, _) in [(0xDF, 0), (0x149, 0), (0x1F0, 0), (0xFB01, 0), (0x1FB3, 0)] do
    IO.println s!"  upper-case U+{(Nat.toDigits 16 c).asString}: jank {(jUpper (Jank.Str.jstr [c])).show}, Clojure {(cUpper [c]).show}"
  IO.println s!"  lower-case U+0130: jank {(jLower (Jank.Str.jstr [0x130])).show}; ΣΑΣ: jank {(jLower (Jank.Str.jstr [0x3A3, 0x391, 0x3A3])).show}"

open Jank.Str Jank.R7.Native.StrAbbrev in
def abbrevPart : IO Unit := do
  IO.println "== abbrev: every text of ≤ 8 code points over {a, é, €, 😀}, n = 20 (the callers' n), complete"
  let alpha := [0x61, 0xE9, 0x20AC, 0x1F600]
  let mut texts : List (List Nat) := [[]]
  let mut all : Array (List Nat) := #[[]]
  for _ in [0:8] do
    texts := texts.flatMap fun t => alpha.map (· :: t)
    all := all ++ texts.toArray
  let mut total := 0
  let mut invalid := 0
  let mut ruleBroken := 0
  let mut differClj := 0
  for cps in all do
    total := total + 1
    let b := jstr cps
    let out := jAbbrev 20 b
    let valid := (decodeUtf8 out).isSome
    if !valid then invalid := invalid + 1
    if valid != (b.length < 20 || boundary b 20) then ruleBroken := ruleBroken + 1
    if unitsToBytes (cAbbrev 20 (cstr cps)) != out then differClj := differClj + 1
  IO.println s!"  {total} texts: logged string invalid UTF-8 for {invalid}; rule 'valid iff shorter than 20 bytes or byte 20 starts a character' broken {ruleBroken} times; differs from the same code on UTF-16 units {differClj} times"

open Jank.R3.Regex Jank.R5.Regex in
def regexPart : IO Unit := do
  IO.println "== regex: positions with non-ASCII text (round 3-5 replica vs round 5's Java model)"
  let cps (s : String) : List Nat := s.toList.map Char.toNat
  let pats := ["", "x*", "(?=.)", ".", "\\S", "[^a]", "(?=a)", "a?", "\\b", "(.)", "é", "é?", "(?=é)", "a|", "\\W"]
  let alpha := [0x61, 0xE9, 0x20AC, 0x1F600]
  let mut inputs : List (List Nat) := [[]]
  let mut level : List (List Nat) := [[]]
  for _ in [0:3] do
    level := level.flatMap fun t => alpha.map (· :: t)
    inputs := inputs ++ level
  let apis : List Api := [.find, .seq, .matches, .replace (cps "-"), .replaceFn, .split 0]
  let mut total := 0
  let mut differ := 0
  let mut byClass : List (String × Nat) := []
  let mut ex : Array String := #[]
  for api in apis do
    for p in pats do
      for inp in inputs do
        let q : Q := { api, pat := cps p, inp }
        total := total + 1
        let (v, j, c) := verdict5 .utf8 {} q
        match v with
        | .differ =>
          differ := differ + 1
          let cls0 := (classify5 .utf8 q).getD (trigger q)
          -- R78's trigger split by the shape of the cause: an ASCII analog (every non-ASCII code
          -- point replaced by `z`) agrees, so the encoding is the cause; then whether the pattern
          -- matches "" (regex_iterator's one-byte step after an empty match, V75's cause) or an atom
          -- matches one byte (R78).
          let cls :=
            if cls0 != "bytes (R78)" then cls0 else
            let qa : Q := { q with pat := q.pat.map (fun x => if x ≥ 0x80 then 0x7A else x), inp := q.inp.map (fun x => if x ≥ 0x80 then 0x7A else x) }
            let (va, _, _) := verdict5 .utf8 {} qa
            let emptyOk := match verdict5 .utf8 {} { api := .matches, pat := q.pat, inp := [] } with
              | (_, _, .str _) => true | (_, _, .vec _) => true | _ => false
            if va != .agree then s!"bytes (R78), ASCII analog also differs: {(classify5 .utf8 qa).getD (trigger qa)}"
            else if q.pat.any (· ≥ 0x80) then "bytes: a non-ASCII pattern character is bytes, a quantifier takes its last (S22)"
            else if emptyOk then "bytes: an empty match steps one byte (V75's cause)"
            else "bytes: an atom matches one byte (R78)"
          byClass := tally byClass cls
          if ex.size < 30 && (ex.all fun e => !e.startsWith s!"[{cls}]") then
            ex := ex.push s!"[{cls}] {q.program}: Clojure {Jank.R3.Regex.CV.show c}, jank {Jank.R3.Regex.V.show j}"
        | _ => pure ()
  IO.println s!"  {total} questions (6 apis × {pats.length} patterns × {inputs.length} inputs of ≤ 3 code points over a é € 😀), {differ} differ"
  for (k, n) in byClass do IO.println s!"    {k}: {n}"
  for e in ex do IO.println s!"    e.g. {e}"

open Jank.R3.Regex Jank.R5.Regex in
def vw2Part : IO Unit := do
  IO.println "== vW2: replace with an empty pattern (round 3's replica; Clojure from round 5's Java model)"
  for (api, inp) in [(Api.replace [0x2D], [0xE9]), (Api.replace [0x2D], [0x61, 0xE9]), (Api.replaceFn, [0xE9]), (Api.replaceFirst [0x2D], [0xE9])] do
    let q : Q := { api, pat := [], inp }
    let (_, j, c) := verdict5 .utf8 {} q
    IO.println s!"  {q.program}: Clojure {Jank.R3.Regex.CV.show c}, jank {Jank.R3.Regex.V.show j}"

def main (args : List String) : IO Unit := do
  let part := args.headD "all"
  if part == "brief" || part == "all" then briefPart
  if part == "unary" || part == "all" then unaryPart
  if part == "nan" || part == "all" then nanPart
  if part == "case" || part == "all" then casePart
  if part == "abbrev" || part == "all" then abbrevPart
  if part == "regex" || part == "all" then regexPart
  if part == "vw2" || part == "regex" || part == "all" then vw2Part
