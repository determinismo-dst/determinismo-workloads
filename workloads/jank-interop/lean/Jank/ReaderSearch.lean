import Jank.Read
import Jank.ReadClj
import Jank.ReadSyntaxQuote
import Jank.ReadRoundtrip
import Jank.LexTheorems

/-!
# The reader's searches (round 2, fork A)

- `total`: random and exhaustive byte strings; jank's lexer and parser must return or error.
- `agree.*`: inputs drawn character by character from an area's alphabet; jank must read what
  Clojure reads, to the same value (accepting what Clojure rejects is counted, not a violation).
- tables: every string up to a length over each alphabet, by verdict.
- `roundtrip`: values printed by jank's printers and read back by jank's reader.
- `read-string`: what parsing the second form does.
- `locale`: the C locale.
- `syntax-quote`: what the expansions evaluate to.
-/

namespace Jank.ReaderSearch

open Determinismo Jank.LexBytes Jank.ReadValue Jank.ReadRoundtrip

/-- Names compared by their printed form (`ns/name`): Clojure's `arraySymbolPat` splits `a/b/1`
differently from jank, which nothing but `namespace` can see. -/
partial def flatNames : Val → Val
  | .sym ns n => .sym [] (if ns.isEmpty then n else ns ++ [47] ++ n)
  | .kw ns n => .kw [] (if ns.isEmpty then n else ns ++ [47] ++ n)
  | .list xs => .list (xs.map flatNames)
  | .vec xs => .vec (xs.map flatNames)
  | .set xs => .set (xs.map flatNames)
  | .map kvs => .map (kvs.map fun (k, v) => (flatNames k, flatNames v))
  | .withMeta m v => .withMeta (flatNames m) (flatNames v)
  | v => v

def outCanon : Outcome → Outcome
  | .ok vs => .ok (vs.map (canon ∘ flatNames))
  | o => o

def jankReadB (bs : List UInt8) (loc : Locale := .utf8) : Outcome := outCanon (Jank.Read.readAll bs.toArray loc)
def jankRead (cs : List Nat) (loc : Locale := .utf8) : Outcome := jankReadB (cs.flatMap utf8Encode) loc
def cljRead (cs : List Nat) : Outcome := outCanon (Jank.ReadClj.readAll cs)

def codesOf (s : String) : List Nat := s.toList.map Char.toNat

structure World where
  decisions : Decisions := {}

instance : Chaotic World where
  decisions w := w.decisions
  setDecisions w d := { w with decisions := d }

abbrev WM := EStateM Stop World

def runW (body : WM Unit) (source : Source) : Ended :=
  match body.run { decisions := { source } } with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }
  | .error (.nodeDown _) w => { taken := w.decisions.taken, violation := none }

/-! ## Alphabets -/

/-- Bytes for the totality search: delimiters, macro characters, digits, NUL, a UTF-8 é, a lone
continuation byte, an invalid byte. -/
def totalBytes : List UInt8 :=
  [40, 41, 91, 93, 123, 125, 34, 92, 59, 35, 126, 94, 64, 39, 96, 58, 45, 48, 49, 97, 47, 37,
   32, 10, 13, 0, 0xC3, 0xA9, 0xFF, 95, 1, 0x1C, 0x7F, 9]

def alphaNumbers : List Nat := codesOf "012469-+.exrNM/Z] "
def alphaStrings : List Nat := codesOf "\"\\u0041noaxé" ++ [0]
def alphaChars : List Nat := codesOf "\\uo041nwlaeé( " ++ [0x2003]
def alphaSymbols : List Nat := codesOf ":/a.#%'@~^\"1 "
def alphaDelims : List Nat := codesOf "()[]{}#_'@^;\r1a: "

/-- Draws a string of up to `maxLen` characters from `alphabet`. -/
def drawString (alphabet : List Nat) (maxLen : Nat) : WM (List Nat) := do
  let n ← decide (σ := World) "read.len" (maxLen + 1)
  let mut out := #[]
  for _ in [0:n] do
    let c ← pick (σ := World) "read.char" alphabet
    out := out.push (c.getD 32)
  return out.toList

def drawBytes (alphabet : List UInt8) (maxLen : Nat) : WM (List UInt8) := do
  let n ← decide (σ := World) "read.len" (maxLen + 1)
  let mut out := #[]
  for _ in [0:n] do
    let c ← pick (σ := World) "read.byte" alphabet
    out := out.push (c.getD 32)
  return out.toList

/-! ## Properties -/

def totalBody (maxLen : Nat) : WM Unit := do
  let bs ← drawBytes totalBytes maxLen
  match jankReadB bs with
  | .hang w => violate (σ := World) "read is total" s!"{showBytes bs}: hangs in {w}"
  | .crash w => violate (σ := World) "read is total" s!"{showBytes bs}: {w}"
  | _ => pure ()
  -- read-string parses a second form too.
  match (Jank.Read.readString bs.toArray).1 with
  | .hang w => violate (σ := World) "read is total" s!"(read-string {showBytes bs}): hangs in {w}"
  | .crash w => violate (σ := World) "read is total" s!"(read-string {showBytes bs}): {w}"
  | _ => pure ()

def agreeBody (alphabet : List Nat) (maxLen : Nat) : WM Unit := do
  let cs ← drawString alphabet maxLen
  let j := jankRead cs
  let c := cljRead cs
  match verdict j c with
  | .notTotal | .wrongValue | .rejectsValid =>
    violate (σ := World) "jank reads what Clojure reads"
      s!"{showCodes cs}: Clojure {c.show}, jank {j.show}"
  | _ => pure ()

/-! ## Tables: every string up to a length -/

partial def allStrings (alphabet : List Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 => [] :: (alphabet.flatMap fun c => (allStrings alphabet n).map (c :: ·))

def dedupStrings (xs : List (List Nat)) : List (List Nat) :=
  ((xs.toArray.qsort (fun a b => a.length < b.length || (a.length == b.length && showCodes a < showCodes b))).toList).eraseDups

structure Tally where
  total : Nat := 0
  agree : Nat := 0
  notTotal : Array (List Nat) := #[]
  wrong : Array (List Nat) := #[]
  rejects : Array (List Nat) := #[]
  accepts : Array (List Nat) := #[]

def tally (alphabet : List Nat) (len : Nat) : Tally := Id.run do
  let mut t : Tally := {}
  for cs in dedupStrings (allStrings alphabet len) do
    t := { t with total := t.total + 1 }
    match verdict (jankRead cs) (cljRead cs) with
    | .agree => t := { t with agree := t.agree + 1 }
    | .notTotal => t := { t with notTotal := t.notTotal.push cs }
    | .wrongValue => t := { t with wrong := t.wrong.push cs }
    | .rejectsValid => t := { t with rejects := t.rejects.push cs }
    | .acceptsInvalid => t := { t with accepts := t.accepts.push cs }
  return t

def showCase (cs : List Nat) : String :=
  s!"{showCodes cs}  =>  jank {(jankRead cs).show} | Clojure {(cljRead cs).show}"

/-- A string's shape: digits 1-9 as `1`, surrounding spaces dropped (examples are shown once per
shape). -/
def shape (cs : List Nat) : List Nat :=
  ((cs.map fun c => if 49 ≤ c && c ≤ 57 then 49 else c).dropWhile (· == 32)).reverse.dropWhile (· == 32) |>.reverse

def distinctShapes (xs : List (List Nat)) : List (List Nat) :=
  (xs.foldl (fun (acc : List (List Nat) × List (List Nat)) cs =>
    let sh := shape cs
    if acc.1.contains sh then acc else (sh :: acc.1, acc.2 ++ [cs])) ([], [])).2

def printTally (name : String) (alphabet : List Nat) (len : Nat) (shown : Nat := 10) : IO Unit := do
  let t := tally alphabet len
  IO.println s!"== table {name}: every string of length ≤ {len} over {showCodes alphabet} ({t.total} strings)"
  IO.println s!"  agree {t.agree}; jank hangs/crashes {t.notTotal.size}; different values {t.wrong.size}; jank rejects valid {t.rejects.size}; jank accepts invalid {t.accepts.size}"
  for (label, xs) in [("hang/crash", t.notTotal), ("different value", t.wrong), ("rejects valid", t.rejects), ("accepts invalid", t.accepts)] do
    -- Examples: a few with `+` (one cause dominates), then the others.
    let (plus, rest) := (distinctShapes xs.toList).partition (·.contains 43)
    for cs in plus.take 3 ++ rest.take shown do
      IO.println s!"    {label}: {showCase cs}"

/-! ## Reports -/

def describe (c : Counterexample) : String :=
  s!"{c.property} after {c.runs} timelines, {c.taken.size} decisions: {c.detail}"

def indentTape (taken : Array Taken) : String :=
  "\n".intercalate ((tape taken).splitOn "\n" |>.map ("      " ++ ·))

def report (name : String) (run : Source → Ended) (seeds : Nat) (maxRuns : Nat) : IO Unit := do
  IO.println s!"== {name}"
  match explore run seeds with
  | some c =>
    IO.println s!"  explore ({seeds} seeds): {describe c}"
    let s := shrink run c
    IO.println s!"  shrunk to {s.taken.size} decisions: {s.detail}"
    IO.println s!"    tape:\n{indentTape s.taken}"
  | none => IO.println s!"  explore ({seeds} seeds): nothing"
  match exhaust run maxRuns with
  | .found c =>
    IO.println s!"  exhaust: found after {c.runs} timelines: {c.detail}"
    let s := shrink run c
    IO.println s!"  shrunk to {s.taken.size} decisions: {s.detail}"
  | .complete n => IO.println s!"  exhaust: complete, {n} timelines, nothing"
  | .stopped n => IO.println s!"  exhaust: stopped at {n} timelines, nothing"

/-! ## Round trips -/

def rtStrings : List (List Nat) :=
  [codesOf "a", [0], [7], [11], [0x1B], [0x7F], codesOf "\"", codesOf "\\", [0xE9], [0x2003],
   [0x1F600], codesOf "a\nb", [97, 0, 98], codesOf "\\u0041"]

def rtValues : List Val :=
  [.long 0, .long 1, .long (-1), .long 2147483647, .long (-2147483648), .long 9223372036854775807,
   .long (-9223372036854775808), .big 9223372036854775808, .big (-9223372036854775809), .ratio 1 2, .ratio (-7) 3,
   .dbl ⟨false, 0, 0⟩, .dbl ⟨true, 0, 0⟩, .dbl ⟨false, 15, -1⟩, .dbl ⟨false, 1, 21⟩, .dbl ⟨false, 1, -7⟩,
   .dbl ⟨true, 123, 0⟩, .inf false, .inf true, .nan, .bigdec ⟨false, 15, -1⟩,
   .kw [] (codesOf "a"), .kw (codesOf "ns") (codesOf "b"), .sym [] (codesOf "a.b"), .sym (codesOf "clojure.core") (codesOf "/"),
   .char 0, .char 32, .char 10, .char 0x2003, .char 0xE9, .char 40, .char 92, .char 44, .char 7]
  ++ rtStrings.map Val.str
  ++ [.vec [.long 1, .str (codesOf "x")], .list [], .set [.long 1, .kw [] (codesOf "a")],
      .map [(.kw [] (codesOf "a"), .long 1)]]

def roundtrips : IO Unit := do
  IO.println "== roundtrip: (read-string (pr-str x)) with jank's printers and jank's reader"
  let mut bad := 0
  let mut typeChanged := 0
  for v in rtValues do
    for which in [0, 1] do
      let txt := jankPr which v
      let back := jankReadB txt
      let ok := match back with
        | .ok [w] => w == canon (flatNames v)
        | _ => false
      let sameEq := match back with
        | .ok [w] => Jank.Read.jankEqual w v
        | _ => false
      if !ok then
        if sameEq then typeChanged := typeChanged + 1 else bad := bad + 1
        IO.println s!"  {v.show}: printed {showBytes txt}, read back {back.show}{if sameEq then "  (= holds, the type changed)" else ""}"
      if which == 0 then
        -- Clojure's own printers and reader on the same value (the model's sanity).
        match v with
        | .str _ | .char _ =>
          let cb := cljRead (cljPr v)
          if cb != .ok [canon (flatNames v)] then IO.println s!"  Clojure model fails to round-trip {v.show}: {cb.show}"
        | _ => pure ()
  IO.println s!"  {rtValues.length} values × 2 double formats: {bad} not read back, {typeChanged} read back = but with another type"

/-! ## read-string's second form -/

def readStringCases : List String :=
  ["1 2", "1 )", "1 \"a\u0000\"", "1 a\u0000", "1 #\u0000", "1 ;\u0000", "1 (", "1.5N", "1-2", "[1]]"]

def readStringTable : IO Unit := do
  IO.println "== read-string: the first form, after parsing the second (context.cpp:261-283)"
  for s in readStringCases do
    let bs := bytesOf s
    let (o, second) := Jank.Read.readString bs.toArray
    let secondTxt := match second with
      | .ok none => "eof" | .ok (some v) => s!"form {v.show}" | .err m => s!"error {m}"
      | .hang w => s!"HANG {w}" | .crash w => s!"CRASH {w}"
    IO.println s!"  (read-string {showBytes bs}): jank {o.show} [second form: {secondTxt}] | Clojure {(outCanon (Jank.ReadClj.readString1 (codesOf s))).show}"

/-! ## The C locale -/

def localeCases : List String := ["\"é\"", "\"\\u00e9\"", "\\é", ":é", "é", "(str \"日本\")", "\"\\u0041\""]

def localeTable : IO Unit := do
  IO.println "== locale: jank under LANG unset (C locale, glibc) vs a UTF-8 locale vs Clojure"
  for s in localeCases do
    let cs := codesOf s
    IO.println s!"  {showCodes cs}: jank C {(jankRead cs .c).show} | jank UTF-8 {(jankRead cs .utf8).show} | Clojure {(cljRead cs).show}"

/-! ## Hand-written inputs -/

def handCases : List String :=
  ["[-0]", "(+ -0 1)", "(- 5 -0)\n", "+5", "(+ +1 2)", "-9223372036854775808", "36rN", "36rZN", "24rN0",
   "-010/3", "-09/3", "08M", "(str\"a\")", "\"a\"\"b\"", "[1\"a\"]", ";x\r42", "\"\\0\"", "\"\\101\"",
   "\"\\a\"", "\\u41", "\\o400", "#(+ %10 %1)", "^\"String\" x", "^[long] x", "^foo x", "@a",
   "#{1 1N}", "{1 :a 1N :b}", "#{0.0 -0.0}", ":/", "a@b", "~é", "(\u2003a)", "[1\u001c2]",
   "#:a{:b 1}", "#^:a x", "#\"(?i)abc\"", "#\"(?<=a)b\"", "#\"(?<n>a)\"", "#\"a*+\"", "#\"(?:a)(?=b)\"",
   ":1", ":1/a", "a::b", ":a:", "\"\\uD800\"", "\"\\uD83D\\uDE00\"", "258r11", "16re", "36rr", "9223372036854775808/2", "18446744073709551616/18446744073709551616",
   "\"a\u0000b\"", "a\u0000", ":a\u0000", ";\u0000", "\\\u0000", "#\u0000", "~\u0000", "\u0000"]

def hand : IO Unit := do
  IO.println "== reader: hand-written inputs"
  for s in handCases do
    let cs := codesOf s
    IO.println s!"  {showCase cs}  [{reprStr (verdict (jankRead cs) (cljRead cs))}]"

def without (alpha : List Nat) (drop : String) : List Nat := alpha.filter (!(codesOf drop).contains ·)

/-- Each search again with the characters behind the deviations already found removed from its
alphabet, to reach the next one. -/
def residual : List (String × List Nat × Nat) :=
  [("numbers without +", without alphaNumbers "+", 5),
   ("numbers without + and space", without alphaNumbers "+ ", 5),
   ("numbers without +, space and ]", without alphaNumbers "+ ]", 5),
   ("numbers without +, space, ], N and M", without alphaNumbers "+ ]NM", 5),
   ("strings without NUL", alphaStrings.filter (· != 0), 5),
   ("characters without U+2003", alphaChars.filter (· != 0x2003), 5),
   ("symbols and keywords without @ and /", without alphaSymbols "@/", 4),
   ("delimiters and macros without @ and \\r", without alphaDelims "@\r", 4)]

def searches (args : List String) : IO Unit := do
  let only := args.head?
  let want := fun (k : String) => only.isNone || only == some k
  if want "hand" then hand
  if want "total" then
    report "read is total: byte strings ≤ 6 (random), ≤ 3 (exhaustive)" (runW (totalBody 6)) 3000 0
    report "read is total: byte strings ≤ 3, exhaustive" (runW (totalBody 3)) 0 100000
  if want "agree" then
    for (name, alpha, len) in [("numbers", alphaNumbers, 5), ("strings", alphaStrings, 5),
        ("characters", alphaChars, 5), ("symbols and keywords", alphaSymbols, 4),
        ("delimiters and macros", alphaDelims, 4)] do
      report s!"agree, {name}: strings ≤ {len} over {showCodes alpha}" (runW (agreeBody alpha len)) 3000 200000
  if want "residual" then
    report "read is total without NUL bytes: byte strings ≤ 12 (random, 20000 seeds)"
      (runW (do
        let bs ← drawBytes (totalBytes.filter (· != 0)) 12
        match jankReadB bs with
        | .hang w => violate (σ := World) "read is total" s!"{showBytes bs}: hangs in {w}"
        | .crash w => violate (σ := World) "read is total" s!"{showBytes bs}: {w}"
        | _ => pure ())) 20000 0
    report "read is total without NUL bytes: byte strings ≤ 4 (exhaustive)"
      (runW (do
        let bs ← drawBytes (totalBytes.filter (· != 0)) 4
        match jankReadB bs with
        | .hang w => violate (σ := World) "read is total" s!"{showBytes bs}: hangs in {w}"
        | .crash w => violate (σ := World) "read is total" s!"{showBytes bs}: {w}"
        | _ => pure ())) 3000 2000000
    for (name, alpha, len) in residual do
      report s!"agree, {name}: strings ≤ {len} over {showCodes alpha}" (runW (agreeBody alpha len)) 3000 2000000
    report "syntax quote without dotted symbols: the expansion evaluates as Clojure's"
      Jank.ReadSyntaxQuote.runNoDots 3000 2000000
  if want "tables" then
    printTally "numbers" alphaNumbers 4
    printTally "strings" alphaStrings 4
    printTally "characters" alphaChars 4
    printTally "symbols and keywords" alphaSymbols 3
    printTally "delimiters and macros" alphaDelims 3
  if want "roundtrip" then roundtrips
  if want "read-string" then readStringTable
  if want "locale" then localeTable
  if want "syntax-quote" then
    report "syntax quote: the expansion evaluates as Clojure's" Jank.ReadSyntaxQuote.run 3000 200000

end Jank.ReaderSearch
