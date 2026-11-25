import Jank.R3.Boost.Checks
import Jank.R3.Boost.Tables
import Jank.R3.Boost.Search
import Jank.R3.Boost.Reader
import Jank.R3.Boost.Codegen
import Jank.R3.Boost.Theorems
import Jank.R3.Boost.Assumptions

/-! Round 3 driver: Boost (boost::multiprecision as jank uses it). -/

open Jank.R3.Boost

/-- SplitMix64 finalizer over the seed index: `Source.seeded i` passes a small `i` straight to
`mkStdGen`, whose first draw is the same for every seed 0..2,999 (library defect, round 3). -/
def mixSeed (i : Nat) : Nat :=
  let z : UInt64 := (UInt64.ofNat i) + 0x9E3779B97F4A7C15
  let z := (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31)).toNat

/-- `explore` over mixed seeds. -/
def exploreMixed (run : Determinismo.Source → Determinismo.Ended) (count : Nat) : Option Determinismo.Counterexample := Id.run do
  for i in List.range count do
    let o := run { gen := mkStdGen (mixSeed i) }
    if let some (property, detail) := o.violation then
      return some { taken := o.taken, property, detail, runs := i + 1 }
  return none

def header : String :=
  "deps/boost-multiprecision/include/boost/multiprecision/cpp_dec_float.hpp"

def checks : IO Unit := do
  IO.println "== replica checks"
  let text ← IO.FS.readFile header
  let (n, bad) := Checks.pow2TableMatchesHeader text
  IO.println s!"  pow2 table: {n} header entries, {bad.length} differ from the exact powers of two"
  for b in bad.take 5 do IO.println s!"    {b}"
  let (n, bad) := Checks.cppIntChecks
  IO.println s!"  cpp_int str/convert_to<double>: {n} values, {bad.length} wrong"
  for b in bad.take 5 do IO.println s!"    {b}"
  let (n, bad) := Checks.decChecks
  IO.println s!"  cpp_dec_float rd_string/operator=(double) exactness: {n} values, {bad.length} wrong"
  for b in bad.take 5 do IO.println s!"    {b}"

def ra5 (len : Nat) : IO Unit := do
  let (n, bad) := Checks.ra5Check len
  IO.println s!"== RA5: round 2's boostParse vs the replica do_assign_string, every string ≤ {len} over \"{String.ofList (Checks.ra5Alphabet.map Char.ofNat)}\": {n} strings, {bad.length} differ"
  for b in bad.take 10 do IO.println s!"    {b}"

def raw : IO Unit := do
  let qs := Tables.unaryQs ++ Tables.binaryQs
  IO.println s!"== raw: {qs.length} questions"
  for o in Tables.operands do
    IO.println s!"  operand {o.src}: jank {o.j.prStr} | Clojure {o.c.prStr}"
  for q in qs do
    let a := q.answer
    if !a.agree then IO.println s!"  [{q.name}] {q.program}  jank {a.jank} | Clojure {a.clj}"

def allQs : Array Tables.Q := (Tables.unaryQs ++ Tables.binaryQs).toArray

def tables : IO Unit := do
  let qs := allQs
  let mut byClass : Std.HashMap String (Nat × Array String) := {}
  let mut agree := 0
  for q in qs do
    let c := Search.classify q
    if c == "" then agree := agree + 1
    else
      let a := q.answer
      let (n, ex) := byClass.getD c (0, #[])
      byClass := byClass.insert c (n + 1, ex.push s!"{q.program}  jank {a.jank} | Clojure {a.clj}")
  IO.println s!"== table: {qs.size} questions over {Tables.operands.length} operands; {agree} agree"
  let classes := byClass.toList.toArray.qsort (fun a b => a.1 < b.1)
  for (c, (n, ex)) in classes do
    IO.println s!"  {c}: {n}"
    let sorted := ex.qsort (fun a b => a.length < b.length)
    for e in sorted.toList.take (if c == "UNCLASSIFIED" then 200 else 4) do IO.println s!"      {e}"

def residual : IO Unit := do
  let qs := allQs
  IO.println s!"== residual searches: one question per timeline ({qs.size} questions), exhaust"
  let mut aside : List String := []
  for _ in [0:40] do
    match Determinismo.exhaust (Search.runW (Search.body qs aside)) 100000 with
    | .found c =>
      let cls := String.ofList (((c.property.splitOn "[").getD 1 "").toList.filter (· != ']'))
      IO.println s!"  aside {aside.length}: found after {c.runs} timelines [{cls}]: {c.detail}"
      IO.println s!"    tape: {Determinismo.tape c.taken}"
      aside := aside ++ [cls]
    | .complete n =>
      IO.println s!"  aside {aside.length}: complete, {n} timelines, nothing"
      break
    | .stopped n =>
      IO.println s!"  aside {aside.length}: stopped at {n}"
      break

def printTransitions (sw : Reader.Swap) : IO Unit := do
  let mut tr : Std.HashMap String Nat := {}
  for (_, a, b) in sw.transitions do tr := tr.insert s!"{a} -> {b}" (tr.getD s!"{a} -> {b}" 0 + 1)
  for (k, n) in tr.toList do IO.println s!"    verdict {k}: {n}"
  let mut shown : Std.HashMap String Nat := {}
  for (x, a, b) in sw.transitions.toList do
    let k := s!"{a} -> {b}"
    if shown.getD k 0 < 4 then
      shown := shown.insert k (shown.getD k 0 + 1)
      IO.println s!"      {x}: {a} -> {b}   [jank r2 {(Jank.ReaderSearch.jankRead (x.toList.map Char.toNat)).show} | replica {Reader.jankOne x} | Clojure {Reader.cljOne x}]"

def reader : IO Unit := do
  let alpha := Jank.ReaderSearch.alphaNumbers
  let sw := Reader.swapCheck alpha 4
  IO.println s!"== reader: round 2's numbers table (every string ≤ 4 over {Jank.LexBytes.showCodes alpha}) with the boost replica in place of RA5/RA7"
  IO.println s!"  {sw.strings} strings; {sw.bigTokens} big_integer tokens, {sw.decTokens} big_decimal tokens; {sw.diffs.size} values change"
  for d in sw.diffs.toList.take 20 do IO.println s!"    {d}"
  printTransitions sw
  let alpha2 := Jank.R3.Boost.Dec.codes "01789.eE-xMN/"
  let sw := Reader.swapCheck alpha2 6
  IO.println s!"== reader: every string ≤ 6 over 01789.eE-xMN/ ({sw.strings} strings; {sw.bigTokens} big_integer, {sw.decTokens} big_decimal tokens): {sw.diffs.size} values change"
  for d in sw.diffs.toList.take 10 do IO.println s!"    {d}"
  printTransitions sw
  IO.println "== reader: inputs past round 2's bounds (jank: round 2's lexer + this replica; Clojure: round 2's LispReader replica)"
  for s in Reader.handCases do
    IO.println s!"  {s}  =>  jank {Reader.jankOne s} | Clojure {Reader.cljOne s}"

def cgMantissas : Array String :=
  #["1", "5", "-7", "15", "123456789", "1.5", "0.001", "-2.25", "100",
    "1234567890123456789012345678901234567890", "3.14159265358979323846264338327950288419716939937510"]
def cgExps : Array Int := (Array.range 301).map fun (i : Nat) => (i : Int) - 150

/-- The AOT class of a BigDecimal literal `{m}e{e}M`: "" when the module rebuilds the same
object, else why not. -/
def cgClass (m : String) (e : Int) : String × String :=
  let lit := s!"{m}e{e}"
  match Jank.R3.Boost.Dec.rdString (Num.bytes lit) with
  | .error err => ("", s!"literal rejected: {err}")
  | .ok d =>
    let v := Num.JV.dec d
    match Codegen.aotLoad v with
    | .error err => ("AOT load throws", s!"{lit}M: JIT {v.prStr}; AOT text {Codegen.genConstant v}; load: {err}")
    | .ok w => if Codegen.sameObj v w then ("", "") else ("AOT value differs", s!"{lit}M: JIT {v.prStr}, AOT {w.prStr}")

def codegen : IO Unit := do
  IO.println s!"== codegen: BigDecimal literal constants (mantissas {cgMantissas.size} × exponents -150..150), JIT object vs AOT text rebuilt at load"
  let mut counts : Std.HashMap String Nat := {}
  let mut examples : Std.HashMap String (Array String) := {}
  let mut n := 0
  for m in cgMantissas do
    for e in cgExps do
      n := n + 1
      let (c, d) := cgClass m e
      if c != "" then
        counts := counts.insert c (counts.getD c 0 + 1)
        examples := examples.insert c ((examples.getD c #[]).push d)
  IO.println s!"  {n} literals"
  for (c, k) in counts.toList do
    IO.println s!"  {c}: {k}"
    for ex in ((examples.getD c #[]).qsort (fun a b => a.length < b.length)).toList.take 6 do IO.println s!"      {ex}"
  -- BigInt constants: decimal text, boost assign.
  let mut bad := 0
  let mut nb := 0
  for k in [0:400] do
    for v in [(10 : Int) ^ k, -((10 : Int) ^ k) - 1, (2 : Int) ^ k + 1, -((2 : Int) ^ k)] do
      nb := nb + 1
      match Codegen.aotLoad (.big v) with
      | .ok (.big w) => if w != v then bad := bad + 1
      | _ => bad := bad + 1
  IO.println s!"  BigInt constants: {nb} values, {bad} not rebuilt exactly"
  -- The search: one literal per timeline; residual with the load failures set aside.
  let run := fun (aside : List String) => Search.runW (do
    let i ← Determinismo.decide (σ := Search.World) "codegen.mantissa" cgMantissas.size
    let j ← Determinismo.decide (σ := Search.World) "codegen.exponent" cgExps.size
    let (c, d) := cgClass cgMantissas[i]! cgExps[j]!
    if c != "" && !aside.contains c then
      Determinismo.violate (σ := Search.World) s!"AOT constant denotes the literal [{c}]" d)
  for aside in [([] : List String), ["AOT load throws"]] do
    match Determinismo.exhaust (run aside) 100000 with
    | .found c => IO.println s!"  exhaust, aside {aside}: found after {c.runs} timelines: {c.detail}\n    tape: {Determinismo.tape c.taken}"
    | .complete k => IO.println s!"  exhaust, aside {aside}: complete, {k} timelines, nothing"
    | .stopped k => IO.println s!"  exhaust, aside {aside}: stopped at {k}"
    match exploreMixed (run aside) 3000 with
    | some c => IO.println s!"  explore 3000 mixed seeds, aside {aside}: found after {c.runs}: {c.detail}"
    | none => IO.println s!"  explore 3000 mixed seeds, aside {aside}: nothing"

def strAlphabet : List Nat := Jank.R3.Boost.Dec.codes "019x-+.eN"

def strings (len : Nat) : IO Unit := do
  for dec in [false, true] do
    let name := if dec then "bigdec" else "bigint"
    let (n, counts, ex) := Checks.foldStrings strAlphabet len ((0 : Nat), ({} : Std.HashMap String Nat), ({} : Std.HashMap String (Array String)))
      fun (n, counts, ex) s =>
        let c := Search.strClass dec s
        if c == "" then (n + 1, counts, ex)
        else
          let j := if dec then Num.jBigdecStr s else Num.jBigintStr s
          let cl := if dec then Num.cBigdecStr s else Num.cBigintStr s
          let e := ex.getD c #[]
          (n + 1, counts.insert c (counts.getD c 0 + 1),
            if e.size < 400 then ex.insert c (e.push s!"({name} \"{String.ofList (s.map Char.ofNat)}\")  jank {j.show} | Clojure {cl.show}") else ex)
    IO.println s!"== ({name} s): every string ≤ {len} over \"{String.ofList (strAlphabet.map Char.ofNat)}\": {n} strings"
    for (c, k) in counts.toList do
      IO.println s!"  {c}: {k}"
      for e in ((ex.getD c #[]).qsort (fun a b => a.length < b.length)).toList.take 8 do IO.println s!"      {e}"

def random (seeds : Nat) : IO Unit := do
  let known := ((allQs.toList.map Search.classify).filter (· != "")).eraseDups
  IO.println s!"== random literals (longs, doubles, BigInts ≤ 25 digits, BigDecimals ≤ 25 digits with exponents ±30, ratios): explore {seeds} mixed seeds"
  let mut aside : List String := []
  for _ in [0:30] do
    match exploreMixed (Search.runW (Search.randomBody aside)) seeds with
    | some c =>
      let cls := String.ofList (((c.property.splitOn "[").getD 1 "").toList.filter (· != ']'))
      IO.println s!"  aside {aside.length}: found after {c.runs} seeds [{cls}]{if known.contains cls then "" else " (NEW)"}: {c.detail}"
      aside := aside ++ [cls]
    | none =>
      IO.println s!"  aside {aside.length}: {seeds} seeds, nothing"
      break

def assumptions : IO Unit := do
  IO.println "== round 1/2 assumptions against the replica"
  for (name, (n, bad)) in [("RC2 (Compare.cppNumCmp: BigDecimal vs double exactly)", Assumptions.rc2),
      ("RB7 (Print.jankDec: no trailing zeros, fixed, .0)", Assumptions.rb7),
      ("D7 (Numbers.jankBigdecOfLong)", Assumptions.d7),
      ("D8 (Numbers.jankDecEq)", Assumptions.d8)] do
    IO.println s!"  {name}: {n} inputs, {bad.length} differ"
    for b in bad.take 12 do IO.println s!"      {b}"


def spot : IO Unit := do
  IO.println "== spot checks (both sides on single programs)"
  let o := Tables.mkOperand
  let qs : List Tables.Q :=
    [.arith .div (o "6M") (o "3M"), .arith .div (o "6M") (o "3"), .arith .div (o "3") (o "6M"),
     .arith .div (o "1.5M") (o "3"), .arith .div (o "1M") (o "7M"), .arith .div (o "1M") (o "3"),
     .arith .add (o "1M") (o "0.5"), .arith .mul (o "6M") (o "0.1"), .arith .add (o "1") (o "1E130M"),
     .arith .sub (o "1M") (o "1E-130M"), .arith .div (o "7N") (o "2"),
     .rem (o "1E130M") (o "3"), .rem (o "1E130M") (o "123456789.123456789M"), .rem (o "1/2") (o "0.1M"),
     .rem (o "1.75M") (o "1/2"),
     .lt (o "0.1M") (o "0.1"), .cmp (o "9.007199254740992E15") (o "9007199254740993N"),
     .lt (o "9.007199254740992E15") (o "9007199254740993N"),
     .equal (o "1M") (o "1.0000000000000000001M"), .hashEq (o "1M") (o "1.0000000000000000001M"),
     .equiv (o "1M") (o "1.0000000000000000001M"), .quot (o "1") (o "0.00001M"),
     .str (o "0.00001M"), .prStr (o "1E130M"), .str (o "1.50M"), .prStr (o "1M"),
     .toDouble (o "9007199254740993.00000000000000000001M"), .toDouble (o "1E-310M"),
     .toDouble (o "3E-320M"), .toLong (o "1E130M"), .toLong (o "9007199254740993.00000000000000000001M"),
     .bigdec (o "0.1"), .bigint (o "1.0E23"), .bigint (o "1.0E300"), .bigdec (o "1/3"), .bigdec (o "9007199254740993"),
     .bigint (o "100000000000000000000/3"), .toDouble (o "-7/3"), .arith .mul (o "0N") (o "1/2")]
  for q in qs do
    let a := q.answer
    IO.println s!"  {q.program}  jank {a.jank} | Clojure {a.clj}{if a.agree then "  (agree)" else ""}"
  for s in ["010", "0x10", "1N", "-", "+5", "08"] do
    IO.println s!"  (bigint \"{s}\")  jank {(Num.jBigintStr (Num.bytes s)).show} | Clojure {(Num.cBigintStr (Num.bytes s)).show}"
  for s in ["inf", "nan", "NaNxyz", "1e", ".", "1.5e", "0x10", "+5", "1e400"] do
    IO.println s!"  (bigdec \"{s}\")  jank {(Num.jBigdecStr (Num.bytes s)).show} | Clojure {(Num.cBigdecStr (Num.bytes s)).show}"
  -- pr-str then read back with jank's reader (round 2's lexer, this replica)
  for src in ["0.00001M", "1E130M", "1.5E-7M", "0.1M"] do
    let v := (o src).j
    let txt := v.prStr
    IO.println s!"  (read-string (pr-str {src})): text {txt}; jank reads {match Tables.jankLiteral txt with | .ok w => w.prStr | .error e => s!"error ({e})"}"

def ra5bytes : IO Unit := do
  let alpha := (List.range 255).map (· + 1)
  let (n, bad) := Checks.foldStrings alpha 3 ((0 : Nat), (#[] : Array String)) fun (n, bad) s =>
    let r2 := Jank.LexBytes.boostParse (s.map (·.toUInt8))
    let r3 := CppInt.assignString s
    let ok := match r2, r3 with
      | .ok a, .ok b => a == b
      | .error _, .error _ => true
      | _, _ => false
    (n + 1, if ok || bad.size > 10 then bad else bad.push s!"{s}: round 2 {reprStr r2}, replica {reprStr r3}")
  IO.println s!"== RA5 over bytes: every string ≤ 3 of the bytes 1..255: {n} strings, {bad.size} differ"
  for b in bad.toList do IO.println s!"    {b}"
  -- NUL: boost stops at the first NUL (strlen); round 2 rejects it.
  for s in [[49, 0, 50], [0], [45, 0]] do
    IO.println s!"    with NUL {s}: round 2 {reprStr (Jank.LexBytes.boostParse (s.map (·.toUInt8)))}, replica {reprStr (CppInt.assignString s)}"

def main (args : List String) : IO UInt32 := do
  let only := args.head?
  let want := fun (k : String) => only.isNone || only == some k
  if want "checks" then checks
  if want "ra5" then ra5 5
  if want "ra5bytes" then ra5bytes
  if want "assumptions" then assumptions
  if want "reader" then reader
  if want "tables" then tables
  if want "residual" then residual
  if want "random" then random 20000
  if want "strings" then strings 5
  if want "codegen" then codegen
  if want "spot" then spot
  if only == some "raw" then raw
  return 0
