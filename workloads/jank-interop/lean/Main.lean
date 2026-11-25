import Jank

open Determinismo

def describe (c : Counterexample) : String :=
  s!"{c.property} after {c.runs} timelines, {c.taken.size} decisions: {c.detail}"

def report (name : String) (run : Source → Ended) (seeds : Nat) (maxRuns : Nat) : IO Unit := do
  IO.println s!"== {name}"
  match explore run seeds with
  | some c =>
    IO.println s!"  explore ({seeds} seeds): {describe c}"
    let s := shrink run c
    IO.println s!"  shrunk to {s.taken.size} decisions: {s.detail}"
    IO.println s!"  tape:\n{(tape s.taken).splitOn "\n" |>.map ("    " ++ ·) |> "\n".intercalate}"
  | none => IO.println s!"  explore ({seeds} seeds): nothing"
  match exhaust run maxRuns with
  | .found c =>
    IO.println s!"  exhaust: found after {c.runs} timelines: {c.detail}"
    let s := shrink run c
    if s.taken.size > 0 then
      IO.println s!"  exhaust's counterexample shrunk to {s.taken.size} decisions; tape:\n{(tape s.taken).splitOn "\n" |>.map ("    " ++ ·) |> "\n".intercalate}"
  | .complete n => IO.println s!"  exhaust: complete, {n} timelines, nothing"
  | .stopped n => IO.println s!"  exhaust: stopped at {n} timelines, nothing"

section
open Jank.Numbers
def numbers : IO Unit := do
  report "numbers: + - * +' -' *' / on longs" runArith 3000 100000
  -- The full table: every question, the ones jank's documentation does not allow.
  let bad := allQuestions.filter (!·.allowed)
  IO.println s!"  table: {bad.length} of {allQuestions.length} questions deviate; first per operator:"
  let firsts := [("+", fun (q : Question) => match q with | .arith .add .. => true | _ => false),
                 ("-", fun q => match q with | .arith .sub .. => true | _ => false),
                 ("*", fun q => match q with | .arith .mul .. => true | _ => false),
                 ("+'", fun q => match q with | .promoting .add .. => true | _ => false),
                 ("-'", fun q => match q with | .promoting .sub .. => true | _ => false),
                 ("*'", fun q => match q with | .promoting .mul .. => true | _ => false),
                 ("/", fun q => match q with | .divide .. => true | _ => false)]
  for (op, sel) in firsts do
    let qs := bad.filter sel
    IO.println s!"    {op}: {qs.length} deviate"
    for q in qs.take 3 do
      IO.println s!"      {q.program}: Clojure {showE q.clj}, jank {showE q.jank}"
  -- Doubles.
  IO.println "== numbers: doubles"
  let q1 := jankQuot .x86_64 (.ofInt 9007199254740993) (.ofInt 1)
  IO.println s!"  (quot 9007199254740993 1): Clojure {showE (cljQuot (.long 9007199254740993) (.long 1))}, jank {showE q1}"
  IO.println s!"  (quot 7.5 2): Clojure {showE (cljQuot (.double 7.5) (.long 2))}, jank {showE (jankQuot .x86_64 (.real 7.5) (.ofInt 2))}"
  IO.println s!"  (quot -9223372036854775808 -1): Clojure {showE (cljQuot (.long i64min) (.long (-1)))}, jank x86-64 {showE (jankQuot .x86_64 (.ofInt i64min) (.ofInt (-1)))}, jank aarch64 {showE (jankQuot .aarch64 (.ofInt i64min) (.ofInt (-1)))}"
  IO.println s!"  (== 9007199254740993 9007199254740992): Clojure {cljEquiv (.long 9007199254740993) (.long 9007199254740992)}, jank {jankEquiv (.ofInt 9007199254740993) (.ofInt 9007199254740992)}"
  IO.println s!"  (abs -0.0): Clojure {cljAbsReal (-0.0)}, jank {jankAbsReal (-0.0)}"
  IO.println s!"  (bigdec 9007199254740993): Clojure {cljBigdecOfLong 9007199254740993}M, jank {jankBigdecOfLong 9007199254740993}M"
  -- Search the quot / == / bigdec deviations over the interesting longs.
  let longs := interesting.filter fun v => i64min ≤ v ∧ v ≤ i64max
  let equivBad := longs.flatMap fun a => longs.filterMap fun b =>
    if cljEquiv (.long a) (.long b) != jankEquiv (.ofInt a) (.ofInt b) then some (a, b) else none
  IO.println s!"  == over {longs.length}² long pairs: {equivBad.length} deviate, e.g. {equivBad.take 3}"
  let quotBad := longs.flatMap fun a => longs.filterMap fun b =>
    if b == 0 then none else
    if !sameResult (jankQuot .x86_64 (.ofInt a) (.ofInt b)) (cljQuot (.long a) (.long b)) then some (a, b) else none
  IO.println s!"  quot over {longs.length}² long pairs (x86-64): {quotBad.length} deviate, e.g. {quotBad.take 4}"
  -- BigDecimal equality.
  let decs : List Dec := [⟨0, 0⟩, ⟨1, 0⟩, ⟨10, 1⟩, ⟨10000000000000000001, 19⟩, ⟨15, 17⟩, ⟨3, 16⟩, ⟨1, 16⟩, ⟨-1, 17⟩]
  let decBad := decs.flatMap fun a => decs.filterMap fun b => if jankDecEq a b != cljDecEq a b then some s!"(= {a.code} {b.code}) jank {jankDecEq a b}" else none
  IO.println s!"  bigdec = over {decs.length}² pairs: {decBad.length} deviate, e.g. {decBad.take 4}"
  -- NaN boxing.
  IO.println "== numbers: NaN boxing"
  for (label, bits) in [("x86-64 default NaN (Inf-Inf, 0*Inf, 0/0)", defaultNaN .x86_64), ("AArch64 default NaN", defaultNaN .aarch64),
      ("##NaN (jank_nan)", (0x7FF8000000000000 : BitVec 64)), ("-0.0", (0x8000000000000000 : BitVec 64))] do
    IO.println s!"  {label}: bits {bits.toHex}, decoded as {reprStr (decode (tagReal bits))}"
  -- parse-long / parse-double over every string of length ≤ 3 on a small alphabet.
  IO.println "== numbers: parse-long, parse-double"
  let alphabet := ['1', ' ', '+', '-', '.', 'e', 'd', 'i', 'n', 'f']
  let rec strings : Nat → List String
    | 0 => [""]
    | n + 1 => strings n ++ ((strings n).filter (·.length == n)).flatMap fun s => alphabet.map fun c => s.push c
  let all := strings 3
  let longBad := all.filter fun s => jankParseLong s != cljParseLong s
  IO.println s!"  parse-long over {all.length} strings: {longBad.length} deviate, e.g. {longBad.take 6 |>.map fun s => (s, cljParseLong s, jankParseLong s)}"
  let dblBad := all.filter fun s => jankParseDouble s != cljParseDouble s
  IO.println s!"  parse-double over {all.length} strings: {dblBad.length} deviate, e.g. {dblBad.take 8 |>.map fun s => (s, reprStr (cljParseDouble s), reprStr (jankParseDouble s))}"
  for s in ["1e400", "1e-400", "inf", "nan", "1.5 ", "1.5d", "Infinity", " 1.5"] do
    IO.println s!"    (parse-double {repr s}): Clojure {reprStr (cljParseDouble s)}, jank {reprStr (jankParseDouble s)}"

end

section
open Jank.Equality Jank.Hash
def equality : IO Unit := do
  for cs in [CharSign.signed] do
    for prop in [EqProperty.agrees, .symmetric, .hashConsistent] do
      report s!"equality: {reprStr prop}" (runEq cs prop) 3000 2000000
    -- The full table over the universe.
    let u := valueUniverse cs
    let pairs := u.flatMap fun a => u.map fun b => (a, b)
    let disagree := pairs.filter fun (a, b) => jankEq cs fuel a b != cljEq fuel a b
    let asym := pairs.filter fun (a, b) => jankEq cs fuel a b != jankEq cs fuel b a
    let hashBad := pairs.filter fun (a, b) => jankEq cs fuel a b && jankHash cs fuel a != jankHash cs fuel b
    IO.println s!"  table over {u.length}² = {pairs.length} pairs: {disagree.length} disagree with Clojure, {asym.length} asymmetric, {hashBad.length} equal with different hashes"
    let showPairs := fun (l : List (V × V)) => l.map fun (a, b) => s!"(= {a.code} {b.code}) jank {jankEq cs fuel a b} clj {cljEq fuel a b}"
    -- smallest examples by printed size
    let bySize := fun (l : List (V × V)) => (l.toArray.qsort fun (a, b) (c, d) => (a.code.length + b.code.length) < (c.code.length + d.code.length)).toList
    IO.println s!"  smallest disagreements:"
    for line in showPairs ((bySize disagree).take 12) do IO.println s!"    {line}"
    IO.println s!"  written by hand:"
    for (a, b) in handPairs do
      IO.println s!"    (= {a.code} {b.code}): jank {jankEq cs fuel a b}, Clojure {cljEq fuel a b}; jank hashes {jankHash cs fuel a} vs {jankHash cs fuel b}"
    IO.println s!"  smallest hash inconsistencies:"
    for (a, b) in (bySize hashBad).take 12 do
      IO.println s!"    (= {a.code} {b.code}) true; hashes {jankHash cs fuel a} vs {jankHash cs fuel b}"

end

section
def collections : IO Unit := do
  IO.println "== vector: transient nth after persistent!"
  IO.println s!"  jank {reprStr ((Jank.Vector.tNth {data := [7], active := false} 0).toOption)}, Clojure {reprStr ((Jank.Vector.cTNth {data := [7], active := false} 0).toOption)}"
  report "array map: a transient never changes the map it came from (3 operations)" (Jank.ArrayMap.run false 3) 3000 3000000
  report "array map, to_transient cloning (the fix), 3 operations" (Jank.ArrayMap.run true 3) 3000 3000000

def concurrency : IO Unit := do
  for sc in [Jank.Atom.selfRemove, Jank.Atom.nestedSwap, Jank.Atom.casFresh, Jank.Atom.casRace, Jank.Atom.counter2, Jank.Atom.counter] do
    for (llsc, label) in [(false, "x86-64 (strong CAS)"), (true, "LL/SC (weak CAS may fail)")] do
      report s!"atom: {sc.name}, jank on {label}" (Jank.Atom.runScenario sc llsc false) 2000 500000
    report s!"atom: {sc.name}, Clojure semantics" (Jank.Atom.runScenario sc true true) 2000 500000
  -- The story of the nested-swap deadlock.
  match exhaust (Jank.Atom.runScenario Jank.Atom.nestedSwap false false) 500000 with
  | .found c =>
    let c := shrink (Jank.Atom.runScenario Jank.Atom.nestedSwap false false) c
    IO.println s!"  story of the shrunk nested-swap deadlock ({c.taken.size} decisions):"
    for line in Jank.Atom.storyOf Jank.Atom.nestedSwap false false (Source.path c.values) do IO.println s!"    {line}"
  | _ => pure ()
  report "alter-meta!: two threads, jank" (Jank.Atom.runAlterMeta false) 200 10000
  report "alter-meta!: two threads, Clojure (synchronized)" (Jank.Atom.runAlterMeta true) 200 10000
  for b in [Jank.Delay.Body.returnsNil, .returnsValue, .throws] do
    report s!"delay: one thread, two derefs, body {reprStr b}, jank" (Jank.Delay.runDelay b false 1 2) 200 10000
    report s!"delay: two threads, one deref each, body {reprStr b}, jank" (Jank.Delay.runDelay b false 2 1) 200 100000
    report s!"delay: two threads, body {reprStr b}, Clojure" (Jank.Delay.runDelay b true 2 1) 200 100000
  report "promise: two concurrent delivers, jank" (Jank.Delay.runPromise false 2 0) 200 100000
  report "promise: two concurrent delivers, Clojure" (Jank.Delay.runPromise true 2 0) 200 100000
  report "promise: a deliver and a deref with a timeout, jank" (Jank.Delay.runPromise false 1 1) 200 100000
  report "promise: a deliver and a deref with a timeout, Clojure" (Jank.Delay.runPromise true 1 1) 200 100000
  report "bindings: futures and OS thread ids, jank" (fun s => (Jank.Bindings.run false s).1) 200 100000
  report "bindings: futures and OS thread ids, Clojure" (fun s => (Jank.Bindings.run true s).1) 200 100000
  match exhaust (fun s => (Jank.Bindings.run false s).1) 100000 with
  | .found c =>
    IO.println "  story of the found timeline:"
    for line in (Jank.Bindings.run false (Source.path c.values)).2 do IO.println s!"    {line}"
  | _ => pure ()

def evaluator : IO Unit := do
  report "try/catch/finally" Jank.Try.run 500 1000
end

def main (args : List String) : IO UInt32 := do
  let only := args.head?
  if only.isNone || only == some "numbers" then numbers
  if only.isNone || only == some "equality" then equality
  if only.isNone || only == some "collections" then collections
  if only.isNone || only == some "concurrency" then concurrency
  if only.isNone || only == some "evaluator" then evaluator
  return 0
