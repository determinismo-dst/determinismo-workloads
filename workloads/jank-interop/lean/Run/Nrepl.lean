import Jank.Nrepl.Search

open Determinismo Jank.NreplServer

def describeC (c : Counterexample) : String :=
  s!"{c.property} after {c.runs} timelines, {c.taken.size} decisions: {c.detail}"

def indent (s : String) : String := "\n".intercalate ((s.splitOn "\n").map ("      " ++ ·))

def reportScenario (s : Scenario) (seeds : Nat) (maxRuns : Nat) : IO Unit := do
  let t0 ← IO.monoMsNow
  IO.println s!"== {s.name}"
  match explore s.run seeds with
  | some c =>
    IO.println s!"  explore ({seeds} seeds): {describeC c}"
    let c := shrink s.run c
    IO.println s!"  shrunk to {c.taken.size} decisions: {c.detail}"
    if c.taken.size > 0 then IO.println s!"  tape:\n{indent (tape c.taken)}"
    IO.println "  story:"
    for line in s.story (Source.path c.values) do IO.println s!"      {line}"
  | none => IO.println s!"  explore ({seeds} seeds): nothing"
  match exhaust s.run maxRuns with
  | .found c =>
    let c := shrink s.run c
    IO.println s!"  exhaust: found after {c.runs} timelines; shrunk to {c.taken.size} decisions: {c.property}"
  | .complete n => IO.println s!"  exhaust: complete, {n} timelines, nothing"
  | .stopped n => IO.println s!"  exhaust: stopped at {n} timelines, nothing"
  IO.println s!"  ({(← IO.monoMsNow) - t0} ms)"
  (← IO.getStdout).flush

def bencodeSearches : IO Unit := do
  let p : Platform := {}
  -- decode(encode x) = x
  let vals := valueUniverse 2
  let bad := vals.filter fun v => !roundTrip p v
  IO.println s!"== bencode: parse (write v) = v over {vals.length} values (longs, strings with \\0 \\n and UTF-8, vectors, string-keyed maps, nested)"
  IO.println s!"  {bad.length} fail{if bad.isEmpty then "" else ": " ++ toString ((bad.take 5).map JVal.render)}"
  let badU := vals.filter fun v => !roundTrip { signedChar := false } v
  IO.println s!"  unsigned char: {badU.length} fail"
  -- arbitrary bytes
  for n in [4, 5] do
    let all := allStrings alphabet n
    let cls := all.map fun b => (b, classify p b)
    let count (k : Class) := (cls.filter (·.2 == k)).length
    IO.println s!"== bencode: every byte string of length ≤ {n} over \"{showBytes alphabet}\" ({all.length} buffers), parse vs the spec decoder"
    IO.println s!"  agree {count .agree}, stall (spec invalid, jank waits forever) {count .stall}, lenient (spec invalid, jank a message) {count .lenient}, wrong message {count .wrongMessage}, crash {count .crash}"
    let ex (k : Class) := ((cls.filter (·.2 == k)).take 8).map fun (b, _) => "\"" ++ showBytes b ++ "\""
    IO.println s!"  stall e.g. {ex .stall}"
    IO.println s!"  lenient e.g. {ex .lenient}"
    if count .wrongMessage > 0 then IO.println s!"  wrong e.g. {ex .wrongMessage}"
  -- hand-picked
  for b in ["d2:op8:describee\n", "i 5e", "i+5e", "i9999999999999999999e", "3x:abc", "ie", "d1:ai1ee", "d1:ai1e1:ai2ee", "li1el", "l"] do
    let bb := bytes b
    IO.println s!"  \"{showBytes bb}\": spec {reprStr (specDecode bb)}, jank {reprStr (parse p (some bb))}"
  -- nesting depth
  IO.println "== bencode: nesting (parse-recur recurses once per level)"
  for d in [63, 64, 65, 1000] do
    IO.println s!"  {d} × 'l' with a 64-frame stack: {reprStr (parse { maxDepth := 64 } (some (List.replicate d 108)))}"
  -- chunked reads
  let m1 := (write (.map [(JVal.s "op", JVal.s "eval"), (JVal.s "code", JVal.s "(+ 1 2)"), (JVal.s "id", JVal.s "7")])).toOption.getD []
  let m2 := (write (.map [(JVal.s "op", JVal.s "describe"), (JVal.s "id", JVal.s "8")])).toOption.getD []
  let m3 := (write (.vec [.int (-12), JVal.s "a:b", .map []])).toOption.getD []
  for (label, stream) in [("two requests", m1 ++ m2), ("a list then a request", m3 ++ m2),
                          ("a request, a newline, a request", m1 ++ [10] ++ m2)] do
    IO.println s!"== read-message across partial reads: {label} ({stream.length} bytes)"
    match explore (chunkRun p stream 40) 3000 with
    | some c =>
      let c := shrink (chunkRun p stream 40) c
      IO.println s!"  explore (3000 seeds, up to 40 reads): found after {c.runs}: {c.detail}"
    | none => IO.println s!"  explore (3000 seeds, up to 40 reads): nothing"
    match exhaust (chunkRun p stream 3) 2000000 with
    | .found c =>
      let c := shrink (chunkRun p stream 3) c
      IO.println s!"  exhaust (every cut into ≤ 4 reads): found after {c.runs} timelines: {c.detail}"
    | .complete n => IO.println s!"  exhaust (every cut into ≤ 4 reads): complete, {n} chunkings, all decode the same"
    | .stopped n => IO.println s!"  exhaust: stopped at {n}"

def main (args : List String) : IO UInt32 := do
  let only := args.head?
  if only.isNone || only == some "bencode" then bencodeSearches
  if only.isNone || only == some "server" then
    for s in scenarios do
      reportScenario s s.seeds s.exhaustRuns
  -- `jank-nrepl scenario <k>`: one scenario.
  if only == some "scenario" then
    let k := (args.getD 1 "0").toNat!
    if let some s := scenarios[k]? then reportScenario s s.seeds s.exhaustRuns
  return 0
