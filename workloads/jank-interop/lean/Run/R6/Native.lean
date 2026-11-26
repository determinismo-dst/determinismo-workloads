import Jank.R6.Native.Types
import Jank.R6.Native.Math
import Jank.R6.Native.Theorems
import Jank.R6.Native.Typing

/-! Round 6 driver, native values (`jank6-native <part>`): `walk` (every source × source × op ×
path, complete), `forms` (the walk's Clojure forms with the model's Clojure prediction, for the
JVM check), `typing` (the analyzer's typing walk), `examples`. -/

open Jank.R6.Native

def swName : List (String × Sw) :=
  [("R33 class (bool natives are numbers to math.hpp): R33a.diff + R33b.diff", { rejectBool := true }),
   ("P9 (char natives are numbers to math.hpp): no diff", { rejectChar := true }),
   ("LG1 (unsigned natives under C++'s conversions in < <= > >= min max /): LG1.diff", { lg1Widen := true }),
   ("R25/D1 class (two narrow ints, or a u32 hash, wrap in + - *): LG2a.diff (agent N)", { checkedOps := true }),
   ("P8 (float array elements compute in binary32): no diff", { floatArith := true }),
   ("P4 (min/max of two native types give their common type): LG1.diff", { minmax := true }),
   ("P5 (max keeps the first operand on a tie): no diff", { maxTie := true }),
   ("P6 (hash is unsigned): no diff", { hashSigned := true }),
   ("P7 (float is a double): no diff", { floatF32 := true }),
   ("R122 (bytes are unsigned): R122a.diff", { bytesSigned := true })]

def classify (c : Case) : String := Id.run do
  for (n, sw) in swName do
    if !c.deviates sw then return n
  if !c.deviates Sw.mine then return "LG1.diff, both parts together"
  if !c.deviates Sw.every then return "several switches together"
  return "residual (no switch)"

structure Tally where
  name : String
  inline : Nat := 0
  fnValue : Nat := 0
  byOp : List (String × Nat) := []
  examples : Array String := #[]
  deriving Inhabited

def bump (l : List (String × Nat)) (k : String) : List (String × Nat) :=
  if l.any (·.1 == k) then l.map (fun (a, n) => if a == k then (a, n + 1) else (a, n)) else l ++ [(k, 1)]

def walk : IO Unit := do
  let cases := allCases
  let mut total := 0
  let mut devs := 0
  let mut devInline := 0
  let mut devFn := 0
  let mut tallies : Array Tally := #[]
  let mut realClj := 0
  for c in cases do
    total := total + 1
    let j := (c.jank Sw.none).seen
    let cr := c.clj true
    -- also count against Clojure without D2/overflow accepted
    if !agrees j (c.clj false) then realClj := realClj + 1
    if !agrees j cr then
      devs := devs + 1
      if c.fnValue then devFn := devFn + 1 else devInline := devInline + 1
      let k := classify c
      let idx := tallies.findIdx? (·.name == k)
      let t : Tally := match idx with | some i => tallies[i]! | none => { name := k }
      let t := if c.fnValue then { t with fnValue := t.fnValue + 1 } else { t with inline := t.inline + 1 }
      let t := { t with byOp := bump t.byOp s!"{c.op.sym}{if c.fnValue then " (fn value)" else ""}" }
      let t := if t.examples.size < 6 && (t.examples.all fun e => !e.startsWith s!"[{c.a.kind} {c.op.sym} {c.b.kind}") then
        { t with examples := t.examples.push s!"[{c.a.kind} {c.op.sym} {c.b.kind}] {c.form}: Clojure {(c.clj false).show}, jank {j.show}" }
        else t
      tallies := match idx with | some i => tallies.set! i t | none => tallies.push t
  IO.println s!"walk: {sources.length} sources × {sources.length} × {Op.all.length} ops × 2 paths (a parameter paired only with a non-parameter): {total} cases, complete"
  IO.println s!"  differ from Clojure 1.12: {realClj}; differ from the reference (Clojure with D2's truncating `/`, long overflow (LG2, agent N) and division by zero set aside): {devs} (inlined {devInline}, fn value {devFn})"
  for t in tallies do
    IO.println s!"  {t.name}: {t.inline + t.fnValue} (inlined {t.inline}, fn value {t.fnValue})"
    IO.println s!"    by op: {t.byOp}"
    for e in t.examples do IO.println s!"    e.g. {e}"
  -- residuals after the fixes
  let mut afterMine := 0
  let mut afterEvery := 0
  for c in cases do
    if c.deviates Sw.mine then afterMine := afterMine + 1
    if c.deviates Sw.every then afterEvery := afterEvery + 1
  IO.println s!"  with LG1.diff: {afterMine} differ; with every switch: {afterEvery}"
  -- the fn-value path never sees a native type: does it deviate only by D1, X5, X3, X6, R122?
  let mut fnNative := 0
  for c in cases do
    if c.fnValue && c.deviates { Sw.every with lg1Widen := false, minmax := false } then fnNative := fnNative + 1
  IO.println s!"  fn-value cases still differing with every switch except LG1.diff's: {fnNative} (no fn-value case needs LG1.diff)"
where
  showJ (j : CR) : String := j.show

/-- The model's Clojure prediction as a token the JVM checker reads: `L:n` a long-category
number, `D:bits` a double or float (the double's bits), `R:n/d`, `B:b`, `C:c`, `T` throws. -/
def token : CR → String
  | .val (.long v) => s!"L:{v}"
  | .val (.dbl x _) => s!"D:{(BitVec.ofNat 64 x.toBits.toNat).toInt}"
  | .val (.ratio n d) => s!"R:{n}/{d}"
  | .val (.bool b) => s!"B:{b}"
  | .val (.char c) => s!"C:{c}"
  | .threw _ => "T"
  | .accepted => "A"

/-- The walk's forms with the model's (real) Clojure prediction, `form<TAB>token`, for the JVM. -/
def forms (path : String) : IO Unit := do
  let mut lines : Array String := #[]
  for c in allCases do
    lines := lines.push s!"{c.form}\t{token (c.clj false)}"
  IO.FS.writeFile path ("\n".intercalate lines.toList ++ "\n")
  IO.println s!"wrote {lines.size} forms to {path}"

def examples : IO Unit := do
  let ex : List Case :=
    [{ op := .lt, a := .lit (-1), b := .count 1, fnValue := false },
     { op := .lt, a := .param (-1), b := .count 1, fnValue := false },
     { op := .lt, a := .lit (-1), b := .count 1, fnValue := true },
     { op := .gt, a := .count 1, b := .lit (-1), fnValue := false },
     { op := .lte, a := .lit (-1), b := .count 1, fnValue := false },
     { op := .max, a := .count 1, b := .lit (-1), fnValue := false },
     { op := .max, a := .count 1, b := .param (-1), fnValue := false },
     { op := .min, a := .count 3, b := .lit (-1), fnValue := false },
     { op := .div, a := .count 3, b := .lit (-1), fnValue := false },
     { op := .div, a := .lit (-2), b := .count 3, fnValue := false },
     { op := .lt, a := .int_ (-1), b := .count 1, fnValue := false },
     { op := .lt, a := .bitAnd (-1), b := .count 1, fnValue := false },
     { op := .lt, a := .lit (-1), b := .alength 2, fnValue := false },
     { op := .lt, a := .hash 2, b := .lit 0, fnValue := false },
     { op := .sub, a := .hash 0, b := .lit 1, fnValue := false },
     { op := .mul, a := .hash 1, b := .lit 2, fnValue := false },
     { op := .max, a := .lit 1, b := .dlit 0.5, fnValue := false },
     { op := .min, a := .lit 1, b := .dlit 2.5, fnValue := false },
     { op := .max, a := .lit 1, b := .dlit 1.0, fnValue := true },
     { op := .add, a := .float_ 0.1, b := .dlit 2.5, fnValue := false },
     { op := .add, a := .floatA 0.1, b := .lit 1, fnValue := false },
     { op := .add, a := .pred true, b := .lit 1, fnValue := false },
     { op := .add, a := .charA 97, b := .lit 1, fnValue := false },
     { op := .lt, a := .byteA (-1), b := .lit 0, fnValue := false },
     { op := .add, a := .lit 2147483647, b := .lit 1, fnValue := false },
     { op := .mul, a := .count 3, b := .lit (-2), fnValue := false },
     { op := .add, a := .count 1, b := .lit (-3), fnValue := false }]
  for c in ex do
    let j := (c.jank Sw.none).seen
    let jf := (c.jank Sw.mine).seen
    IO.println s!"{c.form}{if c.fnValue then "  [fn value]" else "  [inlined]"}"
    IO.println s!"    Clojure {(c.clj false).show}; jank {j.show}; with LG1.diff {jf.show}"

def main (args : List String) : IO Unit := do
  match args with
  | ["walk"] => walk
  | ["forms", p] => forms p
  | ["examples"] => examples
  | ["typing"] => Typing.run
  | ["hash"] =>
    for v in [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, -1] do
      let h := hashLong v
      IO.println s!"(hash {v}): jank {h.toNat}, Clojure {wrapTo .int h.toNat}"
  | _ => IO.println "usage: jank6-native walk | forms PATH | examples | typing | hash"
