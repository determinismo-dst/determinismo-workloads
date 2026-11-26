import Jank.R8.Boost.Check
import Jank.R8.Boost.X8

/-! Round 8, area B: `jank8-boost`.
- `inputs FILE`: write check.cpp's input lines.
- `compare IN X86 ARM ARMNF`: the replica against boost's three builds, per operation.
- `spec`: the replica against the value-level rules of `Jank.R8.Boost.Spec` (S4).
- `programs`: the programs that see S4: stock, with the combined patch, Clojure.
- `x8scan`: `(compare 1M (* P (/ 1M P)))` for P = 2^k, k = 1..400, stock and patched.
- `brief`: the brief's values. -/

open Jank.R3.Boost.Dec Jank.R8.Boost Jank.R8.Boost.Check

def parseItem (line : String) : Item :=
  match line.splitOn "\t" with
  | [op, a] => { op := op, a := a }
  | [op, a, b] => { op := op, a := a, b := b }
  | _ => { op := "?", a := line }

def readLines (path : String) : IO (Array String) := do
  let ls ← IO.FS.lines path
  return ls

def cmdInputs (path : String) : IO Unit := do
  let items := allInputs
  IO.FS.writeFile path (String.intercalate "\n" (items.map Item.line) ++ "\n")
  IO.println s!"{items.length} lines written to {path}"

def cmdCompare (inp x86 arm armnf : String) : IO Unit := do
  let items := (← readLines inp).map parseItem
  let bx ← readLines x86
  let ba ← readLines arm
  let bn ← readLines armnf
  IO.println s!"lines: input {items.size}, boost x86-64 {bx.size}, arm64 {ba.size}, arm64 no-FMA {bn.size}"
  let ts := compareLines items bx ba bn
  let mut tot := 0
  let mut dx := 0
  for t in ts do
    tot := tot + t.total
    dx := dx + t.diffX86
    IO.println s!"{t.op}: {t.total} lines; replica differs from boost x86-64 on {t.diffX86}, arm64 on {t.diffArm}, arm64 without FMA contraction on {t.diffArmNoFma}; boost arm64 differs from boost x86-64 on {t.armVsX86}"
    for e in t.examples do IO.println s!"  {e}"
  IO.println s!"all: {tot} lines; replica differs from boost x86-64 on {dx}"

def cmdSpec : IO Unit := do
  let ts := specCheck allInputs
  for t in ts do
    IO.println s!"{t.name}: {t.checked} checked, {t.agree} agree, {t.checked - t.agree} differ"
    for e in t.examples do IO.println s!"  {e}"

def cmdPrograms : IO Unit := do
  for (name, p) in programs do
    IO.println s!"{name}\n  {p.src}\n  Clojure {p.clj}\n  jank stock {p.jank false}\n  jank patched {p.jank true}"

def cmdX8Scan : IO Unit := do
  let mut stockFail : Array Nat := #[]
  let mut patchedFail : Array Nat := #[]
  for k in [1:401] do
    let p := x8 k
    if p.jank false != "0" then stockFail := stockFail.push k
    if p.jank true != "0" then patchedFail := patchedFail.push k
  IO.println s!"(compare 1M (* P (/ 1M P))), P = 2^k, k = 1..400 (Clojure 0 for every k)"
  IO.println s!"  stock not 0 for {stockFail.size} k: {stockFail.toList}"
  IO.println s!"  patched not 0 for {patchedFail.size} k: {patchedFail.toList}"

/-- Stock division by a divisor with no prime factor but 2 and 5 (a terminating quotient): how often
is boost's Newton quotient not the exact one (S2's exact_divide gives the exact quotient, cut by S4
only past the kept digits)? Complete over 2^a·5^b, a ≤ 120, b ≤ 80, numerators 1, 3 and 7. -/
def cmdInexact : IO Unit := do
  let mut total := 0
  let mut inexact := 0
  let mut below := 0
  let mut above := 0
  let mut cutOnly := 0
  let mut firstFew : Array String := #[]
  for a in [0:121] do
    for b in [0:81] do
      let d := 2 ^ a * 5 ^ b
      for n in [1, 3, 7] do
        match rd (toString n), rd (toString d) with
        | .ok x, .ok y =>
          total := total + 1
          let q := x.div y
          match exactDivide x y with
          | .ok qx =>
            let c := cmp q qx
            if c != 0 then
              inexact := inexact + 1
              if c < 0 then below := below + 1 else above := above + 1
              if firstFew.size < 12 then firstFew := firstFew.push s!"{n}/2^{a}·5^{b}: stock {if c < 0 then "below" else "above"}"
            -- S2's quotient against Clojure's exact one: is it cut (S4)?
            match Jank.R3.Boost.Java.BD.div (cljRead (toString n)) (cljRead (toString d)) with
            | .ok e => if (Check.exactOf qx).cmp e != 0 then cutOnly := cutOnly + 1
            | .error _ => pure ()
          | .error _ => pure ()
        | _, _ => pure ()
  IO.println s!"stock (/ n 2^a·5^b), n in [1, 3, 7], a <= 120, b <= 80 (complete): {total} quotients, {inexact} not exact ({below} below, {above} above the exact quotient); S2's quotient is cut (S4) on {cutOnly}"
  for f in firstFew do IO.println s!"  {f}"

def cmdBrief : IO Unit := do
  let P := p200
  for it in ([{ op := "div", a := "1", b := P }, { op := "xdiv", a := "1", b := P },
              { op := "pq", a := "1", b := P }, { op := "px", a := "1", b := P },
              { op := "div", a := "6.0", b := "3.0" }, { op := "xdiv", a := "6.0", b := "3.0" },
              { op := "rem", a := "1E130", b := "3" }, { op := "sub", a := "1", b := "1E-130" },
              { op := "div", a := "60", b := "3.0" }, { op := "div", a := "1.000", b := "4" },
              { op := "add", a := "1.25", b := "1.75" }, { op := "div", a := "6", b := "3" },
              { op := "rd", a := "0.00001" }] : List Item) do
    IO.println s!"{it.line}\n  {it.eval}"
  match rd "1", rd P with
  | .ok o, .ok p =>
    let q := o.div p
    IO.println s!"stock inverse limbs {limbsVal q} exp {q.exp}"
    match exactDivide o p with
    | .ok qx => IO.println s!"S2 quotient limbs {limbsVal qx} exp {qx.exp}"
    | .error m => IO.println m
    IO.println s!"P limbs {limbsVal p} exp {p.exp}"
  | _, _ => IO.println "read error"

def main (args : List String) : IO Unit := do
  match args with
  | ["inputs", f] => cmdInputs f
  | ["compare", i, x, a, n] => cmdCompare i x a n
  | ["spec"] => cmdSpec
  | ["programs"] => cmdPrograms
  | ["x8scan"] => cmdX8Scan
  | ["brief"] => cmdBrief
  | ["inexact"] => cmdInexact
  | _ => IO.println "usage: jank8-boost inputs F | compare IN X86 ARM ARMNF | spec | programs | x8scan | brief"
