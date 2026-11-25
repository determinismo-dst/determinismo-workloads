import Jank.R3.Search.Common
import Jank.R5.Core.Inst

/-!
# Round 5, core: the `#inst` searches

- `instWorld`: timestamps built field by field (Clojure's nesting: a field only after the one
  before it), each field drawn from well-formed and malformed variants: years (4 digits, 2
  digits, signed), months and days (valid, out of range, one digit), the `T` (or `t`), hours,
  minutes and seconds (valid, 60, one digit, empty), fractions (none, `.`, 1 to 14 digits),
  offsets (none, `Z`, `z`, ±hh:mm, -00:00, without colon, hours only, one-digit hours, out of
  range, without sign). Every input is read by jank's replica and by Clojure's; each
  disagreement is counted under its trigger class.
- `rawWorld`: every string of length ≤ n over `0 1 2 9 - : T Z + .` (accepted or rejected only).
- `eqWorld`: `=` between two insts that differ below the millisecond.
-/

namespace Jank.R5.Core.InstSearch

open Determinismo Jank.R5.Core.Inst

structure W where
  decisions : Decisions := {}

instance : Chaotic W where
  decisions w := w.decisions
  setDecisions w d := { w with decisions := d }

abbrev WM := EStateM Stop W

def runW (body : WM Unit) (source : Source) : Ended :=
  match body.run { decisions := { source, limit := 1000 } } with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }
  | .error (.nodeDown _) w => { taken := w.decisions.taken, violation := none }

def pickFrom (name : String) (xs : List String) : WM String := do
  let i ← decide (σ := W) name xs.length
  return xs.getD i ""

def years : List String := ["2020", "1969", "9999", "20", "+2020", "-2020"]
def months : List String := ["", "-01", "-02", "-12", "-13", "-1"]
def days : List String := ["", "-01", "-29", "-31", "-1", "-00"]
def tees : List String := ["", "T", "t"]
def hours : List String := ["00", "23", "24", "1"]
def minutes : List String := ["", ":00", ":59", ":60", ":5"]
def seconds : List String := ["", ":00", ":59", ":60", ":5", ":"]
def fractions : List String :=
  ["", ".", ".5", ".0001", ".9995", ".123456789", ".1234567891", ".12345678912",
   ".123456789123", ".1234567891234", ".12345678912345"]
def offsets : List String :=
  ["", "Z", "z", "+05:00", "-05:00", "-00:00", "+0500", "+05", "+5:00", "+24:00", "+05:60",
   "05:00", "+23:59"]

/-- The drawn fields (empty = absent). -/
structure Ts where
  y : String
  mo : String := ""
  d : String := ""
  t : String := ""
  h : String := ""
  mi : String := ""
  s : String := ""
  f : String := ""
  off : String := ""

def Ts.text (x : Ts) : String := x.y ++ x.mo ++ x.d ++ x.t ++ x.h ++ x.mi ++ x.s ++ x.f ++ x.off

def genTs : WM Ts := do
  let y ← pickFrom "inst.year" years
  let mut x : Ts := { y }
  let mo ← pickFrom "inst.month" months
  if mo != "" then
    x := { x with mo }
    let d ← pickFrom "inst.day" days
    if d != "" then
      x := { x with d }
      let t ← pickFrom "inst.T" tees
      if t != "" then
        x := { x with t, h := ← pickFrom "inst.hour" hours }
        let mi ← pickFrom "inst.minute" minutes
        if mi != "" then
          x := { x with mi }
          let s ← pickFrom "inst.second" seconds
          if s != "" then
            x := { x with s, f := ← pickFrom "inst.fraction" fractions }
  return { x with off := ← pickFrom "inst.offset" offsets }

def fracDigits (x : Ts) : Nat := if x.f.length > 0 then x.f.length - 1 else 0

/-- Why Clojure reads it and jank doesn't. -/
def rejectClass (x : Ts) : String :=
  if x.off == "Z" then "G-inst: Z offset rejected"
  else if x.s == ":60" then "G-inst: leap second rejected"
  else if fracDigits x ≥ 10 then "G-inst: fraction of 10+ digits rejected"
  else if x.s == "" then
    (if x.off == "" then "G-inst: partial form rejected (U82)" else "G-inst: partial form with offset rejected (U82)")
  else "unexplained (Clojure reads, jank rejects)"

/-- Why jank reads it and Clojure doesn't (counted, not reported). -/
def acceptClass (x : Ts) : String :=
  if x.y.length != 4 then "accepts-invalid: year not 4 digits or signed"
  else if x.mo == "-1" || x.d == "-1" || x.h == "1" || x.mi == ":5" || x.s == ":5" then "accepts-invalid: one-digit field"
  else if x.mi == ":60" then "accepts-invalid: minute 60"
  else if x.s == ":" then "accepts-invalid: seconds without digits"
  else if x.off ∈ ["+0500", "+05", "+5:00", "05:00"] then "accepts-invalid: offset form"
  else if x.off ∈ ["+24:00", "+05:60"] then "accepts-invalid: offset out of range"
  else if fracDigits x ≥ 10 then "accepts-invalid: digits after a fraction"
  else if x.s != "" && x.f == "" && x.off == "" then "accepts-invalid: other"
  else "accepts-invalid: other"

/-- The property: the same verdict, the same instant (`inst-ms`, hence the printed form), and
`(= x (read-string (pr-str x)))` wherever Clojure's holds. -/
def instCase : WM Unit := do
  let x ← genTs
  let txt := x.text
  let j := jankRead txt.toList
  let c := cljRead txt.toList
  match j, c with
  | none, none => pure ()
  | none, some ms =>
    violate (σ := W) (rejectClass x) s!"#inst \"{txt}\": Clojure {cljPr ms}, jank read error"
  | some _, none =>
    violate (σ := W) (acceptClass x) s!"#inst \"{txt}\": Clojure read error, jank {jankPr j.get!} (format {(jankFormatUsed txt.toList).getD 0})"
  | some ns, some ms =>
    if jankInstMs ns != ms then
      let cls :=
        if fracDigits x ≥ 10 then "G-inst: fraction of 10+ digits read as an offset"
        else if ns < 0 && ns % 1000000 != 0 then "G-inst: sub-millisecond before 1970 rounds toward 1970"
        else "unexplained (instants differ)"
      violate (σ := W) cls s!"#inst \"{txt}\": Clojure {cljPr ms} ({ms}), jank {jankPr ns} ({jankInstMs ns})"
    else
      let printed := (fieldsOfMs (truncMs ns) ++ "-00:00").toList
      let jrt := jankRead printed == some ns
      let crt := cljRead printed == some ms
      if crt && !jrt then
        violate (σ := W) "G-inst: (= x (read-string (pr-str x))) false below the millisecond"
          s!"#inst \"{txt}\": jank keeps {ns} ns, prints {jankPr ns}"

def rawAlphabet : List Char := ['0', '1', '2', '9', '-', ':', 'T', 'Z', '+', '.']

/-- Accepted or rejected, for every short string. -/
def rawCase (maxLen : Nat) : WM Unit := do
  let len ← decide (σ := W) "raw.length" (maxLen + 1)
  let mut cs : List Char := []
  for _ in [0:len] do
    let i ← decide (σ := W) "raw.char" rawAlphabet.length
    cs := cs ++ [rawAlphabet.getD i '0']
  let j := jankRead cs
  let c := cljRead cs
  let txt := String.ofList cs
  match j, c with
  | none, some ms =>
    let cls := if cs.contains 'Z' then "G-inst: Z offset rejected"
      else "G-inst: partial form or offset rejected (U82)"
    violate (σ := W) cls s!"#inst \"{txt}\": Clojure {cljPr ms}, jank read error"
  | some ns, none =>
    violate (σ := W) "accepts-invalid (raw)" s!"#inst \"{txt}\": Clojure read error, jank {jankPr ns}"
  | _, _ => pure ()

def eqFractions : List String := ["", ".0001", ".0002", ".001", ".0019", ".5", ".50001", ".9999"]
def eqBases : List String := ["2020-01-01T00:00:00", "1969-12-31T23:59:59"]

/-- `=`: Clojure compares `getTime()`, jank the time points. -/
def eqCase : WM Unit := do
  let b ← pickFrom "eq.base" eqBases
  let f1 ← pickFrom "eq.f1" eqFractions
  let f2 ← pickFrom "eq.f2" eqFractions
  let a := (b ++ f1).toList
  let c := (b ++ f2).toList
  match jankRead a, jankRead c, cljRead a, cljRead c with
  | some x, some y, some u, some v =>
    if (x == y) != (u == v) then
      violate (σ := W) "G-inst: = below the millisecond"
        s!"(= #inst \"{b}{f1}\" #inst \"{b}{f2}\"): Clojure {u == v}, jank {x == y}"
  | _, _, _, _ => violate (σ := W) "unexplained (a read failed)" s!"{b}{f1} / {b}{f2}"

/-- One line per input for the JVM check: the text, Clojure's milliseconds (or `E`). -/
def dumpLine (txt : String) : String :=
  match cljRead txt.toList with
  | some ms => s!"{txt}\t{ms}"
  | none => s!"{txt}\tE"

/-- Every input of `instWorld`, in walk order (for the JVM check). -/
partial def allTs : List Ts := Id.run do
  let mut out : Array Ts := #[]
  for y in years do
    for off in offsets do
      out := out.push { y, off }
      for mo in months.drop 1 do
        out := out.push { y, mo, off }
        for d in days.drop 1 do
          out := out.push { y, mo, d, off }
          for t in tees.drop 1 do
            for h in hours do
              out := out.push { y, mo, d, t, h, off }
              for mi in minutes.drop 1 do
                out := out.push { y, mo, d, t, h, mi, off }
                for s in seconds.drop 1 do
                  for f in fractions do
                    out := out.push { y, mo, d, t, h, mi, s, f, off }
  return out.toList

end Jank.R5.Core.InstSearch
