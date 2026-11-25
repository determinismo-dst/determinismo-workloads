import Lean

/-!
# Round 5, core: `#inst`, from jank's reader through libstdc++'s `std::chrono::parse`

jank (upstream-r5/compiler+runtime, 94d32623):
- `read/parse.cpp` `parse_reader_macro_tagged` 1007-1124: `*data-readers*`, then
  `*default-data-reader-fn*`, then the built-in tags `#uuid`, `#inst`, `#cpp`;
  `parse_tagged_inst` 948-976 → `make_box<obj::inst>(str->data)`.
- `runtime/obj/inst.cpp` `inst_from_string` 30-57: for each format of
  `{ "%FT%T%Oz", "%FT%T%z", "%FT%T", "%F" }` a fresh `istringstream` imbued with
  `std::locale("en_US.utf-8")`, `is >> std::chrono::parse(format, o)`, success iff
  `!is.fail() && is.peek() == EOF`; else "Unrecognized date/time syntax".
  `inst_time_point` is `time_point<system_clock>` (nanoseconds with libstdc++).
- `to_string_impl` 73-77: `std::format("{:%FT%T}-00:00", time_point_cast<milliseconds>(value))`;
  `equal` 63-71 compares the time points; `to_hash` 104-107; no `compare` (object.cpp 228-233
  throws "compare" unsupported).
- `runtime/core.cpp` `inst_ms` 1056-1066: `duration_cast<milliseconds>(time_since_epoch)`.

libstdc++ 15.3.0 (`deps/libstdcxx-15.3.0/chrono_io.h`):
- `from_stream(…, sys_time<_Duration>&, …)` 2873-2897: `_Parser_t<_Duration>` with
  `_Year|_Month|_Day|_TimeOfDay`; a leap second sets failbit; else
  `tp = round<_Duration>(sys_days + time - offset)`.
- `_Parser::operator()` 3180-4452 (the cases jank's formats reach: literal characters 3344-3354,
  `%F` 3489-3513, `%T`/`%S` 3728-3860, `%z`/`%Oz` 4020-4105, the end 4183-4452), with
  `_S_read_unsigned` 2272-2302, `_S_read_signed` 2306-2321 (the sign is applied only when the read
  failed), `_S_try_read_digit` 2325-2344, `_S_read_chr` 2348-2362 (end of input sets eofbit and
  failbit).
- `basic_istream::peek` (istream.tcc) and its `sentry`: a peek on a stream that is not `good()`
  sets failbit; a peek at the end sets eofbit. This is why a second look past the end fails the
  whole parse.

Clojure 1.12 (`clojure-ref/src/clj/clojure/instant.clj`): `parse-timestamp` 50-121 (the regex,
`zero-fill-right` to 9 digits), `validated` 139-157, `construct-calendar`/`construct-date` 240-260
(a lenient `GregorianCalendar` in the offset's zone, milliseconds `(quot nanos 1000000)`),
`print-date` 163-178 (`yyyy-MM-dd'T'HH:mm:ss.SSS-00:00` in GMT); `LispReader.readTagged` 1435-1451
(`*data-readers*`, then `default-data-readers`, then `*default-data-reader-fn*`); `Date.equals`
and `Date.compareTo` compare `getTime()`.
-/

namespace Jank.R5.Core.Inst

open Lean Elab Term in
/-- `chars% "…"`: a string literal as a `List Char` the kernel can read (`String` is a byte array
in Lean 4.36, which `decide` cannot take apart). -/
elab "chars% " s:str : term => return toExpr s.getString.toList

/-! ## Civil dates (proleptic Gregorian: libstdc++'s `sys_days(year_month_day)`) -/

/-- `days_from_civil`: days since 1970-01-01. -/
def daysFromCivil (y0 : Int) (m d : Nat) : Int :=
  let y : Int := if m ≤ 2 then y0 - 1 else y0
  let era : Int := Int.fdiv y 400
  let yoe : Int := y - era * 400
  let mp : Int := if m > 2 then (m : Int) - 3 else (m : Int) + 9
  let doy : Int := Int.fdiv (153 * mp + 2) 5 + (d : Int) - 1
  let doe : Int := yoe * 365 + Int.fdiv yoe 4 - Int.fdiv yoe 100 + doy
  era * 146097 + doe - 719468

/-- `civil_from_days`: (year, month, day). -/
def civilFromDays (z0 : Int) : Int × Nat × Nat :=
  let z := z0 + 719468
  let era := Int.fdiv z 146097
  let doe := z - era * 146097
  let yoe := Int.fdiv (doe - Int.fdiv doe 1460 + Int.fdiv doe 36524 - Int.fdiv doe 146096) 365
  let y := yoe + era * 400
  let doy := doe - (365 * yoe + Int.fdiv yoe 4 - Int.fdiv yoe 100)
  let mp := Int.fdiv (5 * doy + 2) 153
  let d := doy - Int.fdiv (153 * mp + 2) 5 + 1
  let m := if mp < 10 then mp + 3 else mp - 9
  (if m ≤ 2 then y + 1 else y, m.toNat, d.toNat)

def isLeap (y : Int) : Bool := (y % 4 == 0) && (y % 100 != 0 || y % 400 == 0)

def lastDay (y : Int) (m : Nat) : Nat :=
  match m with
  | 2 => if isLeap y then 29 else 28
  | 4 | 6 | 9 | 11 => 30
  | _ => 31

/-! ## The stream: `istringstream` with libstdc++'s `peek`/`get` and their state bits -/

structure Strm where
  inp : List Char
  eof : Bool := false
  fail : Bool := false
  deriving Repr, BEq

/-- `basic_istream::peek()`: the sentry fails (and sets failbit) unless `good()`; at the end of
the buffer, eofbit and `eof()`. -/
def Strm.peek (s : Strm) : Strm × Option Char :=
  if s.eof || s.fail then ({ s with fail := true }, none)
  else match s.inp with
    | [] => ({ s with eof := true }, none)
    | c :: _ => (s, some c)

/-- `get()` after a `peek` that returned a character. -/
def Strm.get (s : Strm) : Strm := { s with inp := s.inp.drop 1 }

/-! ## `_Parser` for `sys_time<nanoseconds>`: the state of one `operator()` call -/

structure P where
  s : Strm
  errEof : Bool := false
  errFail : Bool := false
  y : Option Int := none
  m : Option Nat := none
  d : Option Nat := none
  /-- `__h`, preset to 0 for time points (PR libstdc++/114240). -/
  h : Option Nat := some 0
  min : Option Nat := none
  /-- `__s` in nanoseconds. -/
  sec : Option Nat := none
  tz : Option Int := none
  /-- `_ChronoParts`: `_Date` and `_TimeOfDay` (the latter preset). -/
  partDate : Bool := false
  partTime : Bool := true
  deriving Repr

def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'
def digitVal (c : Char) : Int := (c.toNat : Int) - ('0'.toNat : Int)

/-- `_S_try_read_digit`: a digit, or -1 (eofbit in `__err` when `peek` returned `eof()`). -/
def tryDigit (p : P) : P × Int :=
  let (s, c) := p.s.peek
  match c with
  | none => ({ p with s, errEof := true }, -1)
  | some ch => if isDigit ch then ({ p with s := s.get }, digitVal ch) else ({ p with s }, -1)

/-- `_S_read_unsigned(n)` for `n ≤ 9`: the first digit or failbit, then up to `n - 1` more
tries (a non-digit does not stop the tries). -/
def readUnsigned (n : Nat) (p : P) : P × Int :=
  let (p, v) := tryDigit p
  if v == -1 then ({ p with errFail := true }, -1)
  else
    (List.range (min n 9 - 1)).foldl (fun (acc : P × Int) _ =>
      let (q, w) := tryDigit acc.1
      if w != -1 then (q, acc.2 * 10 + w) else (q, acc.2)) (p, v)

/-- `_S_read_signed(n)`: an optional sign is consumed; the value is negated only when the read
failed (2316-2319). -/
def readSigned (n : Nat) (p : P) : P × Int :=
  let (s, c) := p.s.peek
  let p := { p with s }
  let (p, neg) := match c with
    | some '-' => ({ p with s := p.s.get }, true)
    | some '+' => ({ p with s := p.s.get }, false)
    | _ => (p, false)
  let (p, v) := readUnsigned n p
  if p.errFail && neg then (p, -v) else (p, v)

/-- `_S_read_chr(c)`: the character, or failbit (and eofbit at the end). -/
def readChr (ch : Char) (p : P) : P × Bool :=
  let (s, c) := p.s.peek
  match c with
  | none => ({ p with s, errEof := true, errFail := true }, false)
  | some x => if x == ch then ({ p with s := s.get }, true) else ({ p with s, errFail := true }, false)

/-- `%F` (3489-3513). -/
def dirF (p : P) : P :=
  let (p, yr) := readSigned 4 p
  let (p, _) := readChr '-' p
  let (p, mo) := readUnsigned 2 p
  let (p, _) := readChr '-' p
  let (p, dy) := readUnsigned 2 p
  if p.errFail then p
  else
    let ok := 1 ≤ mo && mo ≤ 12 && 1 ≤ dy && -32767 ≤ yr && yr ≤ 32767 &&
      dy.toNat ≤ lastDay yr mo.toNat
    if !ok then { p with y := none, m := none, d := none }
    else { p with y := some yr, m := some mo.toNat, d := some dy.toNat, partDate := true }

/-- The digits and point `%S` collected, as `from_chars(…, fixed)` reads them, in nanoseconds
(at most 9 fraction digits: the `long double` value rounds back to the exact nanosecond). -/
def secondsOf (intDigits : List Nat) (frac : Option (List Nat)) : Option Nat :=
  let ip := intDigits.foldl (fun a x => a * 10 + x) 0
  match frac with
  | none => if intDigits.isEmpty then none else some (ip * 1000000000)
  | some fd =>
    if intDigits.isEmpty && fd.isEmpty then none
    else
      let f := fd.foldl (fun a x => a * 10 + x) 0
      some (ip * 1000000000 + f * 10 ^ (9 - fd.length))

/-- `%S` for `nanoseconds` (the fractional branch, 3789-3858; the decimal point is
`numpunct<char>::decimal_point()` of en_US.UTF-8, '.'). -/
def dirS (p : P) : P :=
  let (p, d1) := tryDigit p
  let (p, ints) :=
    if d1 != -1 then
      let (p, d2) := tryDigit p
      if d2 != -1 then (p, [d1.toNat, d2.toNat]) else (p, [d1.toNat])
    else (p, [])
  let (s, c) := p.s.peek
  let p := { p with s }
  let (p, frac) : P × Option (List Nat) := match c with
    | none => ({ p with errEof := true }, none)
    | some '.' =>
      let p := { p with s := p.s.get }
      let rec go : Nat → P → List Nat → P × List Nat
        | 0, p, acc => (p, acc)
        | k + 1, p, acc =>
          let (p, dg) := tryDigit p
          if dg != -1 then go k p (acc ++ [dg.toNat]) else (p, acc)
      let (p, fd) := go 9 p []
      (p, some fd)
    | some _ => (p, none)
  if p.errFail then { p with partTime := true }
  else match secondsOf ints frac with
    | some ns => { p with sec := some ns, partTime := true }
    | none => { p with errFail := true, partTime := true }

/-- `%T` (3728-3765), falling through to `%S`. -/
def dirT (p : P) : P :=
  let (p, hv) := readUnsigned 2 p
  if hv == -1 || hv > 23 then { p with errFail := true }
  else
    let (p, ok) := readChr ':' p
    if !ok then p
    else
      let p := { p with h := some hv.toNat }
      let (p, mv) := readUnsigned 2 p
      if mv == -1 || mv > 60 then { p with errFail := true }
      else
        let p := { p with min := some mv.toNat }
        let (p, ok) := readChr ':' p
        if !ok then p else dirS p

/-- `%z` and `%Oz` (4020-4105). -/
def dirZ (modO : Bool) (p : P) : P :=
  let (s, c) := p.s.peek
  let p := { p with s }
  match c with
  | none => { p with errEof := true, errFail := true }
  | some ic =>
    let neg := ic == '-'
    let p := if ic == '-' || ic == '+' then { p with s := p.s.get } else p
    let (p, hh) :=
      if modO then readUnsigned 2 p
      else
        let (p, a) := tryDigit p
        let (p, b) := tryDigit p
        if a ≥ 0 && b ≥ 0 then (p, 10 * a + b) else ({ p with errFail := true }, 0)
    if p.errFail then p
    else
      let (s, c) := p.s.peek
      let p := { p with s }
      match c with
      | none => { p with errEof := true, tz := some (hh * (if neg then -60 else 60)) }
      | some ic =>
        let (p, readMm) :=
          if modO then (if ic == ':' then ({ p with s := p.s.get }, true) else (p, false))
          else (p, isDigit ic)
        let (p, mm) :=
          if readMm then
            let (p, a) := tryDigit p
            let (p, b) := tryDigit p
            if a ≥ 0 && b ≥ 0 then (p, 10 * a + b) else ({ p with errFail := true }, 0)
          else (p, 0)
        if p.errFail then p
        else
          let z := hh * 60 + mm
          { p with tz := some (if neg then -z else z) }

/-- The format directives jank uses. -/
inductive Tok where
  | lit (c : Char)
  | F
  | T
  | z (modO : Bool)
  deriving Repr, BEq

def fmt1 : List Tok := [.F, .lit 'T', .T, .z true]
def fmt2 : List Tok := [.F, .lit 'T', .T, .z false]
def fmt3 : List Tok := [.F, .lit 'T', .T]
def fmt4 : List Tok := [.F]
def jankFormats : List (List Tok) := [fmt1, fmt2, fmt3, fmt4]

/-- The parse loop: a literal that does not match ends it (3349-3352); a directive that sets
failbit ends it (4188-4189). -/
def loop : List Tok → P → P
  | [], p => p
  | .lit c :: rest, p =>
    let (p, ok) := readChr c p
    if !ok then p else loop rest p
  | t :: rest, p =>
    let p := match t with
      | .F => dirF p
      | .T => dirT p
      | .z o => dirZ o p
      | .lit _ => p
    if p.errFail then p else loop rest p

/-- What `from_stream` leaves: the stream and, on success, the time point (ns since the epoch). -/
structure Parsed where
  s : Strm
  tp : Option Int
  deriving Repr

/-- `_Parser::operator()` then `from_stream(sys_time)`. -/
def fromStream (fmt : List Tok) (inp : List Char) : Parsed :=
  let p0 : P := { s := { inp } }
  let p := loop fmt p0
  -- the end (4320-4452): every needed part, a valid date, the time of day
  let ok := !p.errFail && p.partDate && p.partTime
  let date := match p.y, p.m, p.d with
    | some y, some m, some d => some (y, m, d)
    | _, _, _ => none
  let res : Option (Int × Bool) :=
    if !ok then none
    else match date with
      | none => none
      | some (y, m, d) =>
        let t : Int := (p.h.getD 0 : Int) * 3600000000000 + (p.min.getD 0 : Int) * 60000000000 +
          (p.sec.getD 0 : Int)
        let leap := match p.sec with | some ns => ns ≥ 60000000000 | none => false
        some (daysFromCivil y m d * 86400000000000 + t - (p.tz.getD 0) * 60000000000, leap)
  -- `if (__err) __is.setstate(__err)`, then the leap second's failbit
  let s := { p.s with eof := p.s.eof || p.errEof,
                      fail := p.s.fail || p.errFail || res.isNone }
  match res with
  | some (tp, leap) =>
    if s.fail then { s, tp := none }
    else if leap then { s := { s with fail := true }, tp := none }
    else { s, tp := some tp }
  | none => { s, tp := none }

/-- `inst_from_string`: the first format that parses without failing and leaves nothing. -/
def jankRead (inp : List Char) : Option Int :=
  jankFormats.findSome? fun fmt =>
    let r := fromStream fmt inp
    if r.s.fail then none
    else if (r.s.peek).2.isNone then r.tp else none

/-- The format that read it (1-4), for the report. -/
def jankFormatUsed (inp : List Char) : Option Nat :=
  (jankFormats.zip [1, 2, 3, 4]).findSome? fun (fmt, i) =>
    let r := fromStream fmt inp
    if r.s.fail then none
    else if (r.s.peek).2.isNone then (r.tp.map fun _ => i) else none

/-- `duration_cast<milliseconds>`: truncation toward zero. -/
def truncMs (ns : Int) : Int := Int.tdiv ns 1000000

def jankInstMs (ns : Int) : Int := truncMs ns

def pad (w : Nat) (n : Nat) : String :=
  let s := toString n
  String.ofList (List.replicate (w - s.length) '0') ++ s

/-- `yyyy-MM-ddTHH:mm:ss.SSS` of an epoch millisecond (UTC, proleptic Gregorian, floor). -/
def fieldsOfMs (ms : Int) : String :=
  let days := Int.fdiv ms 86400000
  let rem := (ms - days * 86400000).toNat
  let (y, m, d) := civilFromDays days
  let yStr := if y < 0 then "-" ++ pad 4 y.natAbs else pad 4 y.toNat
  s!"{yStr}-{pad 2 m}-{pad 2 d}T{pad 2 (rem / 3600000)}:{pad 2 (rem / 60000 % 60)}:{pad 2 (rem / 1000 % 60)}.{pad 3 (rem % 1000)}"

/-- `to_code_string`: `#inst "…-00:00"` of `time_point_cast<milliseconds>(value)`. -/
def jankPr (ns : Int) : String := "#inst \"" ++ fieldsOfMs (truncMs ns) ++ "-00:00\""

/-- `print`/`print-str`: `to_string`, without the tag. -/
def jankPrint (ns : Int) : String := fieldsOfMs (truncMs ns) ++ "-00:00"

/-! ## Clojure: `parse-timestamp`, `validated`, `construct-date`, `print-date` -/

structure Groups where
  years : List Char
  months : Option (List Char) := none
  days : Option (List Char) := none
  hours : Option (List Char) := none
  minutes : Option (List Char) := none
  seconds : Option (List Char) := none
  fraction : Option (List Char) := none
  sign : Option Char := none
  offH : Option (List Char) := none
  offM : Option (List Char) := none
  deriving Repr

/-- `(?:[Z]|([-+])(\d\d):(\d\d))?` then the end of the input (`re-matches`). -/
def offsetTail (g : Groups) : List Char → Option Groups
  | [] => some g
  | ['Z'] => some g
  | [sg, a, b, ':', c, d] =>
    if (sg == '-' || sg == '+') && isDigit a && isDigit b && isDigit c && isDigit d then
      some { g with sign := some sg, offH := some [a, b], offM := some [c, d] }
    else none
  | _ => none

/-- Java's backtracking order for the nested greedy optional groups: each group is tried first,
and skipped (falling to the offset) when the rest cannot match. `\d+` is greedy; giving digits
back never helps, because the offset starts with a non-digit. -/
def fracPart (g : Groups) : List Char → Option Groups
  | '.' :: rest =>
    let ds := rest.takeWhile isDigit
    if ds.isEmpty then offsetTail g ('.' :: rest)
    else match offsetTail { g with fraction := some ds } (rest.drop ds.length) with
      | some r => some r
      | none => offsetTail g ('.' :: rest)
  | s => offsetTail g s

def twoDigits (sep : Char) : List Char → Option (List Char × List Char)
  | c :: a :: b :: rest => if c == sep && isDigit a && isDigit b then some ([a, b], rest) else none
  | _ => none

def secPart (g : Groups) (s : List Char) : Option Groups :=
  (match twoDigits ':' s with
   | some (x, rest) => fracPart { g with seconds := some x } rest
   | none => none) <|> offsetTail g s

def minPart (g : Groups) (s : List Char) : Option Groups :=
  (match twoDigits ':' s with
   | some (x, rest) => secPart { g with minutes := some x } rest
   | none => none) <|> offsetTail g s

def hourPart (g : Groups) (s : List Char) : Option Groups :=
  (match twoDigits 'T' s with
   | some (x, rest) => minPart { g with hours := some x } rest
   | none => none) <|> offsetTail g s

def dayPart (g : Groups) (s : List Char) : Option Groups :=
  (match twoDigits '-' s with
   | some (x, rest) => hourPart { g with days := some x } rest
   | none => none) <|> offsetTail g s

def monthPart (g : Groups) (s : List Char) : Option Groups :=
  (match twoDigits '-' s with
   | some (x, rest) => dayPart { g with months := some x } rest
   | none => none) <|> offsetTail g s

def cljMatch (inp : List Char) : Option Groups :=
  match inp with
  | a :: b :: c :: d :: rest =>
    if isDigit a && isDigit b && isDigit c && isDigit d then monthPart { years := [a, b, c, d] } rest
    else none
  | _ => none

def num (cs : List Char) : Nat := cs.foldl (fun a c => a * 10 + (c.toNat - '0'.toNat)) 0

/-- `zero-fill-right` to 9, then `parse-int`. -/
def nanosOf (cs : List Char) : Nat := num ((cs ++ List.replicate 9 '0').take 9)

/-- The fields `parse-timestamp` passes to `new-instant`. -/
structure Fields where
  y : Nat
  mo : Nat
  d : Nat
  h : Nat
  mi : Nat
  s : Nat
  ns : Nat
  sign : Int
  oh : Nat
  om : Nat
  deriving Repr

def fieldsOf (g : Groups) : Fields :=
  { y := num g.years, mo := (g.months.map num).getD 1, d := (g.days.map num).getD 1,
    h := (g.hours.map num).getD 0, mi := (g.minutes.map num).getD 0,
    s := (g.seconds.map num).getD 0, ns := (g.fraction.map nanosOf).getD 0,
    sign := match g.sign with | some '-' => -1 | some '+' => 1 | _ => 0,
    oh := (g.offH.map num).getD 0, om := (g.offM.map num).getD 0 }

/-- `validated`. -/
def valid (f : Fields) : Bool :=
  1 ≤ f.mo && f.mo ≤ 12 && 1 ≤ f.d && f.d ≤ lastDay f.y f.mo && f.h ≤ 23 && f.mi ≤ 59 &&
    f.s ≤ (if f.mi == 59 then 60 else 59) && f.ns ≤ 999999999 && f.oh ≤ 23 && f.om ≤ 59

/-- `construct-date`'s epoch milliseconds, for years whose dates `GregorianCalendar` reads as
Gregorian (from 1583; earlier years are Julian there, assumption coreA5-3). The calendar is
lenient: a leap second (60 at minute 59) rolls into the next minute. -/
def cljMs (f : Fields) : Int :=
  daysFromCivil f.y f.mo f.d * 86400000 + (((f.h * 60 + f.mi) * 60 + f.s) * 1000 : Nat) +
    ((f.ns / 1000000 : Nat) : Int) - f.sign * ((f.oh * 60 + f.om : Nat) : Int) * 60000

/-- `read-instant-date`: the epoch milliseconds, or none for "Unrecognized date/time syntax" and
the `validated` failures. -/
def cljRead (inp : List Char) : Option Int :=
  match cljMatch inp with
  | none => none
  | some g => let f := fieldsOf g; if valid f then some (cljMs f) else none

def cljPr (ms : Int) : String := "#inst \"" ++ fieldsOfMs ms ++ "-00:00\""

/-! ## The reader's tag dispatch -/

/-- Who reads `#tag form`, given whether `*data-readers*` maps the tag and whether
`*default-data-reader-fn*` is set. -/
inductive Reader where
  | dataReaders
  | builtin
  | defaultFn
  | error
  deriving Repr, BEq, DecidableEq

/-- `parse_reader_macro_tagged` 1034-1124: `*data-readers*`, then `*default-data-reader-fn*`,
then `#uuid`/`#inst`/`#cpp`. -/
def jankDispatch (inDataReaders defaultFnSet builtinTag : Bool) : Reader :=
  if inDataReaders then .dataReaders
  else if defaultFnSet then .defaultFn
  else if builtinTag then .builtin
  else .error

/-- `LispReader.readTagged` 1435-1451: `*data-readers*`, then `default-data-readers`, then
`*default-data-reader-fn*`. -/
def cljDispatch (inDataReaders defaultFnSet builtinTag : Bool) : Reader :=
  if inDataReaders then .dataReaders
  else if builtinTag then .builtin
  else if defaultFnSet then .defaultFn
  else .error

/-- With `*default-data-reader-fn*` set, jank hands `#inst` (and `#uuid`) to it; Clojure reads
them with its built-in readers. They differ exactly there. -/
theorem dispatch_differs_iff (dr df bt : Bool) :
    jankDispatch dr df bt ≠ cljDispatch dr df bt ↔ (dr = false ∧ df = true ∧ bt = true) := by
  cases dr <;> cases df <;> cases bt <;> decide

/-! ## Theorems on single inputs (each by evaluation in the kernel) -/

/-- RFC 3339's `Z`: Clojure reads it; no jank format does (`%z`/`%Oz` need a digit). -/
theorem z_rejected : jankRead (chars% "2020-01-01T00:00:00Z") = none := by decide +kernel
theorem z_clojure : cljRead (chars% "2020-01-01T00:00:00Z") = some 1577836800000 := by decide +kernel

/-- A leap second: `from_stream` sets failbit; Clojure rolls into the next minute. -/
theorem leap_rejected : jankRead (chars% "2016-12-31T23:59:60") = none := by decide +kernel
theorem leap_clojure : cljRead (chars% "2016-12-31T23:59:60") = some 1483228800000 := by decide +kernel

/-- An 11-digit fraction: the last two digits are read as a `%Oz` offset of 12 hours. -/
theorem frac11_shifts : jankRead (chars% "2020-01-01T00:00:00.12345678912") = some (1577836800123456789 - 12 * 3600000000000) := by
  decide +kernel
theorem frac11_clojure : cljRead (chars% "2020-01-01T00:00:00.12345678912") = some 1577836800123 := by decide +kernel

/-- Before 1970, a sub-millisecond fraction: jank's `duration_cast` truncates toward zero,
Clojure's millisecond field is the fraction's own (the instant's floor). -/
theorem prefrac_jank : (jankRead (chars% "1969-12-31T23:59:59.9995")).map jankInstMs = some 0 := by decide +kernel
theorem prefrac_clojure : cljRead (chars% "1969-12-31T23:59:59.9995") = some (-1) := by decide +kernel

/-- `=` below the millisecond: Clojure's `Date`s are equal, jank's time points are not. -/
theorem submilli_jank_ne : jankRead (chars% "2020-01-01T00:00:00.0001") ≠ jankRead (chars% "2020-01-01T00:00:00.0002") := by
  decide +kernel
theorem submilli_clojure_eq : cljRead (chars% "2020-01-01T00:00:00.0001") = cljRead (chars% "2020-01-01T00:00:00.0002") := by
  decide +kernel

/-- The common forms agree. -/
theorem offset_agrees : (jankRead (chars% "2020-01-01T05:30:00+05:30")).map jankInstMs = cljRead (chars% "2020-01-01T05:30:00+05:30") := by
  decide +kernel
theorem date_agrees : (jankRead (chars% "2020-02-29")).map jankInstMs = cljRead (chars% "2020-02-29") := by decide +kernel

end Jank.R5.Core.Inst
