import Jank.R3.Boost.Tables
import Jank.R3.Boost.Checks
import Jank.ReaderSearch

/-!
# Round 3, Boost: the reader with the boost replica in place of RA5/RA7

Round 2's lexer (`Jank/Lex.lean`) calls `boostParse` (RA5) for a ratio's numerator and big
denominator, and round 2's parser (`Jank/Read.lean`) builds `big_integer` with
`bigIntegerCreate` (RA5) and `big_decimal` with `bigDecimalCreate` (`strtod`'s exact decimal;
RA7 for an empty literal). The reader reaches boost only through these three functions, so a
reader result changes under the replica exactly when one of them changes on a token the lexer
produces. `swapCheck` runs the lexer on every string of the round-2 numbers table and compares
each `bigInteger`/`bigDecimal` token's value under round 2's functions and under the replica
(`bigCreate`/`rd_string`); `boostParse` itself is compared with the replica by
`Checks.ra5Check`.
-/

namespace Jank.R3.Boost.Reader

open Jank.R3.Boost Jank.R3.Boost.Dec Jank.R3.Boost.Num Jank.LexBytes

/-- An exact decimal as round 2's normalized `LexBytes.Dec`. -/
def cdfToLexDec (x : CDF) : Option Jank.LexBytes.Dec :=
  match x.rat with
  | none => none
  | some (p, q) =>
    -- q is a power of ten; trailing zeros of p are moved into the exponent (no fuel cap).
    let k := (Nat.toDigits 10 q).length - 1
    if p == 0 then some { neg := false, mant := 0, exp := 0 }
    else
      let t := Java.tz p.natAbs
      some { neg := p < 0, mant := p.natAbs / 10 ^ t, exp := (t : Int) - k }

/-- Round 2's decimal with its zeros moved into the exponent without `Dec.norm`'s 400-step cap. -/
def renorm (d : Jank.LexBytes.Dec) : Jank.LexBytes.Dec :=
  if d.mant == 0 then { neg := false, mant := 0, exp := 0 }
  else let t := Java.tz d.mant; { d with mant := d.mant / 10 ^ t, exp := d.exp + t }

structure Swap where
  strings : Nat := 0
  bigTokens : Nat := 0
  decTokens : Nat := 0
  diffs : Array String := #[]
  /-- Round 2's verdict against Clojure → the verdict with the replica's value (an error when
  the replica throws). -/
  transitions : Array (String × String × String) := #[]

def swapOne (acc : Swap) (s : List Nat) : Swap := Id.run do
  let mut acc := { acc with strings := acc.strings + 1 }
  let bytes := (s.flatMap Jank.LexBytes.utf8Encode).toArray
  for o in Jank.Lex.tokens bytes do
    match o with
    | .tok t =>
      match t.kind, t.data with
      | .bigInteger, .big lit radix neg =>
        acc := { acc with bigTokens := acc.bigTokens + 1 }
        let r2 := Jank.Read.bigIntegerCreate lit radix neg
        let r3 := bigCreate (lit.map (·.toNat)) radix neg
        let same := match r2, r3 with
          | .ok a, .ok b => a == b | .error _, .error _ => true | _, _ => false
        if !same then acc := { acc with diffs := acc.diffs.push s!"{showCodes s}: bigint round 2 {reprStr r2}, replica {reprStr r3}" }
      | .bigDecimal, .bigdec lit =>
        acc := { acc with decTokens := acc.decTokens + 1 }
        let r2 := Jank.Read.bigDecimalCreate lit
        let r3 := rdString (lit.map (·.toNat))
        -- A zero is compared without its sign (BigDecimal has no −0; round 2's strtod kept it).
        let same := match r2, r3 with
          | .ok (.bigdec d), .ok x => some (renorm d) == cdfToLexDec x
          | .error _, .error _ => true
          | _, _ => false
        if !same then
          let s3 := match r3 with | .ok x => x.str | .error e => e
          acc := { acc with diffs := acc.diffs.push s!"{showCodes s}: bigdec round 2 {match r2 with | .ok v => v.show | .error e => e}, replica {s3}" }
          let clj := Jank.ReaderSearch.cljRead s
          let old := Jank.ReaderSearch.jankRead s
          let new_ := match r3, old with
            | .error e, _ => Jank.ReadValue.Outcome.err e
            | .ok x, .ok [_] => match cdfToLexDec x with
              | some d => Jank.ReadValue.Outcome.ok [.bigdec d]
              | none => Jank.ReadValue.Outcome.ok [.nan]
            | .ok _, o => o
          acc := { acc with transitions := acc.transitions.push (showCodes s,
            reprStr (Jank.ReadValue.verdict old clj), reprStr (Jank.ReadValue.verdict new_ clj)) }
      | _, _ => pure ()
    | _ => pure ()
  return acc

def swapCheck (alphabet : List Nat) (len : Nat) : Swap :=
  Checks.foldStrings alphabet len {} swapOne

/-! ## Inputs past round 2's bounds -/

/-- jank's value for a whole input that is one number token (round 2's lexer, the replica's
values), or the error. -/
def jankOne (src : String) : String :=
  match Tables.jankLiteral src with
  | .ok v => v.prStr
  | .error e => s!"error ({e})"

def cljOne (src : String) : String :=
  (Jank.ReaderSearch.cljRead (src.toList.map Char.toNat)).show

def handCases : List String :=
  [-- ratio denominators past i64: the lexer passes the digits to boost, a leading 0 is octal
   "1/0100000000000000000000", "1/09999999999999999999", "1/0777777777777777777777",
   -- ratio numerators with two leading zeros: the first 0 is cut, the rest is octal
   "0010/3", "008/3", "-0010/3", "00017/1",
   -- BigDecimal literals boost reads differently from BigDecimal
   "0x1eM", "0x1e5M", "0xeM", "07M", "1.M",
   "1e67108864M", "1e67108865M", "1e67108872M", "1e-67108864M", "1e-67108872M", "1e4294967296M", "1e2147483648M",
   "0.1234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123M",
   "123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012M",
   -- big integers
   "0N", "-0N", "0x10N", "0777777777777777777777N", "-9223372036854775809", "18446744073709551616"]

end Jank.R3.Boost.Reader
