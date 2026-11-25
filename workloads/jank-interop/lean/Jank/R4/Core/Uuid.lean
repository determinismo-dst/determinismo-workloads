/-!
# Round 4: `parse-uuid`

**jank** (core.jank 7796–7803 → core.cpp `parse_uuid` 1020–1038 → obj/uuid.cpp `from_string`
17–28 → stduuid 3afe7193 `uuid::from_string`, include/uuid.h 503–547): a `{` first requires a `}`
last and both are dropped; every `-` anywhere is skipped; exactly 32 hex digits must remain,
two per byte. A failed parse throws inside the constructor and `parse_uuid` turns it into nil.

**Clojure** 1.12 (core.clj 8192–8201): `(UUID/fromString s)`, nil on IllegalArgumentException.
Its docstring gives the grammar of `UUID.toString`: 8-4-4-4-12 hex digits. The JDK (23 here)
`UUID.fromString`: a 36-character string with `-` at 8, 13, 18 and 23 and hex digits elsewhere
takes the fast path (`parse4Nibbles`); otherwise `fromString1`: longer than 36 throws, exactly
four dashes are required, each part goes through `Long.parseLong(s, begin, end, 16)` (a sign is
allowed, an empty part throws, the value must fit a signed long) and is masked to its field
(32/16/16/16/48 bits). So the JDK also takes some strings outside the documented grammar
(`"1-1-1-1-1"`); jank takes others (no dashes, braces, dashes anywhere).
-/

namespace Jank.R4.Core.Uuid

def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- stduuid `from_string` (uuid.h 503–547): the 128-bit value or none. -/
def stduuidFromString (s : String) : Option Nat := Id.run do
  let str := s.toList
  if str.isEmpty then return none
  let braces := str.head? == some '{'
  if braces && str.getLast? != some '}' then return none
  let body := if braces then (str.drop 1).dropLast else str
  -- the loop runs from `hasBraces` to `size - hasBraces` (519)
  let mut index := 0
  let mut first := true
  let mut acc : Nat := 0
  for c in body do
    if c == '-' then continue
    match hexVal c with
    | none => return none
    | some h =>
      if index ≥ 16 then return none
      acc := acc * 16 + h
      if first then first := false
      else
        index := index + 1
        first := true
  if index < 16 then return none
  -- An odd digit left over (first = false) is dropped by stduuid: data[index] was set but
  -- index never advanced; with index = 16 already, the 33rd digit fails the `index >= 16` check.
  return some acc

/-- `Long.parseLong(s, begin, end, 16)`: optional sign, at least one hex digit, fits a long. -/
def parseLongHex (cs : List Char) : Option Int := Id.run do
  let (neg, digits) := match cs with
    | '-' :: r => (true, r)
    | '+' :: r => (false, r)
    | r => (false, r)
  if digits.isEmpty then return none
  let mut acc : Int := 0
  for c in digits do
    match hexVal c with
    | none => return none
    | some h => acc := acc * 16 + h
  let r := if neg then -acc else acc
  if r < -(2 ^ 63) ∨ r ≥ 2 ^ 63 then return none
  return some r

def maskBits (v : Int) (bits : Nat) : Nat := (v % (2 ^ bits : Int)).toNat

/-- JDK `UUID.fromString` (fast path and `fromString1`); the 128-bit value or none. -/
def jdkFromString (s : String) : Option Nat := Id.run do
  let cs := s.toList
  let len := cs.length
  if len == 36 && cs[8]? == some '-' && cs[13]? == some '-' && cs[18]? == some '-' && cs[23]? == some '-' then
    let hexes := (((List.range cs.length).zip cs).filter fun (i, _) => i != 8 && i != 13 && i != 18 && i != 23).map (·.2)
    if hexes.all fun c => (hexVal c).isSome then
      return some (hexes.foldl (fun a c => a * 16 + (hexVal c).getD 0) 0)
  -- fromString1
  if len > 36 then return none
  let dashes := (((List.range cs.length).zip cs).filter fun (_, c) => c == '-').map (·.1)
  if dashes.length != 4 then return none
  let d1 := dashes[0]!
  let d2 := dashes[1]!
  let d3 := dashes[2]!
  let d4 := dashes[3]!
  let part := fun (a b : Nat) => (cs.drop a).take (b - a)
  match parseLongHex (part 0 d1), parseLongHex (part (d1 + 1) d2), parseLongHex (part (d2 + 1) d3),
      parseLongHex (part (d3 + 1) d4), parseLongHex (part (d4 + 1) len) with
  | some p1, some p2, some p3, some p4, some p5 =>
    let msb := (maskBits p1 32 * 2 ^ 16 + maskBits p2 16) * 2 ^ 16 + maskBits p3 16
    let lsb := maskBits p4 16 * 2 ^ 48 + maskBits p5 48
    return some (msb * 2 ^ 64 + lsb)
  | _, _, _, _, _ => return none

/-- The documented grammar (UUID.toString): 8-4-4-4-12 hex digits. -/
def canonical (s : String) : Option Nat :=
  let cs := s.toList
  if cs.length == 36 && cs[8]? == some '-' && cs[13]? == some '-' && cs[18]? == some '-' && cs[23]? == some '-' then
    let hexes := (((List.range cs.length).zip cs).filter fun (i, _) => i != 8 && i != 13 && i != 18 && i != 23).map (·.2)
    if hexes.all fun c => (hexVal c).isSome then
      some (hexes.foldl (fun a c => a * 16 + (hexVal c).getD 0) 0)
    else none
  else none

end Jank.R4.Core.Uuid
