import Jank.Read
import Jank.ReadClj

/-!
# `(read-string (pr-str x))`: jank's printers feeding jank's reader

jank's `pr-str` is each object's `to_code_string`:
- strings: `"` + `util::escape` + `"` (persistent_string.cpp:52-56, escape.cpp:148-201: `\n \t \r
  \\ \" \a \v \f \b` escaped, every other byte as it is, NUL included);
- characters: `get_literal_from_char_bytes` (character.cpp:12-37): the six names, else `\` and
  the character's bytes;
- keywords `:` + ns/name (keyword.cpp:27-43), symbols ns/name;
- integers in decimal (number.cpp:118-131), big integers with `N` (big_integer.cpp:143-146),
  ratios `n/d` (ratio.cpp:128-131);
- doubles: `std::to_chars` shortest form, fixed or scientific (`1e+21`, `1e-07`), with `.0`
  added when neither `.` nor `e` appears (string_builder.cpp:83-133); `##Inf`, `##-Inf`, `##NaN`;
- collections: elements separated by spaces.

Clojure's `pr-str` (core_print.clj): strings escape `" \\ \n \t \r \f \b` (char-escape-string),
everything else raw; characters use char-name-string (newline space tab backspace formfeed
return), else `\` and the character.
-/

namespace Jank.ReadRoundtrip

open Jank.LexBytes Jank.ReadValue

def lit (s : String) : List UInt8 := bytesOf s

/-- A double's text as `to_chars` may print it: fixed (`123.45`, `100` then `.0`) or scientific
with a sign and at least two exponent digits (`1.5e+21`, `1e-07`). Both are produced and read. -/
def decTexts (d : Dec) : List (List UInt8) :=
  let digits := (Nat.toDigits 10 d.mant)
  let sign := if d.neg then "-" else ""
  let n := digits.length
  -- fixed
  let fixed : String :=
    if d.mant == 0 then "0"
    else if d.exp ≥ 0 then String.ofList digits ++ String.ofList (List.replicate d.exp.toNat '0')
    else
      let k := (-d.exp).toNat
      if k < n then String.ofList (digits.take (n - k)) ++ "." ++ String.ofList (digits.drop (n - k))
      else "0." ++ String.ofList (List.replicate (k - n) '0') ++ String.ofList digits
  let fixed := if fixed.contains '.' then fixed else fixed ++ ".0"
  -- scientific: d.ddd e±XX
  let e10 : Int := d.exp + (n - 1 : Int)
  let mantTxt := match digits with
    | [c] => String.singleton c
    | c :: rest => String.singleton c ++ "." ++ String.ofList rest
    | [] => "0"
  let ee := toString e10.natAbs
  let sci := mantTxt ++ "e" ++ (if e10 < 0 then "-" else "+") ++ (if ee.length < 2 then "0" ++ ee else ee)
  [lit (sign ++ fixed), lit (sign ++ sci)]

/-- jank's `util::escape` (escape.cpp:148-201). -/
def jankEscape (bs : List UInt8) : List UInt8 :=
  bs.flatMap fun c =>
    if c == 10 then lit "\\n" else if c == 9 then lit "\\t" else if c == 13 then lit "\\r"
    else if c == 92 then lit "\\\\" else if c == 34 then lit "\\\"" else if c == 7 then lit "\\a"
    else if c == 11 then lit "\\v" else if c == 12 then lit "\\f" else if c == 8 then lit "\\b"
    else [c]

def nameBytes (ns name : List Nat) : List UInt8 :=
  (if ns.isEmpty then [] else ns.flatMap utf8Encode ++ [47]) ++ name.flatMap utf8Encode

/-- `get_literal_from_char_bytes` (character.cpp:12-37). -/
def jankCharPr (c : Nat) : List UInt8 :=
  if c == 10 then lit "\\newline" else if c == 32 then lit "\\space" else if c == 9 then lit "\\tab"
  else if c == 8 then lit "\\backspace" else if c == 12 then lit "\\formfeed" else if c == 13 then lit "\\return"
  else [92] ++ utf8Encode c

/-- jank's `to_code_string` (for doubles, the text chosen by `which`: 0 fixed, 1 scientific). -/
partial def jankPr (which : Nat) : Val → List UInt8
  | .nil => lit "nil"
  | .bool b => lit (toString b)
  | .long v => lit (toString v)
  | .big v => lit (toString v ++ "N")
  | .ratio n d => lit s!"{n}/{d}"
  | .dbl d => (decTexts d).getD which []
  | .inf n => lit (if n then "##-Inf" else "##Inf")
  | .nan => lit "##NaN"
  | .bigdec d => (decTexts d).getD which [] ++ lit "M"
  | .str s => [34] ++ jankEscape (s.flatMap utf8Encode) ++ [34]
  | .bytes bs => [34] ++ jankEscape bs ++ [34]
  | .char c => jankCharPr c
  | .sym ns n => nameBytes ns n
  | .kw ns n => [58] ++ nameBytes ns n
  | .list xs => [40] ++ ([32] : List UInt8).intercalate (xs.map (jankPr which)) ++ [41]
  | .vec xs => [91] ++ ([32] : List UInt8).intercalate (xs.map (jankPr which)) ++ [93]
  | .map kvs => [123] ++ (lit ", ").intercalate (kvs.map fun (k, v) => jankPr which k ++ [32] ++ jankPr which v) ++ [125]
  | .set xs => lit "#{" ++ ([32] : List UInt8).intercalate (xs.map (jankPr which)) ++ [125]
  | .regex s => lit "#\"" ++ s.flatMap utf8Encode ++ [34]
  | .withMeta _ v => jankPr which v

/-- Clojure's `pr-str` (core_print.clj), as code points. -/
partial def cljPr : Val → List Nat
  | .str s => [34] ++ s.flatMap (fun c =>
      if c == 34 then [92, 34] else if c == 92 then [92, 92] else if c == 10 then [92, 110]
      else if c == 9 then [92, 116] else if c == 13 then [92, 114] else if c == 12 then [92, 102]
      else if c == 8 then [92, 98] else [c]) ++ [34]
  | .char c =>
    let named : List (Nat × String) := [(10, "newline"), (32, "space"), (9, "tab"), (8, "backspace"), (12, "formfeed"), (13, "return")]
    match named.lookup c with
    | some n => (("\\" ++ n).toList.map Char.toNat)
    | none => [92, c]
  | .list xs => [40] ++ ([32] : List Nat).intercalate (xs.map cljPr) ++ [41]
  | .vec xs => [91] ++ ([32] : List Nat).intercalate (xs.map cljPr) ++ [93]
  | v => (utf8Decode (jankPr 0 v)).getD []

/-- Set elements in a canonical order (sets are compared as sets). -/
partial def canon : Val → Val
  | .set xs => .set ((xs.map canon).toArray.qsort (fun a b => a.show < b.show)).toList
  | .list xs => .list (xs.map canon)
  | .vec xs => .vec (xs.map canon)
  | .map kvs => .map (kvs.map fun (k, v) => (canon k, canon v))
  | .withMeta m v => .withMeta (canon m) (canon v)
  | v => v

end Jank.ReadRoundtrip
