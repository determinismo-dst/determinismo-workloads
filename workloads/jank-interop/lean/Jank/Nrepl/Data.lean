/-!
# jank data as the nREPL server sees it (bytes, values, the clojure.core helpers it calls)

Strings are bytes: jank's `persistent_string` wraps a `jtl::immutable_string`, and
`persistent_string::count` (obj/persistent_string.cpp:179) is `data.size()`, `substring`
(persistent_string.cpp:139) is `data.substr(start, end - start)`: both count bytes, not
characters. So a string here is `List UInt8`.

Values (`JVal`) are the jank objects the server builds, decodes and encodes: nil, booleans,
longs (i64), doubles (by their printed form, which bencode copies), strings, keywords, symbols,
characters, vectors, lists, sets, maps (entries in iteration order).

The clojure.core functions the nREPL server calls, replicated from their jank definitions:
`count`/`subs` (bytes), `str` (core.jank:499, runtime `str` seq.cpp:807: nil args skipped),
`parse-long` (math.cpp:678, `std::stoll` + full consumption), `merge` (core.jank:5557),
`select-keys` (core.jank:2400), `keyword` (core.jank:2556), `not-empty` (core.jank:3702),
`blank?` (string.jank:201, `immutable_string::is_blank`: `std::isspace` on each `char`).
-/

namespace Jank.NreplServer

abbrev Bytes := List UInt8

/-- The UTF-8 bytes of a Lean string (the literal's bytes in the C++ or jank source). -/
def bytes (s : String) : Bytes := s.toUTF8.toList

/-- Printable form of bytes for stories and reports (non-printables escaped). -/
def showBytes (b : Bytes) : String :=
  String.join (b.map fun c =>
    if c == 10 then "\\n"
    else if c == 13 then "\\r"
    else if c == 9 then "\\t"
    else if c == 34 then "\\\""
    else if c == 92 then "\\\\"
    else if c ≥ 32 && c < 127 then (Char.ofNat c.toNat).toString
    else
      let h := Nat.toDigits 16 c.toNat
      "\\x" ++ String.ofList (if h.length < 2 then '0' :: h else h))

/-- Decimal digits of a natural number, as bytes. -/
def natBytes (n : Nat) : Bytes := bytes (toString n)

/-- Decimal of an integer as `integer::to_string` prints a long (a leading `-` when negative). -/
def intBytes (i : Int) : Bytes := bytes (toString i)

def i64min : Int := -9223372036854775808
def i64max : Int := 9223372036854775807

/-- A jank value, as far as the nREPL server handles them. -/
inductive JVal where
  | nil
  | bool (b : Bool)
  /-- a long (`integer`, i64) -/
  | int (i : Int)
  /-- a double, by the text `real::to_string` prints for it -/
  | real (text : String)
  | str (s : Bytes)
  | kw (ns : Option Bytes) (name : Bytes)
  | sym (ns : Option Bytes) (name : Bytes)
  | char (c : UInt8)
  | vec (xs : List JVal)
  | list (xs : List JVal)
  | set (xs : List JVal)
  /-- a map, entries in iteration order -/
  | map (kvs : List (JVal × JVal))
  deriving Inhabited, Repr, BEq

namespace JVal

def s (x : String) : JVal := .str (bytes x)
def k (x : String) : JVal := .kw none (bytes x)
def y (x : String) : JVal := .sym none (bytes x)

/-- `truthy`: everything but nil and false. -/
def truthy : JVal → Bool
  | .nil => false
  | .bool b => b
  | _ => true

/-- A readable rendering for stories (not jank's printer). -/
partial def render : JVal → String
  | .nil => "nil"
  | .bool b => toString b
  | .int i => toString i
  | .real t => t
  | .str b => "\"" ++ showBytes b ++ "\""
  | .kw none n => ":" ++ showBytes n
  | .kw (some ns) n => ":" ++ showBytes ns ++ "/" ++ showBytes n
  | .sym none n => showBytes n
  | .sym (some ns) n => showBytes ns ++ "/" ++ showBytes n
  | .char c => "\\" ++ showBytes [c]
  | .vec xs => "[" ++ " ".intercalate (xs.map render) ++ "]"
  | .list xs => "(" ++ " ".intercalate (xs.map render) ++ ")"
  | .set xs => "#{" ++ " ".intercalate (xs.map render) ++ "}"
  | .map kvs => "{" ++ ", ".intercalate (kvs.map fun (a, b) => render a ++ " " ++ render b) ++ "}"

/-- Structural equality where maps and sets compare as sets of entries (`=` on these values). -/
partial def same : JVal → JVal → Bool
  | .vec a, .vec b => a.length == b.length && (a.zip b).all fun (x, z) => same x z
  | .list a, .list b => a.length == b.length && (a.zip b).all fun (x, z) => same x z
  | .set a, .set b => a.all (fun x => b.any (same x)) && b.all (fun x => a.any (same x))
  | .map a, .map b =>
    a.length == b.length && a.all fun (k1, v1) => b.any fun (k2, v2) => same k1 k2 && same v1 v2
  | x, z => x == z

end JVal

/-! ## clojure.core helpers -/

/-- `get` on a map with a key (core.jank `get` → `runtime::get`): the value, else `fallback`.
For a non-map (a vector, a string, a long) and a string key the result is the fallback
(persistent_string::get: a non-integral key gives the fallback). -/
def jget (m : JVal) (key : JVal) (fallback : JVal := .nil) : JVal :=
  match m with
  | .map kvs => match kvs.find? (fun (k, _) => JVal.same k key) with
    | some (_, v) => v
    | none => fallback
  | _ => fallback

/-- `find` on a map (core.jank:2395): the entry or nil; nil on a non-map here (assumption: a
request is a map; other top-level values are not decoded into requests in the scripts). -/
def jfind (m : JVal) (key : JVal) : Option (JVal × JVal) :=
  match m with
  | .map kvs => kvs.find? (fun (k, _) => JVal.same k key)
  | _ => none

/-- `assoc` on a map: replaces the entry in place, else appends (array-map order). -/
def assocMap (kvs : List (JVal × JVal)) (k v : JVal) : List (JVal × JVal) :=
  if kvs.any (fun (k', _) => JVal.same k' k) then
    kvs.map fun (k', v') => if JVal.same k' k then (k', v) else (k', v')
  else kvs ++ [(k, v)]

/-- `conj` of a map onto a map: each entry assoc'ed. -/
def conjMap (a : JVal) (b : JVal) : JVal :=
  match a, b with
  | .map x, .map y => .map (y.foldl (fun acc (k, v) => assocMap acc k v) x)
  | .map x, .nil => .map x
  | a, _ => a

/-- `merge` (core.jank:5557): `(when (some identity maps) (reduce #(conj (or %1 {}) %2) maps))`. -/
def merge (maps : List JVal) : JVal :=
  if !(maps.any JVal.truthy) then .nil
  else match maps with
    | [] => .nil
    | first :: rest => rest.foldl (fun acc m =>
        let base := if acc.truthy then acc else .map []
        conjMap base m) first

/-- `select-keys` (core.jank:2400): `(reduce (fn [acc k] (let [e (find m k)] (if e (conj acc e)
acc))) {} ks)`. -/
def selectKeys (m : JVal) (ks : List JVal) : JVal :=
  .map (ks.foldl (fun acc k => match jfind m k with
    | some (k', v) => assocMap acc k' v
    | none => acc) [])

/-- `keyword` arity 1 (core.jank:2556): a keyword stays, a symbol or a string becomes a keyword,
anything else falls through the `cond`: nil. -/
def keyword : JVal → JVal
  | .kw ns n => .kw ns n
  | .sym none n => .kw none n
  | .sym (some ns) n => .kw none (ns ++ bytes "/" ++ n)
  | .str b => .kw none b
  | _ => .nil

/-- C `isspace` in the "C" locale on a `char` (` `, `\t`, `\n`, `\v`, `\f`, `\r`). A byte ≥ 0x80 is
a negative `char` where `char` is signed (x86-64, Apple arm64): `std::isspace` of a negative value
other than EOF is undefined behaviour (flagged by `isspaceUB`). -/
def cIsspace (c : UInt8) : Bool := c == 32 || (c ≥ 9 && c ≤ 13)

def isspaceUB (signedChar : Bool) (c : UInt8) : Bool := signedChar && c ≥ 128

/-- `clojure.string/blank?` (string.jank:201): `(or (nil? s) (.is_blank s))`;
`immutable_string::is_blank` (immutable_string.hpp:635) is true when every `char` is a space. -/
def blank (s : Option Bytes) : Bool :=
  match s with
  | none => true
  | some b => b.all cIsspace

/-- `std::stoll(str, &idx)` then `idx != size` (math.cpp `parse_long`, line 678): skip C
whitespace, an optional sign, at least one decimal digit (else `invalid_argument`: nil), within
i64 (else `out_of_range`: nil), and nothing after the digits (else nil). The same as round 1's
`jankParseLong`, on bytes. -/
def parseLong (s : Bytes) : Option Int :=
  let rest := s.dropWhile cIsspace
  let (neg, rest) := match rest with
    | 45 :: r => (true, r)
    | 43 :: r => (false, r)
    | r => (false, r)
  let digits := rest.takeWhile fun c => c ≥ 48 && c ≤ 57
  if digits.isEmpty then none
  else
    let mag : Int := digits.foldl (fun acc c => acc * 10 + ((c.toNat : Int) - 48)) 0
    let v := if neg then -mag else mag
    if v < i64min || v > i64max then none
    else if rest.length != digits.length then none
    else some v

/-- `not-empty` on a string (core.jank:3702): nil when empty. -/
def notEmpty (b : Bytes) : Option Bytes := if b.isEmpty then none else some b

end Jank.NreplServer
