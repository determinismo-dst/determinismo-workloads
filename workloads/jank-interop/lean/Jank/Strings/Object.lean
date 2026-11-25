import Jank.Strings.Bytes

/-!
# Strings, characters and string sequences as objects

The C++ of `persistent_string`, `character`, `persistent_string_sequence` and the runtime
functions on them (core.cpp, core/seq.cpp, core/equal.cpp, hash.cpp, symbol.cpp, keyword.cpp,
context.cpp), replicated one definition per function, over a small object universe `Obj`, at
jank commit 7135b7708 (upstream-main/compiler+runtime/; line numbers re-read there).

Beside it, `Clj`: Clojure 1.12's documented meaning on the same values, judged by characters
(Unicode code points): a jank string's bytes are decoded as UTF-8 (`decodeUtf8`); a string whose
bytes are not valid UTF-8 has no Clojure counterpart.
-/

namespace Jank.Strings

open Jank.Hash (CharSign)

/-- The objects these functions meet. -/
inductive Obj where
  | nil
  /-- integer / small_integer (an i64). -/
  | int (v : Int)
  /-- real: a finite double by its shortest decimal (`Dec`). -/
  | real (d : Dec)
  /-- persistent_string: its `data`. -/
  | str (b : Bytes)
  /-- character: its `data` (the character's UTF-8 bytes, or whatever bytes it was given). -/
  | chr (b : Bytes)
  /-- persistent_string_sequence: its string's bytes and `index`. -/
  | sseq (s : Bytes) (index : Nat)
  | list (xs : List Obj)
  | vec (xs : List Obj)
  /-- symbol and keyword: `ns` ("" = none) and `name`. -/
  | sym (ns name : Bytes)
  | kw (ns name : Bytes)
  deriving BEq, Repr, Inhabited

/-! ## UTF-8 decoding (the library's `mbrtowc`; and the spec's reading of a jank string) -/

/-- Strict UTF-8 decoding of the first character: its code point and length, `none` when the
bytes do not start with a complete valid encoding (overlong forms, surrogates and values past
U+10FFFF are invalid, as in glibc's and macOS's UTF-8 locales). -/
def decodeOne : Bytes → Option (Nat × Nat)
  | [] => none
  | c :: rest =>
    let c := c.toNat
    let cont (k : Nat) : Option (List Nat) :=
      let bs := (rest.take k).map (·.toNat)
      if bs.length == k && bs.all (fun x => x &&& 0xC0 == 0x80) then some (bs.map (· &&& 0x3F)) else none
    if c < 0x80 then some (c, 1)
    else if c &&& 0xE0 == 0xC0 then
      match cont 1 with
      | some [b1] => let v := ((c &&& 0x1F) <<< 6) ||| b1; if v ≥ 0x80 then some (v, 2) else none
      | _ => none
    else if c &&& 0xF0 == 0xE0 then
      match cont 2 with
      | some [b1, b2] =>
        let v := ((c &&& 0x0F) <<< 12) ||| (b1 <<< 6) ||| b2
        if v ≥ 0x800 && !(0xD800 ≤ v && v ≤ 0xDFFF) then some (v, 3) else none
      | _ => none
    else if c &&& 0xF8 == 0xF0 then
      match cont 3 with
      | some [b1, b2, b3] =>
        let v := ((c &&& 0x07) <<< 18) ||| (b1 <<< 12) ||| (b2 <<< 6) ||| b3
        if v ≥ 0x10000 && v ≤ 0x10FFFF then some (v, 4) else none
      | _ => none
    else none

/-- A valid UTF-8 string's code points; `none` when invalid. -/
def decodeUtf8 (s : Bytes) : Option (List Nat) :=
  let rec go (fuel : Nat) (s : Bytes) (acc : List Nat) : Option (List Nat) :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      if s.isEmpty then some acc.reverse
      else match decodeOne s with
        | some (v, n) => go fuel (s.drop n) (v :: acc)
        | none => none
  go (s.length + 1) s []

/-- UTF-8 encoding of a code point (the spec's strings back to bytes, for comparison). -/
def encodeUtf8 (cp : Nat) : Bytes := (wcrtombUtf8 (Int32.ofInt cp)).getD []

def encodeAll (cps : List Nat) : Bytes := cps.flatMap encodeUtf8

/-- `std::mbrtowc(&wc, data.c_str(), data.size(), &state)` with `wc` starting at 0: the first
character's code point; on an incomplete or invalid sequence `wc` is left 0 (assumption: glibc
and macOS do not write `wc` on failure). -/
def mbrtowc (data : Bytes) : Int :=
  match decodeOne data with
  | some (v, _) => v
  | none => 0

/-! ## character.cpp -/

/-- character.cpp `character(char)` (line 51): `data{ 1, ch }`. -/
def characterOfChar (c : UInt8) : Obj := .chr (fill 1 c)

/-- character.cpp `character(i64)` (line 57): `data{ jtl::to_char(ch) }` (throws). -/
def characterOfI64 (ch : Int) : Except String Obj := do
  let i : Int64 := Int64.ofInt ch
  return .chr (← toChar i)

/-- character.cpp `character::to_integer` (line 104). -/
def characterToInteger (data : Bytes) : Int := mbrtowc data

/-- character.cpp `character::equal` (line 63). -/
def characterEqual (data : Bytes) (o : Obj) : Bool :=
  match o with
  | .chr d => eqBytes data d
  | _ => false

/-- character.cpp `character::compare` (line 99): `data.compare(s.data)` (throws when `o` is not a
character: `try_object`). -/
def characterCompare (data : Bytes) (o : Obj) : Except String Int :=
  match o with
  | .chr d => .ok (compare data d)
  | _ => .error "invalid object type (expected character)"

/-- character.cpp `character::to_hash` (line 89): the string hash of its bytes. -/
def characterToHash (data : Bytes) : UInt32 := toHashValue data

/-! ## persistent_string.cpp -/

/-- persistent_string.cpp `persistent_string::equal` (line 31). -/
def persistentStringEqual (data : Bytes) (o : Obj) : Bool :=
  match o with
  | .str d => eqBytes data d
  | _ => false

/-- persistent_string.cpp `persistent_string::compare(object const &)` (line 63). -/
def persistentStringCompare (data : Bytes) (o : Obj) : Except String Int :=
  match o with
  | .str d => .ok (compare data d)
  | _ => .error "invalid object type (expected persistent_string)"

/-- core/math.cpp `is_integral`: integer or big_integer. -/
def isIntegral : Obj → Bool
  | .int _ => true
  | _ => false

/-- core/math.cpp `to_i64` / `to_int`. A real truncates (`static_cast<i64>`, NaN → 0); a
character is `to_integer` (mbrtowc). -/
def toInt : Obj → Except String Int
  | .int v => .ok v
  | .real d =>
    -- truncation toward zero of the decimal
    let n := d.digits.length
    let mant : Int := (String.ofList d.digits).toNat!
    let shift : Int := d.exp - (n - 1)
    let v : Int := if shift ≥ 0 then mant * 10 ^ shift.toNat else mant / 10 ^ (-shift).toNat
    .ok (if d.neg then -v else v)
  | .chr d => .ok (characterToInteger d)
  | _ => .error "not a number"

/-- persistent_string.cpp `persistent_string::get(key, fallback)` (line 78). -/
def persistentStringGet (data : Bytes) (key fallback : Obj) : Obj :=
  match key with
  | .int i =>
    if i < 0 || data.length ≤ toUsize i then fallback
    else characterOfChar (data.getD (toUsize i) 0)
  | _ => fallback

/-- persistent_string.cpp `persistent_string::contains` (line 95). -/
def persistentStringContains (data : Bytes) (key : Obj) : Except String Bool :=
  match key with
  | .int i => .ok (0 ≤ i && toUsize i < data.length)
  | _ => .error "The `contains?` operation on a `persistent_string` requires an integer index"

/-- persistent_string.cpp `persistent_string::nth(index)` (line 107). -/
def persistentStringNth (data : Bytes) (index : Obj) : Except String Obj :=
  match index with
  | .int i =>
    if i < 0 || data.length ≤ toUsize i then .error s!"The index `{i}` is out of bounds for this `persistent_string`."
    else .ok (characterOfChar (data.getD (toUsize i) 0))
  | _ => .error "The `nth` operation on a `persistent_string` requires an integer index"

/-- persistent_string.cpp `persistent_string::nth(index, fallback)` (line 128). -/
def persistentStringNthOr (data : Bytes) (index fallback : Obj) : Obj :=
  persistentStringGet data index fallback

/-- persistent_string.cpp `persistent_string::substring(start, end)` (line 139). -/
def persistentStringSubstring2 (data : Bytes) (start end_ : Int) : Except String Bytes :=
  if start < 0 then .error s!"start index {start} is less than 0"
  else if end_ < start then .error s!"end index {end_} is less than start {start}"
  else if toUsize end_ > data.length then .error s!"end index {end_} out of bounds for length {data.length}"
  else substr data (toUsize start) (some (toUsize (end_ - start)))

/-- persistent_string.cpp `persistent_string::substring(start)` (line 133). -/
def persistentStringSubstring1 (data : Bytes) (start : Int) : Except String Bytes :=
  persistentStringSubstring2 data start data.length

/-- persistent_string.cpp `first_index_of` (line 157), the argument already `to_string`ed. -/
def persistentStringFirstIndexOf (data m : Bytes) : Int :=
  let found := find data m 0
  if found == npos then -1 else usizeToI64 found

/-- persistent_string.cpp `last_index_of` (line 168). -/
def persistentStringLastIndexOf (data m : Bytes) : Int :=
  let found := rfind data m npos
  if found == npos then -1 else usizeToI64 found

/-- persistent_string.cpp `count` (line 179): `data.size()`, bytes. -/
def persistentStringCount (data : Bytes) : Nat := data.length

/-- persistent_string.cpp `fresh_seq` / `seq` (lines 184, 189). -/
def persistentStringSeq (data : Bytes) : Obj := if data.isEmpty then .nil else .sseq data 0

/-- persistent_string.cpp `to_hash` (line 58). -/
def persistentStringToHash (data : Bytes) : UInt32 := toHashValue data

/-! ## persistent_string_sequence.cpp -/

/-- persistent_string_sequence.cpp `first` (line 122). -/
def sseqFirst (s : Bytes) (index : Nat) : Except String Obj := do
  let size ← nextCharSize s index
  return .chr (← substr s index (some size))

/-- persistent_string_sequence.cpp `next` (line 128): `n == size` ends it; past the end it does
not (a truncated last character leaves `n > size`). -/
def sseqNext (s : Bytes) (index : Nat) : Except String Obj := do
  let n := index + (← nextCharSize s index)
  if n == s.length then return .nil
  return .sseq s n

/-- persistent_string_sequence.cpp `count` (line 78). -/
def sseqCount (s : Bytes) (index : Nat) : Except String Nat := do
  let size := s.length
  let rec go (fuel : Nat) (i count : Nat) : Except String Nat := do
    match fuel with
    | 0 => throw "fuel"
    | fuel + 1 => if i < size then go fuel (i + (← nextCharSize s i)) (count + 1) else return count
  go (size + 1) index 0

/-- persistent_string_sequence.cpp `to_hash` (line 72): `hash::ordered` over the bytes from
`index`, each byte `hash::visit(char)`. -/
def sseqToHash (cs : CharSign) (s : Bytes) (index : Nat) : UInt32 := orderedBytes cs (s.drop index)

/-- The elements a `sequence_range` over the sequence `(s, index)` yields: `first()` then
`next()` until nil (at most `s.length + 1` turns; past them a walk off the end is reported). -/
def sseqElements (s : Bytes) (index : Nat) : Except String (List Obj) := do
  let rec go (fuel : Nat) (o : Obj) (acc : List Obj) : Except String (List Obj) := do
    match fuel with
    | 0 => throw "UB: the sequence walked past the end of its string"
    | fuel + 1 =>
      match o with
      | .sseq s i => go fuel (← sseqNext s i) ((← sseqFirst s i) :: acc)
      | _ => return acc.reverse
  go (s.length + 1) (.sseq s index) []

/-! ## Sequences of objects (`make_sequence_range`), `=` and `hash` -/

/-- `has_behavior(seqable)`. -/
def Obj.seqable : Obj → Bool
  | .nil | .str _ | .sseq _ _ | .list _ | .vec _ => true
  | _ => false

/-- core/seq.cpp `is_sequential` (line 65): `behavior::sequential<T>` (`T::is_sequential`):
persistent_list, persistent_vector, persistent_string_sequence; not nil, not a string. -/
def Obj.sequential : Obj → Bool
  | .sseq _ _ | .list _ | .vec _ => true
  | _ => false

/-- persistent_string_sequence.cpp `empty` (line 157, new at 7135b7708): the empty list. -/
def sseqEmpty : Obj := .list []

/-- The elements `make_sequence_range(o)` yields (`o.seq()` then `first`/`next`). -/
def seqElements : Obj → Except String (List Obj)
  | .nil => .ok []
  | .str d => match persistentStringSeq d with
    | .sseq s i => sseqElements s i
    | _ => .ok []
  | .sseq s i => sseqElements s i
  | .list xs => .ok xs
  | .vec xs => .ok xs
  | _ => .error "not seqable"

/-- core/equal.cpp `equal(char const lhs, object_ref const rhs)` (line 8). -/
def equalCharObj (lhs : UInt8) (rhs : Obj) : Bool :=
  match rhs with
  | .chr d => d.length == 1 && d.head? == some lhs
  | _ => false

mutual
/-- `runtime::equal(l, r)` → `l.equal(r)`: each type's `equal`. -/
partial def jankEqual (l r : Obj) : Except String Bool :=
  match l with
  | .nil => .ok (r == .nil)
  | .int v => .ok (match r with | .int w => v == w | _ => false)
  | .real d => .ok (match r with | .real e => d == e | _ => false)
  | .str d => .ok (persistentStringEqual d r)
  | .chr d => .ok (characterEqual d r)
  | .sym ns n => .ok (match r with | .sym ns' n' => eqBytes ns ns' && eqBytes n n' | _ => false)
  | .kw ns n => .ok (match r with | .kw ns' n' => eqBytes (ns ++ bs "/" ++ n) (ns' ++ bs "/" ++ n') | _ => false)
  -- persistent_string_sequence.cpp `equal` (line 34): `runtime::equal(o, bytes from index)`.
  | .sseq s i => seqExtEqualBytes r (s.drop i)
  -- persistent_list.cpp `equal` (line 70): `runtime::equal(o, data.begin(), data.end())`.
  | .list xs => seqExtEqualObjs r xs
  -- persistent_vector.cpp `equal` (line 65): a vector elementwise, else `sequence_equal`.
  | .vec xs => match r with
    | .vec ys =>
      if xs.length != ys.length then .ok false
      else (xs.zip ys).allM fun (a, b) => jankEqual a b
    | _ => sequenceEqual l r

/-- seq_ext.hpp `equal(o, begin, end)` (line 13) over a byte range (`It` = `char const *`):
false unless `is_sequential(o)` (line 17; at f3d82d654 it was "not nil and seqable"), then each
element of `o`'s sequence against a byte with `equal(char, object_ref)`. -/
partial def seqExtEqualBytes (o : Obj) (bytes : Bytes) : Except String Bool := do
  if !o.sequential then return false
  let elems ← seqElements o
  return elems.length == bytes.length && (bytes.zip elems).all fun (c, e) => equalCharObj c e

/-- seq_ext.hpp `equal(o, begin, end)` over objects: `runtime::equal(*it, *seq_it)`. -/
partial def seqExtEqualObjs (o : Obj) (xs : List Obj) : Except String Bool := do
  if !o.sequential then return false
  let elems ← seqElements o
  if elems.length != xs.length then return false
  (xs.zip elems).allM fun (a, b) => jankEqual a b

/-- core/seq.cpp `sequence_equal` (line 881): false unless both are `is_sequential` (line 890;
at f3d82d654: both seqable). (`l == r` identity is not modeled: values here are fresh objects;
`Obj` has no identity.) -/
partial def sequenceEqual (l r : Obj) : Except String Bool := do
  if !l.sequential || !r.sequential then return false
  let ls ← seqElements l
  let rs ← seqElements r
  if ls.length != rs.length then return false
  (ls.zip rs).allM fun (a, b) => jankEqual a b
end

/-- Each type's `to_hash`. -/
partial def jankHash (cs : CharSign) : Obj → UInt32
  | .nil => 0
  | .int v => Jank.Hash.integer (UInt64.ofInt v)
  | .real _ => 0x7EA1
  | .str d => persistentStringToHash d
  | .chr d => characterToHash d
  | .sseq s i => sseqToHash cs s i
  | .list xs | .vec xs =>
    Jank.Hash.mixCollectionHash (xs.foldl (fun h x => 31 * h + jankHash cs x) 1) xs.length.toUInt32
  | .sym ns n => Jank.Hash.symbol cs ns n
  | .kw ns n => Jank.Hash.keyword cs ns n

/-! ## to_string, str, printing -/

/-- Decimal text of an i64. -/
def intText (v : Int) : Bytes := bs (toString v)

/-- Each type's `to_string(buff)`: what `str` appends. -/
partial def toStringBytes : Obj → Except String Bytes
  | .nil => .ok (bs "nil")
  | .int v => .ok (intText v)
  | .real d => .ok (bs (builderDouble d))
  | .str d => .ok d
  | .chr d => .ok d
  | .sym ns n => .ok (if ns.isEmpty then n else ns ++ bs "/" ++ n)
  | .kw ns n => .ok (b ':' :: (if ns.isEmpty then n else ns ++ bs "/" ++ n))
  | .sseq s i => do
    -- persistent_string_sequence.cpp `to_string` (line 39): each character's code string.
    let chars ← utf8Chars (← substr s i none)
    return [b '('] ++ (" ".toList.map b).intercalate (chars.map charToCodeString) ++ [b ')']
  | .list xs => do
    let parts ← xs.mapM toStringBytes
    return [b '('] ++ [b ' '].intercalate parts ++ [b ')']
  | .vec xs => do
    let parts ← xs.mapM toStringBytes
    return [b '['] ++ [b ' '].intercalate parts ++ [b ']']

/-- core/seq.cpp `str(o, args)` (line 807), with core.jank `str` (line 495): no argument "",
one argument `.to_string` ("" for nil), more: each non-nil `to_string`, concatenated. -/
def jankStr (args : List Obj) : Except String Bytes := do
  match args with
  | [] => return []
  | [o] => if o == .nil then return [] else toStringBytes o
  | os => do
    let parts ← (os.filter (· != .nil)).mapM toStringBytes
    return parts.flatten

/-! ## core.cpp -/

/-- core.cpp `is_string` (line 59). -/
def isString : Obj → Bool | .str _ => true | _ => false
/-- core.cpp `is_char` (line 64). -/
def isChar : Obj → Bool | .chr _ => true | _ => false

/-- core.cpp `subs(s, start)` (line 398): `to_int(start)`, then `.expect_ok()` (a failed result
throws). -/
def coreSubs1 (s start : Obj) : Except String Obj := do
  match s with
  | .str d => return .str (← persistentStringSubstring1 d (← toInt start))
  | _ => throw "The first argument to `subs` must be a `persistent_string`"

/-- core.cpp `subs(s, start, end)` (line 411). -/
def coreSubs2 (s start end_ : Obj) : Except String Obj := do
  match s with
  | .str d => return .str (← persistentStringSubstring2 d (← toInt start) (← toInt end_))
  | _ => throw "The first argument to `subs` must be a `persistent_string`"

/-- core/seq.cpp `sequence_length` (line 842): countable → `count()`; nil → 0. -/
def sequenceLength : Obj → Except String Nat
  | .nil => .ok 0
  | .str d => .ok (persistentStringCount d)
  | .sseq s i => sseqCount s i
  | .list xs | .vec xs => .ok xs.length
  | _ => .error "not seqable"

/-- core/seq.cpp `nth(o, idx)` (line 648) on a string or nil. -/
def coreNth (o idx : Obj) : Except String Obj := do
  let index ← toInt idx
  match o with
  | .nil => return .nil
  | .str d =>
    if index < 0 then throw s!"The index `{index}` is out of bounds"
    persistentStringNth d idx
  | _ => throw "not modeled"

/-- core/seq.cpp `nth(o, idx, fallback)` (line 698). -/
def coreNthOr (o idx fallback : Obj) : Except String Obj := do
  let index ← toInt idx
  if index < 0 || o == .nil then return fallback
  match o with
  | .str d => return persistentStringNthOr d idx fallback
  | _ => throw "not modeled"

/-- core/seq.hpp `get(m, key)` / `get(m, key, fallback)` on a string. -/
def coreGet (m key fallback : Obj) : Obj :=
  match m with
  | .str d => persistentStringGet d key fallback
  | _ => fallback

/-- core/equal.cpp `compare(l, r)` (line 24) on strings and characters. -/
def coreCompare (l r : Obj) : Except String Int :=
  if l != .nil && r == .nil then .ok 1
  else match l with
    | .str d => persistentStringCompare d r
    | .chr d => characterCompare d r
    | _ => .error "not modeled"

/-- core.cpp `to_char(x)` (line 1311): a character as is, else `character(to_int(x))`. -/
def coreToChar (x : Obj) : Except String Obj := do
  match x with
  | .chr _ => return x
  | _ => characterOfI64 (← toInt x)

/-- symbol.cpp `separate` (line 8): the first '/' splits, unless the string is "/" itself
(`s.size() > 1`). -/
def separate (s : Bytes) : Bytes × Bytes :=
  let found := find s [b '/'] 0
  if found != npos && s.length > 1 then (s.take found, s.drop (found + 1)) else ([], s)

/-- core.cpp `to_unqualified_symbol` (line 84) on a string: `symbol(data)` → `separate`. -/
def toUnqualifiedSymbol : Obj → Except String Obj
  | .str d => let (ns, n) := separate d; .ok (.sym ns n)
  | .sym ns n => .ok (.sym ns n)
  | .kw ns n => .ok (.sym ns n)
  | _ => .error "cannot be converted to symbols"

/-- core.jank `symbol` (line 517): one argument `to_unqualified_symbol`; two: nil ns is the
one-argument case, else `to_qualified_symbol` → `symbol(ns.to_string(), name.to_string())`. -/
def jankSymbol (ns : Option Obj) (name : Obj) : Except String Obj := do
  match ns with
  | none | some .nil => toUnqualifiedSymbol name
  | some n => return .sym (← toStringBytes n) (← toStringBytes name)

/-- context.cpp `intern_keyword(s)` (line 588) → keyword.cpp `keyword(s)` → `symbol(s)`
(`separate`); interned by the whole string. -/
def internKeyword (s : Bytes) : Obj := let (ns, n) := separate s; .kw ns n

/-- core.cpp `keyword(ns, name)` (line 521) with context.cpp `intern_keyword(ns, name, true)`
(line 561): "ns/name" (just name when ns is empty), then `intern_keyword(s)`. -/
def coreKeyword (ns name : Obj) : Except String Obj := do
  if ns != .nil && !isString ns then throw "The `keyword` function expects the namespace to be `nil` or a `persistent_string`"
  let .str n := name | throw "The `keyword` function expects the name to be a `persistent_string`"
  match ns with
  | .nil => return internKeyword n
  | .str nsb => return internKeyword (if nsb.isEmpty then n else nsb ++ bs "/" ++ n)
  | _ => throw "unreachable"

/-- core.jank `keyword` (line 2557). -/
def jankKeyword (ns : Option Obj) (name : Obj) : Except String Obj := do
  match ns with
  | none => match name with
    | .kw .. => return name
    | .sym ns n => coreKeyword .nil (.str (if ns.isEmpty then n else ns ++ bs "/" ++ n))
    | .str _ => coreKeyword .nil name
    | _ => return .nil
  | some ns => coreKeyword ns name

/-- core.cpp `name` (line 460). -/
def coreName : Obj → Except String Bytes
  | .str d => .ok d
  | .sym _ n | .kw _ n => .ok n
  | _ => .error "not nameable"

/-- core.cpp `namespace_` (line 484): an empty ns is nil. -/
def coreNamespace : Obj → Except String Obj
  | .sym ns _ | .kw ns _ => .ok (if ns.isEmpty then .nil else .str ns)
  | _ => .error "not nameable"

/-! ## Clojure 1.12 (the spec), on code points -/

namespace Clj

/-- A Clojure value for these questions: strings and characters as code points; `sym`/`kw` with
an optional namespace (Java `null` vs ""). -/
inductive V where
  | nil
  | int (v : Int)
  | str (cps : List Nat)
  | chr (cp : Nat)
  /-- A seq over a string (StringSeq) or another sequential collection: its elements. -/
  | seq (xs : List V)
  | list (xs : List V)
  | vec (xs : List V)
  | sym (ns : Option (List Nat)) (name : List Nat)
  | kw (ns : Option (List Nat)) (name : List Nat)
  deriving BEq, Repr, Inhabited

/-- A jank object's Clojure counterpart, when its bytes are valid UTF-8 and a character holds
exactly one character. -/
partial def ofObj : Obj → Option V
  | .nil => some .nil
  | .int v => some (.int v)
  | .real _ => none
  | .str d => (decodeUtf8 d).map .str
  | .chr d => match decodeUtf8 d with | some [c] => some (.chr c) | _ => none
  | .sseq s i => do
    let cps ← decodeUtf8 (s.drop i)
    if cps.isEmpty then none else some (.seq (cps.map .chr))
  | .list xs => (xs.mapM ofObj).map .list
  | .vec xs => (xs.mapM ofObj).map .vec
  | .sym ns n => do
    let nsv ← if ns.isEmpty then some none else (decodeUtf8 ns).map some
    some (.sym nsv (← decodeUtf8 n))
  | .kw ns n => do
    let nsv ← if ns.isEmpty then some none else (decodeUtf8 ns).map some
    some (.kw nsv (← decodeUtf8 n))

def V.sequential : V → Bool
  | .seq _ | .list _ | .vec _ => true
  | _ => false

def V.elems : V → List V
  | .seq xs | .list xs | .vec xs => xs
  | _ => []

/-- Util.equiv: strings by content, characters by value, sequential collections elementwise
(a String is not sequential), symbols and keywords by namespace and name. -/
partial def equiv (a b : V) : Bool :=
  match a, b with
  | .nil, .nil => true
  | .int x, .int y => x == y
  | .str x, .str y => x == y
  | .chr x, .chr y => x == y
  | .sym n1 m1, .sym n2 m2 => n1 == n2 && m1 == m2
  | .kw n1 m1, .kw n2 m2 => n1 == n2 && m1 == m2
  | x, y =>
    if x.sequential && y.sequential then
      x.elems.length == y.elems.length && (x.elems.zip y.elems).all fun (p, q) => equiv p q
    else false

/-- `(count s)`: characters. -/
def count (s : List Nat) : Nat := s.length

/-- `(nth s i)`: the character at i, StringIndexOutOfBounds otherwise. -/
def nth (s : List Nat) (i : Int) : Except String Nat :=
  if 0 ≤ i ∧ i < s.length then .ok (s.getD i.toNat 0) else .error "StringIndexOutOfBoundsException"

/-- `(get s i nf)`: RT.get on a String: the character when `0 ≤ i < count`, else nf. -/
def get (s : List Nat) (i : Int) : Option Nat := if 0 ≤ i ∧ i < s.length then some (s.getD i.toNat 0) else none

/-- `(subs s start end)`: String.substring: start ≥ 0, end ≤ length, start ≤ end. -/
def subs (s : List Nat) (start end_ : Int) : Except String (List Nat) :=
  if start < 0 ∨ end_ > s.length ∨ start > end_ then .error "StringIndexOutOfBoundsException"
  else .ok ((s.drop start.toNat).take (end_ - start).toNat)

/-- `(clojure.string/index-of s value from)`: String.indexOf(str, fromIndex): fromIndex ≥ length
→ (length for an empty target, else -1); negative → 0; empty target → fromIndex; else the first
occurrence at or after it. -/
def indexOf (s t : List Nat) (from_ : Int) : Int :=
  if from_ ≥ s.length then (if t.isEmpty then s.length else -1)
  else
    let f := if from_ < 0 then 0 else from_.toNat
    if t.isEmpty then f
    else match (List.range (s.length + 1)).find? (fun i => i ≥ f && (s.drop i).take t.length == t) with
      | some i => i
      | none => -1

/-- `(clojure.string/last-index-of s value from)`: String.lastIndexOf(str, fromIndex):
rightIndex = length - tlen; from > rightIndex → rightIndex; negative → -1; empty → from; else
the last occurrence at or before it. -/
def lastIndexOf (s t : List Nat) (from_ : Int) : Int :=
  let right : Int := (s.length : Int) - t.length
  let from_ := if from_ > right then right else from_
  if from_ < 0 then -1
  else if t.isEmpty then from_
  else match ((List.range (from_.toNat + 1)).reverse).find? (fun i => (s.drop i).take t.length == t) with
    | some i => i
    | none => -1

/-- Symbol.intern(nsname) (Symbol.java line 61). -/
def symbolIntern (s : List Nat) : V :=
  let slash := '/'.toNat
  match s.idxOf? slash with
  | none => .sym none s
  | some i => if s == [slash] then .sym none s else .sym (some (s.take i)) (s.drop (i + 1))

end Clj

end Jank.Strings
