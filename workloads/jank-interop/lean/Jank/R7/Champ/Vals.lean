import Jank.R3.Boost.Num
import Jank.Hash

/-!
# Round 7, CHAMP: jank's `=` and `hash` over every kind the brief names, beside Clojure's `=`

Round 1's value model (`Jank.Equality.V`) had longs, BigInts, doubles, strings, characters,
unqualified keywords and collections. This one adds ratios and BigDecimals (round 3's exact replicas:
`Jank.R3.Boost.Num.jEqual`/`jHash` over boost's `cpp_int` and `cpp_dec_float`, Clojure's `cEqual`
over Java's BigDecimal), string seqs (`(seq s)`), symbols and namespaced keywords. Each kind's jank
`equal` and `to_hash`, at 94d32623 (upstream-r5/compiler+runtime):

- numbers: integer/small_integer/big_integer by value (number.cpp 95-116, 184-205; big_integer.cpp
  116-131), real/small_real by C++ `==` (number.cpp 267-282, 385-400; tagged values oref.hpp 402-436,
  which hands a tagged left operand to the right one's `equal`: symmetric for these kinds), ratio
  only a ratio (ratio.cpp 139-147), big_decimal only a big_decimal within 2^-52 (big_decimal.cpp
  146-155). Hashes: hash::integer, boost limb hash (big_integer.cpp 155-170), hash::real of the bits
  (hash.cpp 116-127), combine of the parts (ratio.cpp 133-137), `cpp_dec_float::hash` (177-180).
- character: same type and UTF-8 data (character.cpp 63-72), hash of the data (89-92);
  persistent_string the same (persistent_string.cpp 31-40, 58-61).
- persistent_string_sequence (`(seq s)`): `equal` is seq_ext.hpp `equal(o, bytes)` (13-34): `o`
  sequential and each BYTE of the string `equal` (core/equal.cpp 8-17) to `o`'s next element, a
  character whose data is that one byte; `to_hash` is hash.hpp `ordered` over the bytes with
  `visit(char)` = the byte sign-extended (hash.cpp 151-154). Its elements, as a sequence, are
  characters, one per UTF-8 code point (round 6's SeqCount replica).
- symbol: ns and name (symbol.cpp 67-76), hash combine(string(name), string(ns)) (152-155);
  keyword: identity (object.cpp 47-50; interned), hash symbol + 0x9e3779b9 (keyword.cpp 45-48).
- collections as round 1's `Jank.Equality` (persistent_vector, persistent_list via seq_ext,
  lazy_sequence and map sequences via core/seq.cpp `sequence_equal`, persistent_hash_set 55-81,
  base_persistent_map).

Clojure (clojure-ref, 1.12): Util.equiv; Numbers.equal (same category, then equiv); Character,
String equals; StringSeq is sequential over UTF-16 units (BMP text only here); Symbol/Keyword equals
by ns and name; sequential collections equal elementwise; sets and maps by contents.

`Fix` switches turn each KNOWN cause off (its fix), so that what survives with every switch on is
outside the known classes.
-/

namespace Jank.R7.Champ.Vals

open Jank.R3.Boost Jank.R3.Boost.Num Jank.R3.Boost.Dec Jank.R3.Boost.Java
open Jank.Hash (CharSign)

inductive W where
  | nil
  | num (j : JV) (c : CV) (code : String)
  | char (c : Char)
  | str (s : String)
  /-- `(seq s)`, `s` nonempty: a persistent_string_sequence at index 0. -/
  | strseq (s : String)
  | kw (ns name : String)
  | sym (ns name : String)
  | vec (xs : List W)
  | list (xs : List W)
  /-- A realized lazy_sequence over `xs`. -/
  | lazy (xs : List W)
  | set (xs : List W)
  | map (kvs : List (W × W))
  /-- `(seq m)` of a nonempty array map. -/
  | mapseq (kvs : List (W × W))
  deriving Inhabited

partial def W.code : W → String
  | .nil => "nil"
  | .num _ _ c => c
  | .char c => if c.toNat < 128 then s!"\\{c}" else s!"(char {c.toNat})"
  | .str s => "\"" ++ String.join (s.toList.map fun c => if c.toNat < 128 then c.toString else s!"\\u{(Nat.toDigits 16 c.toNat).asString}") ++ "\""
  | .strseq s => s!"(seq {(W.str s).code})"
  | .kw ns n => if ns.isEmpty then s!":{n}" else s!":{ns}/{n}"
  | .sym ns n => if ns.isEmpty then s!"'{n}" else s!"'{ns}/{n}"
  | .vec xs => "[" ++ " ".intercalate (xs.map W.code) ++ "]"
  | .list xs => if xs.isEmpty then "()" else "(list " ++ " ".intercalate (xs.map W.code) ++ ")"
  | .lazy xs => if xs.isEmpty then "(lazy-seq nil)" else "(lazy-seq [" ++ " ".intercalate (xs.map W.code) ++ "])"
  | .set xs => if xs.isEmpty then "#{}" else "(hash-set " ++ " ".intercalate (xs.map W.code) ++ ")"
  | .map kvs => "{" ++ ", ".intercalate (kvs.map fun (k, v) => k.code ++ " " ++ v.code) ++ "}"
  | .mapseq kvs => "(seq {" ++ ", ".intercalate (kvs.map fun (k, v) => k.code ++ " " ++ v.code) ++ "})"

/-- The known causes, each one switchable to its fix. -/
structure Fix where
  /-- D12/V84: hash -0.0 as 0.0 (Clojure's Numbers.hasheq). -/
  negzero : Bool := false
  /-- V85: the collections' equality tests identity first (Util.equiv). -/
  identity : Bool := false
  /-- D12: a BigInt in the long range hashes as the long. -/
  bigint : Bool := false
  /-- D12: an empty lazy seq hashes as the empty list. -/
  lazyEmpty : Bool := false
  /-- D12: a map's seq hashes as an ordered collection. -/
  mapseq : Bool := false
  /-- R55/R56: a string seq compares and hashes by characters. -/
  strseq : Bool := false
  /-- D8/S10: BigDecimals compare exactly and hash by value. -/
  bigdec : Bool := false
  /-- S59: an `=` element or key already stored is kept (Clojure keeps the old key). -/
  keepOld : Bool := false
  deriving Repr, Inhabited

def Fix.all : Fix := ⟨true, true, true, true, true, true, true, true⟩
def Fix.none : Fix := {}

def cs : CharSign := .signed

def utf8 (s : String) : List UInt8 := s.toUTF8.toList

def W.seqJ : W → Bool
  | .vec _ | .list _ | .lazy _ | .mapseq _ | .strseq _ => true
  | _ => false

/-- The elements a sequence over the value yields. -/
def W.elems : W → List W
  | .nil => []
  | .str s | .strseq s => s.toList.map W.char
  | .vec xs | .list xs | .lazy xs | .set xs => xs
  | .map kvs | .mapseq kvs => kvs.map fun (k, v) => W.vec [k, v]
  | _ => []

/-- core/equal.cpp 8-17 `equal(char, object)`: a character whose data is that one byte. -/
def byteEq (b : UInt8) : W → Bool
  | .char c => utf8 c.toString == [b]
  | _ => false

def allP (eq : W → W → Bool) : List W → List W → Bool
  | [], [] => true
  | x :: xs, y :: ys => eq x y && allP eq xs ys
  | _, _ => false

/-! ## jank -/

def bdNormHash (d : BD) : UInt32 :=
  -- a consistent hash for the fixed side: the value with trailing zeros stripped
  let rec strip (u : Int) (s : Int) (fuel : Nat) : Int × Int :=
    match fuel with
    | 0 => (u, s)
    | f + 1 => if u != 0 && u % 10 == 0 then strip (u / 10) (s - 1) f else (u, s)
  let (u, s) := if d.u == 0 then (0, 0) else strip d.u d.s 400
  Jank.Hash.combine (Jank.Hash.integer (UInt64.ofInt u)) (Jank.Hash.integer (UInt64.ofInt s))

mutual
def jHashW (fx : Fix) : Nat → W → UInt32
  | 0, _ => 0
  | _ + 1, .nil => 0
  | _ + 1, .num j c _ => match j, c with
    | .dbl x, _ => if fx.negzero && x.toBits == 0x8000000000000000 then 0 else jHash j
    | .big v, _ => if fx.bigint && CppInt.fitsI64 v then Jank.Hash.integer (UInt64.ofInt v) else jHash j
    | .dec _, .dec d => if fx.bigdec then bdNormHash d else jHash j
    | _, _ => jHash j
  | _ + 1, .char c => Jank.Hash.immutableString (utf8 c.toString)
  | _ + 1, .str s => Jank.Hash.immutableString (utf8 s)
  | f + 1, .strseq s =>
    if fx.strseq then Jank.Hash.orderedRange (s.toList.map fun c => jHashW fx f (.char c))
    else Jank.Hash.orderedRange ((utf8 s).map fun b => UInt32.ofNat (if b.toNat ≥ 128 then b.toNat + 0xFFFFFF00 else b.toNat))
  | _ + 1, .kw ns n => Jank.Hash.keyword cs (utf8 ns) (utf8 n)
  | _ + 1, .sym ns n => Jank.Hash.symbol cs (utf8 ns) (utf8 n)
  | f + 1, .vec xs => Jank.Hash.orderedRange (hashL fx f xs)
  | f + 1, .list xs => Jank.Hash.orderedRange (hashL fx f xs)
  | f + 1, .lazy xs => if xs.isEmpty then (if fx.lazyEmpty then Jank.Hash.orderedRange [] else 1)
      else Jank.Hash.orderedSeq (hashL fx f xs)
  | f + 1, .set xs => Jank.Hash.unorderedRange (hashL fx f xs)
  | f + 1, .map kvs => Jank.Hash.unorderedPairs (hashP fx f kvs)
  | f + 1, .mapseq kvs =>
    if fx.mapseq then Jank.Hash.orderedRange ((hashP fx f kvs).map fun (a, b) => Jank.Hash.orderedRange [a, b])
    else Jank.Hash.unorderedSeq ((hashP fx f kvs).map fun (a, b) => Jank.Hash.orderedRange [a, b])

def hashL (fx : Fix) : Nat → List W → List UInt32
  | _, [] => []
  | f, x :: xs => jHashW fx f x :: hashL fx f xs

def hashP (fx : Fix) : Nat → List (W × W) → List (UInt32 × UInt32)
  | _, [] => []
  | f, (k, v) :: kvs => (jHashW fx f k, jHashW fx f v) :: hashP fx f kvs
end

mutual
/-- `runtime::equal(a, b)` = `a.equal(b)`. -/
def jEqW (fx : Fix) : Nat → W → W → Bool
  | 0, _, _ => false
  | _ + 1, .nil, r => match r with | .nil => true | _ => false
  | _ + 1, .num a ca _, r => match r with
    | .num b cb _ => match a, b, ca, cb with
      | .dec _, .dec _, .dec x, .dec y => if fx.bigdec then x.cmp y == 0 else jEqual a b
      | _, _, _, _ => jEqual a b
    | _ => false
  | _ + 1, .char a, r => match r with | .char b => a == b | _ => false
  | _ + 1, .str a, r => match r with | .str b => a == b | _ => false
  | f + 1, .strseq s, r =>
    if fx.strseq then seqEqW fx f (.strseq s) r
    else if !r.seqJ then false
    else
      let es := r.elems
      (utf8 s).length == es.length && ((utf8 s).zip es).all fun (b, e) => byteEq b e
  | _ + 1, .kw a n, r => match r with | .kw b m => a == b && n == m | _ => false
  | _ + 1, .sym a n, r => match r with | .sym b m => a == b && n == m | _ => false
  | f + 1, .vec xs, r => match r with
    | .vec ys => xs.length == ys.length && allP (jEqW fx f) xs ys
    | _ => seqEqW fx f (.vec xs) r
  | f + 1, .list xs, r => if !r.seqJ then false else allP (jEqW fx f) xs r.elems
  | f + 1, .lazy xs, r => seqEqW fx f (.lazy xs) r
  | f + 1, .mapseq kvs, r => seqEqW fx f (.mapseq kvs) r
  | f + 1, .set xs, r => match r with
    | .set ys => xs.length == ys.length && xs.all fun e => ys.any fun y => jHashW fx (f + 1) y == jHashW fx (f + 1) e && jEqW fx f y e
    | _ => false
  | f + 1, .map kvs, r => match r with
    | .map kvs' => kvs.length == kvs'.length && kvs.all fun (k, v) =>
        match kvs'.find? (fun (k', _) => jEqW fx f k' k) with
        | some (_, v') => jEqW fx f v v'
        | none => false
    | _ => false

/-- core/seq.cpp `sequence_equal`. -/
def seqEqW (fx : Fix) : Nat → W → W → Bool
  | 0, _, _ => false
  | f + 1, l, r => if !l.seqJ || !r.seqJ then false else allP (jEqW fx f) l.elems r.elems
end

/-! ## Clojure -/

mutual
def cEqW : Nat → W → W → Bool
  | 0, _, _ => false
  | _ + 1, .nil, r => match r with | .nil => true | _ => false
  | _ + 1, .num _ a _, r => match r with | .num _ b _ => cEqual a b == some true | _ => false
  | _ + 1, .char a, r => match r with | .char b => a == b | _ => false
  | _ + 1, .str a, r => match r with | .str b => a == b | _ => false
  | _ + 1, .kw a n, r => match r with | .kw b m => a == b && n == m | _ => false
  | _ + 1, .sym a n, r => match r with | .sym b m => a == b && n == m | _ => false
  | f + 1, .set xs, r => match r with
    | .set ys => xs.length == ys.length && xs.all fun e => ys.any (cEqW f e)
    | _ => false
  | f + 1, .map kvs, r => match r with
    | .map kvs' => kvs.length == kvs'.length && kvs.all fun (k, v) => kvs'.any fun (k', v') => cEqW f k k' && cEqW f v v'
    | _ => false
  | f + 1, l, r => l.seqJ && r.seqJ && cAll f l.elems r.elems

def cAll : Nat → List W → List W → Bool
  | 0, _, _ => false
  | _ + 1, [], [] => true
  | f + 1, x :: xs, y :: ys => cEqW f x y && cAll f xs ys
  | _ + 1, _, _ => false
end

def fuel : Nat := 10

def jEq (fx : Fix) (a b : W) : Bool := jEqW fx fuel a b
def jH (fx : Fix) (a : W) : UInt32 := jHashW fx fuel a
def cEq (a b : W) : Bool := cEqW fuel a b

/-! ## Constructors -/

def long (n : Int) : W := .num (.long n) (.long n) s!"{n}"
def bigI (n : Int) : W := .num (.big n) (.big n) s!"{n}N"
def dbl (bits : UInt64) (code : String) : W := .num (.dbl (Float.ofBits bits)) (.dbl (Float.ofBits bits)) code
def ratio (n d : Int) : W := .num (.ratio n d) (.ratio n d) s!"{n}/{d}"
def dec (s : String) : W :=
  let cs := s.toList.map Char.toNat
  match rdString cs, BD.ofString cs with
  | .ok j, .ok c => .num (.dec j) (.dec c) (s ++ "M")
  | _, _ => .nil

end Jank.R7.Champ.Vals
