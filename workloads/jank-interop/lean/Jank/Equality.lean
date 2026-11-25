import Determinismo
import Jank.Hash

/-!
# `=` and `hash` across values: jank's `equal` dispatch beside Clojure's `Util.equiv`

jank's `=` (core.jank `=` → core/equal.cpp `equal(l, r)` → `l.equal(r)`) dispatches on the left
operand's type to its C++ `equal(object const &)`:

- `nil::equal` (nil.cpp): `o.type == nil`;
- integers (number.cpp `integer::equal`, `small_integer::equal`; big_integer.cpp): any integer
  type with the same value; reals (number.cpp `real::equal`): reals with `==`;
- `persistent_string::equal`, `character::equal`: same type and data; keywords: identity
  (interned);
- `persistent_vector::equal` (persistent_vector.cpp): a vector elementwise, anything else
  through `sequence_equal`;
- `persistent_list::equal` → seq_ext.hpp `equal(o, begin, end)`: false unless `o` is
  sequential (`is_sequential`, seq_ext.hpp:17 at jank 7135b7708; at f3d82d654 it was "nil or a
  non-`seqable`"), else elementwise over `o`'s sequence;
- `lazy_sequence::equal`, `cons::equal`, `base_persistent_map_sequence::equal` →
  core/seq.cpp `sequence_equal`;
- `persistent_hash_set::equal`: a set-like of the same count containing each element;
  `base_persistent_map::equal`: a map-like of the same count with equal values per key.

core/seq.cpp `sequence_equal(l, r)` (seq.cpp:881 at 7135b7708): identical → true; either not
sequential (`is_sequential`, seq.cpp:890) → false; else the two sequences elementwise. At
f3d82d654 the test was `seqable`, and `seqable` objects include nil, strings, sets and maps (their
`obj_behaviors`), none of which is sequential in Clojure.

Clojure (Util.equiv, APersistentVector.doEquiv, ASeq.equiv, LazySeq.equals, APersistentSet.equiv,
APersistentMap.equiv): a sequential collection equals only another `Sequential`/`List` with equal
elements; a set only a `Set`; a map only a `Map`; nil only nil.
-/

namespace Jank.Equality

open Jank.Hash

/-- A value: the jank object kinds that matter for `=` and `hash`. -/
inductive V where
  | nil
  /-- small_integer / integer: a long. -/
  | int (v : Int)
  /-- big_integer (`1N`, or `bigint`, or what `+'` promoted). -/
  | big (v : Int)
  /-- a double, by its bits (0.0 and -0.0 differ in bits). -/
  | real (bits : UInt64)
  | str (s : String)
  | char (c : Char)
  | kw (name : String)
  | vec (xs : List V)
  | list (xs : List V)
  /-- a realized lazy_sequence over `xs` (`(lazy-seq ...)`, `(map identity ...)`). -/
  | lazy (xs : List V)
  /-- persistent_hash_set, its elements in iteration order. -/
  | set (xs : List V)
  /-- persistent_array_map, its entries in order. -/
  | map (kvs : List (V × V))
  /-- `(seq m)`: a persistent_array_map_sequence. -/
  | mapseq (kvs : List (V × V))
  deriving Inhabited, BEq

partial def V.code : V → String
  | .nil => "nil"
  | .int v => s!"{v}"
  | .big v => s!"{v}N"
  | .real b => if b == 0x8000000000000000 then "-0.0" else if b == 0 then "0.0" else s!"(double-bits {b})"
  | .str s => s!"\"{s}\""
  | .char c => s!"\\{c}"
  | .kw k => s!":{k}"
  | .vec xs => "[" ++ " ".intercalate (xs.map V.code) ++ "]"
  | .list xs => if xs.isEmpty then "'()" else "'(" ++ " ".intercalate (xs.map V.code) ++ ")"
  | .lazy xs => if xs.isEmpty then "(lazy-seq nil)" else "(lazy-seq [" ++ " ".intercalate (xs.map V.code) ++ "])"
  | .set xs => if xs.isEmpty then "#{}" else "(hash-set " ++ " ".intercalate (xs.map V.code) ++ ")"
  | .map kvs => "{" ++ ", ".intercalate (kvs.map fun (k, v) => k.code ++ " " ++ v.code) ++ "}"
  | .mapseq kvs => "(seq {" ++ ", ".intercalate (kvs.map fun (k, v) => k.code ++ " " ++ v.code) ++ "})"

instance : Repr V where reprPrec v _ := v.code

/-- seq.cpp:65 `is_sequential`: `behavior::sequential<T>` (`T::is_sequential`, true for
persistent_vector, persistent_list, lazy_sequence, base_persistent_map_sequence and the other
sequence types; not for nil, strings, sets, maps). -/
def V.sequentialJ : V → Bool
  | .vec _ | .list _ | .lazy _ | .mapseq _ => true
  | _ => false

/-- `has_behavior(object_behavior::seqable)` (each type's `obj_behaviors`). -/
def V.seqable : V → Bool
  | .nil | .str _ | .vec _ | .list _ | .lazy _ | .set _ | .map _ | .mapseq _ => true
  | _ => false

/-- `make_sequence_range(o)`: the elements a sequence over `o` yields (a string's characters,
a map's entries as `[k v]` vectors, base_persistent_map_sequence.cpp `first`). -/
def V.elements : V → List V
  | .nil => []
  | .str s => s.toList.map V.char
  | .vec xs | .list xs | .lazy xs | .set xs => xs
  | .map kvs | .mapseq kvs => kvs.map fun (k, v) => V.vec [k, v]
  | _ => []

def utf8 (s : String) : List UInt8 := s.toUTF8.toList

/-! ## jank's hash (each type's `to_hash`) -/

/-- `to_hash()` of each kind. `fuel` bounds the recursion (values are small). -/
def jankHash (cs : CharSign) : Nat → V → UInt32
  | 0, _ => 0
  | _ + 1, .nil => 0                                        -- nil.cpp
  | _ + 1, .int v => integer (UInt64.ofInt v)               -- number.cpp: hash::integer(i64)
  | _ + 1, .big v => bigInteger v                           -- big_integer.cpp
  | _ + 1, .real b => real b                                -- number.cpp: hash::real
  | _ + 1, .str s => immutableString (utf8 s)               -- persistent_string.cpp
  | _ + 1, .char c => immutableString (utf8 (String.singleton c))  -- character.cpp
  | _ + 1, .kw k => keyword cs [] (utf8 k)                  -- keyword.cpp
  | f + 1, .vec xs => orderedRange (xs.map (jankHash cs f)) -- persistent_vector.cpp
  | f + 1, .list xs => orderedRange (xs.map (jankHash cs f)) -- persistent_list.cpp
  | f + 1, .lazy xs =>                                      -- lazy_sequence.cpp:98 (1 when empty, :103)
    if xs.isEmpty then 1 else orderedSeq (xs.map (jankHash cs f))
  | f + 1, .set xs => unorderedRange (xs.map (jankHash cs f)) -- persistent_hash_set.cpp
  | f + 1, .map kvs =>                                      -- base_persistent_map.cpp
    unorderedPairs (kvs.map fun (k, v) => (jankHash cs f k, jankHash cs f v))
  | f + 1, .mapseq kvs =>                                   -- base_persistent_map_sequence.cpp
    unorderedSeq (kvs.map fun (k, v) => orderedRange [jankHash cs f k, jankHash cs f v])

/-! ## jank's `=` -/

/-- Pairwise over two element lists, all equal and the same length. -/
def allPairs (eq : V → V → Bool) : List V → List V → Bool
  | [], [] => true
  | x :: xs, y :: ys => eq x y && allPairs eq xs ys
  | _, _ => false

mutual
/-- core/equal.cpp `equal(lhs, rhs)` = `lhs.equal(rhs)`. -/
def jankEq (cs : CharSign) : Nat → V → V → Bool
  | 0, _, _ => false
  | _ + 1, .nil, r => r == .nil                                   -- nil.cpp: o.type == nil
  | _ + 1, .int a, r => match r with                              -- number.cpp integer::equal
    | .int b | .big b => a == b | _ => false
  | _ + 1, .big a, r => match r with                              -- big_integer.cpp
    | .int b | .big b => a == b | _ => false
  | _ + 1, .real a, r => match r with                             -- real::equal: `data == r->data`
    | .real b => (Float.ofBits a) == (Float.ofBits b) | _ => false
  | _ + 1, .str a, r => r == .str a                               -- persistent_string::equal
  | _ + 1, .char a, r => r == .char a                             -- character::equal
  | _ + 1, .kw a, r => r == .kw a                                 -- interned: identity
  | f + 1, .vec xs, r => match r with                             -- persistent_vector::equal
    | .vec ys => xs.length == ys.length && allPairs (jankEq cs f) xs ys
    | _ => sequenceEqual cs f (.vec xs) r
  | f + 1, .list xs, r =>                                         -- seq_ext.hpp:15 equal(o, b, e)
    if !r.sequentialJ then false else allPairs (jankEq cs f) xs r.elements
  | f + 1, .lazy xs, r => sequenceEqual cs f (.lazy xs) r         -- lazy_sequence::equal
  | f + 1, .mapseq kvs, r => sequenceEqual cs f (.mapseq kvs) r   -- base_persistent_map_sequence
  | f + 1, .set xs, r => match r with                             -- persistent_hash_set::equal
    | .set ys => xs.length == ys.length && xs.all fun e => containsH cs f ys e
    | _ => false
  | f + 1, .map kvs, r => match r with                            -- base_persistent_map::equal
    | .map kvs' => kvs.length == kvs'.length && kvs.all fun (k, v) =>
        match lookupA cs f kvs' k with
        | some v' => jankEq cs f v v'
        | none => false
    | _ => false

/-- core/seq.cpp:881 `sequence_equal(l, r)` (identity elided: our values are freshly built). -/
def sequenceEqual (cs : CharSign) : Nat → V → V → Bool
  | 0, _, _ => false
  | f + 1, l, r =>
    if !l.sequentialJ || !r.sequentialJ then false
    else allPairs (jankEq cs f) l.elements r.elements

/-- An immer set's `count(e)`: the element with the same hash that `std::equal_to` (runtime
`equal`) accepts. -/
def containsH (cs : CharSign) : Nat → List V → V → Bool
  | 0, _, _ => false
  | f + 1, ys, e => ys.any fun y => jankHash cs (f + 1) y == jankHash cs (f + 1) e && jankEq cs f y e

/-- native_array_map.hpp `find`: keyword keys by identity, others by `runtime::equal`. -/
def lookupA (cs : CharSign) : Nat → List (V × V) → V → Option V
  | 0, _, _ => none
  | f + 1, kvs, k => (kvs.find? fun (k', _) => jankEq cs f k' k).map (·.2)
end

/-! ## Clojure's `=` (Util.equiv) -/

def V.sequential : V → Bool
  | .vec _ | .list _ | .lazy _ | .mapseq _ => true
  | _ => false

mutual
def cljEq : Nat → V → V → Bool
  | 0, _, _ => false
  | _ + 1, .nil, r => r == .nil
  -- Numbers.equal: the same category (INTEGER for Long and BigInt) and value.
  | _ + 1, .int a, r => match r with | .int b | .big b => a == b | _ => false
  | _ + 1, .big a, r => match r with | .int b | .big b => a == b | _ => false
  | _ + 1, .real a, r => match r with
    | .real b => Float.ofBits a == Float.ofBits b | _ => false
  | _ + 1, .str a, r => r == .str a
  | _ + 1, .char a, r => r == .char a
  | _ + 1, .kw a, r => r == .kw a
  -- APersistentVector.doEquiv / ASeq.equiv / LazySeq: only another Sequential.
  | f + 1, l@(.vec _), r | f + 1, l@(.list _), r | f + 1, l@(.lazy _), r
  | f + 1, l@(.mapseq _), r =>
    r.sequential && allPairsC f l.elements r.elements
  -- APersistentSet.equiv: only a Set.
  | f + 1, .set xs, r => match r with
    | .set ys => xs.length == ys.length && xs.all fun e => ys.any (cljEq f e)
    | _ => false
  -- APersistentMap.equiv: only a Map.
  | f + 1, .map kvs, r => match r with
    | .map kvs' => kvs.length == kvs'.length && kvs.all fun (k, v) =>
        kvs'.any fun (k', v') => cljEq f k k' && cljEq f v v'
    | _ => false

def allPairsC : Nat → List V → List V → Bool
  | 0, _, _ => false
  | _ + 1, [], [] => true
  | f + 1, x :: xs, y :: ys => cljEq f x y && allPairsC f xs ys
  | _ + 1, _, _ => false
end

/-! ## The world: two values drawn, three properties judged -/

/-- The atoms drawn. -/
def atoms : List V :=
  [.nil, .int 0, .int 1, .big 1, .real 0, .real 0x8000000000000000, .str "", .str "a", .char 'a', .kw "a"]

/-- The collection kinds drawn, each over 0, 1 or 2 atoms. -/
def collKinds : List (List V → V) :=
  [V.vec, V.list, V.lazy, V.set, fun xs => V.map (xs.map fun x => (x, x)),
   fun xs => V.mapseq (xs.map fun x => (x, x))]

/-- A set as jank builds one (`hash-set`, `conj`): an element is skipped when one with the same
hash is `equal` (immer's insert). -/
def jankSet (cs : CharSign) (xs : List V) : V :=
  .set (xs.foldl (fun acc x => if containsH cs 8 acc x then acc else acc ++ [x]) [])

structure EqWorld where
  decisions : Determinismo.Decisions := {}

instance : Determinismo.Chaotic EqWorld where
  decisions w := w.decisions
  setDecisions w d := { w with decisions := d }

open Determinismo in
def drawAtom (name : String) : EStateM Stop EqWorld V := do
  pure (atoms.getD (← decide (σ := EqWorld) name atoms.length) .nil)

open Determinismo in
/-- A value: an atom, or a collection of up to two atoms. -/
def drawValue (cs : CharSign) (name : String) : EStateM Stop EqWorld V := do
  let k ← decide (σ := EqWorld) s!"{name}.kind" (1 + collKinds.length)
  if k == 0 then drawAtom s!"{name}.atom"
  else
    let n ← decide (σ := EqWorld) s!"{name}.size" 3
    let mut xs := []
    for i in List.range n do
      xs := xs ++ [← drawAtom s!"{name}.elem{i}"]
    let build := collKinds.getD (k - 1) V.vec
    let v := build xs
    -- sets are built as jank builds them; maps keep distinct keys.
    pure (match v with
      | .set ys => jankSet cs ys
      | .map kvs => .map (kvs.foldl (fun acc (k, x) => if acc.any (·.1 == k) then acc else acc ++ [(k, x)]) [])
      -- `(seq {})` is nil (base_persistent_map.cpp `seq` on an empty map).
      | .mapseq [] => .nil
      | .mapseq kvs => .mapseq (kvs.foldl (fun acc (k, x) => if acc.any (·.1 == k) then acc else acc ++ [(k, x)]) [])
      | v => v)

inductive EqProperty where
  /-- jank's `(= a b)` is Clojure's. -/
  | agrees
  /-- `(= a b)` is `(= b a)`. -/
  | symmetric
  /-- `(= a b)` implies `(= (hash a) (hash b))`. -/
  | hashConsistent
  deriving Repr, BEq

def fuel : Nat := 12

open Determinismo in
def eqBody (cs : CharSign) (prop : EqProperty) : EStateM Stop EqWorld Unit := do
  let a ← drawValue cs "a"
  let b ← drawValue cs "b"
  let j := jankEq cs fuel a b
  match prop with
  | .agrees =>
    let c := cljEq fuel a b
    if j != c then
      violate (σ := EqWorld) "jank = is Clojure's =" s!"(= {a.code} {b.code}): Clojure {c}, jank {j}"
  | .symmetric =>
    let j' := jankEq cs fuel b a
    if j != j' then
      violate (σ := EqWorld) "= is symmetric" s!"(= {a.code} {b.code}) is {j} but (= {b.code} {a.code}) is {j'}"
  | .hashConsistent =>
    let ha := jankHash cs fuel a
    let hb := jankHash cs fuel b
    if j && ha != hb then
      violate (σ := EqWorld) "= implies equal hashes"
        s!"(= {a.code} {b.code}) is true but (hash {a.code}) = {ha}, (hash {b.code}) = {hb}"

open Determinismo in
def runEq (cs : CharSign) (prop : EqProperty) (source : Source) : Ended :=
  match (eqBody cs prop).run { decisions := { source } } with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }
  | .error (.nodeDown _) w => { taken := w.decisions.taken, violation := none }

/-- Every value of the drawn universe (for a full table of disagreements). -/
def valueUniverse (cs : CharSign) : List V := List.eraseDups <|
  atoms ++ (collKinds.flatMap fun build =>
    [build []] ++ (atoms.map fun a => build [a]) ++
      (atoms.flatMap fun a => atoms.map fun b => build [a, b])).map fun v => match v with
    | .set ys => jankSet cs ys
    | .map kvs => .map (kvs.foldl (fun acc (k, x) => if acc.any (·.1 == k) then acc else acc ++ [(k, x)]) [])
    | .mapseq [] => .nil
    | .mapseq kvs => .mapseq (kvs.foldl (fun acc (k, x) => if acc.any (·.1 == k) then acc else acc ++ [(k, x)]) [])
    | v => v

/-- Pairs written by hand: a map's seq against the vector of its entries, an empty lazy seq
against the empty list and vector, -0.0 against 0.0 inside collections. -/
def handPairs : List (V × V) :=
  [(.mapseq [(.kw "a", .int 1)], .vec [.vec [.kw "a", .int 1]]),
   (.mapseq [(.kw "a", .int 1)], .list [.vec [.kw "a", .int 1]]),
   (.lazy [], .list []), (.lazy [], .vec []),
   (.real 0, .real 0x8000000000000000),
   (.vec [.real 0], .vec [.real 0x8000000000000000]),
   (.int 1, .big 1), (.map [(.kw "a", .int 1)], .map [(.kw "a", .big 1)])]

end Jank.Equality
