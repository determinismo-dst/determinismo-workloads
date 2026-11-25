import Std.Tactic.BVDecide
import Determinismo

/-!
# seq.cpp's dispatch on behaviors: `empty`, `coll?`, `get-in`, `find`; core/array.cpp's bytes

seq.cpp decides many operations by C++ concepts on the object's type (`behavior::*<T>`, checked
by `visit_object`), not by Clojure's interfaces:

- `empty` (seq.cpp:787) and `coll?` (`is_collection`, seq.cpp:77) need `collection_like<T>`
  (collection_like.hpp: a static `empty()` and a `conj` member). At jank 7135b7708 `cons`,
  `chunked_cons`, `repeat`, `native_vector_sequence` and `native_array_sequence` have no static
  `empty()` (their headers), so for them `empty` returns nil and `coll?` false. (At f3d82d654
  `lazy_sequence` and `persistent_string_sequence` had none either; 7135b7708 adds them:
  lazy_sequence.hpp:49 / lazy_sequence.cpp:113, persistent_string_sequence.hpp:55 / .cpp:157.)
  In Clojure every one of these is an `ISeq`, hence an `IPersistentCollection`: `(empty s)` is
  `()` and `(coll? s)` is true.
- `get-in` (seq.cpp:473, 490) returns nil at once when `m` lacks the `get` behavior (numbers,
  keywords: number.hpp, keyword.hpp), before looking at `ks`; Clojure's is `(reduce get m ks)`.
- `find` on maps (persistent_array_map.cpp:55, persistent_hash_map.cpp:94) builds the entry from
  the key passed in, not the key stored.
- `byte-array` (core/array.cpp:263) stores into `u8` and `aget` boxes the `u8` through
  `convert<u8>::into_object` (`make_box(static_cast<i64>(o))`): bytes read back as 0..255.
  Java's `byte` is signed: `(aget (byte-array [-1]) 0)` is -1.
-/

namespace Jank.Seq.Core

open Determinismo

/-- The object types that matter here (object_type values). -/
inductive Ty where
  | nil | integer | keyword | persistentString
  | persistentList | persistentVector | persistentArrayMap | persistentHashMap | persistentHashSet
  | persistentVectorSequence | persistentArrayMapSequence | persistentHashSetSequence
  | integerRange | range | iterator
  | cons | chunkedCons | lazySequence | repeat | nativeVectorSequence | nativeArraySequence
  | persistentStringSequence
  deriving Repr, BEq, DecidableEq, Inhabited

def allTys : List Ty :=
  [.nil, .integer, .keyword, .persistentString, .persistentList, .persistentVector,
   .persistentArrayMap, .persistentHashMap, .persistentHashSet, .persistentVectorSequence,
   .persistentArrayMapSequence, .persistentHashSetSequence, .integerRange, .range, .iterator,
   .cons, .chunkedCons, .lazySequence, .repeat, .nativeVectorSequence, .nativeArraySequence,
   .persistentStringSequence]

/-- A program producing a value of the type. -/
def Ty.example : Ty → String
  | .nil => "nil" | .integer => "5" | .keyword => ":k" | .persistentString => "\"ab\""
  | .persistentList => "'(1 2)" | .persistentVector => "[1 2]" | .persistentArrayMap => "{:a 1}"
  | .persistentHashMap => "(hash-map :a 1)" | .persistentHashSet => "#{1}"
  | .persistentVectorSequence => "(seq [1 2])" | .persistentArrayMapSequence => "(seq {:a 1})"
  | .persistentHashSetSequence => "(seq #{1})" | .integerRange => "(range 3)"
  | .range => "(range 2.5)" | .iterator => "(iterate inc 0)" | .cons => "(cons 0 [1])"
  | .chunkedCons => "(seq (map inc (range 0.5 2.0)))" | .lazySequence => "(map inc [1 2])"
  | .repeat => "(repeat 2 :x)" | .nativeVectorSequence => "(sort [2 1])"
  | .nativeArraySequence => "(seq (long-array 2))" | .persistentStringSequence => "(seq \"ab\")"

/-- Has a static `empty()` at jank 7135b7708 (grep of each obj/*.hpp; map and set sequences
through detail/base_persistent_map_sequence.hpp:65 and detail/iterator_sequence.hpp:59;
`lazy_sequence` and `persistent_string_sequence` new in 7135b7708). -/
def Ty.hasStaticEmpty : Ty → Bool
  | .persistentString | .persistentList | .persistentVector | .persistentArrayMap
  | .persistentHashMap | .persistentHashSet | .persistentVectorSequence
  | .persistentArrayMapSequence | .persistentHashSetSequence | .integerRange | .range | .iterator
  | .lazySequence | .persistentStringSequence => true
  | _ => false

/-- Has a `conj` member (behavior::conjable). -/
def Ty.hasConj : Ty → Bool
  | .nil | .integer | .keyword | .persistentString => false
  | _ => true

/-- collection_like.hpp: `T::empty()` and `conjable<T>`. -/
def Ty.collectionLike (t : Ty) : Bool := t.hasStaticEmpty && t.hasConj

/-- `has_behavior(object_behavior::get)` (each type's `obj_behaviors`). -/
def Ty.hasGet : Ty → Bool
  | .nil | .persistentString | .persistentVector | .persistentArrayMap | .persistentHashMap
  | .persistentHashSet => true
  | _ => false

/-- What `empty` returns: the type of the empty value, `none` for nil. -/
inductive Empty where
  | nil | emptyList | emptyVector | emptyMap | emptySet | emptyString
  deriving Repr, BEq, DecidableEq

/-- `T::empty()` of the collection-like types. -/
def Ty.emptyValue : Ty → Empty
  | .persistentVector => .emptyVector
  | .persistentArrayMap | .persistentHashMap => .emptyMap
  | .persistentHashSet => .emptySet
  | .persistentString => .emptyString
  | _ => .emptyList

/-- seq.cpp:787 `empty`: `collection_like<T>` → `with_meta(T::empty(), meta(o))`, else nil. -/
def jankEmpty (t : Ty) : Empty := if t.collectionLike then t.emptyValue else .nil

/-- seq.cpp:77 `is_collection` (`coll?`): `collection_like<T>`. -/
def jankIsColl (t : Ty) : Bool := t.collectionLike

/-- Clojure: `IPersistentCollection`: every seq, list, vector, map, set; not nil, numbers,
keywords, strings. -/
def Ty.cljColl : Ty → Bool
  | .nil | .integer | .keyword | .persistentString => false
  | _ => true

/-- core.clj `empty`: `(.empty coll)` for an IPersistentCollection: a seq's is `()`. -/
def cljEmpty (t : Ty) : Empty := if t.cljColl then t.emptyValue else .nil

/-! ## get-in -/

/-- Values for `get-in`: nil, a number, a keyword, `{:a v}`, `[v]`. -/
inductive GV where
  | nil | num (n : Int) | kw | mapA (v : GV) | vec1 (v : GV)
  deriving Repr, BEq, DecidableEq, Inhabited

def GV.code : GV → String
  | .nil => "nil" | .num n => toString n | .kw => ":k"
  | .mapA v => "{:a " ++ v.code ++ "}" | .vec1 v => "[" ++ v.code ++ "]"

/-- Keys: `:a` or `0`. -/
inductive GK where
  | a | zero
  deriving Repr, BEq, DecidableEq, Inhabited

def GK.code : GK → String | .a => ":a" | .zero => "0"

def GV.hasGet : GV → Bool
  | .nil | .mapA _ | .vec1 _ => true
  | _ => false

/-- A result: a value, or the not-found argument. -/
inductive GR where
  | val (v : GV)
  | notFound
  deriving Repr, BEq, DecidableEq

/-- `m.get(key, fallback)` (persistent_array_map, persistent_vector, nil; object::get's
default returns the fallback). -/
def getF (m : GV) (k : GK) (fb : GR) : GR :=
  match m, k with
  | .mapA v, .a => .val v
  | .vec1 v, .zero => .val v
  | _, _ => fb

/-- seq.cpp:473 `get_in(m, keys)`: nil unless `m` has `get`; then `ret = get(ret, e)` per key. -/
def jankGetIn2 (m : GV) (ks : List GK) : GV :=
  if !m.hasGet then .nil
  else ks.foldl (fun ret k => match getF ret k (.val .nil) with | .val v => v | .notFound => .nil) m

/-- seq.cpp:490 `get_in(m, keys, fallback)`: nil (not the fallback) unless `m` has `get`; then
`get(ret, e, sentinel)` per key, the fallback at the sentinel. -/
def jankGetIn3 (m : GV) (ks : List GK) : GR :=
  if !m.hasGet then .val .nil
  else
    let rec go : GV → List GK → GR
      | ret, [] => .val ret
      | ret, k :: ks => match getF ret k .notFound with
        | .notFound => .notFound
        | .val v => go v ks
    go m ks

/-- core.clj 6205 `get-in`: `(reduce1 get m ks)`; with not-found, the sentinel loop. -/
def cljGetIn2 (m : GV) (ks : List GK) : GV :=
  ks.foldl (fun ret k => match getF ret k (.val .nil) with | .val v => v | .notFound => .nil) m

def cljGetIn3 (m : GV) (ks : List GK) : GR :=
  let rec go : GV → List GK → GR
    | ret, [] => .val ret
    | ret, k :: ks => match getF ret k .notFound with
      | .notFound => .notFound
      | .val v => go v ks
  go m ks

/-! ## find: the entry's key -/

/-- Keys equal under `=` with equal hashes but different types: `[1]` and `'(1)`. -/
inductive FK where
  | vec1 | list1
  deriving Repr, BEq, DecidableEq

def FK.code : FK → String | .vec1 => "[1]" | .list1 => "'(1)"

/-- persistent_array_map.cpp:55 `find`: `make_box<persistent_vector>(std::in_place, key, value)`
with the key passed in. -/
def jankFindKey (_stored passed : FK) : FK := passed

/-- APersistentMap / PersistentArrayMap.entryAt: the stored key. -/
def cljFindKey (stored _passed : FK) : FK := stored

/-! ## byte-array -/

/-- core/array.cpp:263 `byte_array(o)`: `a->data[i] = e.to_integer()` (an i64 into `u8`), then
`aget` (core/array.cpp:282 → array::nth → `convert<u8>::into_object` = `make_box(static_cast<i64>(u8))`). -/
def jankByteRoundTrip (x : BitVec 64) : BitVec 64 := (x.truncate 8).zeroExtend 64

/-- clojure.lang.Numbers.byte_array: `((Number) s.first()).byteValue()`; aget gives that byte. -/
def cljByteRoundTrip (x : BitVec 64) : BitVec 64 := (x.truncate 8).signExtend 64

/-- They agree exactly when bit 7 is clear. -/
theorem byte_roundtrip_agree_iff (x : BitVec 64) :
    jankByteRoundTrip x = cljByteRoundTrip x ↔ x.getLsbD 7 = false := by
  unfold jankByteRoundTrip cljByteRoundTrip
  constructor
  · intro h; bv_decide
  · intro h; bv_decide

/-- `(aget (byte-array [-1]) 0)`: Clojure -1, jank 255. -/
theorem byte_minus_one : (jankByteRoundTrip (-1)).toInt = 255 ∧ (cljByteRoundTrip (-1)).toInt = -1 := by
  constructor <;> decide

/-- `(coll? (cons 0 [1]))`: Clojure true, jank false; `(empty (cons 0 [1]))`: Clojure (), jank nil.
A lazy seq is a collection at 7135b7708. -/
theorem cons_not_coll :
    jankIsColl .cons = false ∧ Ty.cljColl .cons = true ∧
    jankEmpty .cons = .nil ∧ cljEmpty .cons = .emptyList ∧
    jankIsColl .lazySequence = true ∧ jankEmpty .lazySequence = .emptyList := by decide

/-! ## The world -/

structure World where
  decisions : Decisions := {}

instance : Chaotic World where
  decisions w := w.decisions
  setDecisions w d := { w with decisions := d }

def gvs : List GV := [.nil, .num 5, .kw, .mapA (.num 1), .mapA (.mapA (.num 2)), .vec1 (.num 3), .mapA .kw]
def kss : List (List GK) := [[], [.a], [.zero], [.a, .a], [.a, .zero]]

inductive Question where
  | empty (t : Ty)
  | coll (t : Ty)
  | getIn2 (m : GV) (ks : List GK)
  | getIn3 (m : GV) (ks : List GK)
  | find (stored passed : FK)
  | byte (x : BitVec 64)

def bytes : List (BitVec 64) := [0, 1, 127, 128, 200, 255, 256, -1, -128, -129]

def Question.verdict : Question → Option String
  | .empty t =>
    let (j, c) := (jankEmpty t, cljEmpty t)
    if j != c then some s!"(empty {t.example}): Clojure {reprStr c}, jank {reprStr j}" else none
  | .coll t =>
    let (j, c) := (jankIsColl t, t.cljColl)
    if j != c then some s!"(coll? {t.example}): Clojure {c}, jank {j}" else none
  | .getIn2 m ks =>
    let (j, c) := (jankGetIn2 m ks, cljGetIn2 m ks)
    let kc := "[" ++ " ".intercalate (ks.map GK.code) ++ "]"
    if j != c then some s!"(get-in {m.code} {kc}): Clojure {c.code}, jank {j.code}" else none
  | .getIn3 m ks =>
    let (j, c) := (jankGetIn3 m ks, cljGetIn3 m ks)
    let kc := "[" ++ " ".intercalate (ks.map GK.code) ++ "]"
    let sh := fun (r : GR) => match r with | .val v => v.code | .notFound => ":nf"
    if j != c then some s!"(get-in {m.code} {kc} :nf): Clojure {sh c}, jank {sh j}" else none
  | .find s p =>
    let (j, c) := (jankFindKey s p, cljFindKey s p)
    if j != c then some s!"(key (find \{{s.code} :v} {p.code})): Clojure {c.code}, jank {j.code}" else none
  | .byte x =>
    let (j, c) := (jankByteRoundTrip x, cljByteRoundTrip x)
    if j != c then some s!"(aget (byte-array [{x.toInt}]) 0): Clojure {c.toInt}, jank {j.toInt}" else none

def drawQuestion : EStateM Stop World Question := do
  match ← decide (σ := World) "core.function" 6 with
  | 0 => return .empty ((← pick (σ := World) "core.type" allTys).getD .nil)
  | 1 => return .coll ((← pick (σ := World) "core.type" allTys).getD .nil)
  | 2 => return .getIn2 ((← pick (σ := World) "core.m" gvs).getD .nil) ((← pick (σ := World) "core.ks" kss).getD [])
  | 3 => return .getIn3 ((← pick (σ := World) "core.m" gvs).getD .nil) ((← pick (σ := World) "core.ks" kss).getD [])
  | 4 => return .find ((← pick (σ := World) "core.stored" [FK.vec1, .list1]).getD .vec1)
                      ((← pick (σ := World) "core.passed" [FK.vec1, .list1]).getD .vec1)
  | _ => return .byte ((← pick (σ := World) "core.byte" bytes).getD 0)

def body : EStateM Stop World Unit := do
  let q ← drawQuestion
  if let some d := q.verdict then violate (σ := World) "agrees with Clojure" d

def run (source : Source) : Ended :=
  match body.run { decisions := { source } } with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }
  | .error (.nodeDown _) w => { taken := w.decisions.taken, violation := none }

def allQuestions : List Question :=
  allTys.map .empty ++ allTys.map .coll ++
  (gvs.flatMap fun m => kss.map (.getIn2 m)) ++ (gvs.flatMap fun m => kss.map (.getIn3 m)) ++
  [.find .vec1 .vec1, .find .vec1 .list1, .find .list1 .vec1, .find .list1 .list1] ++ bytes.map .byte

end Jank.Seq.Core
