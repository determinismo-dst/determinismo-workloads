import Jank.R4.Core.Value

/-!
# Round 4: type predicates and the functions built on them

**`counted?`** (core.jank 7007–7011 → core/seq.cpp `is_counted` 131–141): true when the object's
C++ type has a `count()` member (`behavior::countable`, behavior/countable.hpp 8–10). Clojure:
`(instance? clojure.lang.Counted coll)`. The table below is read from each type's header at
7135b7708 (`count() const`, including the bases `detail::base_persistent_map_sequence` 42–43 and
`detail::iterator_sequence` 40–41) and from Clojure 1.12's classes (`implements … Counted`,
IndexedSeq extends Counted).

**`bounded-count`** (core.jank 7521–7531, 7532–7542, defined twice, same text): Clojure's text;
it differs where `counted?` does.

**`map-entry?`** (core.jank 5075–5080): `(and (vector? x) (== 2 (count x)))`. Clojure:
`(instance? java.util.Map$Entry x)`. jank has no entry type (its map seqs yield vectors).

**`shuffle`** (core/seq.cpp 1178–1201): throws unless the type is `collection_like` (a static
`empty()` and `conj`, behavior/collection_like.hpp 10–14) and not `map_like`. Clojure:
`(java.util.ArrayList. ^java.util.Collection coll)`: any java.util.Collection (every ISeq,
vector, set; not maps, strings or arrays).
-/

namespace Jank.R4.Core.Preds

open Jank.R4.Core

structure Ty where
  name : String
  /-- Clojure source building an example with three elements where it can. -/
  src : String
  count : Nat
  jankCountable : Bool
  cljCounted : Bool
  jankShuffle : Bool
  cljShuffle : Bool
  deriving Repr, Inhabited

/-- Each object type a program can hold, with its behaviors on both sides. -/
def table : List Ty :=
  [ ⟨"persistent_string", "\"abc\"", 3, true, false, false, false⟩,
    ⟨"array (long)", "(long-array [1 2 3])", 3, true, false, false, false⟩,
    ⟨"persistent_vector", "[1 2 3]", 3, true, true, true, true⟩,
    ⟨"persistent_list", "'(1 2 3)", 3, true, true, true, true⟩,
    ⟨"persistent_array_map", "{:a 1 :b 2 :c 3}", 3, true, true, false, false⟩,
    ⟨"persistent_hash_map", "(hash-map :a 1 :b 2 :c 3)", 3, true, true, false, false⟩,
    ⟨"persistent_hash_set", "#{1 2 3}", 3, true, true, true, true⟩,
    ⟨"persistent_sorted_set", "(sorted-set 1 2 3)", 3, true, true, true, true⟩,
    ⟨"persistent_sorted_map", "(sorted-map 1 1 2 2 3 3)", 3, true, true, false, false⟩,
    ⟨"integer_range", "(range 3)", 3, true, true, true, true⟩,
    ⟨"range (real)", "(range 0.5 3)", 3, false, false, true, true⟩,
    ⟨"cons", "(cons 0 [1 2])", 3, false, false, false, true⟩,
    ⟨"lazy_sequence", "(map inc [1 2 3])", 3, false, false, true, true⟩,
    ⟨"repeat", "(repeat 3 :x)", 3, false, false, false, true⟩,
    ⟨"persistent_vector_sequence", "(seq [1 2 3])", 3, true, true, true, true⟩,
    ⟨"persistent_string_sequence", "(seq \"abc\")", 3, true, true, true, true⟩,
    ⟨"persistent_array_map_sequence", "(seq {:a 1 :b 2 :c 3})", 3, true, true, true, true⟩,
    ⟨"persistent_hash_map_sequence", "(seq (hash-map :a 1 :b 2 :c 3))", 3, true, false, true, true⟩,
    ⟨"persistent_hash_set_sequence", "(seq #{1 2 3})", 3, true, false, true, true⟩,
    ⟨"persistent_sorted_map_sequence", "(seq (sorted-map 1 1 2 2 3 3))", 3, true, false, true, true⟩,
    ⟨"persistent_sorted_set_sequence", "(seq (sorted-set 1 2 3))", 3, true, false, true, true⟩,
    ⟨"native_vector_sequence", "(sort [3 1 2])", 3, true, true, false, true⟩ ]

/-- `bounded-count` (core.jank 7521–7531), given `counted?`: the count, or at most `n` steps of
the seq. -/
def boundedCount (counted : Bool) (len n : Nat) : Nat :=
  if counted then len else min n len

def jankBoundedCount (t : Ty) (n : Nat) : Nat := boundedCount t.jankCountable t.count n
def cljBoundedCount (t : Ty) (n : Nat) : Nat := boundedCount t.cljCounted t.count n

/-- jank's `map-entry?` (core.jank 5075–5080) on the value model: `vector?` holds for vectors
(and for the entries jank's map seqs make, which are vectors). -/
def jankMapEntry : V → Bool
  | .vec xs => xs.length == 2
  | .entry .. => true
  | _ => false

/-- Clojure's `map-entry?`: `(instance? java.util.Map$Entry x)`. -/
def cljMapEntry : V → Bool
  | .entry .. => true
  | _ => false

/-- For every 2-vector, jank's `map-entry?` holds and Clojure's does not. -/
theorem jank_map_entry_any_pair (a b : V) : jankMapEntry (.vec [a, b]) = true ∧ cljMapEntry (.vec [a, b]) = false := by
  simp [jankMapEntry, cljMapEntry]

/-- Where the two agree: every value that is not a vector of two. -/
theorem map_entry_agree (v : V) (h : ∀ a b, v ≠ .vec [a, b]) : jankMapEntry v = cljMapEntry v := by
  cases v with
  | vec xs =>
    match xs, h with
    | [], _ => rfl
    | [_], _ => rfl
    | [a, b], h => exact absurd rfl (h a b)
    | _ :: _ :: _ :: _, _ => rfl
  | _ => rfl

/-- `bounded-count` agrees on every type whose `counted?` agrees, for every bound. -/
theorem bounded_count_agree (t : Ty) (n : Nat) (h : t.jankCountable = t.cljCounted) :
    jankBoundedCount t n = cljBoundedCount t n := by
  simp [jankBoundedCount, cljBoundedCount, h]

end Jank.R4.Core.Preds
