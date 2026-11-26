set_option linter.deprecated false

/-!
# Round 9, area Coll: get-in, contains?, coll?/empty, select-keys and empty metadata, assert,
# the walk demos, update-vals (M9-3, M9-4, M9-7 .. M9-10; R120 and R121 re-modelled)

Each pair is jank's function (94d32623) beside Clojure 1.12's, over an abstract value type that
keeps only what the two read.
-/

namespace Jank.R9.Coll.Paths

/-! ## get-in (round 2's R121, its new instances): seq.cpp `get_in` 473-511 against core.clj `get-in` -/

section GetIn

variable {V : Type} (nil : V) (hasGet : V → Bool) (look : V → V → Option V)

/-- `RT.get(m, k)` / jank `object_ref::get(k)`: a found value, else nil (also for a value without
lookup: `object::get` 190-193 returns nil, Clojure's RT.getFrom returns null). -/
def get1 (m k : V) : V := (look m k).getD nil

/-- `get` with a not-found value: `Option` keeps the miss (jank's sentinel / Clojure's). -/
def get3 (m k : V) : Option V := look m k

/-- Clojure `(get-in m ks)`: `(reduce1 get m ks)`. -/
def cljGetIn (m : V) (ks : List V) : V := ks.foldl (get1 nil look) m

/-- jank `get_in(m, keys)`: nil at once when `m` lacks the `get` behavior. -/
def jankGetIn (m : V) (ks : List V) : V :=
  if hasGet m then ks.foldl (get1 nil look) m else nil

/-- Clojure `(get-in m ks nf)`: a loop of `get` with a sentinel. -/
def cljGetInNf (m : V) (ks : List V) (nf : V) : V :=
  match ks with
  | [] => m
  | k :: ks => match look m k with
    | none => nf
    | some m' => cljGetInNf m' ks nf

/-- jank `get_in(m, keys, fallback)`. -/
def jankGetInNf (m : V) (ks : List V) (nf : V) : V :=
  if hasGet m then cljGetInNf look m ks nf else nil

/-- ★ For every root with the `get` behavior and every key list, both arities agree. -/
theorem getIn_agree (m : V) (hm : hasGet m = true) (ks : List V) (nf : V) :
    jankGetIn nil hasGet look m ks = cljGetIn nil look m ks ∧
    jankGetInNf nil hasGet look m ks nf = cljGetInNf look m ks nf := by
  simp [jankGetIn, cljGetIn, jankGetInNf, hm]

/-- ★ R121: for every root without it, jank gives nil; Clojure gives the root for no keys, and with
keys: the fold of `get` (nil after the first, as the root finds nothing) or the not-found value. -/
theorem getIn_no_lookup (m : V) (hm : hasGet m = false) (hl : ∀ k, look m k = none)
    (ks : List V) (nf : V) :
    jankGetIn nil hasGet look m ks = nil ∧ jankGetInNf nil hasGet look m ks nf = nil ∧
    cljGetInNf look m ks nf = (if ks.isEmpty then m else nf) := by
  refine ⟨by simp [jankGetIn, hm], by simp [jankGetInNf, hm], ?_⟩
  cases ks with
  | nil => rfl
  | cons k ks => simp [cljGetInNf, hl]

end GetIn

/-! ## contains? (M9-3): seq.cpp `contains` 518-533 against RT.contains 850-874 -/

/-- What `contains?` is given, by the branch each side takes. -/
inductive CKind where
  | nil
  /-- maps, vectors, sets, transient maps/sets/vectors: both answer by lookup -/
  | lookup (found : Bool)
  /-- a string with an integer key (in range or not): both answer by the index -/
  | strInt (inRange : Bool)
  /-- a string with a non-integer number (Clojure reads intValue; jank throws) -/
  | strFrac (inRange : Bool)
  /-- a string with a non-number key: both throw -/
  | strOther
  /-- lists, seqs, numbers, keywords, symbols, fns: no `get` behavior in jank; Clojure throws -/
  | other
  deriving DecidableEq, Repr

def cljContains : CKind → Option Bool
  | .nil => some false
  | .lookup f => some f
  | .strInt r => some r
  | .strFrac r => some r
  | .strOther => none
  | .other => none

def jankContains : CKind → Option Bool
  | .nil => some false
  | .lookup f => some f
  | .strInt r => some r
  | .strFrac _ => none
  | .strOther => none
  | .other => some false

/-- ★ The two disagree exactly on a non-lookup collection (Clojure throws, jank false) and on a
string with a non-integer number (M9-2); the first is M9-3. -/
theorem contains_differs_iff (k : CKind) :
    jankContains k ≠ cljContains k ↔ (k = .other ∨ ∃ r, k = .strFrac r) := by
  cases k <;> simp [jankContains, cljContains]

/-! ## coll? and empty (round 2's R120 and M9-10): seq.cpp `is_collection` 77-87 and `empty` 787-805 -/

/-- jank's object types that `coll?`/`empty` meet, with what their headers declare: a static
`empty()` (collection_like's first half) and `conj` (its second), and Clojure's class for the same
value: IPersistentCollection or not, and whether its `empty()` keeps metadata. -/
structure TypeRow where
  name : String
  jankEmpty : Bool
  jankConj : Bool
  cljColl : Bool
  /-- Clojure's `(empty x)`: keeps x's meta (true), drops it (false); `none` for non-collections
  and MapEntry (empty is nil) -/
  cljEmptyMeta : Option Bool
  deriving Repr

/-- obj/*.hpp at 94d32623: `static ... empty()` and `conj(object_ref` members. Clojure's classes:
PersistentList, PersistentVector, PersistentArrayMap/HashMap/TreeMap, PersistentHashSet/TreeSet
(empty keeps meta), Cons (keeps meta: `PersistentList.EMPTY.withMeta(meta())`), ASeq subclasses
(APersistentVector.Seq, ChunkedCons, LongRange/Range, Repeat, StringSeq, map seqs, ArraySeq,
Iterate) and LazySeq (`PersistentList.EMPTY`, no meta); String is not a collection. -/
def table : List TypeRow :=
  [ ⟨"persistent_list", true, true, true, some true⟩,
    ⟨"persistent_vector", true, true, true, some true⟩,
    ⟨"persistent_array_map", true, true, true, some true⟩,
    ⟨"persistent_hash_map", true, true, true, some true⟩,
    ⟨"persistent_sorted_map", true, true, true, some true⟩,
    ⟨"persistent_hash_set", true, true, true, some true⟩,
    ⟨"persistent_sorted_set", true, true, true, some true⟩,
    ⟨"cons", false, true, true, some true⟩,
    ⟨"repeat", false, true, true, some false⟩,
    ⟨"chunked_cons", false, true, true, some false⟩,
    ⟨"native_array_sequence", false, true, true, some false⟩,
    ⟨"native_vector_sequence", false, true, true, some false⟩,
    ⟨"persistent_vector_sequence", true, true, true, some false⟩,
    ⟨"persistent_string_sequence", true, true, true, some false⟩,
    ⟨"lazy_sequence", true, true, true, some false⟩,
    ⟨"range", true, true, true, some false⟩,
    ⟨"integer_range", true, true, true, some false⟩,
    ⟨"iterator", true, true, true, some false⟩,
    ⟨"persistent_string", true, false, false, none⟩ ]

def jankColl (r : TypeRow) : Bool := r.jankEmpty && r.jankConj

/-- jank `empty`: `with_meta(T::empty(), meta(o))` for a collection, else nil. Returns whether the
result is an empty collection and whether it keeps the meta. -/
def jankEmptyMeta (r : TypeRow) : Option Bool := if jankColl r then some true else none

/-- R120: the types where `coll?` differs (fixes/R120.diff gives cons an `empty()`). -/
theorem coll_differs :
    (table.filter fun r => jankColl r != r.cljColl).map (·.name) =
      ["cons", "repeat", "chunked_cons", "native_array_sequence", "native_vector_sequence"] := by
  decide

/-- R120 and M9-10: the types where `(meta (empty x))` differs (`none` = `empty` gives nil). -/
theorem empty_meta_differs :
    (table.filter fun r => jankEmptyMeta r != r.cljEmptyMeta).map (·.name) =
      ["cons", "repeat", "chunked_cons", "native_array_sequence", "native_vector_sequence",
       "persistent_vector_sequence", "persistent_string_sequence", "lazy_sequence", "range",
       "integer_range", "iterator"] := by
  decide

/-! ## select-keys keeps the map's metadata (M9-4) -/

/-- A map with metadata, as an association list. -/
structure MMap where
  kvs : List (Nat × Nat)
  md : Option Nat
  deriving DecidableEq, Repr

def find? (m : MMap) (k : Nat) : Option (Nat × Nat) := m.kvs.find? (·.1 == k)

/-- core.jank 2400-2409: reduce `conj` of found entries into `{}`. -/
def jankSelectKeys (m : MMap) (ks : List Nat) : MMap :=
  ⟨ks.filterMap (find? m), none⟩

/-- core.clj select-keys: the same entries, then `(with-meta ret (meta map))`. -/
def cljSelectKeys (m : MMap) (ks : List Nat) : MMap :=
  ⟨ks.filterMap (find? m), m.md⟩

/-- ★ For every map and key list: the same entries; the metadata differs exactly when the map has
some. -/
theorem selectKeys_differs (m : MMap) (ks : List Nat) :
    (jankSelectKeys m ks).kvs = (cljSelectKeys m ks).kvs ∧
    (jankSelectKeys m ks ≠ cljSelectKeys m ks ↔ m.md ≠ none) := by
  refine ⟨rfl, ?_⟩
  simp [jankSelectKeys, cljSelectKeys, eq_comm]

/-! ## assert (M9-7): core.jank 915-930 against core.clj `assert` -/

/-- The thrown value's message (as characters) and data, for a failed `(assert form)` (`form` is
`(pr-str form)`). -/
def jankAssert (form : List Char) : List Char × Option (List Char) :=
  ("assertion failed".toList, some form)

def cljPrefix : List Char := "Assert failed: ".toList

def cljAssert (form : List Char) : List Char × Option (List Char) := (cljPrefix ++ form, none)

theorem cljPrefix_head : cljPrefix.head? = some 'A' := by decide +kernel
theorem jank_head : "assertion failed".toList.head? = some 'a' := by decide +kernel

/-- ★ For every asserted form: the messages differ (their first characters already) and only jank's
thrown value carries data. -/
theorem assert_differs (form : List Char) :
    (jankAssert form).1 ≠ (cljAssert form).1 ∧ (jankAssert form).2 ≠ none ∧
    (cljAssert form).2 = none := by
  refine ⟨?_, by simp [jankAssert], rfl⟩
  intro h
  have := congrArg List.head? h
  simp only [jankAssert, cljAssert, List.head?_append, cljPrefix_head, jank_head] at this
  simp at this

/-! ## The walk demos (M9-8): `println` against `prn` of a string -/

def walked : List Char := "Walked: ".toList

/-- `(print s)` writes a string's characters; `(prn s)` writes it readably, in quotes (a string
without `"` or `\` inside). -/
def jankDemo (s : List Char) : List Char := walked ++ s ++ ['\n']
def cljDemo (s : List Char) : List Char := walked ++ ['"'] ++ s ++ ['"'] ++ ['\n']

/-- ★ For every string walked, the two printed lines differ (by two characters). -/
theorem demo_differs (s : List Char) : jankDemo s ≠ cljDemo s := by
  intro h
  have := congrArg List.length h
  simp [jankDemo, cljDemo] at this

/-! ## update-vals of a sorted map (M9-9) -/

/-- Whether the result is sorted: jank builds into `(transient m)` when `(transientable? m)`, which
holds for sorted maps (persistent_sorted_map.hpp `to_transient`); Clojure only for
IEditableCollection, which PersistentTreeMap is not. -/
def jankUpdateValsSorted (inputSorted : Bool) : Bool := inputSorted
def cljUpdateValsSorted (_ : Bool) : Bool := false

theorem updateVals_sorted_differs (b : Bool) :
    jankUpdateValsSorted b ≠ cljUpdateValsSorted b ↔ b = true := by
  cases b <;> simp [jankUpdateValsSorted, cljUpdateValsSorted]

end Jank.R9.Coll.Paths
