import Determinismo
import Jank.Compare

/-!
# Sorted collections: jank's `std::map`/`std::set` beside Clojure's `PersistentTreeMap`/`Set`

jank (commit 7135b7708, `upstream-main/compiler+runtime/`; of the files below only core/seq.cpp and
obj/native_vector_sequence.cpp changed since f3d82d654):

- `include/cpp/jank/runtime/detail/type.hpp` 49–65: `native_persistent_sorted_set` is
  `std::set<object_ref, object_ref_compare>` and `native_persistent_sorted_map` is
  `std::map<object_ref, object_ref, object_ref_compare>`; the transient types are the same
  containers. `src/cpp/jank/runtime/detail/type.cpp` 6: `object_ref_compare` is
  `runtime::compare(l, r) < 0`, i.e. fork C's `Jank.Compare.jankCompare` (imported read-only).
- `obj/persistent_sorted_map.cpp` (every member), `obj/persistent_sorted_set.cpp` (every member),
  `obj/transient_sorted_map.cpp`, `obj/transient_sorted_set.cpp`,
  `obj/detail/base_persistent_map.cpp` (`equal`, `conj`, `count`, `seq`, the shared map base),
  `core/seq.cpp` `find` (513), `contains` (518), `empty` (787), `is_sorted` (155), `sort` (1098),
  `obj/native_vector_sequence.cpp` (`seq`, `first`, `next`, `count`), `core/meta.cpp`
  `reset_meta` (84), and core.jank `sorted-map` (444), `sorted-set` (2431), `sorted-set-by`
  (2438), `sorted-map-by` (5032), `rseq` (5081), `subseq` (6510), `rsubseq` (6527).

Clojure 1.12 (clojure-ref): `PersistentTreeMap.java` (`create` 74, `entryAt` 313, `replace`
466, `without` 140, `equiv` 108: a `ClassCastException` inside is caught and answers false),
`PersistentTreeSet.java` (`cons`, `disjoin`, `equiv` catching the same), `APersistentSet.equiv`
(walks the *other* set and asks this one), `APersistentMap.equiv`, `RT.find` (`entryAt`: the
stored entry), core.clj `sort` (`()` for an empty coll).

Library behaviour assumed (the C++ standard library is not readable here):
- S1. `std::map`/`std::set` with a strict weak ordering keep their keys sorted and unique up to
  equivalence (`!(a<b) && !(b<a)`); `operator[]` and `insert_or_assign` keep the stored key and
  replace the value; `insert` of an equivalent key does nothing; `find`/`contains`/`erase` use
  equivalence. Which comparisons a lookup makes is unspecified; the replica descends a balanced
  tree as a binary search over the sorted keys, comparing `comp(k, node)` then `comp(node, k)`
  (both libstdc++ and libc++ descend from the root). An exception from the comparator leaves the
  container unchanged and propagates.
- S2. Clojure's red-black tree is also searched from its root with `doCompare(key, node)`; it is
  modeled by the same binary search (so both sides compare the same pairs in the same order).
-/

namespace Jank.Core.Sorted

open Determinismo
open Jank.Compare (CV Cmp jankCompare cljCompare fuel)

/-! ## Outcomes -/

/-- What a C++ or Java call ended with. -/
inductive R (α : Type) where
  | ok (v : α)
  /-- A catchable exception. -/
  | throws (why : String)
  /-- Undefined behavior (a debug-build abort or a wild read in a release build). -/
  | ub (why : String)
  deriving Inhabited

instance : Monad R where
  pure := .ok
  bind x f := match x with
    | .ok v => f v
    | .throws w => .throws w
    | .ub w => .ub w

def throwR {α : Type} (w : String) : R α := .throws w

/-! ## Values -/

/-- Sizes for the recursion through lists of pairs (round 3: the definitions below terminate). -/
theorem sizeOf_fst_lt {α β : Type} [SizeOf α] [SizeOf β] {p : α × β} {l : List (α × β)} (h : p ∈ l) :
    sizeOf p.1 < sizeOf l := by
  have := List.sizeOf_lt_of_mem h; cases p; simp at this ⊢; omega

theorem sizeOf_snd_lt {α β : Type} [SizeOf α] [SizeOf β] {p : α × β} {l : List (α × β)} (h : p ∈ l) :
    sizeOf p.2 < sizeOf l := by
  have := List.sizeOf_lt_of_mem h; cases p; simp at this ⊢; omega

theorem sizeOf_zip_fst {α β : Type} [SizeOf α] [SizeOf β] {a : List α} {b : List β} {p : α × β}
    (h : p ∈ a.zip b) : sizeOf p.1 < sizeOf a := List.sizeOf_lt_of_mem (List.of_mem_zip h).1

theorem sizeOf_zip_snd {α β : Type} [SizeOf α] [SizeOf β] {a : List α} {b : List β} {p : α × β}
    (h : p ∈ a.zip b) : sizeOf p.2 < sizeOf b := List.sizeOf_lt_of_mem (List.of_mem_zip h).2

/-- Structural equality of the drawn values (jank `=` on these: same type and value; a long
never equals a double, as in round 1's `jankEq`). -/
def cvEq : CV → CV → Bool
  | .nil, .nil => true
  | .bool a, .bool b => a == b
  | .long a, .long b => a == b
  | .dbl a, .dbl b => a.f == b.f
  | .str a, .str b => a == b
  | .char a, .char b => a == b
  | .kw a b, .kw c d => a == c && b == d
  | .sym a b, .sym c d => a == c && b == d
  | .vec xs, .vec ys => xs.length == ys.length && (xs.zip ys).attach.all fun xy => cvEq xy.1.1 xy.1.2
  | .other a _, .other b _ => a == b
  | _, _ => false
termination_by x => sizeOf x
decreasing_by
  all_goals simp_wf
  have := sizeOf_zip_fst xy.2
  omega

/-- The same object (`identical?`): the code string and constructor, for these atoms. -/
def sameText (a b : CV) : Bool := a.code == b.code

/-! ## The comparator, both sides -/

/-- detail/type.cpp 6 `object_ref_compare::operator()`: `runtime::compare(l, r) < 0`. -/
def objectRefCompare (l r : CV) : R Bool :=
  match jankCompare fuel l r with
  | .ok s => .ok (s < 0)
  | .throws w => .throws w
  | .ub w => .ub w

/-- PersistentTreeMap.doCompare with the default comparator (`RT.DEFAULT_COMPARATOR` →
`Util.compare`): the sign; a ClassCastException is a `throws`. -/
def cljDoCompare (l r : CV) : R Int :=
  match cljCompare fuel l r with
  | .ok s => .ok s
  | .throws w => .throws w
  | .ub w => .ub w

/-! ## The search tree (assumptions S1, S2) -/

/-- jank: descend for `k` over sorted keys `ks[lo, hi)`: `comp(k, node)` → left,
`comp(node, k)` → right, else found. Returns the index and whether it was found. -/
def jankLocate (ks : Array CV) (k : CV) : Nat → Nat → Nat → R (Nat × Bool)
  | 0, lo, _ => .ok (lo, false)
  | fuel + 1, lo, hi =>
    if lo ≥ hi then .ok (lo, false)
    else
      let mid := (lo + hi) / 2
      let node := ks[mid]!
      do
        if ← objectRefCompare k node then jankLocate ks k fuel lo mid
        else if ← objectRefCompare node k then jankLocate ks k fuel (mid + 1) hi
        else pure (mid, true)

/-- Clojure: the same descent with `doCompare(key, t.key)` (entryAt 313: `c == 0` found,
`c < 0` left, else right). -/
def cljLocate (ks : Array CV) (k : CV) : Nat → Nat → Nat → R (Nat × Bool)
  | 0, lo, _ => .ok (lo, false)
  | fuel + 1, lo, hi =>
    if lo ≥ hi then .ok (lo, false)
    else
      let mid := (lo + hi) / 2
      do
        let c ← cljDoCompare k ks[mid]!
        if c == 0 then pure (mid, true)
        else if c < 0 then cljLocate ks k fuel lo mid
        else cljLocate ks k fuel (mid + 1) hi

/-- A sorted map's entries (sorted by key, unique up to the comparator). -/
abbrev Entries := Array (CV × CV)

def jankFindIdx (m : Entries) (k : CV) : R (Option Nat) := do
  let (i, found) ← jankLocate (m.map (·.1)) k (m.size + 1) 0 m.size
  pure (if found then some i else none)

def cljFindIdx (m : Entries) (k : CV) : R (Option Nat) := do
  let (i, found) ← cljLocate (m.map (·.1)) k (m.size + 1) 0 m.size
  pure (if found then some i else none)

/-- `std::map::operator[](key) = val` (S1): an equivalent stored key keeps its key and gets the
value; otherwise the key is inserted at its place. -/
def jankAssign (m : Entries) (k v : CV) : R Entries := do
  let (i, found) ← jankLocate (m.map (·.1)) k (m.size + 1) 0 m.size
  pure (if found then m.set! i (m[i]!.1, v) else m.insertIdx! i (k, v))

/-- `std::map::erase(key)` (S1). -/
def jankErase (m : Entries) (k : CV) : R Entries := do
  match ← jankFindIdx m k with
  | some i => pure (m.eraseIdx! i)
  | none => pure m

/-! ## jank: persistent_sorted_map.cpp -/

/-- A persistent or transient sorted map: its entries and, for a transient, `active`. -/
structure SMap where
  data : Entries := #[]
  active : Bool := true
  deriving Inhabited

/-- persistent_sorted_map.cpp 39 `create_from_seq`: pairs into a transient `std::map` with
`transient[key] = val`; an odd count throws. -/
def smCreateFromSeq (kvs : List CV) : R SMap := do
  let rec go : List CV → Entries → R Entries
    | [], acc => pure acc
    | [_], _ => throwR "The sequence used to create a `persistent_sorted_map` must contain an even number of elements."
    | k :: v :: rest, acc => do go rest (← jankAssign acc k v)
  pure { data := ← go kvs #[] }

/-- persistent_sorted_map.cpp 60/70 `get(key[, fallback])`. -/
def smGet (m : SMap) (k : CV) (fallback : CV := .nil) : R CV := do
  match ← jankFindIdx m.data k with
  | some i => pure m.data[i]!.2
  | none => pure fallback

/-- persistent_sorted_map.cpp 80 `find(key)`: `make_box<persistent_vector>(std::in_place, key,
res->second)` — the *queried* key with the stored value. -/
def smFind (m : SMap) (k : CV) : R CV := do
  match ← jankFindIdx m.data k with
  | some i => pure (.vec [k, m.data[i]!.2])
  | none => pure .nil

/-- persistent_sorted_map.cpp 90 `contains(key)`: `data.contains(key)`. -/
def smContains (m : SMap) (k : CV) : R Bool := do
  pure (← jankFindIdx m.data k).isSome

/-- persistent_sorted_map.cpp 95 `assoc`: copy, `copy[key] = val`. -/
def smAssoc (m : SMap) (k v : CV) : R SMap := do pure { m with data := ← jankAssign m.data k v }

/-- persistent_sorted_map.cpp 103 `dissoc`: copy, `erase(key)`. -/
def smDissoc (m : SMap) (k : CV) : R SMap := do pure { m with data := ← jankErase m.data k }

/-- persistent_sorted_map.cpp 110/115 `call`: `get`. -/
def smCall (m : SMap) (k : CV) (fallback : CV := .nil) : R CV := smGet m k fallback

/-- persistent_sorted_map.cpp 120 `to_transient`: a copy of the data. -/
def smToTransient (m : SMap) : SMap := { data := m.data, active := true }

/-- base_persistent_map.cpp 163 `count`. -/
def smCount (m : SMap) : Nat := m.data.size

/-- base_persistent_map.cpp 138 `seq`: nil when empty, else the entries in key order as
`[k v]` vectors (persistent_sorted_map_sequence). -/
def smSeq (m : SMap) : Option (List CV) :=
  if m.data.isEmpty then none else some (m.data.toList.map fun (k, v) => .vec [k, v])

/-- base_persistent_map.cpp 31 `equal(o)` against another sorted map (`visit_map_like`): counts,
then for each own entry `typed_o->contains(k)` and `runtime::equal(v, typed_o->get(k))`. -/
def smEqual (m o : SMap) : R Bool := do
  if o.data.size != m.data.size then return false
  for (k, v) in m.data do
    let found ← smContains o k
    if !found then return false
    if !cvEq v (← smGet o k) then return false
  return true

/-- base_persistent_map.cpp 169 `conj(head)` for these heads: nil → same; a two-element vector →
`assoc`; another vector or a non-map → throws "invalid map entry". -/
def smConj (m : SMap) (head : CV) : R SMap :=
  match head with
  | .nil => pure m
  | .vec [k, v] => smAssoc m k v
  | _ => throwR "invalid map entry"

/-! ## jank: transient_sorted_map.cpp -/

/-- transient_sorted_map.cpp 147 `assert_active`. -/
def tmAssertActive (t : SMap) : R Unit :=
  if t.active then pure () else throwR "This `transient_sorted_map` has already been made persistent."

/-- transient_sorted_map.cpp 34 `count`. -/
def tmCount (t : SMap) : R Nat := do tmAssertActive t; pure t.data.size

/-- transient_sorted_map.cpp 40/51 `get`. -/
def tmGet (t : SMap) (k : CV) (fallback : CV := .nil) : R CV := do
  tmAssertActive t; smGet t k fallback

/-- transient_sorted_map.cpp 62 `find`: the queried key, as persistent `find`. -/
def tmFind (t : SMap) (k : CV) : R CV := do tmAssertActive t; smFind t k

/-- transient_sorted_map.cpp 73 `contains`. -/
def tmContains (t : SMap) (k : CV) : R Bool := do tmAssertActive t; smContains t k

/-- transient_sorted_map.cpp 80 `assoc_in_place`. -/
def tmAssocInPlace (t : SMap) (k v : CV) : R SMap := do
  tmAssertActive t; pure { t with data := ← jankAssign t.data k v }

/-- transient_sorted_map.cpp 87 `dissoc_in_place`. -/
def tmDissocInPlace (t : SMap) (k : CV) : R SMap := do
  tmAssertActive t; pure { t with data := ← jankErase t.data k }

/-- transient_sorted_map.cpp 94 `conj_in_place`: nil → same; a map merges (not drawn); a
two-element vector → `insert_or_assign` (S1: keeps the stored key); else throws. -/
def tmConjInPlace (t : SMap) (head : CV) : R SMap := do
  tmAssertActive t
  match head with
  | .nil => pure t
  | .vec [k, v] => pure { t with data := ← jankAssign t.data k v }
  | .vec _ => throwR "The `conj` operation on a transient sorted map requires a two-element vector entry"
  | _ => throwR "The `conj` operation on a transient sorted map requires a two-element `persistent_vector`"

/-- transient_sorted_map.cpp 130 `to_persistent`: inactive afterwards. -/
def tmToPersistent (t : SMap) : R (SMap × SMap) := do
  tmAssertActive t
  pure ({ data := t.data, active := true }, { t with active := false })

/-! ## jank: persistent_sorted_set.cpp and transient_sorted_set.cpp -/

/-- A sorted set's elements (sorted, unique up to the comparator). -/
structure SSet where
  data : Array CV := #[]
  active : Bool := true
  deriving Inhabited

def jankSetFind (s : SSet) (e : CV) : R (Option Nat) := do
  let (i, found) ← jankLocate s.data e (s.data.size + 1) 0 s.data.size
  pure (if found then some i else none)

/-- `std::set::insert(e)` (S1): nothing when an equivalent element is stored. -/
def jankSetInsert (s : Array CV) (e : CV) : R (Array CV) := do
  let (i, found) ← jankLocate s e (s.size + 1) 0 s.size
  pure (if found then s else s.insertIdx! i e)

/-- persistent_sorted_set.cpp 46 `create_from_seq`: `transient.insert(e)` for each. -/
def ssCreateFromSeq (xs : List CV) : R SSet := do
  let mut d : Array CV := #[]
  for x in xs do d ← jankSetInsert d x
  pure { data := d }

/-- persistent_sorted_set.cpp 126 `count`. -/
def ssCount (s : SSet) : Nat := s.data.size

/-- persistent_sorted_set.cpp 193 `contains`. -/
def ssContains (s : SSet) (e : CV) : R Bool := do pure (← jankSetFind s e).isSome

/-- persistent_sorted_set.cpp 158/173/183 `call`/`get`: the stored element (`*found`). -/
def ssGet (s : SSet) (e : CV) (fallback : CV := .nil) : R CV := do
  match ← jankSetFind s e with
  | some i => pure s.data[i]!
  | none => pure fallback

/-- persistent_sorted_set.cpp 150 `conj`. -/
def ssConj (s : SSet) (e : CV) : R SSet := do pure { s with data := ← jankSetInsert s.data e }

/-- persistent_sorted_set.cpp 198 `disj`. -/
def ssDisj (s : SSet) (e : CV) : R SSet := do
  match ← jankSetFind s e with
  | some i => pure { s with data := s.data.eraseIdx! i }
  | none => pure s

/-- persistent_sorted_set.cpp 56 `equal(o)` against another sorted set (`visit_set_like`): counts,
then for each own element `typed_o->contains(entry)`. -/
def ssEqual (s o : SSet) : R Bool := do
  if o.data.size != s.data.size then return false
  for e in s.data do
    if !(← ssContains o e) then return false
  return true

/-- persistent_sorted_set.cpp 109 `seq`: nil when empty. -/
def ssSeq (s : SSet) : Option (List CV) := if s.data.isEmpty then none else some s.data.toList

/-- transient_sorted_set.cpp 96 `assert_active`. -/
def tsAssertActive (t : SSet) : R Unit :=
  if t.active then pure () else throwR "This `transient_sorted_set` has already been made persistent."

/-- transient_sorted_set.cpp 37 `conj_in_place`. -/
def tsConjInPlace (t : SSet) (e : CV) : R SSet := do
  tsAssertActive t; pure { t with data := ← jankSetInsert t.data e }

/-- transient_sorted_set.cpp 89 `disjoin_in_place`. -/
def tsDisjoinInPlace (t : SSet) (e : CV) : R SSet := do tsAssertActive t; ssDisj t e

/-- transient_sorted_set.cpp 51/62/73 `call`/`get`. -/
def tsGet (t : SSet) (e : CV) : R CV := do tsAssertActive t; ssGet t e

/-- transient_sorted_set.cpp 83 `contains`. -/
def tsContains (t : SSet) (e : CV) : R Bool := do tsAssertActive t; ssContains t e

/-- transient_sorted_set.cpp 31 `count`. -/
def tsCount (t : SSet) : R Nat := do tsAssertActive t; pure t.data.size

/-- transient_sorted_set.cpp 44 `to_persistent`. -/
def tsToPersistent (t : SSet) : R (SSet × SSet) := do
  tsAssertActive t; pure ({ data := t.data }, { t with active := false })

/-! ## Clojure: PersistentTreeMap / PersistentTreeSet -/

/-- PersistentTreeMap.assoc / replace (466): an existing key keeps `t.key` and takes the value. -/
def cljAssign (m : Entries) (k v : CV) : R Entries := do
  let (i, found) ← cljLocate (m.map (·.1)) k (m.size + 1) 0 m.size
  pure (if found then m.set! i (m[i]!.1, v) else m.insertIdx! i (k, v))

/-- PersistentTreeMap.create (74): `assoc` pairs; an odd count throws "No value supplied". -/
def cljTmCreate (kvs : List CV) : R Entries :=
  let rec go : List CV → Entries → R Entries
    | [], acc => pure acc
    | [k], _ => throwR s!"No value supplied for key: {k.code}"
    | k :: v :: rest, acc => do go rest (← cljAssign acc k v)
  go kvs #[]

/-- PersistentTreeMap.valAt (296). -/
def cljTmGet (m : Entries) (k : CV) (nf : CV := .nil) : R CV := do
  match ← cljFindIdx m k with
  | some i => pure m[i]!.2
  | none => pure nf

/-- RT.find → `entryAt` (313): the stored node, as `[stored-key val]`. -/
def cljTmFind (m : Entries) (k : CV) : R CV := do
  match ← cljFindIdx m k with
  | some i => pure (.vec [m[i]!.1, m[i]!.2])
  | none => pure .nil

def cljTmContains (m : Entries) (k : CV) : R Bool := do pure (← cljFindIdx m k).isSome

/-- PersistentTreeMap.without (140). -/
def cljTmWithout (m : Entries) (k : CV) : R Entries := do
  match ← cljFindIdx m k with
  | some i => pure (m.eraseIdx! i)
  | none => pure m

/-- `catch (ClassCastException e) { return false; }` (PersistentTreeMap.equiv 108,
PersistentTreeSet.equiv): only a Java exception is caught. -/
def catchCCE (x : R Bool) : R Bool :=
  match x with
  | .throws _ => .ok false
  | other => other

/-- PersistentTreeMap.equiv (108) → APersistentMap.equiv: counts, then for each own entry
`m.containsKey(k)` and `Util.equiv(v, m.get(k))`; a ClassCastException answers false. -/
def cljTmEquiv (m o : Entries) : R Bool := catchCCE do
  if o.size != m.size then return false
  for (k, v) in m do
    if !(← cljTmContains o k) then return false
    if !cvEq v (← cljTmGet o k) then return false
  return true

/-- PersistentTreeSet.cons: `if(contains(o)) return this;` else `impl.assoc(o, o)`. -/
def cljTsCons (s : Array CV) (e : CV) : R (Array CV) := do
  let (i, found) ← cljLocate s e (s.size + 1) 0 s.size
  pure (if found then s else s.insertIdx! i e)

def cljTsCreate (xs : List CV) : R (Array CV) := do
  let mut d : Array CV := #[]
  for x in xs do d ← cljTsCons d x
  pure d

def cljTsContains (s : Array CV) (e : CV) : R Bool := do
  let (_, found) ← cljLocate s e (s.size + 1) 0 s.size
  pure found

/-- APersistentSet.get → `impl.valAt(key)`: the stored element. -/
def cljTsGet (s : Array CV) (e : CV) : R CV := do
  let (i, found) ← cljLocate s e (s.size + 1) 0 s.size
  pure (if found then s[i]! else .nil)

/-- PersistentTreeSet.equiv → APersistentSet.equiv (78): counts, then for each element of the
*other* set `this.contains(it)`; a ClassCastException answers false. -/
def cljTsEquiv (s o : Array CV) : R Bool := catchCCE do
  if o.size != s.size then return false
  for e in o do
    if !(← cljTsContains s e) then return false
  return true

def cljTsDisj (s : Array CV) (e : CV) : R (Array CV) := do
  let (i, found) ← cljLocate s e (s.size + 1) 0 s.size
  pure (if found then s.eraseIdx! i else s)

/-! ## Observing results -/

/-- What a program prints of a result. -/
inductive Obs where
  | v (x : CV)
  | bool (x : Bool)
  | nat (x : Nat)
  | coll (xs : List CV)
  | throws
  | ub (why : String)
  deriving Inhabited

def Obs.code : Obs → String
  | .v x => x.code
  | .bool x => toString x
  | .nat x => toString x
  | .coll xs => "(" ++ " ".intercalate (xs.map CV.code) ++ ")"
  | .throws => "throws"
  | .ub w => s!"undefined behavior ({w})"

def Obs.same : Obs → Obs → Bool
  | .v a, .v b => cvEq a b
  | .bool x, .bool y => x == y
  | .nat x, .nat y => x == y
  | .coll a, .coll b => a.length == b.length && (a.zip b).all fun (x, y) => cvEq x y
  | .throws, .throws => true
  | _, _ => false

def obsOf {α : Type} (f : α → Obs) : R α → Obs
  | .ok x => f x
  | .throws _ => .throws
  | .ub w => .ub w

/-! ## The world: a sorted map or set built from drawn keys, then one operation -/

/-- Keys drawn: numbers (1 and 1.0 equivalent under `compare`), strings, keywords, a vector. -/
def d1 : CV := .dbl { f := 1.0, num := 1, den := 1, code := "1.0" }
def keyAtoms : List CV :=
  [.long 0, .long 1, d1, .long 2, .str "a", .str "b", .kw "" "a", .kw "" "b", .vec [.long 1]]

def valAtoms : List CV := [.kw "" "x", .kw "" "y"]

structure World where
  decisions : Decisions := {}

instance : Chaotic World where
  decisions w := w.decisions
  setDecisions w d := { w with decisions := d }

def drawKey (name : String) : EStateM Stop World CV := do
  pure (keyAtoms.getD (← decide (σ := World) name keyAtoms.length) .nil)

def drawVal (name : String) : EStateM Stop World CV := do
  pure (valAtoms.getD (← decide (σ := World) name valAtoms.length) .nil)

/-- The operations on a sorted map. -/
inductive MapOp where
  | get | find | contains | dissoc | assoc | count | seq | conj | equal
  | tAssoc | tFind | tGetAfterPersistent | selectKeys
  deriving Repr, BEq, Inhabited

def mapOps : List MapOp :=
  [.get, .find, .contains, .dissoc, .assoc, .count, .seq, .conj, .equal, .tAssoc, .tFind,
   .tGetAfterPersistent, .selectKeys]

def entriesObs (e : Entries) : Obs := .coll (e.toList.map fun (k, v) => .vec [k, v])

/-- core.jank `select-keys` (2400): `(reduce (fn [acc k] (let [e (find m k)] (if e (conj acc e)
acc))) {} ks)` — the entries come from `find`. Both sides build the result the same way; only
`find` differs. -/
def jankSelectKeys (m : SMap) (ks : List CV) : R (List (CV × CV)) := do
  let mut acc : List (CV × CV) := []
  for k in ks do
    match ← smFind m k with
    | .vec [a, b] => acc := acc ++ [(a, b)]
    | _ => pure ()
  pure acc

def cljSelectKeys (m : Entries) (ks : List CV) : R (List (CV × CV)) := do
  let mut acc : List (CV × CV) := []
  for k in ks do
    match ← cljTmFind m k with
    | .vec [a, b] => acc := acc ++ [(a, b)]
    | _ => pure ()
  pure acc

/-- Run one map program on both sides: `(sorted-map k0 v0 … )` then the operation. -/
def runMapOp (kvs : List CV) (op : MapOp) (k v : CV) (other : List CV) : Obs × Obs × String :=
  let prog := s!"(sorted-map {" ".intercalate (kvs.map CV.code)})"
  let j : Obs := match smCreateFromSeq kvs with
    | .throws _ => .throws
    | .ub w => .ub w
    | .ok m => match op with
      | .get => obsOf .v (smGet m k)
      | .find => obsOf .v (smFind m k)
      | .contains => obsOf .bool (smContains m k)
      | .dissoc => obsOf (fun (m : SMap) => entriesObs m.data) (smDissoc m k)
      | .assoc => obsOf (fun (m : SMap) => entriesObs m.data) (smAssoc m k v)
      | .count => .nat (smCount m)
      | .seq => .coll ((smSeq m).getD [])
      | .conj => obsOf (fun (m : SMap) => entriesObs m.data) (smConj m (.vec [k, v]))
      | .equal => match smCreateFromSeq other with
        | .ok o => obsOf .bool (smEqual m o)
        | .throws _ => .throws
        | .ub w => .ub w
      | .tAssoc => obsOf (fun (p : SMap × SMap) => entriesObs p.1.data)
          (do let t ← tmAssocInPlace (smToTransient m) k v; tmToPersistent t)
      | .tFind => obsOf .v (tmFind (smToTransient m) k)
      | .tGetAfterPersistent => obsOf .v (do
          let (_, t') ← tmToPersistent (smToTransient m)
          tmGet t' k)
      | .selectKeys => obsOf (fun es => .coll (es.map fun (a, b) => .vec [a, b])) (jankSelectKeys m [k])
  let c : Obs := match cljTmCreate kvs with
    | .throws _ => .throws
    | .ub w => .ub w
    | .ok m => match op with
      | .get => obsOf .v (cljTmGet m k)
      | .find => obsOf .v (cljTmFind m k)
      | .contains => obsOf .bool (cljTmContains m k)
      | .dissoc => obsOf entriesObs (cljTmWithout m k)
      | .assoc => obsOf entriesObs (cljAssign m k v)
      | .count => .nat m.size
      | .seq => .coll (m.toList.map fun (a, b) => .vec [a, b])
      | .conj => obsOf entriesObs (cljAssign m k v)
      | .equal => match cljTmCreate other with
        | .ok o => obsOf .bool (cljTmEquiv m o)
        | .throws _ => .throws
        | .ub w => .ub w
      -- Clojure 1.12: PersistentTreeMap is not an IEditableCollection: `transient` throws.
      | .tAssoc | .tFind => .throws
      -- `(get t k)` after `persistent!` (an ATransientMap ensures editable) — not reachable in
      -- Clojure (no sorted transients): counted as agreeing when jank throws.
      | .tGetAfterPersistent => .throws
      | .selectKeys => obsOf (fun es => .coll (es.map fun (a, b) => .vec [a, b])) (cljSelectKeys m [k])
  let code := match op with
    | .get => s!"(get {prog} {k.code})"
    | .find => s!"(find {prog} {k.code})"
    | .contains => s!"(contains? {prog} {k.code})"
    | .dissoc => s!"(dissoc {prog} {k.code})"
    | .assoc => s!"(assoc {prog} {k.code} {v.code})"
    | .count => s!"(count {prog})"
    | .seq => s!"(seq {prog})"
    | .conj => s!"(conj {prog} [{k.code} {v.code}])"
    | .equal => s!"(= {prog} (sorted-map {" ".intercalate (other.map CV.code)}))"
    | .tAssoc => s!"(persistent! (assoc! (transient {prog}) {k.code} {v.code}))"
    | .tFind => s!"(find (transient {prog}) {k.code})"
    | .tGetAfterPersistent => s!"(let [t (transient {prog})] (persistent! t) (get t {k.code}))"
    | .selectKeys => s!"(select-keys {prog} [{k.code}])"
  (j, c, code)

/-- jank's transients of sorted maps exist where Clojure has none (`transient` throws there): an
extension, not a deviation. -/
def MapOp.extension : MapOp → Bool
  | .tAssoc | .tFind | .tGetAfterPersistent => true
  | _ => false

/-- Fork C's C2 (a keyword compared with a non-keyword is undefined behavior where Clojure
throws) is already reported: such outcomes are not counted again here. -/
def isKnownC2 (j c : Obs) : Bool :=
  match j, c with
  | .ub _, .throws => true
  | _, _ => false

/-- A map built from keys that are not mutually comparable fails at construction on both sides
(fork C's C1/C2): only programs whose maps build on both sides are judged. -/
def knownOrConstruction (j c : Obs) (kvs : List CV) (other : List CV) (op : MapOp) : Bool :=
  isKnownC2 j c ||
  (match smCreateFromSeq kvs, cljTmCreate kvs with
    | .ok _, .ok _ => false
    | _, _ => true) ||
  (op == .equal && match smCreateFromSeq other, cljTmCreate other with
    | .ok _, .ok _ => false
    | _, _ => true)

/-- One drawn program: 0–2 entries, an operation, its key/value (and a second map for `=`). -/
def mapBody (skip : List MapOp := []) : EStateM Stop World Unit := do
  let n ← decide (σ := World) "smap.size" 3
  let mut kvs : List CV := []
  for i in List.range n do
    kvs := kvs ++ [← drawKey s!"smap.key{i}", ← drawVal s!"smap.val{i}"]
  let op := mapOps.getD (← decide (σ := World) "smap.op" mapOps.length) .get
  let k ← drawKey "smap.arg.key"
  let v ← drawVal "smap.arg.val"
  let other ← if op == .equal then do
      let m ← decide (σ := World) "smap.other.size" 3
      let mut o : List CV := []
      for i in List.range m do
        o := o ++ [← drawKey s!"smap.other.key{i}", ← drawVal s!"smap.other.val{i}"]
      pure o
    else pure []
  let (j, c, code) := runMapOp kvs op k v other
  -- Sorted transients are jank's own (Clojure has none): run, not judged (their only failures
  -- are fork C's C1/C2 through compare).
  if op.extension || skip.contains op then pure ()
  else if knownOrConstruction j c kvs other op then pure ()
  else if !j.same c then
    violate (σ := World) "sorted map as Clojure's" s!"{code}: Clojure {c.code}, jank {j.code}"

/-- The operations on a sorted set. -/
inductive SetOp where
  | get | contains | conj | disj | count | seq | equal | tConj
  deriving Repr, BEq, Inhabited

def setOps : List SetOp := [.get, .contains, .conj, .disj, .count, .seq, .equal, .tConj]

def runSetOp (xs : List CV) (op : SetOp) (e : CV) (other : List CV) : Obs × Obs × String :=
  let prog := s!"(sorted-set {" ".intercalate (xs.map CV.code)})"
  let j : Obs := match ssCreateFromSeq xs with
    | .throws _ => .throws
    | .ub w => .ub w
    | .ok s => match op with
      | .get => obsOf .v (ssGet s e)
      | .contains => obsOf .bool (ssContains s e)
      | .conj => obsOf (fun (s : SSet) => .coll s.data.toList) (ssConj s e)
      | .disj => obsOf (fun (s : SSet) => .coll s.data.toList) (ssDisj s e)
      | .count => .nat (ssCount s)
      | .seq => .coll ((ssSeq s).getD [])
      | .equal => match ssCreateFromSeq other with
        | .ok o => obsOf .bool (ssEqual s o)
        | .throws _ => .throws
        | .ub w => .ub w
      | .tConj => obsOf (fun (p : SSet × SSet) => .coll p.1.data.toList)
          (do let t ← tsConjInPlace { data := s.data } e; tsToPersistent t)
  let c : Obs := match cljTsCreate xs with
    | .throws _ => .throws
    | .ub w => .ub w
    | .ok s => match op with
      | .get => obsOf .v (cljTsGet s e)
      | .contains => obsOf .bool (cljTsContains s e)
      | .conj => obsOf .coll (Array.toList <$> cljTsCons s e)
      | .disj => obsOf .coll (Array.toList <$> cljTsDisj s e)
      | .count => .nat s.size
      | .seq => .coll s.toList
      | .equal => match cljTsCreate other with
        | .ok o => obsOf .bool (cljTsEquiv s o)
        | .throws _ => .throws
        | .ub w => .ub w
      | .tConj => .throws
  let code := match op with
    | .get => s!"(get {prog} {e.code})"
    | .contains => s!"(contains? {prog} {e.code})"
    | .conj => s!"(conj {prog} {e.code})"
    | .disj => s!"(disj {prog} {e.code})"
    | .count => s!"(count {prog})"
    | .seq => s!"(seq {prog})"
    | .equal => s!"(= {prog} (sorted-set {" ".intercalate (other.map CV.code)}))"
    | .tConj => s!"(persistent! (conj! (transient {prog}) {e.code}))"
  (j, c, code)

def knownSet (j c : Obs) (xs : List CV) (other : List CV) (op : SetOp) : Bool :=
  isKnownC2 j c ||
  (match ssCreateFromSeq xs, cljTsCreate xs with
    | .ok _, .ok _ => false
    | _, _ => true) ||
  (op == .equal && match ssCreateFromSeq other, cljTsCreate other with
    | .ok _, .ok _ => false
    | _, _ => true)

def setBody (skip : List SetOp := []) : EStateM Stop World Unit := do
  let n ← decide (σ := World) "sset.size" 3
  let mut xs : List CV := []
  for i in List.range n do xs := xs ++ [← drawKey s!"sset.elem{i}"]
  let op := setOps.getD (← decide (σ := World) "sset.op" setOps.length) .get
  let e ← drawKey "sset.arg"
  let other ← if op == .equal then do
      let m ← decide (σ := World) "sset.other.size" 3
      let mut o : List CV := []
      for i in List.range m do o := o ++ [← drawKey s!"sset.other.elem{i}"]
      pure o
    else pure []
  let (j, c, code) := runSetOp xs op e other
  if op == .tConj || skip.contains op then pure ()
  else if knownSet j c xs other op then pure ()
  else if !j.same c then
    violate (σ := World) "sorted set as Clojure's" s!"{code}: Clojure {c.code}, jank {j.code}"

def runBody (body : EStateM Stop World Unit) (source : Source) : Ended :=
  match body.run { decisions := { source } } with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }
  | .error (.nodeDown _) w => { taken := w.decisions.taken, violation := none }

/-- The full table of map programs with every key drawn from one comparable group (numbers):
which operations disagree, so the findings are not only about mixed types. -/
def numberKeys : List CV := [.long 0, .long 1, d1, .long 2]

def mapTable (keys : List CV) : List (String × Obs × Obs) := Id.run do
  let mut out := []
  let maps : List (List CV) := [[]] ++ (keys.map fun k => [k, .kw "" "x"]) ++
    (keys.flatMap fun a => keys.map fun b => [a, .kw "" "x", b, .kw "" "y"])
  for kvs in maps do
    for op in mapOps do
      if op.extension || op == .equal then continue
      for k in keys do
        let (j, c, code) := runMapOp kvs op k (.kw "" "z") []
        if !j.same c then out := out ++ [(code, c, j)]
  return out

/-! ## `=` between two sorted collections whose keys are not mutually comparable -/

/-- `(= (sorted-set a) (sorted-set b))` for every pair of atoms: jank vs Clojure. -/
def setEqualTable : List (String × Obs × Obs) := Id.run do
  let mut out := []
  for a in keyAtoms do
    for b in keyAtoms do
      let (j, c, code) := runSetOp [a] .equal .nil [b]
      if !j.same c then out := out ++ [(code, c, j)]
  return out

def mapEqualTable : List (String × Obs × Obs) := Id.run do
  let mut out := []
  for a in keyAtoms do
    for b in keyAtoms do
      let (j, c, code) := runMapOp [a, .kw "" "x"] .equal .nil .nil [b, .kw "" "x"]
      if !j.same c then out := out ++ [(code, c, j)]
  return out

/-! ## `sort` of an empty collection (core/seq.cpp 1098) -/

/-- obj/native_vector_sequence: its vector and index. -/
structure NVSeq where
  data : List CV
  index : Nat
  deriving Inhabited

/-- core/seq.cpp 1098 `sort(coll)` (and 1131 with a comparator) on 7135b7708: `visit_seqable`
(nil included) copies every element into a vector; an empty vector returns
`persistent_list::empty()` (1108–1111, 1155–1158); else `std::stable_sort` and
`make_box<native_vector_sequence>(meta, vec)` (1121). On f3d82d654 only nil returned the empty
list and an empty input built an empty `native_vector_sequence` through the meta constructor
(native_vector_sequence.cpp 35, no emptiness check): C16, fixed. (The sort itself is fork C's;
elements are drawn sorted.) -/
inductive SortResult where
  | emptyList
  | nvs (s : NVSeq)
  deriving Inhabited

def jankSort (coll : Option (List CV)) : SortResult :=
  match coll.getD [] with
  | [] => .emptyList
  | xs => .nvs { data := xs, index := 0 }

/-- The f3d82d654 code (seq.cpp 1091 then): only nil gave the empty list. -/
def jankSortOld (coll : Option (List CV)) : SortResult :=
  match coll with
  | none => .emptyList
  | some xs => .nvs { data := xs, index := 0 }

/-- native_vector_sequence.cpp 89 `seq`: `data.empty() ? nil : this`. -/
def nvsSeq (s : NVSeq) : Option NVSeq := if s.data.isEmpty then none else some s

/-- native_vector_sequence.cpp 107 `first`: `jank_debug_assert(index < data.size()); return
data[index];` — past the end it reads outside the vector (fbvector: an empty one has no storage,
so `data[0]` reads through a null pointer). -/
def nvsFirst (s : NVSeq) : R CV :=
  if s.index < s.data.length then .ok (s.data.getD s.index .nil)
  else .ub s!"native_vector_sequence::first reads data[{s.index}] of a vector of {s.data.length}"

/-- native_vector_sequence.cpp 113 `next`: `++n; if(n == data.size()) return nil;` — from an
empty vector, n = 1 ≠ 0: a new sequence at index 1. -/
def nvsNext (s : NVSeq) : Option NVSeq :=
  if s.index + 1 == s.data.length then none else some { s with index := s.index + 1 }

/-- native_vector_sequence.cpp 101 `count`: `data.size() - index` in `usize` (wraps below 0). -/
def nvsCount (s : NVSeq) : UInt64 := s.data.length.toUInt64 - s.index.toUInt64

/-- core/seq.cpp 299 `first(o)`: a `sequence_like` object answers its own `first()`. -/
def jankFirstOfSort (r : SortResult) : R CV :=
  match r with
  | .emptyList => .ok .nil
  | .nvs s => nvsFirst s

/-- core/seq.cpp 313 `next(o)`. -/
def jankNextOfSort (r : SortResult) : Option NVSeq :=
  match r with
  | .emptyList => none
  | .nvs s => nvsNext s

/-- core.jank `last` (413): `(if (next s) (recur (next s)) (first s))`, with `fuel` turns. From an
empty sort result `next` never answers nil (the index passes the size and `n == data.size()`
never holds again): `none` when the fuel runs out. -/
def jankLastOfSort (r : SortResult) (fuel : Nat) : Option (R CV) :=
  match r with
  | .emptyList => some (.ok .nil)
  | .nvs s0 =>
    let rec go : Nat → NVSeq → Option (R CV)
      | 0, _ => none
      | f + 1, s => match nvsNext s with
        | some s' => go f s'
        | none => some (nvsFirst s)
    go fuel s0

/-- Clojure core.clj `sort`: `(if (seq coll) (… (seq a) …) ())`: an empty coll gives `()`. -/
def cljSort (coll : Option (List CV)) : List CV := coll.getD []

/-! ## `reset-meta!` on the shared empty sorted map (core/meta.cpp 84) -/

/-- A tiny heap: the static `persistent_sorted_map::empty()` (persistent_sorted_map.cpp 33,
`static persistent_sorted_map const ret; return &ret;`) and its metadata. -/
structure MetaHeap where
  emptyMeta : Option String := none
  deriving Inhabited

/-- `(sorted-map)` (core.jank 444): the static empty map, object 0. -/
def sortedMapEmpty (h : MetaHeap) : Option String := h.emptyMeta

/-- core/meta.cpp 84 `reset_meta`: any metadatable object; a map has no public `meta` member, so
`set_meta` (base_persistent_map.cpp 213) mutates it in place — here the shared static (declared
`const`: writing it is undefined behavior). -/
def jankResetMetaOfEmpty (_h : MetaHeap) (m : String) : MetaHeap × String :=
  ({ emptyMeta := some m }, "undefined behavior: writes the `const` static empty map")

/-- The program `(reset-meta! (sorted-map) {:x 1}) [(meta (sorted-map)) (meta (into (sorted-map)
{1 2}))]`: jank's into keeps `(meta to)` (core.jank `into`). Clojure: `reset-meta!` needs an
`IReference` (core.clj `reset-meta!` → `(.resetMeta ^clojure.lang.IReference iref …)`), so it
throws ClassCastException. -/
def resetMetaProgram : String × String :=
  let h : MetaHeap := {}
  let (h, _) := jankResetMetaOfEmpty h "{:x 1}"
  let a := (sortedMapEmpty h).getD "nil"
  let b := (sortedMapEmpty h).getD "nil"
  (s!"[{a} {b}] (after undefined behavior)", "ClassCastException at reset-meta!")

/-! ## Unported sorted-collection functions in core.jank -/

/-- Each throws `ex-info` ("TODO: port …"/"not yet implemented") in core.jank; Clojure 1.12
implements them. Not listed in book/src/differences-from-clojure.md. -/
def unported : List (String × String × String) :=
  [("sorted-set-by", "core.jank 2438", "(sorted-set-by > 1 2) ; Clojure #{2 1}"),
   ("sorted-map-by", "core.jank 5032", "(sorted-map-by > 1 :a 2 :b) ; Clojure {2 :b, 1 :a}"),
   ("rseq", "core.jank 5081", "(rseq [1 2]) ; Clojure (2 1); (rseq (sorted-set 1 2)) ; (2 1)"),
   ("subseq", "core.jank 6510 (mk-bound-fn 6505)", "(subseq (sorted-set 1 2 3) > 1) ; Clojure (2 3)"),
   ("rsubseq", "core.jank 6527", "(rsubseq (sorted-set 1 2 3) < 3) ; Clojure (2 1)")]

/-! ## Theorems -/

/-- jank's `find` (persistent_sorted_map.cpp 80) answers the *queried* key whenever a key is
found, whatever key is stored. -/
theorem find_returns_query_key (m : SMap) (k : CV) (i : Nat)
    (h : jankFindIdx m.data k = .ok (some i)) :
    smFind m k = .ok (.vec [k, m.data[i]!.2]) := by
  unfold smFind; rw [h]; rfl

/-- Clojure's (`RT.find` → `entryAt`) answers the *stored* key. -/
theorem clj_find_returns_stored_key (m : Entries) (k : CV) (i : Nat)
    (h : cljFindIdx m k = .ok (some i)) :
    cljTmFind m k = .ok (.vec [m[i]!.1, m[i]!.2]) := by
  unfold cljTmFind; rw [h]; rfl

/-- On f3d82d654, `next` of an empty sort result was a non-nil sequence whose `count` wraps to
2^64 − 1 (C16). -/
theorem next_of_empty_sort_old :
    (match jankNextOfSort (jankSortOld (some [])) with
      | some s => nvsCount s
      | none => 0) = 0xFFFFFFFFFFFFFFFF := by
  rfl

/-- On 7135b7708, sorting an empty collection gives the empty list: `first` and `next` are nil. -/
theorem sort_empty_is_empty_list :
    (match jankSort (some []) with | .emptyList => true | .nvs _ => false) = true ∧
    (jankNextOfSort (jankSort (some []))).isNone = true := by
  constructor <;> rfl

end Jank.Core.Sorted
