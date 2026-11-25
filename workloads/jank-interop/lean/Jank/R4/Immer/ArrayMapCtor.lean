import Determinismo

/-!
# `array-map` (round 4): `persistent_array_map::create_from_seq`

jank (7135b7708): core.jank 6249–6255 `(array-map & keyvals)` →
obj/persistent_array_map.cpp `create_from_seq` 36–55: a local `transient_array_map`, then
`transient.assoc_in_place(key, val)` for each pair, **its result discarded**, then
`to_persistent()`. obj/transient_array_map.cpp `assoc_in_place` 67–89: when the array already
holds `max_size` = 8 entries (detail/native_array_map.hpp 30; `size()` is `length / 2`, .cpp 304)
it builds and returns a *new* `transient_hash_map` holding the entries and the pair (promotion),
leaving `this` unchanged; else `data.insert_or_assign` (native_array_map.cpp: replace the value
of an `=` key in place, else append). So from the ninth distinct key on, every pair is dropped,
updates of existing keys included.

Clojure 1.12 (core.clj `array-map`, PersistentArrayMap.java `createAsIfByAssoc`): every pair is
assoc'ed in order; an equal key keeps its first position and takes the last value; the result is
an array map of any size.

Keys and values are naturals compared by `==` (keywords or longs: jank's `=` is an equivalence
on them).
-/

namespace Jank.R4.Immer.ArrayMap

open Determinismo

/-- `native_array_map::insert_or_assign`: an equal key's value replaced in place, else appended. -/
def insertOrAssign : List (Nat × Nat) → Nat → Nat → List (Nat × Nat)
  | [], k, v => [(k, v)]
  | (k', v') :: t, k, v => if k' == k then (k', v) :: t else (k', v') :: insertOrAssign t k v

/-- `transient_array_map::assoc_in_place` as `create_from_seq` sees it: at 8 entries the promoted
map is returned and dropped, `this` unchanged. -/
def assocInPlaceKept (m : List (Nat × Nat)) (k v : Nat) : List (Nat × Nat) :=
  if m.length == 8 then m else insertOrAssign m k v

/-- jank's `(array-map k1 v1 k2 v2 ...)`. -/
def jankArrayMap (kvs : List (Nat × Nat)) : List (Nat × Nat) :=
  kvs.foldl (fun m (k, v) => assocInPlaceKept m k v) []

/-- Clojure's `createAsIfByAssoc`. -/
def cljArrayMap (kvs : List (Nat × Nat)) : List (Nat × Nat) :=
  kvs.foldl (fun m (k, v) => insertOrAssign m k v) []

theorem insertOrAssign_length_le (m : List (Nat × Nat)) (k v : Nat) :
    (insertOrAssign m k v).length ≤ m.length + 1 := by
  induction m with
  | nil => simp [insertOrAssign]
  | cons p t ih =>
    obtain ⟨k', v'⟩ := p
    simp only [insertOrAssign]
    split <;> simp <;> omega

/-- **jank's `array-map` never holds more than 8 entries**, for every list of pairs (Clojure's
holds one per distinct key). -/
theorem jank_array_map_at_most_8 (kvs : List (Nat × Nat)) : (jankArrayMap kvs).length ≤ 8 := by
  unfold jankArrayMap
  suffices h : ∀ (m : List (Nat × Nat)), m.length ≤ 8 →
      (kvs.foldl (fun m (k, v) => assocInPlaceKept m k v) m).length ≤ 8 from h [] (by simp)
  induction kvs with
  | nil => intro m hm; simpa using hm
  | cons p t ih =>
    intro m hm
    obtain ⟨k, v⟩ := p
    simp only [List.foldl_cons]
    apply ih
    unfold assocInPlaceKept
    split
    · exact hm
    · rename_i h8
      have := insertOrAssign_length_le m k v
      simp at h8; omega

/-- Nine distinct keys: Clojure keeps nine, jank eight (kernel evaluation). -/
theorem nine_keys :
    (cljArrayMap ((List.range 9).map fun i => (i, i))).length = 9 ∧
    (jankArrayMap ((List.range 9).map fun i => (i, i))).length = 8 := by decide

/-- An update of an existing key after eight entries is dropped: `(get (array-map 0 0 ... 7 7 0 9) 0)`
is 9 in Clojure, 0 in jank. -/
theorem update_dropped :
    (cljArrayMap (((List.range 8).map fun i => (i, i)) ++ [(0, 9)])).lookup 0 = some 9 ∧
    (jankArrayMap (((List.range 8).map fun i => (i, i)) ++ [(0, 9)])).lookup 0 = some 0 := by decide

/-! ## The world: a prefix of distinct keys, then pairs drawn from a small alphabet -/

structure W where
  decisions : Decisions := {}

instance : Chaotic W where
  decisions := W.decisions
  setDecisions w d := { w with decisions := d }

/-- A timeline: `pre` distinct filler keys (100, 101, ...), then up to `n` pairs with keys from
{0, 1, 2, 100} and values {0, 1}; compares the entries (key order and values) of both maps. -/
def body (pres : List Nat) (n : Nat) : EStateM Stop W Unit := do
  let pre := pres.getD (← decide "prefix" pres.length) 0
  let len ← decide "pairs" (n + 1)
  let mut kvs : List (Nat × Nat) := (List.range pre).map fun i => (100 + i, 0)
  for _ in [0:len] do
    let k := [0, 1, 2, 100].getD (← decide "key" 4) 0
    let v ← decide "value" 2
    kvs := kvs ++ [(k, v)]
  let j := jankArrayMap kvs
  let c := cljArrayMap kvs
  if j != c then
    let cls := if c.length > 8 then "past-8-entries" else if c.length == 8 then "update-after-8" else "other"
    violate cls s!"(array-map {kvs.map fun (k, v) => s!"{k} {v}"}): jank {j}, Clojure {c}"

def run (pres : List Nat) (n : Nat) (source : Source) : Ended :=
  match (body pres n).run { decisions := { source } } with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }
  | .error (.nodeDown _) w => { taken := w.decisions.taken, violation := none }

end Jank.R4.Immer.ArrayMap
