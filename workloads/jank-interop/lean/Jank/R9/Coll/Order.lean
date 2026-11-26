import Jank.R8.Champ.Programs

/-!
# Round 9, area Coll: which order a jank map shows after it becomes a hash map (M9-5, M9-6, U81)

jank's hash maps are immer CHAMPs (round 3's `Jank.R3.Immer.Champ`, iterated by `Champ.toList`,
the replica of `champ_iterator`); a long hashes as hash.cpp `integer(i64)` (`Jank.Hash.integer`,
equal to Clojure's Murmur3 `hashLong`, round 1's `integer_eq_hashLong`). Clojure's array maps keep
insertion order (PersistentArrayMap: an array of pairs, `assoc` of a present key replaces the value
in place, a new key goes at the end).

The programs below all end in a jank hash map where Clojure keeps an array map:
- `persistent_array_map::assoc` (persistent_array_map.cpp 70-89) promotes to a hash map when the map
  holds 8 entries, before looking for the key: `(assoc m k v)` of a present key of an 8-entry
  array map (Clojure: PersistentArrayMap.assoc 186-203 replaces in place);
- `transient_array_map::assoc_in_place` (transient_array_map.cpp 67-89), the same in a transient:
  `frequencies`, `group-by`, `into {}` (Clojure: TransientArrayMap.doAssoc 341-358);
- `destructure`'s map of keyword arguments, `(apply hash-map gmap)` (core.jank 3427-3436; Clojure:
  PersistentArrayMap/createAsIfByAssoc);
- `zipmap`, `(transient (hash-map))` (core.jank 2411-2422; Clojure: `(transient {})`).

The hash maps are built by `native_transient_hash_map::set` (immer `set` on a transient: the
replica's `addMut` with one owner token); the order does not depend on the token.
-/

namespace Jank.R9.Coll.Order

open Jank.R3.Immer.Champ Jank.R8.Champ.Programs

/-- A transient hash map that receives `kvs` by `set`, in order (one owner token). -/
def build (kvs : List (Int × Nat)) : Champ (Int × Nat) :=
  ((kvs.foldlM (fun c kv => c.addMut mapCfg tokT kv) (Champ.empty : Champ (Int × Nat))) : M _).run {} |>.1

/-- `(keys m)` of the jank hash map holding `kvs` (inserted in order). -/
def jankKeys (kvs : List (Int × Nat)) : List Int := keysOf (build kvs)

/-- Clojure's array map: `assoc` replaces a present key's value in place, appends a new key. -/
def cljAssoc (m : List (Int × Nat)) (k : Int) (v : Nat) : List (Int × Nat) :=
  if m.any (·.1 == k) then m.map (fun p => if p.1 == k then (k, v) else p) else m ++ [(k, v)]

/-- Its keys after assoc of a present key: unchanged, for every map and key. -/
theorem clj_assoc_present_keeps_keys (m : List (Int × Nat)) (k : Int) (v : Nat)
    (h : m.any (·.1 == k) = true) : (cljAssoc m k v).map Prod.fst = m.map Prod.fst := by
  simp only [cljAssoc, h, ite_true, List.map_map]
  apply List.map_congr_left
  intro p _
  by_cases hp : p.1 = k <;> simp [hp]

/-- jank's `persistent_array_map::assoc`: the array map's entries (an association list in
insertion order), or the hash map it promotes to. `max_size` is 8 (native_array_map.hpp 30). -/
inductive JMap where
  | array (kvs : List (Int × Nat))
  | hash (kvs : List (Int × Nat))  -- the entries in insertion order; shown in `jankKeys` order

def JMap.keys : JMap → List Int
  | .array kvs => kvs.map Prod.fst
  | .hash kvs => jankKeys kvs

def jankAssoc (m : JMap) (k : Int) (v : Nat) : JMap :=
  match m with
  | .array kvs => if kvs.length == 8 then .hash (kvs ++ [(k, v)]) else .array (cljAssoc kvs k v)
  | .hash kvs => .hash (kvs ++ [(k, v)])

/-- For every 8-entry array map and every key, present or not, jank's `assoc` promotes. -/
theorem jank_assoc_at_8_promotes (kvs : List (Int × Nat)) (h : kvs.length = 8) (k : Int) (v : Nat) :
    ∃ l, jankAssoc (.array kvs) k v = .hash l := by
  simp [jankAssoc, h]

/-- Below 8 entries jank's array map `assoc` is Clojure's, for every map and key. -/
theorem jank_assoc_below_8 (kvs : List (Int × Nat)) (h : kvs.length ≠ 8) (k : Int) (v : Nat) :
    jankAssoc (.array kvs) k v = .array (cljAssoc kvs k v) := by
  simp [jankAssoc, h]

def range8 : List (Int × Nat) := (List.range 8).map fun (i : Nat) => ((i : Int), i)

/-- `(let [m (into {} (map vector (range 8) (range 8)))] (keys (assoc m 0 :x)))`: Clojure
`(0 1 2 3 4 5 6 7)`; jank the CHAMP order. -/
theorem promoted_keys :
    (jankAssoc (.array range8) 0 99).keys = [0, 7, 1, 4, 6, 3, 2, 5] ∧
    (cljAssoc range8 0 99).map Prod.fst = [0, 1, 2, 3, 4, 5, 6, 7] := by
  decide +kernel

/-- `(keys (frequencies [7 6 5 4 3 2 1 0 0]))`: the 9th `assoc!` (of the present key 0) promotes;
Clojure `(7 6 5 4 3 2 1 0)`. -/
theorem frequencies_keys :
    jankKeys ([7, 6, 5, 4, 3, 2, 1, 0].map (fun i => ((i : Int), 1)) ++ [(0, 2)]) =
      [0, 7, 1, 4, 6, 3, 2, 5] := by
  decide +kernel

/-- `((fn [& {:as m}] (keys m)) 2 :x 1 :y)`: Clojure `(2 1)`; jank's `(apply hash-map ...)`. -/
theorem kwargs_keys : jankKeys [(2, 0), (1, 1)] = [1, 2] := by decide +kernel

/-- `(keys (zipmap [2 1] [:a :b]))`: Clojure `(2 1)`; jank's hash-map transient. -/
theorem zipmap_keys : jankKeys [(2, 0), (1, 1)] = [1, 2] := by decide +kernel

end Jank.R9.Coll.Order

namespace Jank.R9.Coll.Order

/-- Clojure's `PersistentArrayMap/createAsIfByAssoc` on keyword arguments `k1 v1 k2 v2 ...`: one
entry per distinct key, in the order of first occurrence, with the last value. -/
def cljAsIfByAssoc (kvs : List (Int × Nat)) : List (Int × Nat) :=
  kvs.foldl (fun m kv => cljAssoc m kv.1 kv.2) []

/-- ★ For every argument list whose keys are distinct, Clojure's map lists them in argument order. -/
theorem clj_kwargs_order (kvs : List (Int × Nat)) (h : (kvs.map Prod.fst).Nodup) :
    (cljAsIfByAssoc kvs).map Prod.fst = kvs.map Prod.fst := by
  unfold cljAsIfByAssoc
  suffices ∀ acc : List (Int × Nat), (acc.map Prod.fst ++ kvs.map Prod.fst).Nodup →
      (kvs.foldl (fun m kv => cljAssoc m kv.1 kv.2) acc).map Prod.fst =
        acc.map Prod.fst ++ kvs.map Prod.fst by
    simpa using this [] (by simpa using h)
  clear h
  induction kvs with
  | nil => intro acc _; simp
  | cons kv kvs ih =>
    intro acc hnd
    simp only [List.foldl_cons]
    have hnot : acc.any (·.1 == kv.1) = false := by
      rw [List.any_eq_false]
      intro x hx heq
      have hx' : x.1 ∈ acc.map Prod.fst := List.mem_map_of_mem hx
      simp at heq
      rw [List.map_cons, List.nodup_append] at hnd
      exact hnd.2.2 _ hx' _ (by simp [heq]) rfl
    have hstep : (cljAssoc acc kv.1 kv.2) = acc ++ [(kv.1, kv.2)] := by
      simp [cljAssoc, hnot]
    rw [hstep, ih]
    · simp
    · simpa [List.map_append, List.append_assoc] using hnd

end Jank.R9.Coll.Order
