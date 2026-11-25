/-!
# Map and set expressions with keys known only at run time; `strip_source_meta`'s mutation

**Map/set expressions** (`{k1 v1 k2 v2}` / `#{a b}` where some key is not a constant):

- compiled (`ir/processor.cpp` `gen(map)` 164-184: an array map up to 8 pairs, else a hash map;
  `cpp_processor.cpp` 652-706 → `_jank_amap`/`_jank_hmap`/`_jank_hset`, codegen/api.cpp
  330-449): `assoc_in_place` / `conj_in_place` one pair (element) at a time, so a repeated key
  keeps its first position with the last value (`native_array_map::insert_or_assign`,
  native_array_map.cpp 139-165), a repeated set element is dropped;
- interpreted at the top level (`evaluate.cpp` `eval(map)` 447-491: up to 8 pairs the evaluated
  keys and values go straight into a `persistent_array_map` built `in_place_unique`, without a
  check; more than 8 through a transient hash map; `eval(set)` 493-509 through a transient hash
  set).

Clojure (Compiler.java `MapExpr.emit` 3534-3558, `RT.map` → `createWithCheck`; `SetExpr.emit`,
`RT.set` → `PersistentHashSet.createWithCheck`): a duplicate key or element throws
`IllegalArgumentException: Duplicate key` (a map of one pair cannot have one).

**`strip_source_meta`** (analyze/pass/strip_source_meta.cpp 13-42, run by `pass::optimize` on
every analyzed form, including `eval`'s, context_dynamic.cpp 220-226): for every
`primitive_literal` whose object is metadatable, `reset_meta(obj, strip_source_from_meta(meta))`
(core/meta.cpp 84-113, 229-239) writes the object's `meta` field **in place**: the object is the
quoted object itself (`analyze_quote` → `analyze_primitive_literal`, processor.cpp 2799,
3244), so any value that reaches `(quote v)` (a macro or `eval` building `(list 'quote v)`) loses a
`:jank/source` key, and an empty map becomes `nil`. Clojure never changes a value's metadata.
-/

namespace Jank.R3.Codegen.Literals

/-- A key or element: a small integer (its value is the key's identity class under `=`). -/
abbrev K := Nat

inductive MapOut where
  /-- The map: entries in order (key, value index), and `count`. -/
  | map (entries : List (K × Nat))
  | set (elems : List K)
  | duplicate (k : K)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- `insert_or_assign` one pair at a time: an existing key keeps its place, takes the new value. -/
def assocAll (kvs : List (K × Nat)) : List (K × Nat) :=
  kvs.foldl (fun acc (k, v) =>
    if acc.any (·.1 == k) then acc.map (fun (k2, v2) => if k2 == k then (k2, v) else (k2, v2))
    else acc ++ [(k, v)]) []

def conjAll (xs : List K) : List K :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

/-- jank, compiled: `_jank_amap` (≤ 8 pairs) or `_jank_hmap`; values are the pair's index. -/
def jankCompiledMap (keys : List K) : MapOut :=
  .map (assocAll (keys.zipIdx))

/-- jank, top level: `in_place_unique` for ≤ 8 pairs (every pair kept), a transient hash map
(last value wins) above. -/
def jankTopMap (keys : List K) : MapOut :=
  if keys.length ≤ 8 then .map keys.zipIdx else .map (assocAll keys.zipIdx)

def jankSet (elems : List K) : MapOut := .set (conjAll elems)

def firstDup (xs : List K) : Option K :=
  (xs.zipIdx.find? fun (x, i) => (xs.take i).contains x).map (·.1)

/-- Clojure: `RT.map`/`RT.set` `createWithCheck` (a single pair: `mapUniqueKeys`). -/
def cljMap (keys : List K) : MapOut :=
  if keys.length ≤ 1 then .map keys.zipIdx
  else match firstDup keys with
    | some k => .duplicate k
    | none => .map keys.zipIdx

def cljSet (elems : List K) : MapOut :=
  match firstDup elems with
  | some k => .duplicate k
  | none => .set elems

/-- `count` and `(get m k)` as a program sees them. -/
def MapOut.count : MapOut → Option Nat
  | .map es => some es.length
  | .set es => some es.length
  | .duplicate _ => none

def MapOut.get (m : MapOut) (k : K) : Option Nat :=
  match m with
  | .map es => (es.find? (·.1 == k)).map (·.2)
  | _ => none

/-- Two keys equal at run time: Clojure throws; compiled jank keeps one entry with the last
value; the top-level interpreter keeps both pairs (`count` 2, `get` finds the first). -/
theorem dup_pair :
    cljMap [1, 1] = .duplicate 1 ∧ jankCompiledMap [1, 1] = .map [(1, 1)]
    ∧ jankTopMap [1, 1] = .map [(1, 0), (1, 1)] := by decide

theorem dup_set : cljSet [1, 1] = .duplicate 1 ∧ jankSet [1, 1] = .set [1] := by decide

/-- For every key list with no repetition, all three agree on the entries. -/
theorem no_dup_agree (keys : List K) (h : firstDup keys = none) (hn : keys.length ≤ 8) :
    jankTopMap keys = .map keys.zipIdx ∧ (keys.length ≤ 1 → cljMap keys = .map keys.zipIdx)
    ∧ (2 ≤ keys.length → cljMap keys = .map keys.zipIdx) := by
  refine ⟨by simp [jankTopMap, hn], fun h1 => by simp [cljMap, h1], fun h2 => ?_⟩
  have : ¬ keys.length ≤ 1 := by omega
  simp [cljMap, this, h]

/-! ## `strip_source_meta` on a shared object -/

/-- Metadata maps as their keys (`:jank/source` or a user key) — enough for the effect. -/
inductive Meta where
  | none
  | keys (ks : List String)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- `strip_source_from_meta` (core/meta.cpp 229-239): `dissoc :jank/source`, empty → nil. -/
def stripSource : Meta → Meta
  | .none => .none
  | .keys ks =>
    let r := ks.filter (· != "jank/source")
    if r.isEmpty then .none else .keys r

/-- The heap: object id → its metadata. `eval` of `(quote o)` in jank: `pass::optimize` resets
`o`'s metadata in place; in Clojure the heap is unchanged. -/
def jankEvalQuote (heap : List (Nat × Meta)) (o : Nat) : List (Nat × Meta) :=
  heap.map fun (i, m) => if i == o then (i, stripSource m) else (i, m)

def cljEvalQuote (heap : List (Nat × Meta)) (_o : Nat) : List (Nat × Meta) := heap

/-- `(def v (with-meta [1] {}))  (eval (list 'quote v))  (meta v)`: Clojure `{}`, jank `nil`. -/
theorem quote_empty_meta_becomes_nil :
    (jankEvalQuote [(0, .keys [])] 0).lookup 0 = some .none
    ∧ (cljEvalQuote [(0, .keys [])] 0).lookup 0 = some (.keys []) := by decide

/-- For every metadata: jank changes it exactly when it is empty or holds `:jank/source`. -/
theorem strip_changes_iff (ks : List String) :
    stripSource (.keys ks) ≠ .keys ks ↔ (ks = [] ∨ "jank/source" ∈ ks) := by
  unfold stripSource
  by_cases h : ks.filter (· != "jank/source") = []
  · simp only [h, List.isEmpty_nil, if_true]
    constructor
    · intro _
      by_cases hk : ks = []
      · exact .inl hk
      · right
        cases ks with
        | nil => exact absurd rfl hk
        | cons x xs =>
          have hx : (x != "jank/source") = false := by
            have := List.filter_eq_nil_iff.mp h x (List.mem_cons_self ..)
            simpa using this
          simp at hx; simp [hx]
    · intro _; simp
  · have hne : (ks.filter (· != "jank/source")).isEmpty = false := by
      simpa [List.isEmpty_iff] using h
    simp only [hne]
    constructor
    · intro hn
      by_cases hk : "jank/source" ∈ ks
      · exact .inr hk
      · exfalso; apply hn
        simp only [Bool.false_eq_true, if_false]
        congr 1
        apply List.filter_eq_self.mpr
        intro a ha; simp; intro hc; exact hk (hc ▸ ha)
    · intro hd
      rcases hd with hd | hd
      · exact absurd (by simp [hd]) h
      · intro heq
        have := congrArg (fun m => match m with | Meta.keys l => "jank/source" ∈ l | _ => False) heq
        simp at this
        exact this hd

end Jank.R3.Codegen.Literals
