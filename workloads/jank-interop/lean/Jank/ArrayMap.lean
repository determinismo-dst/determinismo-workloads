import Determinismo

/-!
# Array maps and their transients: persistence

jank's small maps (≤ 8 entries) are `persistent_array_map`s over a `native_array_map`
(runtime/detail/native_array_map.{hpp,cpp}): a GC-allocated array of keys and values (`data`),
its capacity `cap` and its `length` (2 per entry). Its copy constructor is the default one: a copy
shares `data`. `clone()` allocates a new array.

- `persistent_array_map::assoc` / `dissoc` (persistent_array_map.cpp) `clone()` first: safe.
- `persistent_array_map::to_transient` → `make_box<transient_array_map>(data)` → the
  `transient_array_map(native_array_map const &)` constructor. At jank f3d82d654 it was
  `data{ d }`: a **shallow** copy, sharing the persistent map's array (`jTransientShallow`). At
  jank 7135b7708 it is `data{ d.clone() }` (transient_array_map.cpp:24-27): a new array
  (`jTransient`), so the paragraph below describes f3d82d654 only.
- `transient_array_map::assoc_in_place` → `native_array_map::insert_or_assign`, which on an
  existing key writes `data[i + 1] = val` in place; `dissoc_in_place` → `erase`, which shifts the
  later entries left in place; `insert_unique` → `make_next_array`, which writes in place when
  `length + 2 <= cap`.

So a transient's `assoc!` of an existing key, or `dissoc!`, writes into the array the persistent
map it came from still reads. Clojure: "transients ... the persistent source is unaffected"
(clojure.org/reference/transients: "In fact, the original collection is not affected").

The model below is that code, with the array as a heap cell, and Clojure's spec as pure
association lists. A timeline is a sequence of operations drawn by decisions.
-/

namespace Jank.ArrayMap

/-- Keys are keywords (interned: compared by identity, `data[i] == key`), values small ints. -/
abbrev Key := Nat
abbrev Val := Nat

/-- A backing array: `cap` slots, each a key or a value (`none`: never written). -/
structure Arr where
  slots : Array (Option Nat)
  deriving Repr, BEq, Inhabited

/-- `native_array_map`: which array, its capacity and length (counted in slots, as the C++). -/
structure NativeMap where
  data : Nat   -- heap address of the array
  cap : Nat
  length : Nat
  deriving Repr, BEq, Inhabited

structure Heap where
  arrays : Array Arr := #[]
  deriving Repr

def Heap.alloc (h : Heap) (slots : Array (Option Nat)) : Heap × Nat :=
  ({ arrays := h.arrays.push { slots } }, h.arrays.size)

def Heap.read (h : Heap) (a : Nat) (i : Nat) : Option Nat :=
  ((h.arrays.getD a { slots := #[] }).slots.getD i none)

def Heap.write (h : Heap) (a : Nat) (i : Nat) (v : Nat) : Heap :=
  { arrays := h.arrays.modify a fun arr => { slots := arr.slots.set! i (some v) } }

/-- The entries a native map shows (its first `length` slots). -/
def NativeMap.entries (h : Heap) (m : NativeMap) : List (Key × Val) :=
  (List.range (m.length / 2)).map fun i =>
    ((h.read m.data (2 * i)).getD 999, (h.read m.data (2 * i + 1)).getD 999)

/-- native_array_map.cpp `make_next_array`: in place when `length + 2 <= cap`, else a new
array of `length + 2` slots (the `switch(length)` cases) with the old entries and the new pair. -/
def makeNextArray (h : Heap) (prev : Nat) (cap length : Nat) (key : Key) (value : Val) : Heap × Nat :=
  if length + 2 ≤ cap then
    ((h.write prev length key).write prev (length + 1) value, prev)
  else
    let old := (List.range length).map fun i => h.read prev i
    h.alloc (old.toArray ++ #[some key, some value])

/-- `native_array_map::insert_unique`. -/
def insertUnique (h : Heap) (m : NativeMap) (key : Key) (val : Val) : Heap × NativeMap :=
  let (h, data) := makeNextArray h m.data m.cap m.length key val
  let length := m.length + 2
  (h, { data, length, cap := max length m.cap })

/-- `native_array_map::insert_or_assign`: an existing key's value written in place. -/
def insertOrAssign (h : Heap) (m : NativeMap) (key : Key) (val : Val) : Heap × NativeMap :=
  match (List.range (m.length / 2)).find? (fun i => h.read m.data (2 * i) == some key) with
  | some i => (h.write m.data (2 * i + 1) val, m)
  | none => insertUnique h m key val

/-- `native_array_map::erase`: the later entries shifted left in place, `length -= 2`. -/
def erase (h : Heap) (m : NativeMap) (key : Key) : Heap × NativeMap :=
  match (List.range (m.length / 2)).find? (fun i => h.read m.data (2 * i) == some key) with
  | none => (h, m)
  | some i =>
    let h := (List.range (m.length / 2 - i - 1)).foldl (fun h j =>
      let k := 2 * (i + 1 + j)
      let h := match h.read m.data k with | some v => h.write m.data (k - 2) v | none => h
      match h.read m.data (k + 1) with | some v => h.write m.data (k - 1) v | none => h) h
    (h, { m with length := m.length - 2 })

/-- `native_array_map::clone`: a new array of `cap` slots, the first `length` copied. -/
def clone (h : Heap) (m : NativeMap) : Heap × NativeMap :=
  let slots := (List.range m.cap).map fun i => if i < m.length then h.read m.data i else none
  let (h, data) := h.alloc slots.toArray
  (h, { m with data })

/-- The maps and transients of a timeline. A persistent map is either an array map (a native
map) or, past 8 entries, a hash map (its entries, immutable: immer). -/
inductive PMap where
  | array (m : NativeMap)
  | hash (entries : List (Key × Val))
  deriving Repr, Inhabited

structure Transient where
  data : NativeMap
  active : Bool := true
  /-- Promoted to a transient hash map (transient_hash_map from the array's entries: a copy). -/
  promoted : Option (List (Key × Val)) := none
  deriving Repr, Inhabited

def maxSize : Nat := 8

def PMap.entries (h : Heap) : PMap → List (Key × Val)
  | .array m => m.entries h
  | .hash es => es

/-! ## jank's operations (persistent_array_map.cpp, transient_array_map.cpp) -/

/-- `persistent_array_map::assoc`: promote at 8 entries, else clone and insert_or_assign. -/
def jAssoc (h : Heap) (m : PMap) (k : Key) (v : Val) : Heap × PMap :=
  match m with
  | .hash es => (h, .hash (if es.any (·.1 == k) then es.map fun (k', v') => if k' == k then (k', v) else (k', v') else es ++ [(k, v)]))
  | .array nm =>
    if nm.length / 2 == maxSize then
      let es := nm.entries h
      (h, .hash (if es.any (·.1 == k) then es.map fun (k', v') => if k' == k then (k', v) else (k', v') else es ++ [(k, v)]))
    else
      let (h, c) := clone h nm
      let (h, c) := insertOrAssign h c k v
      (h, .array c)

/-- `persistent_array_map::dissoc`: clone and erase. -/
def jDissoc (h : Heap) (m : PMap) (k : Key) : Heap × PMap :=
  match m with
  | .hash es => (h, .hash (es.filter (·.1 != k)))
  | .array nm => let (h, c) := clone h nm; let (h, c) := erase h c k; (h, .array c)

/-- jank f3d82d654: `persistent_array_map::to_transient` → `transient_array_map(native_array_map
const &)`: `data{ d }`, the default (shallow) copy. -/
def jTransientShallow (m : PMap) (h : Heap) : Heap × Transient :=
  match m with
  | .array nm => (h, { data := nm })
  | .hash es => (h, { data := { data := 0, cap := 0, length := 0 }, promoted := some es })

/-- jank 7135b7708: `persistent_array_map::to_transient` → `transient_array_map(native_array_map
const &)` (transient_array_map.cpp:24): `data{ d.clone() }`. -/
def jTransient (m : PMap) (h : Heap) : Heap × Transient :=
  match m with
  | .array nm => let (h, c) := clone h nm; (h, { data := c })
  | .hash es => (h, { data := { data := 0, cap := 0, length := 0 }, promoted := some es })

/-- `transient_array_map::assoc_in_place`. -/
def jAssocBang (h : Heap) (t : Transient) (k : Key) (v : Val) : Except String (Heap × Transient) :=
  if !t.active then .error "This transient has already been made persistent." else
  match t.promoted with
  | some es => .ok (h, { t with promoted := some (if es.any (·.1 == k) then es.map fun (k', v') => if k' == k then (k', v) else (k', v') else es ++ [(k, v)]) })
  | none =>
    if t.data.length / 2 == maxSize then
      let es := t.data.entries h
      .ok (h, { t with promoted := some (if es.any (·.1 == k) then es.map fun (k', v') => if k' == k then (k', v) else (k', v') else es ++ [(k, v)]) })
    else
      let (h, d) := insertOrAssign h t.data k v
      .ok (h, { t with data := d })

/-- `transient_array_map::dissoc_in_place`. -/
def jDissocBang (h : Heap) (t : Transient) (k : Key) : Except String (Heap × Transient) :=
  if !t.active then .error "This transient has already been made persistent." else
  match t.promoted with
  | some es => .ok (h, { t with promoted := some (es.filter (·.1 != k)) })
  | none => let (h, d) := erase h t.data k; .ok (h, { t with data := d })

/-- `transient_array_map::to_persistent`: `make_box<persistent_array_map>(std::move(data))`. -/
def jPersistent (t : Transient) : Except String (Transient × PMap) :=
  if !t.active then .error "This transient has already been made persistent." else
  .ok ({ t with active := false }, match t.promoted with | some es => .hash es | none => .array t.data)

/-! ## Clojure: maps are values -/

def cAssoc (es : List (Key × Val)) (k : Key) (v : Val) : List (Key × Val) :=
  if es.any (·.1 == k) then es.map fun (k', v') => if k' == k then (k', v) else (k', v') else es ++ [(k, v)]

def cDissoc (es : List (Key × Val)) (k : Key) : List (Key × Val) := es.filter (·.1 != k)

/-! ## The same operations with a deep copy in `to_transient` (`data.clone()`): the property
holds, so the shallow copy is the cause. -/

def jTransientFixed (m : PMap) (h : Heap) : Heap × Transient :=
  match m with
  | .array nm => let (h, c) := clone h nm; (h, { data := c })
  | .hash es => (h, { data := { data := 0, cap := 0, length := 0 }, promoted := some es })


/-! ## The world -/

structure World where
  decisions : Determinismo.Decisions := {}
  heap : Heap := {}
  /-- jank's persistent maps, each with Clojure's value for it (fixed at creation). -/
  maps : Array (PMap × List (Key × Val)) := #[]
  /-- jank's transients, each with Clojure's value for it. -/
  transients : Array (Transient × List (Key × Val)) := #[]
  story : Array String := #[]

instance : Determinismo.Chaotic World where
  decisions w := w.decisions
  setDecisions w d := { w with decisions := d }

def kw (k : Key) : String := s!":{Char.ofNat ('a'.toNat + k)}"
def showMap (es : List (Key × Val)) : String :=
  "{" ++ ", ".intercalate (es.map fun (k, v) => s!"{kw k} {v}") ++ "}"

def sameEntries (a b : List (Key × Val)) : Bool :=
  a.length == b.length && a.all fun e => b.contains e

open Determinismo in
/-- One operation, drawn: assoc, dissoc, transient, assoc!, dissoc!, persistent!. -/
def step (fixed : Bool) : EStateM Stop World Unit := do
  let op ← decide (σ := World) "map.op" 6
  -- A key for assoc, dissoc, assoc!, dissoc!; a value for assoc and assoc!.
  let k ← if op == 2 || op == 5 then pure 0 else decide (σ := World) "map.key" 2
  let v ← if op == 0 || op == 3 then decide (σ := World) "map.val" 3 else pure 0
  match op with
  | 0 | 1 | 2 =>
    let i ← decide (σ := World) "map.which" (← get).maps.size
    -- Read the world after the decisions (a `set` of an older copy would undo them).
    let w ← get
    let (m, c) := w.maps[i]!
    match op with
    | 0 =>
      let (h, m') := jAssoc w.heap m k v
      set { w with heap := h, maps := w.maps.push (m', cAssoc c k v),
                   story := w.story.push s!"m{w.maps.size} = (assoc m{i} {kw k} {v})" }
    | 1 =>
      let (h, m') := jDissoc w.heap m k
      set { w with heap := h, maps := w.maps.push (m', cDissoc c k),
                   story := w.story.push s!"m{w.maps.size} = (dissoc m{i} {kw k})" }
    | _ =>
      let (h, t) := (if fixed then jTransientFixed else jTransient) m w.heap
      set { w with heap := h, transients := w.transients.push (t, c),
                   story := w.story.push s!"t{w.transients.size} = (transient m{i})" }
  | _ =>
    if (← get).transients.isEmpty then return
    let j ← decide (σ := World) "map.which_transient" (← get).transients.size
    let w ← get
    let (t, c) := w.transients[j]!
    if !t.active then return  -- both sides throw: not interesting
    match op with
    | 3 =>
      match jAssocBang w.heap t k v with
      | .ok (h, t') => set { w with heap := h, transients := w.transients.set! j (t', cAssoc c k v),
                                    story := w.story.push s!"(assoc! t{j} {kw k} {v})" }
      | .error _ => pure ()
    | 4 =>
      match jDissocBang w.heap t k with
      | .ok (h, t') => set { w with heap := h, transients := w.transients.set! j (t', cDissoc c k),
                                    story := w.story.push s!"(dissoc! t{j} {kw k})" }
      | .error _ => pure ()
    | _ =>
      match jPersistent t with
      | .ok (t', m) => set { w with transients := w.transients.set! j ({ t' with active := false }, c),
                                    maps := w.maps.push (m, c),
                                    story := w.story.push s!"m{w.maps.size} = (persistent! t{j})" }
      | .error _ => pure ()

open Determinismo in
/-- Every persistent map still shows its value. -/
def check : EStateM Stop World Unit := do
  let w ← get
  for i in List.range w.maps.size do
    let (m, c) := w.maps[i]!
    let shown := m.entries w.heap
    if !sameEntries shown c then
      violate (σ := World) "a persistent map never changes"
        s!"{"; ".intercalate w.story.toList}: m{i} is {showMap shown}, Clojure {showMap c}"

/-- The literal maps a timeline starts from: `{}` and `{:a 0 :b 1}` (a literal is built by
`persistent_array_map::create_unique`: `cap == length`). -/
def start : World :=
  let (h, a) := ({ } : Heap).alloc #[some 0, some 0, some 1, some 1]
  { heap := h,
    maps := #[(.array { data := 999, cap := 0, length := 0 }, []),
              (.array { data := a, cap := 4, length := 4 }, [(0, 0), (1, 1)])],
    story := #["m0 = {}", "m1 = {:a 0, :b 1}"] }

open Determinismo in
def body (fixed : Bool) (ops : Nat) : EStateM Stop World Unit := do
  for _ in List.range ops do
    step fixed
    check

open Determinismo in
def run (fixed : Bool) (ops : Nat) (source : Source) : Ended :=
  match (body fixed ops).run { start with decisions := { source } } with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }
  | .error (.nodeDown _) w => { taken := w.decisions.taken, violation := none }

/-! ## The two minimal stories, evaluated -/

/-- `(let [m {:a 0 :b 1} t (transient m)] (assoc! t :a 2) m)`: what `m` shows after, with a
given `to_transient`. -/
def assocBangStoryWith (toT : PMap → Heap → Heap × Transient) : List (Key × Val) :=
  let (h, a) := ({ } : Heap).alloc #[some 0, some 0, some 1, some 1]
  let m : PMap := .array { data := a, cap := 4, length := 4 }
  let (h, t) := toT m h
  match jAssocBang h t 0 2 with
  | .ok (h, _) => m.entries h
  | .error _ => []

/-- `(let [m {:a 0 :b 1} t (transient m)] (dissoc! t :a) m)`. -/
def dissocBangStoryWith (toT : PMap → Heap → Heap × Transient) : List (Key × Val) :=
  let (h, a) := ({ } : Heap).alloc #[some 0, some 0, some 1, some 1]
  let m : PMap := .array { data := a, cap := 4, length := 4 }
  let (h, t) := toT m h
  match jDissocBang h t 0 with
  | .ok (h, _) => m.entries h
  | .error _ => []

def assocBangStory : List (Key × Val) := assocBangStoryWith jTransient
def dissocBangStory : List (Key × Val) := dissocBangStoryWith jTransient

/-- jank f3d82d654 (D14): the transient wrote into its source. -/
theorem assoc_bang_changes_source_f3d82d654 : assocBangStoryWith jTransientShallow = [(0, 2), (1, 1)] := by decide
theorem dissoc_bang_changes_source_f3d82d654 : dissocBangStoryWith jTransientShallow = [(1, 1), (1, 1)] := by decide

/-- jank 7135b7708: the source map is unaffected. -/
theorem assoc_bang_keeps_source : assocBangStory = [(0, 0), (1, 1)] := by decide
theorem dissoc_bang_keeps_source : dissocBangStory = [(0, 0), (1, 1)] := by decide

end Jank.ArrayMap
