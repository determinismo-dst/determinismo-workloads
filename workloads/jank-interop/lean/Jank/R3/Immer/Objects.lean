import Jank.Equality
import Jank.R3.Immer.Rbts
import Jank.R3.Immer.Champ

/-!
# jank's collection objects over the immer replica

The jank functions that call immer, replicated over `Rbts` and `Champ`:

- persistent_vector.cpp (`conj` 177, `assoc` 266, `pop` 312, `peek` 302, `nth` 322, `get` 218,
  `contains` 253, `to_transient` 189), transient_vector.cpp (`conj_in_place` 46, `nth` 53,
  `assoc_in_place` 81, `to_persistent` 118, `pop_in_place` 234, `assert_active` 248),
  core/seq.cpp `subvec` 621 (`native_persistent_vector{ begin + start, begin + end }` =
  `from_range`), persistent_vector.cpp `create` 44 (`vec`).
- persistent_hash_map.cpp (`assoc` 110 = `data.set`, `dissoc` 116 = `data.erase`, `get` 74/84,
  `find` 94, `contains` 104, `to_transient` 132, the promotion constructor 12,
  `create_from_seq` 55), transient_hash_map.cpp (`assoc_in_place` 96, `dissoc_in_place` 103,
  `to_persistent` 145 = `std::move(data).persistent()`, reads 50-93 with `assert_active`, the
  promotion constructor 36), detail/base_persistent_map.cpp (`equal` 31, `to_hash` 132).
- persistent_array_map.cpp (`assoc` 70 promotes when `data.size() == max_size` (8) whether or
  not the key is present, `dissoc` 91, `find` 55, `to_transient` 108),
  transient_array_map.cpp (`assoc_in_place` 67 promotes the same way, `dissoc_in_place` 91,
  `to_persistent` 126 moves `data` (native_array_map's defaulted move copies the pointer: the
  dead transient still reads the same array), `get(key)` 41 asserts, `get(key, fallback)` 47,
  `find` 52, `contains` 62 do not), detail/native_array_map.{hpp,cpp} (`find`: keywords by
  pointer, others by `runtime::equal(data[i], key)`; `insert_or_assign` writes the value only;
  `erase` shifts).
- persistent_hash_set.cpp (`conj` 149 = `data.insert`, `disj` 191 = `data.erase`, `contains`
  186, `call`/`get` 156/171/176 return the stored element, `equal` 55, `to_hash` 103,
  `create_from_seq` 45), transient_hash_set.cpp (`conj_in_place` 43, `disjoin_in_place` 103,
  `to_persistent` 50 = `data.persistent()` (lvalue), reads with `assert_active`).

Elements and keys are round 1's values (`Jank.Equality.V`), hashed with `jankHash` (each type's
`to_hash`, `std::hash<object_ref>`) and compared with `jankEq` (each type's `equal`,
`std::equal_to<object_ref>`) on x86-64 (`char` signed).
-/

namespace Jank.R3.Immer.Objects

open Jank.Equality (V jankEq jankHash cljEq)
open Jank.Hash (CharSign)

def cs : CharSign := .signed
def fuel : Nat := 12

/-- `runtime::equal(l, r)` = `l.equal(r)`. -/
def jEq (a b : V) : Bool := jankEq cs fuel a b
/-- `to_hash()`. -/
def jHash (v : V) : UInt32 := jankHash cs fuel v
/-- Clojure's `=` (Util.equiv). -/
def cEq (a b : V) : Bool := cljEq fuel a b

/-- `immer::map<object_ref, object_ref, ...>`: pairs, `hash_key`, `equal_key`. -/
def mapCfg : Champ.Cfg (V × V) V where
  hashT p := (jHash p.1).toNat
  hashK k := (jHash k).toNat
  eqTT a b := jEq a.1 b.1
  eqTK a k := jEq a.1 k

/-- `immer::set<object_ref, ...>`. -/
def setCfg : Champ.Cfg V V where
  hashT v := (jHash v).toNat
  hashK k := (jHash k).toNat
  eqTT := jEq
  eqTK := jEq

/-- jank results: a value, or a thrown exception. -/
inductive R (α : Type) where
  | ok (x : α)
  | throws (msg : String)
  deriving Repr, BEq

/-! ## Array maps (native_array_map) -/

def isKw : V → Bool
  | .kw _ => true
  | _ => false

/-- The key test of `find`/`insert_or_assign`/`erase`: a keyword key by pointer (interned:
same name), else `runtime::equal(data[i], key)`. -/
def amMatch (stored key : V) : Bool := if isKw key then stored == key else jEq stored key

def amFind (es : List (V × V)) (k : V) : Option V := (es.find? fun e => amMatch e.1 k).map (·.2)

/-- `insert_or_assign`: the value of the first matching key replaced (the key kept), else
appended (`insert_unique`). -/
def amInsertOrAssign (es : List (V × V)) (k v : V) : List (V × V) :=
  match es.findIdx? (fun e => amMatch e.1 k) with
  | some i => es.set i ((es.getD i (k, v)).1, v)
  | none => es ++ [(k, v)]

def amErase (es : List (V × V)) (k : V) : List (V × V) :=
  match es.findIdx? (fun e => amMatch e.1 k) with
  | some i => es.eraseIdx i
  | none => es

def maxArray : Nat := 8

/-! ## Persistent maps -/

inductive JMap where
  | array (es : List (V × V))
  | hash (c : Champ.Champ (V × V))
  deriving Repr

instance : Inhabited JMap := ⟨.array []⟩

def JMap.entries : JMap → List (V × V)
  | .array es => es
  | .hash c => c.toList

def JMap.count : JMap → Nat
  | .array es => es.length
  | .hash c => c.size

/-- The promotion: a `native_transient_hash_map` (fresh owner, empty) `set` with each entry of
the array, then with the new pair (persistent_hash_map.cpp:12 / transient_hash_map.cpp:36). -/
def promote (es : List (V × V)) : Champ.M (Champ.Transient (V × V)) := do
  let t ← Champ.Transient.empty
  let mut c := t.champ
  for e in es do
    c ← c.addMut mapCfg t.tok e
  pure { t with champ := c }

def JMap.assoc (m : JMap) (k v : V) : Champ.M JMap := do
  match m with
  | .array es =>
    if es.length == maxArray then
      let t ← promote es
      let c ← t.champ.addMut mapCfg t.tok (k, v)
      -- `data = transient.persistent()` (lvalue: the local owner gets a fresh token)
      let (c, _) ← ({ t with champ := c } : Champ.Transient (V × V)).persistentL
      pure (.hash c)
    else pure (.array (amInsertOrAssign es k v))
  | .hash c => pure (.hash (← c.add mapCfg (k, v)))

def JMap.dissoc (m : JMap) (k : V) : Champ.M JMap := do
  match m with
  | .array es => pure (.array (amErase es k))
  | .hash c => pure (.hash (← c.sub mapCfg k))

def JMap.get (m : JMap) (k : V) : Option V :=
  match m with
  | .array es => amFind es k
  | .hash c => (c.get mapCfg k).map (·.2)

/-- `find`: `[key, *res]` with the key passed in (R123). -/
def JMap.find (m : JMap) (k : V) : Option (V × V) := (m.get k).map fun v => (k, v)

def JMap.contains (m : JMap) (k : V) : Bool := (m.get k).isSome

/-- base_persistent_map.cpp `equal`: a map of the same count containing each key with an equal
value (`contains` then `runtime::equal(entry.second, o.get(entry.first))`). -/
def JMap.equal (a b : JMap) : Bool :=
  a.count == b.count && a.entries.all fun (k, v) => b.contains k && (match b.get k with | some w => jEq v w | none => false)

/-- `hash::unordered(begin, end)` over pairs: `31 * h(k) + h(v)` summed from 0. -/
def JMap.hashOf (m : JMap) : UInt32 := Jank.Hash.unorderedPairs (m.entries.map fun (k, v) => (jHash k, jHash v))

/-- `hash-map` → `persistent_hash_map::create_from_seq`: a fresh transient, `set` each pair,
`persistent()` (lvalue). -/
def JMap.fromPairs (ps : List (V × V)) : Champ.M JMap := do
  let t ← Champ.Transient.empty
  let mut c := t.champ
  for p in ps do
    c ← c.addMut mapCfg t.tok p
  let (c', _) ← ({ t with champ := c } : Champ.Transient (V × V)).persistentL
  pure (.hash c')

/-! ## Transient maps -/

inductive TBody where
  | array (es : List (V × V))
  | hash (t : Champ.Transient (V × V))
  deriving Repr

structure TMap where
  body : TBody
  active : Bool := true
  deriving Repr

instance : Inhabited TMap := ⟨{ body := .array [] }⟩

/-- `persistent_array_map::to_transient` (a clone) / `persistent_hash_map::to_transient`
(`d.transient()`: a fresh owner). -/
def JMap.toTransient (m : JMap) : Champ.M TMap := do
  match m with
  | .array es => pure { body := .array es }
  | .hash c => pure { body := .hash (← c.transient) }

def deadMsg : String := "transient used after persistent!"

/-- `assoc!`: the transient to use next (a different object after an array map's promotion). -/
def TMap.assocBang (t : TMap) (k v : V) : Champ.M (R TMap) := do
  if !t.active then return .throws deadMsg
  match t.body with
  | .array es =>
    if es.length == maxArray then
      let h ← promote es
      let c ← h.champ.addMut mapCfg h.tok (k, v)
      pure (.ok { body := .hash { h with champ := c } })
    else pure (.ok { t with body := .array (amInsertOrAssign es k v) })
  | .hash h =>
    let c ← h.champ.addMut mapCfg h.tok (k, v)
    pure (.ok { t with body := .hash { h with champ := c } })

def TMap.dissocBang (t : TMap) (k : V) : Champ.M (R TMap) := do
  if !t.active then return .throws deadMsg
  match t.body with
  | .array es => pure (.ok { t with body := .array (amErase es k) })
  | .hash h =>
    let c ← h.champ.subMut mapCfg h.tok k
    pure (.ok { t with body := .hash { h with champ := c } })

/-- `persistent!`: the map, and the transient left behind (inactive). -/
def TMap.persistentBang (t : TMap) : R (JMap × TMap) :=
  if !t.active then .throws deadMsg
  else match t.body with
    | .array es => .ok (.array es, { t with active := false })  -- `std::move(data)`: same array
    | .hash h =>
      let (c, h') := h.persistentR  -- `std::move(data).persistent()`
      .ok (.hash c, { body := .hash h', active := false })

def TMap.lookup (t : TMap) (k : V) : Option V :=
  match t.body with
  | .array es => amFind es k
  | .hash h => (h.champ.get mapCfg k).map (·.2)

def TMap.count' (t : TMap) : Nat :=
  match t.body with
  | .array es => es.length
  | .hash h => h.champ.size

/-- The reads on a transient map, as jank dispatches them. -/
inductive TRead where
  | count
  | get1 (k : V)        -- (get t k), (t k)
  | get2 (k nf : V)     -- (get t k nf), (t k nf)
  | contains (k : V)    -- (contains? t k)
  | find (k : V)        -- (find t k)
  deriving Repr, BEq

def TRead.code (t : String) : TRead → String
  | .count => s!"(count {t})"
  | .get1 k => s!"(get {t} {k.code})"
  | .get2 k nf => s!"(get {t} {k.code} {nf.code})"
  | .contains k => s!"(contains? {t} {k.code})"
  | .find k => s!"(find {t} {k.code})"

/-- A read's result: `(count)`, a value, a boolean, an entry. -/
inductive RV where
  | num (x : Nat)
  | val (x : V)
  | bool (x : Bool)
  | entry (x : Option (V × V))
  deriving BEq

def RV.code : RV → String
  | .num x => s!"{x}"
  | .val x => x.code
  | .bool x => s!"{x}"
  | .entry none => "nil"
  | .entry (some (k, v)) => s!"[{k.code} {v.code}]"

/-- jank: transient_array_map `count` 35 and `get(key)` 41 assert; `get(key, fallback)` 47,
`find` 52, `contains` 62 do not. transient_hash_map: every read asserts (50-93). -/
def TMap.read (t : TMap) (r : TRead) : R RV :=
  let asserts : Bool := match t.body, r with
    | .array _, .get2 .. | .array _, .contains _ | .array _, .find _ => false
    | _, _ => true
  if asserts && !t.active then .throws deadMsg
  else match r with
    | .count => .ok (.num t.count')
    | .get1 k => .ok (.val ((t.lookup k).getD .nil))
    | .get2 k nf => .ok (.val ((t.lookup k).getD nf))
    | .contains k => .ok (.bool (t.lookup k).isSome)
    | .find k => .ok (.entry ((t.lookup k).map fun v => (k, v)))

/-! ## Sets -/

abbrev JSet := Champ.Champ V

def JSet.conj (s : JSet) (x : V) : Champ.M JSet := s.add setCfg x
def JSet.disj (s : JSet) (x : V) : Champ.M JSet := s.sub setCfg x
def JSet.contains (s : JSet) (x : V) : Bool := (s.get setCfg x).isSome
/-- `(s x)` / `(get s x)`: the stored element. -/
def JSet.call (s : JSet) (x : V) : Option V := s.get setCfg x
def JSet.equal (a b : JSet) : Bool := a.size == b.size && a.toList.all fun e => b.contains e
def JSet.hash (s : JSet) : UInt32 := Jank.Hash.unorderedRange (s.toList.map jHash)

/-- `hash-set` → `create_from_seq`: a fresh transient, `insert` each, `persistent()`. -/
def JSet.fromList (xs : List V) : Champ.M JSet := do
  let t ← Champ.Transient.empty
  let mut c := t.champ
  for x in xs do
    c ← c.addMut setCfg t.tok x
  let (c', _) ← ({ t with champ := c } : Champ.Transient V).persistentL
  pure c'

structure TSet where
  t : Champ.Transient V
  active : Bool := true
  deriving Repr

instance : Inhabited TSet := ⟨{ t := { champ := Champ.Champ.empty, tok := 0 } }⟩

def JSet.toTransient (s : JSet) : Champ.M TSet := do pure { t := ← s.transient }

def TSet.conjBang (t : TSet) (x : V) : Champ.M (R TSet) := do
  if !t.active then return .throws deadMsg
  let c ← t.t.champ.addMut setCfg t.t.tok x
  pure (.ok { t with t := { t.t with champ := c } })

def TSet.disjBang (t : TSet) (x : V) : Champ.M (R TSet) := do
  if !t.active then return .throws deadMsg
  let c ← t.t.champ.subMut setCfg t.t.tok x
  pure (.ok { t with t := { t.t with champ := c } })

/-- `to_persistent`: `data.persistent()` on an lvalue (the owner gets a fresh token). -/
def TSet.persistentBang (t : TSet) : Champ.M (R (JSet × TSet)) := do
  if !t.active then return .throws deadMsg
  let (c, t') ← t.t.persistentL
  pure (.ok (c, { t := t', active := false }))

/-- Transient set reads: all assert (transient_hash_set.cpp 37-101). -/
def TSet.read (t : TSet) (r : TRead) : R RV :=
  if !t.active then .throws deadMsg
  else match r with
    | .count => .ok (.num t.t.champ.size)
    | .get1 k => .ok (.val ((t.t.champ.get setCfg k).getD .nil))
    | .get2 k nf => .ok (.val ((t.t.champ.get setCfg k).getD nf))
    | .contains k => .ok (.bool (t.t.champ.get setCfg k).isSome)
    | .find _ => .throws "find unsupported"

/-! ## Vectors (elements are naturals: identity of positions is what is checked) -/

abbrev JVec := Rbts.Tree Nat

def vecNth (v : JVec) (i : Int) : R Nat :=
  if i < 0 || v.size ≤ i.toNat then .throws "index out of bounds"
  else match v.get i.toNat with
    | some x => .ok x
    | none => .throws "UB: unreachable read"

def vecConj (v : JVec) (x : Nat) (n : Nat) : JVec × Nat := v.pushBack x n

/-- persistent_vector.cpp `assoc` 266: `i > size || 0 > i` throws; `i == size` push_back; else
`set`. -/
def vecAssoc (v : JVec) (i : Int) (x : Nat) (n : Nat) : R JVec × Nat :=
  if i > v.size || 0 > i then (.throws "index out of bounds", n)
  else if i.toNat == v.size then let (w, n) := v.pushBack x n; (.ok w, n)
  else let (w, n) := v.assoc i.toNat x n; (.ok w, n)

/-- `pop` 312: empty throws, else `take(size - 1)`. -/
def vecPop (v : JVec) (n : Nat) : R JVec × Nat :=
  if v.size == 0 then (.throws "pop empty", n)
  else let (w, n) := v.take (v.size - 1) n; (.ok w, n)

/-- core/seq.cpp `subvec` 621: bounds, `start == end` → the empty vector, else
`native_persistent_vector{ begin + start, begin + end }` (iterator reads, `from_range`). -/
def vecSubvec (v : JVec) (s e : Int) (n : Nat) : R JVec × Nat :=
  if e < s || s < 0 || e > v.size then (.throws "index out of bounds", n)
  else if s == e then (.ok Rbts.Tree.empty, n)
  else
    let xs := (v.iter.drop s.toNat).take (e - s).toNat
    let xs := xs.map (·.getD 0)
    let (w, n) := Rbts.Tree.fromList xs n
    (.ok w, n)

structure TVec where
  t : Rbts.Transient Nat
  active : Bool := true
  deriving Repr

instance : Inhabited TVec := ⟨{ t := { tree := Rbts.Tree.empty, tok := 0 } }⟩

def vecTransient (v : JVec) (n : Nat) : TVec × Nat := let (t, n) := v.transient n; ({ t }, n)

def TVec.conjBang (t : TVec) (x : Nat) (n : Nat) : R TVec × Nat :=
  if !t.active then (.throws deadMsg, n)
  else let (u, n) := t.t.pushBack x n; (.ok { t with t := u }, n)

/-- `assoc_in_place` 81. -/
def TVec.assocBang (t : TVec) (i : Int) (x : Nat) (n : Nat) : R TVec × Nat :=
  if !t.active then (.throws deadMsg, n)
  else if i > t.t.tree.size || 0 > i then (.throws "index out of bounds", n)
  else if i.toNat == t.t.tree.size then let (u, n) := t.t.pushBack x n; (.ok { t with t := u }, n)
  else let (u, n) := t.t.set i.toNat x n; (.ok { t with t := u }, n)

/-- `pop_in_place` 234: `data.take(data.size() - 1)` (vector_transient::take: `take_mut`). -/
def TVec.popBang (t : TVec) (n : Nat) : R TVec × Nat :=
  if !t.active then (.throws deadMsg, n)
  else if t.t.tree.size == 0 then (.throws "pop empty", n)
  else let (u, n) := t.t.take (t.t.tree.size - 1) n; (.ok { t with t := u }, n)

def TVec.nth (t : TVec) (i : Int) : R Nat :=
  if !t.active then .throws deadMsg else vecNth t.t.tree i

def TVec.count (t : TVec) : R Nat := if !t.active then .throws deadMsg else .ok t.t.tree.size

/-- `to_persistent` 118: `data.persistent()` (lvalue: fresh owner token), inactive. -/
def TVec.persistentBang (t : TVec) (n : Nat) : R (JVec × TVec) × Nat :=
  if !t.active then (.throws deadMsg, n)
  else
    let (tree, u, n) := t.t.persistent n
    (.ok (tree, { t := u, active := false }), n)

end Jank.R3.Immer.Objects
