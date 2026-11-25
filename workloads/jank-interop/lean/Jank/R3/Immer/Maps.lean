import Jank.R3.Immer.Objects
import Jank.R3.Immer.Kit

/-!
# The map and set worlds: jank (over the immer replica) beside Clojure

Clojure's spec (PersistentHashMap, PersistentArrayMap, PersistentHashSet and their transients,
clojure-ref/src/jvm/clojure/lang): a map is its entries compared by `Util.equiv`; `assoc` of a key
already present keeps the stored key and replaces the value (`BitmapIndexedNode.assoc`:
`Util.equiv(key, keyOrNull)` → `cloneAndSet(array, 2*idx+1, val)`; HashCollisionNode and
PersistentArrayMap likewise); `find` returns the stored key (`MapEntry.create(keyOrNull, ...)`);
a transient used after `persistent!` throws (ATransientMap `ensureEditable` in `valAt`, `count`,
`assoc`, `without`; `containsKey` and `entryAt` go through `valAt`). A set is a map from each
element to itself: `conj` of a present element returns the set unchanged
(PersistentHashSet.cons); `conj!` is `impl.assoc(val, val)` (ATransientSet.conj: the key kept,
the value replaced); `get`/invoke return `impl.valAt(key)`; seq walks the keys.
Iteration order is unspecified for hash maps and sets.

Each timeline: start values, then `steps` operations drawn by decisions; after every step every
live value is checked. A violation's property is its class:

- `count`, `get`, `contains`: lookups disagree;
- `find-key`: `find`'s entry key is not the stored key (round 2's R123);
- `key-identity`: counts and lookups agree but the stored keys or elements are other objects;
- `entries`: anything else in the entries;
- `=`: jank's `=` disagrees with Clojure's on two live values; `hash`: equal (jank) but hashes
  differ;
- `dead-read`: a read of a transient after `persistent!` does not throw;
- `structure`: a CHAMP invariant (`check_champ`, buffer counts, `size`);
- `aliasing`: an object owned by a live transient is reachable from another live value or twice,
  or a freed object is reachable.
-/

namespace Jank.R3.Immer.Maps

open Determinismo
open Jank.Equality (V)
open Objects

/-! ## Clojure -/

def cFindE (es : List (V × V)) (k : V) : Option (V × V) := es.find? fun e => cEq e.1 k
def cGet (es : List (V × V)) (k : V) : Option V := (cFindE es k).map (·.2)

def cAssoc (es : List (V × V)) (k v : V) : List (V × V) :=
  match es.findIdx? (fun e => cEq e.1 k) with
  | some i => es.set i ((es.getD i (k, v)).1, v)
  | none => es ++ [(k, v)]

def cDissoc (es : List (V × V)) (k : V) : List (V × V) := es.filter fun e => !cEq e.1 k

/-- APersistentMap.equiv. -/
def cMapEq (a b : List (V × V)) : Bool :=
  a.length == b.length && a.all fun (k, v) => match cGet b k with | some w => cEq v w | none => false

/-- APersistentSet.equiv (`setEquals`): same count, each element of one contained in the other. -/
def cSetEq (a b : List (V × V)) : Bool := a.length == b.length && a.all fun (k, _) => (cFindE b k).isSome

/-- Multiset equality, structurally (`BEq V` tells a vector from a list). -/
def sameMultiset {β : Type} [BEq β] (a b : List β) : Bool :=
  a.length == b.length && a.all fun x => a.count x == b.count x

def showEntries (es : List (V × V)) : String :=
  "{" ++ ", ".intercalate (es.map fun (k, v) => s!"{k.code} {v.code}") ++ "}"

def showSet (es : List (V × V)) : String := "#{" ++ " ".intercalate (es.map fun (k, _) => k.code) ++ "}"

/-! ## Aliasing -/

/-- Objects reachable from live values; `owners`: (token, objects reached from that transient). -/
def aliasing (persistents : List (List (Nat × Nat))) (owners : List (Nat × List (Nat × Nat)))
    (freed : List Nat) : Option String := Id.run do
  let all := persistents.flatten ++ owners.flatMap (·.2)
  for (id, _) in all do
    if freed.contains id then return some s!"object {id} was freed (GC_free) and is still reachable"
  for (e, mine) in owners do
    for (id, tok) in mine do
      if tok == e then
        let n := all.countP (·.1 == id)
        if n != 1 then
          return some s!"object {id}, owned by a live transient's token {e}, is reachable {n} times"
  return none

/-! ## The map world -/

inductive Op where
  | assoc | dissoc | transient | assocBang | dissocBang | persistentBang | deadRead | hashMap
  deriving BEq, Repr

structure CT where
  es : List (V × V)
  active : Bool := true

instance : Inhabited CT := ⟨{ es := [] }⟩

structure Cfg where
  keys : List V
  vals : List V := [.int 0, .int 1]
  ops : List Op
  steps : Nat
  /-- name, entries, built as a hash map (`hash-map`) or an array map (`{...}` / `(into {} ...)`). -/
  starts : List (String × List (V × V) × Bool)
  aside : List String := []
  /-- check `=`/`hash` across every pair of live maps (quadratic). -/
  pairs : Bool := true

structure World where
  decisions : Decisions := {}
  al : Champ.Al := {}
  maps : Array (JMap × List (V × V)) := #[]
  trs : Array (TMap × CT) := #[]
  story : Array String := #[]

instance : Chaotic World where
  decisions w := w.decisions
  setDecisions w d := { w with decisions := d }

abbrev W := EStateM Stop World

def runM {β : Type} (m : Champ.M β) : W β := do
  let w ← get
  let (x, al) := m.run w.al
  set { w with al := al }
  pure x

def say (line : String) : W Unit := modify fun w => { w with story := w.story.push line }

def storyText (w : World) : String := "; ".intercalate w.story.toList

def flag (cfg : Cfg) (cls : String) (detail : String) : W Unit := do
  if cfg.aside.contains cls then return
  let w ← get
  violate cls s!"{storyText w} ⇒ {detail}"

/-- Build an array map as `(into {} ...)` would, or a hash map as `hash-map`. -/
def build (es : List (V × V)) (hash : Bool) : Champ.M JMap := do
  if hash then JMap.fromPairs es
  else
    let mut m : JMap := .array []
    for (k, v) in es do
      m ← m.assoc k v
    pure m

def start (cfg : Cfg) (decisions : Decisions) : World := Id.run do
  let mut w : World := { decisions }
  for (name, es, hash) in cfg.starts do
    let (m, al) := (build es hash).run w.al
    let ce := es.foldl (fun acc (k, v) => cAssoc acc k v) []
    w := { w with al, maps := w.maps.push (m, ce),
                  story := w.story.push s!"(def m{w.maps.size} {name})" }
  return w

/-- Every check on every live value. -/
def check (cfg : Cfg) : W Unit := do
  let w ← get
  -- maps
  for i in [0:w.maps.size] do
    let (m, ce) := w.maps[i]!
    let nm := s!"m{i}"
    if m.count != ce.length then
      flag cfg "count" s!"(count {nm}) jank {m.count}, Clojure {ce.length}"
    for k in cfg.keys do
      let j := m.get k
      let c := cGet ce k
      if j != c then
        flag cfg "get" s!"(get {nm} {k.code}) jank {(j.getD .nil).code}{if j.isNone then " (absent)" else ""}, Clojure {(c.getD .nil).code}{if c.isNone then " (absent)" else ""}"
      match m.find k, cFindE ce k with
      | some (jk, _), some (ck, _) =>
        if !(jk == ck) then flag cfg "find-key" s!"(key (find {nm} {k.code})) jank {jk.code}, Clojure {ck.code}"
      | _, _ => pure ()
    match m with
    | .hash c =>
      if !(c.checkChamp mapCfg && Champ.wfNode 13 c.root && c.toList.length == c.size) then
        flag cfg "structure" s!"{nm}: CHAMP invariant broken"
    | _ => pure ()
    let je := m.entries
    if !sameMultiset je ce then
      let lookupsAgree := je.length == ce.length && ce.all fun (k, v) => m.get k == some v
      flag cfg (if lookupsAgree then "key-identity" else "entries")
        s!"{nm} jank {showEntries je}, Clojure {showEntries ce}"
  -- live transients agree with Clojure's
  for j in [0:w.trs.size] do
    let (t, ct) := w.trs[j]!
    if t.active then
      if t.count' != ct.es.length then
        flag cfg "count" s!"(count t{j}) jank {t.count'}, Clojure {ct.es.length}"
      for k in cfg.keys do
        if t.lookup k != cGet ct.es k then
          flag cfg "get" s!"(get t{j} {k.code}) jank {((t.lookup k).getD .nil).code}, Clojure {((cGet ct.es k).getD .nil).code}"
  -- pairs
  if cfg.pairs then
    for i in [0:w.maps.size] do
      for i' in [0:w.maps.size] do
        if i != i' then
          let (a, ca) := w.maps[i]!
          let (b, cb) := w.maps[i']!
          let je := a.equal b
          let je' := b.equal a
          let ce := cMapEq ca cb
          if je != je' then
            flag cfg "=-asymmetric" s!"(= m{i} m{i'}) jank {je} but (= m{i'} m{i}) jank {je'}; Clojure {ce} (m{i} = {showEntries a.entries}, m{i'} = {showEntries b.entries})"
          if je != ce then
            flag cfg "=" s!"(= m{i} m{i'}) jank {je}, Clojure {ce} (m{i} = {showEntries a.entries}, m{i'} = {showEntries b.entries})"
          if je && a.hashOf != b.hashOf then
            flag cfg "hash" s!"(= m{i} m{i'}) but (hash m{i}) = {a.hashOf}, (hash m{i'}) = {b.hashOf}"
  -- aliasing
  let pers := w.maps.toList.filterMap fun (m, _) => match m with | .hash c => some c.reach | _ => none
  let owners := w.trs.toList.filterMap fun (t, _) =>
    if !t.active then none else match t.body with | .hash h => some (h.tok, h.champ.reach) | _ => none
  match aliasing pers owners w.al.freed with
  | some d => flag cfg "aliasing" d
  | none => pure ()

def pickKey (cfg : Cfg) (name : String) : W V := do
  pure (cfg.keys.getD (← decide name cfg.keys.length) .nil)

def pickVal (cfg : Cfg) : W V := do
  pure (cfg.vals.getD (← decide "val" cfg.vals.length) .nil)

def step (cfg : Cfg) : W Unit := do
  let op := cfg.ops.getD (← decide "op" cfg.ops.length) .assoc
  match op with
  | .assoc =>
    let i ← decide "map" (← get).maps.size
    let k ← pickKey cfg "key"
    let v ← pickVal cfg
    let (m, ce) := (← get).maps[i]!
    let m' ← runM (m.assoc k v)
    let n := (← get).maps.size
    modify fun w => { w with maps := w.maps.push (m', cAssoc ce k v) }
    say s!"(def m{n} (assoc m{i} {k.code} {v.code}))"
  | .dissoc =>
    let i ← decide "map" (← get).maps.size
    let k ← pickKey cfg "key"
    let (m, ce) := (← get).maps[i]!
    let m' ← runM (m.dissoc k)
    let n := (← get).maps.size
    modify fun w => { w with maps := w.maps.push (m', cDissoc ce k) }
    say s!"(def m{n} (dissoc m{i} {k.code}))"
  | .transient =>
    let i ← decide "map" (← get).maps.size
    let (m, ce) := (← get).maps[i]!
    let t ← runM m.toTransient
    let n := (← get).trs.size
    modify fun w => { w with trs := w.trs.push (t, { es := ce }) }
    say s!"(def t{n} (transient m{i}))"
  | .assocBang | .dissocBang =>
    let trs0 := (← get).trs
    let actives := (List.range trs0.size).filter fun j => (trs0[j]!).1.active
    if actives.isEmpty then return
    let j := actives.getD (← decide "transient" actives.length) 0
    let k ← pickKey cfg "key"
    let v ← if op == .assocBang then pickVal cfg else pure .nil
    let (t, ct) := (← get).trs[j]!
    let r ← runM (if op == .assocBang then t.assocBang k v else t.dissocBang k)
    match r with
    | .ok t' =>
      let ces := if op == .assocBang then cAssoc ct.es k v else cDissoc ct.es k
      modify fun w => { w with trs := w.trs.set! j (t', { ct with es := ces }) }
      say (if op == .assocBang then s!"(def t{j} (assoc! t{j} {k.code} {v.code}))"
           else s!"(def t{j} (dissoc! t{j} {k.code}))")
    | .throws _ => pure ()
  | .persistentBang =>
    let trs0 := (← get).trs
    let actives := (List.range trs0.size).filter fun j => (trs0[j]!).1.active
    if actives.isEmpty then return
    let j := actives.getD (← decide "transient" actives.length) 0
    let (t, ct) := (← get).trs[j]!
    match t.persistentBang with
    | .ok (m, t') =>
      let n := (← get).maps.size
      modify fun w => { w with maps := w.maps.push (m, ct.es), trs := w.trs.set! j (t', { ct with active := false }) }
      say s!"(def m{n} (persistent! t{j}))"
    | .throws _ => pure ()
  | .deadRead =>
    let trs0 := (← get).trs
    let dead := (List.range trs0.size).filter fun j => !(trs0[j]!).1.active
    if dead.isEmpty then return
    let j := dead.getD (← decide "transient" dead.length) 0
    let kind ← decide "read" 5
    let k ← pickKey cfg "key"
    let r : TRead := match kind with
      | 0 => .count | 1 => .get1 k | 2 => .get2 k (.kw "nf") | 3 => .contains k | _ => .find k
    let (t, _) := (← get).trs[j]!
    match t.read r with
    | .ok x => flag cfg "dead-read" s!"{r.code s!"t{j}"} after (persistent! t{j}): jank {x.code}, Clojure throws (IllegalAccessError: Transient used after persistent! call)"
    | .throws _ => pure ()
  | .hashMap =>
    let k1 ← pickKey cfg "key"
    let v1 ← pickVal cfg
    let k2 ← pickKey cfg "key2"
    let v2 ← pickVal cfg
    let m ← runM (JMap.fromPairs [(k1, v1), (k2, v2)])
    let n := (← get).maps.size
    modify fun w => { w with maps := w.maps.push (m, cAssoc (cAssoc [] k1 v1) k2 v2) }
    say s!"(def m{n} (hash-map {k1.code} {v1.code} {k2.code} {v2.code}))"

def body (cfg : Cfg) : W Unit := do
  check cfg
  for _ in [0:cfg.steps] do
    step cfg
    check cfg

def run (cfg : Cfg) (source : Source) : Ended :=
  match (body cfg).run (start cfg { source }) with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }

/-! ## The set world -/

inductive SOp where
  | conj | disj | transient | conjBang | disjBang | persistentBang | deadRead | hashSet
  deriving BEq, Repr

structure SCfg where
  keys : List V
  ops : List SOp
  steps : Nat
  starts : List (String × List V)
  aside : List String := []

structure SWorld where
  decisions : Decisions := {}
  al : Champ.Al := {}
  sets : Array (JSet × List (V × V)) := #[]
  trs : Array (TSet × CT) := #[]
  story : Array String := #[]

instance : Chaotic SWorld where
  decisions w := w.decisions
  setDecisions w d := { w with decisions := d }

abbrev SW := EStateM Stop SWorld

def srunM {β : Type} (m : Champ.M β) : SW β := do
  let w ← get
  let (x, al) := m.run w.al
  set { w with al := al }
  pure x

def ssay (line : String) : SW Unit := modify fun w => { w with story := w.story.push line }

def sflag (cfg : SCfg) (cls : String) (detail : String) : SW Unit := do
  if cfg.aside.contains cls then return
  let w ← get
  violate cls s!"{"; ".intercalate w.story.toList} ⇒ {detail}"

/-- Clojure's persistent `conj`: unchanged when present. -/
def csConj (es : List (V × V)) (x : V) : List (V × V) := if (cFindE es x).isSome then es else es ++ [(x, x)]

def sstart (cfg : SCfg) (decisions : Decisions) : SWorld := Id.run do
  let mut w : SWorld := { decisions }
  for (name, xs) in cfg.starts do
    let (s, al) := (JSet.fromList xs).run w.al
    w := { w with al, sets := w.sets.push (s, xs.foldl (fun acc x => cAssoc acc x x) []),
                  story := w.story.push s!"(def s{w.sets.size} {name})" }
  return w

def scheck (cfg : SCfg) : SW Unit := do
  let w ← get
  for i in [0:w.sets.size] do
    let (s, ce) := w.sets[i]!
    let nm := s!"s{i}"
    if s.size != ce.length then sflag cfg "count" s!"(count {nm}) jank {s.size}, Clojure {ce.length}"
    for k in cfg.keys do
      if s.contains k != (cFindE ce k).isSome then
        sflag cfg "contains" s!"(contains? {nm} {k.code}) jank {s.contains k}, Clojure {(cFindE ce k).isSome}"
      let j := s.call k
      let c := cGet ce k
      if j != c then
        sflag cfg "key-identity" s!"({nm} {k.code}) jank {(j.getD .nil).code}, Clojure {(c.getD .nil).code} (the element stored for that key)"
    if !(s.checkChamp setCfg && Champ.wfNode 13 s.root && s.toList.length == s.size) then
      sflag cfg "structure" s!"{nm}: CHAMP invariant broken"
    if !sameMultiset s.toList (ce.map (·.1)) then
      sflag cfg "key-identity" s!"(seq {nm}) jank {showSet (s.toList.map fun x => (x, x))}, Clojure {showSet ce}"
  for j in [0:w.trs.size] do
    let (t, ct) := w.trs[j]!
    if t.active then
      if t.t.champ.size != ct.es.length then
        sflag cfg "count" s!"(count ts{j}) jank {t.t.champ.size}, Clojure {ct.es.length}"
  for i in [0:w.sets.size] do
    for i' in [0:w.sets.size] do
      if i != i' then
        let (a, ca) := w.sets[i]!
        let (b, cb) := w.sets[i']!
        let je := a.equal b
        let ce := cSetEq ca cb
        if je != ce then sflag cfg "=" s!"(= s{i} s{i'}) jank {je}, Clojure {ce}"
        if je && a.hash != b.hash then sflag cfg "hash" s!"(= s{i} s{i'}) but hashes differ"
  let pers := w.sets.toList.map fun (s, _) => s.reach
  let owners := w.trs.toList.filterMap fun (t, _) => if t.active then some (t.t.tok, t.t.champ.reach) else none
  match aliasing pers owners w.al.freed with
  | some d => sflag cfg "aliasing" d
  | none => pure ()

def spickKey (cfg : SCfg) (name : String) : SW V := do
  pure (cfg.keys.getD (← decide name cfg.keys.length) .nil)

def sstep (cfg : SCfg) : SW Unit := do
  let op := cfg.ops.getD (← decide "op" cfg.ops.length) .conj
  match op with
  | .conj | .disj =>
    let i ← decide "set" (← get).sets.size
    let k ← spickKey cfg "key"
    let (s, ce) := (← get).sets[i]!
    let s' ← srunM (if op == .conj then s.conj k else s.disj k)
    let n := (← get).sets.size
    modify fun w => { w with sets := w.sets.push (s', if op == .conj then csConj ce k else cDissoc ce k) }
    ssay s!"(def s{n} ({if op == .conj then "conj" else "disj"} s{i} {k.code}))"
  | .transient =>
    let i ← decide "set" (← get).sets.size
    let (s, ce) := (← get).sets[i]!
    let t ← srunM s.toTransient
    let n := (← get).trs.size
    modify fun w => { w with trs := w.trs.push (t, { es := ce }) }
    ssay s!"(def ts{n} (transient s{i}))"
  | .conjBang | .disjBang =>
    let trs0 := (← get).trs
    let actives := (List.range trs0.size).filter fun j => (trs0[j]!).1.active
    if actives.isEmpty then return
    let j := actives.getD (← decide "transient" actives.length) 0
    let k ← spickKey cfg "key"
    let (t, ct) := (← get).trs[j]!
    match ← srunM (if op == .conjBang then t.conjBang k else t.disjBang k) with
    | .ok t' =>
      -- ATransientSet.conj: impl.assoc(val, val) (key kept, value replaced)
      let ces := if op == .conjBang then cAssoc ct.es k k else cDissoc ct.es k
      modify fun w => { w with trs := w.trs.set! j (t', { ct with es := ces }) }
      ssay s!"(def ts{j} ({if op == .conjBang then "conj!" else "disj!"} ts{j} {k.code}))"
    | .throws _ => pure ()
  | .persistentBang =>
    let trs0 := (← get).trs
    let actives := (List.range trs0.size).filter fun j => (trs0[j]!).1.active
    if actives.isEmpty then return
    let j := actives.getD (← decide "transient" actives.length) 0
    let (t, ct) := (← get).trs[j]!
    match ← srunM t.persistentBang with
    | .ok (s, t') =>
      let n := (← get).sets.size
      modify fun w => { w with sets := w.sets.push (s, ct.es), trs := w.trs.set! j (t', { ct with active := false }) }
      ssay s!"(def s{n} (persistent! ts{j}))"
    | .throws _ => pure ()
  | .deadRead =>
    let trs0 := (← get).trs
    let dead := (List.range trs0.size).filter fun j => !(trs0[j]!).1.active
    if dead.isEmpty then return
    let j := dead.getD (← decide "transient" dead.length) 0
    let kind ← decide "read" 4
    let k ← spickKey cfg "key"
    let r : TRead := match kind with
      | 0 => .count | 1 => .get1 k | 2 => .get2 k (.kw "nf") | _ => .contains k
    let (t, _) := (← get).trs[j]!
    match t.read r with
    | .ok x => sflag cfg "dead-read" s!"{r.code s!"ts{j}"} after persistent!: jank {x.code}, Clojure throws"
    | .throws _ => pure ()
  | .hashSet =>
    let k1 ← spickKey cfg "key"
    let k2 ← spickKey cfg "key2"
    let s ← srunM (JSet.fromList [k1, k2])
    let n := (← get).sets.size
    -- PersistentHashSet.create: a transient, `conj!` each (ATransientSet.conj: impl.assoc(x, x))
    modify fun w => { w with sets := w.sets.push (s, cAssoc (cAssoc [] k1 k1) k2 k2) }
    ssay s!"(def s{n} (hash-set {k1.code} {k2.code}))"

def sbody (cfg : SCfg) : SW Unit := do
  scheck cfg
  for _ in [0:cfg.steps] do
    sstep cfg
    scheck cfg

def srun (cfg : SCfg) (source : Source) : Ended :=
  match (sbody cfg).run (sstart cfg { source }) with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }

end Jank.R3.Immer.Maps
