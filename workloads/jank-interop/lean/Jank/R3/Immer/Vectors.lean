import Jank.R3.Immer.Objects
import Jank.R3.Immer.Maps

/-!
# The vector world: jank's vectors (over the rbts replica) beside Clojure's PersistentVector

Elements are naturals (a start of size `n` holds `0 .. n-1`; every added element is fresh), so a
misplaced or lost element shows. Clojure's spec: a vector is a list; `conj` appends, `assoc i`
sets (`i = count` appends, out of range throws), `pop` drops the last (empty throws), `subvec`
checks its bounds, `nth` checks its bounds; a transient used after `persistent!` throws; a
persistent vector never changes (no aliasing with a transient derived from it or from which it
came).

After every step, every live vector and active transient is checked: the replica's tree is well
formed (`Tree.wf`), its elements (`toList`), its iteration (`rbtree_iterator`) and `nth` at
boundary indices are Clojure's; objects owned by an active transient's token are reachable once
and from nothing else (`aliasing`). Big vectors (more than `fullLimit` elements) are checked at
boundary indices only.
-/

namespace Jank.R3.Immer.Vectors

open Determinismo
open Objects

inductive Op where
  | conj | assoc | pop | subvec | into | transient | conjBang | assocBang | popBang | persistentBang
  | deadRead
  deriving BEq, Repr

structure Cfg where
  /-- start sizes, each built by `(vec (range n))` (a transient, `persistent()`) or
  `(reduce conj [] (range n))` (persistent `push_back`). -/
  starts : List Nat
  ops : List Op
  steps : Nat
  aside : List String := []
  fullLimit : Nat := 2200
  /-- batch sizes for `pop!` repeated and `into`. -/
  batches : List Nat := [1, 31, 32, 33]

structure World where
  decisions : Decisions := {}
  next : Nat := Rbts.firstId
  fresh : Nat := 1000000
  vecs : Array (JVec × List Nat) := #[]
  trs : Array (TVec × List Nat) := #[]
  story : Array String := #[]

instance : Chaotic World where
  decisions w := w.decisions
  setDecisions w d := { w with decisions := d }

abbrev W := EStateM Stop World

def say (line : String) : W Unit := modify fun w => { w with story := w.story.push line }

def flag (cfg : Cfg) (cls detail : String) : W Unit := do
  if cfg.aside.contains cls then return
  let w ← get
  violate cls s!"{"; ".intercalate w.story.toList} ⇒ {detail}"

/-- `(vec (range n))`: persistent_vector::create → a `native_transient_vector`, `push_back` each,
`persistent()`. -/
def buildVec (k next : Nat) : JVec × Nat :=
  let (t, next) := (Rbts.Transient.empty next : Rbts.Transient Nat × Nat)
  let (t, next) := (List.range k).foldl (fun (acc : Rbts.Transient Nat × Nat) x => acc.1.pushBack x acc.2) (t, next)
  let (tree, _, next) := t.persistent next
  (tree, next)

/-- `(reduce conj [] (range n))`: persistent `push_back` each. -/
def buildConj (k next : Nat) : JVec × Nat :=
  (List.range k).foldl (fun (acc : JVec × Nat) x => acc.1.pushBack x acc.2) (Rbts.Tree.empty, next)

/-- Indices around the boundaries of a vector of `n` elements. -/
def boundaryIndices (n : Nat) : List Nat :=
  let tailOff := Rbts.tailOffset n
  let raw := [0, 1, 30, 31, 32, 33, 63, 64, 1023, 1024, 1025, 1055, 1056, 1057, 32767, 32768, 32799, 32800,
    tailOff, tailOff + 1, n - 1, n - 2, n - 32, n - 33]
  ((raw.filter (· < n)) ++ (if tailOff > 0 then [tailOff - 1] else [])).eraseDups

/-- The index choices of `assoc`/`assoc!`/`nth` for a vector of size `n` (`n` itself appends,
`n + 1` is out of bounds). -/
def indexChoices (n : Nat) : List Int :=
  let tailOff := Rbts.tailOffset n
  ([0, 31, 32, (n : Int) - 1, n, n + 1, tailOff, (tailOff : Int) - 1, 1024, -1]).eraseDups

def subvecChoices (n : Nat) : List (Int × Int) :=
  let tailOff := (Rbts.tailOffset n : Int)
  [(0, n), (1, n), (0, (n : Int) - 1), (32, 64), (tailOff - 1, n), ((n : Int) - 33, n), (0, 1057), (5, 5)]

def checkVec (cfg : Cfg) (name : String) (v : JVec) (spec : List Nat) : W Unit := do
  if v.size != spec.length then flag cfg "count" s!"(count {name}) jank {v.size}, Clojure {spec.length}"
  if !v.wf then flag cfg "structure" s!"{name}: the rbtree is not well formed (size {v.size}, shift {v.shift})"
  if spec.length ≤ cfg.fullLimit then
    if v.toList != spec then flag cfg "elements" s!"{name}: elements differ from Clojure's (size {spec.length})"
    if v.iter != spec.map some then flag cfg "iteration" s!"(seq {name}) differs from Clojure's (size {spec.length})"
  for i in boundaryIndices spec.length do
    let j := v.get i
    let c := spec[i]?
    if j != c then flag cfg "nth" s!"(nth {name} {i}) jank {j}, Clojure {c}"
    let it := (v.arrayFor i).bind (·[Rbts.lIndex i]?)
    if it != c then flag cfg "iteration" s!"element {i} of (seq {name}) jank {it}, Clojure {c}"

def check (cfg : Cfg) : W Unit := do
  let w ← get
  for i in [0:w.vecs.size] do
    let (v, spec) := w.vecs[i]!
    checkVec cfg s!"v{i}" v spec
  for j in [0:w.trs.size] do
    let (t, spec) := w.trs[j]!
    if t.active then checkVec cfg s!"t{j}" t.t.tree spec
  let pers := w.vecs.toList.map fun (v, _) => v.reach
  let owners := w.trs.toList.filterMap fun (t, _) => if t.active then some (t.t.tok, t.t.tree.reach) else none
  match Maps.aliasing pers owners [] with
  | some d => flag cfg "aliasing" d
  | none => pure ()

def freshVal : W Nat := modifyGet fun w => (w.fresh, { w with fresh := w.fresh + 1 })

def withNext {β : Type} (f : Nat → β × Nat) : W β := do
  let w ← get
  let (x, n) := f w.next
  set { w with next := n }
  pure x

def pushVec (v : JVec) (spec : List Nat) (line : String) : W Unit := do
  let n := (← get).vecs.size
  modify fun w => { w with vecs := w.vecs.push (v, spec) }
  say s!"(def v{n} {line})"

def actives : W (List Nat) := do
  let trs := (← get).trs
  pure ((List.range trs.size).filter fun j => (trs[j]!).1.active)

def clojureAssoc (spec : List Nat) (i : Int) (x : Nat) : Option (List Nat) :=
  if i < 0 || i > spec.length then none
  else if i.toNat == spec.length then some (spec ++ [x]) else some (spec.set i.toNat x)

def step (cfg : Cfg) : W Unit := do
  let op := cfg.ops.getD (← decide "op" cfg.ops.length) .conj
  match op with
  | .conj =>
    let i ← decide "vec" (← get).vecs.size
    let (v, spec) := (← get).vecs[i]!
    let x ← freshVal
    let v' ← withNext (v.pushBack x)
    pushVec v' (spec ++ [x]) s!"(conj v{i} {x})"
  | .assoc =>
    let i ← decide "vec" (← get).vecs.size
    let (v, spec) := (← get).vecs[i]!
    let ch := indexChoices spec.length
    let idx := ch.getD (← decide "index" ch.length) 0
    let x ← freshVal
    let r ← withNext (vecAssoc v idx x)
    match r, clojureAssoc spec idx x with
    | .ok v', some s => pushVec v' s s!"(assoc v{i} {idx} {x})"
    | .throws _, none => pure ()
    | .ok _, none => flag cfg "assoc" s!"(assoc v{i} {idx} {x}) jank returns, Clojure throws"
    | .throws _, some _ => flag cfg "assoc" s!"(assoc v{i} {idx} {x}) jank throws, Clojure returns"
  | .pop =>
    let i ← decide "vec" (← get).vecs.size
    let (v, spec) := (← get).vecs[i]!
    match ← withNext (vecPop v) with
    | .ok v' => pushVec v' (spec.take (spec.length - 1)) s!"(pop v{i})"
    | .throws _ => if spec.length != 0 then flag cfg "pop" s!"(pop v{i}) jank throws"
  | .subvec =>
    let i ← decide "vec" (← get).vecs.size
    let (v, spec) := (← get).vecs[i]!
    let ch := subvecChoices spec.length
    let (s, e) := ch.getD (← decide "range" ch.length) (0, 0)
    let cOk := !(e < s || s < 0 || e > spec.length)
    match ← withNext (vecSubvec v s e), cOk with
    | .ok v', true => pushVec v' ((spec.drop s.toNat).take (e - s).toNat) s!"(subvec v{i} {s} {e})"
    | .throws _, false => pure ()
    | _, _ => flag cfg "subvec" s!"(subvec v{i} {s} {e}): jank and Clojure disagree on throwing"
  | .into =>
    let i ← decide "vec" (← get).vecs.size
    let (v, spec) := (← get).vecs[i]!
    let k := cfg.batches.getD (← decide "batch" cfg.batches.length) 1
    -- `(into v (range ...))`: transient, conj! each, persistent!
    let base := (← get).fresh
    modify fun w => { w with fresh := w.fresh + k }
    let xs := (List.range k).map (base + ·)
    let (t, n) := vecTransient v (← get).next
    let (t, n) := xs.foldl (fun (acc : TVec × Nat) x => match acc.1.conjBang x acc.2 with
      | (.ok u, n) => (u, n) | (.throws _, n) => (acc.1, n)) (t, n)
    match t.persistentBang n with
    | (.ok (v', _), n) =>
      modify fun w => { w with next := n }
      pushVec v' (spec ++ xs) s!"(into v{i} (range {base} {base + k}))"
    | (.throws _, n) => modify fun w => { w with next := n }
  | .transient =>
    let i ← decide "vec" (← get).vecs.size
    let (v, spec) := (← get).vecs[i]!
    let t ← withNext (vecTransient v)
    let n := (← get).trs.size
    modify fun w => { w with trs := w.trs.push (t, spec) }
    say s!"(def t{n} (transient v{i}))"
  | .conjBang | .assocBang | .popBang =>
    let as ← actives
    if as.isEmpty then return
    let j := as.getD (← decide "transient" as.length) 0
    let (t, spec) := (← get).trs[j]!
    match op with
    | .conjBang =>
      let x ← freshVal
      match ← withNext (t.conjBang x) with
      | .ok t' =>
        modify fun w => { w with trs := w.trs.set! j (t', spec ++ [x]) }
        say s!"(conj! t{j} {x})"
      | .throws _ => pure ()
    | .assocBang =>
      let ch := indexChoices spec.length
      let idx := ch.getD (← decide "index" ch.length) 0
      let x ← freshVal
      match ← withNext (t.assocBang idx x), clojureAssoc spec idx x with
      | .ok t', some s =>
        modify fun w => { w with trs := w.trs.set! j (t', s) }
        say s!"(assoc! t{j} {idx} {x})"
      | .throws _, none => pure ()
      | _, _ => flag cfg "assoc" s!"(assoc! t{j} {idx} {x}): jank and Clojure disagree on throwing"
    | _ =>
      let k := cfg.batches.getD (← decide "batch" cfg.batches.length) 1
      let k := min k spec.length
      let mut t := t
      for _ in [0:k] do
        match ← withNext t.popBang with
        | .ok t' => t := t'
        | .throws _ => flag cfg "pop" s!"(pop! t{j}) jank throws"
      modify fun w => { w with trs := w.trs.set! j (t, spec.take (spec.length - k)) }
      say s!"(dotimes [_ {k}] (pop! t{j}))"
  | .persistentBang =>
    let as ← actives
    if as.isEmpty then return
    let j := as.getD (← decide "transient" as.length) 0
    let (t, spec) := (← get).trs[j]!
    match ← withNext t.persistentBang with
    | .ok (v, t') =>
      modify fun w => { w with trs := w.trs.set! j (t', spec) }
      pushVec v spec s!"(persistent! t{j})"
    | .throws _ => pure ()
  | .deadRead =>
    let trs := (← get).trs
    let dead := (List.range trs.size).filter fun j => !(trs[j]!).1.active
    if dead.isEmpty then return
    let j := dead.getD (← decide "transient" dead.length) 0
    let (t, _) := trs[j]!
    match t.nth 0, t.count with
    | .throws _, .throws _ => pure ()
    | _, _ => flag cfg "dead-read" s!"(nth t{j} 0) / (count t{j}) after persistent! do not throw"

/-- Start vectors are built once per size and builder (closed terms are evaluated once). -/
def startVec (k : Nat) (byConj : Bool) : JVec × Nat := if byConj then buildConj k Rbts.firstId else buildVec k Rbts.firstId

def body (cfg : Cfg) (cache : Array (JVec × Nat)) : W Unit := do
  let si ← decide "start" cfg.starts.length
  let byConj ← decide "build" 2
  let k := cfg.starts.getD si 0
  let (v, n) := cache.getD (2 * si + byConj) (Rbts.Tree.empty, Rbts.firstId)
  modify fun w => { w with next := n }
  pushVec v (List.range k) (if byConj == 1 then s!"(reduce conj [] (range {k}))" else s!"(vec (range {k}))")
  check cfg
  for _ in [0:cfg.steps] do
    step cfg
    check cfg

def mkCache (cfg : Cfg) : Array (JVec × Nat) :=
  (cfg.starts.flatMap fun k => [startVec k false, startVec k true]).toArray

def run (cfg : Cfg) (cache : Array (JVec × Nat)) (source : Source) : Ended :=
  match (body cfg cache).run { decisions := { source } } with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }
  | .error (.nodeDown _) w => { taken := w.decisions.taken, violation := none }

end Jank.R3.Immer.Vectors
