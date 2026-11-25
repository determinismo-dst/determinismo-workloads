import Determinismo

/-!
# Round 4, Runtime: thread bindings as user code sees them

Replicated (upstream-main/compiler+runtime at 7135b7708):

- core.jank `push-thread-bindings` 2766-2780 → core.cpp `push_thread_bindings` 764-767 →
  context.cpp `push_thread_bindings(object_ref)` 693-702: **only a `persistent_hash_map`** is
  accepted ("invalid thread binding map (must be hash map)"); a map literal of up to 8 entries
  is a `persistent_array_map`; `expect_ok()` throws the error (jtl result.hpp 42-67);
- context.cpp `push_thread_bindings(hash_map)` 704-747: the new frame starts from the current
  frame's bindings; each var must be dynamic (else an error, after `thread_bound` was set on the
  vars before it); each value is boxed in a `var_thread_binding` (an unwrapped one when the value
  already is one); the frame is pushed in front;
- context.cpp `pop_thread_bindings` 749-760: with no frame, returns silently;
- context.cpp `get_thread_bindings` 762-772: **the front frame's map itself**, whose values are
  the `var_thread_binding` boxes; var.hpp 155-171 / var.cpp 322-343: a box prints as its value
  and hashes as its value, but has no `equal` (object.cpp 47-50: identity), so `(= 1 box)` is
  false;
- core.cpp future 1091-1170: the future's thread pushes the creator's bindings as one frame
  (1093, 1126).

Clojure 1.12 (clojure-ref Var.java): `pushThreadBindings(Associative)` takes any map;
`popThreadBindings` throws `IllegalStateException("Pop without matching push")` when the frame has
no `prev`; `getThreadBindings` builds a map from each var to its `TBox`'s `val`; `future`'s
`binding-conveyor-fn` installs a clone of the creator's frame whose `prev` is null.

The world: one dynamic var `*x*` (root 0), one thread (or a future's thread started with the
creator's bindings), programs of the operations below.
-/

namespace Jank.R4.Runtime.Bindings4

open Determinismo

inductive Op where
  /-- `(push-thread-bindings {#'*x* n})` (array map literal) -/
  | pushArray (n : Nat)
  /-- `(push-thread-bindings (hash-map #'*x* n))` -/
  | pushHash (n : Nat)
  /-- `(pop-thread-bindings)` -/
  | pop
  /-- `*x*` -/
  | deref
  /-- `(= *x* (get (get-thread-bindings) #'*x* *x*))` -/
  | getTB
  /-- `(count (get-thread-bindings))` -/
  | countTB
  deriving BEq, Repr, Inhabited

def Op.clj : Op → String
  | .pushArray n => s!"(push-thread-bindings \{#'*x* {n}})"
  | .pushHash n => s!"(push-thread-bindings (hash-map #'*x* {n}))"
  | .pop => "(pop-thread-bindings)"
  | .deref => "*x*"
  | .getTB => "(= *x* (get (get-thread-bindings) #'*x* *x*))"
  | .countTB => "(count (get-thread-bindings))"

inductive Obs where
  | ok | threw (w : String) | val (n : Nat) | bool (b : Bool)
  deriving BEq, DecidableEq, Repr, Inhabited

def Obs.show : Obs → String
  | .ok => "ok" | .threw w => s!"throws ({w})" | .val n => toString n | .bool b => toString b

/-- A binding of *x* in a frame: jank keeps the box, so the map's value is the box. -/
structure Frame where
  /-- the bound value, if the frame binds *x* -/
  x : Option Nat
  deriving BEq, DecidableEq, Repr, Inhabited

/-- jank: the front frame is the head; Clojure: frames are `prev`-linked, the head the current. -/
structure St where
  frames : List Frame
  deriving BEq, Repr, Inhabited

def bound (s : St) : Option Nat := match s.frames with | f :: _ => f.x | [] => none

/-- jank, context.cpp 693-772. -/
def stepJ (s : St) : Op → Obs × St
  | .pushArray _ => (.threw "invalid thread binding map (must be hash map)", s)
  | .pushHash n => (.ok, { frames := { x := some n } :: s.frames })
  | .pop => (.ok, { frames := s.frames.drop 1 })
  | .deref => (.val ((bound s).getD 0), s)
  | .getTB =>
    -- the map's value is the var_thread_binding box: (= value box) is false; with no binding the
    -- default *x* is returned and = holds
    match bound s with
    | some _ => (.bool false, s)
    | none => (.bool true, s)
  | .countTB => (.val (if (bound s).isSome then 1 else 0), s)

/-- Clojure, Var.java. `base` = the number of frames that have no prev below them (1 for the
TOP frame or a conveyed clone: popping it throws). -/
def stepC (s : St) : Op → Obs × St
  | .pushArray n | .pushHash n => (.ok, { frames := { x := some n } :: s.frames })
  | .pop =>
    match s.frames with
    | [_] | [] => (.threw "Pop without matching push", s)
    | _ :: rest => (.ok, { frames := rest })
  | .deref => (.val ((bound s).getD 0), s)
  | .getTB => (.bool true, s)
  | .countTB => (.val (if (bound s).isSome then 1 else 0), s)

/-- Start states: the main thread (jank: no frame; Clojure: the TOP frame), or a future's thread
started with the creator's bindings (jank: one pushed frame; Clojure: a clone with no prev). -/
def startJ (inFuture : Bool) (creator : Option Nat) : St :=
  if inFuture then { frames := [{ x := creator }] } else { frames := [] }
def startC (inFuture : Bool) (creator : Option Nat) : St :=
  if inFuture then { frames := [{ x := creator }] } else { frames := [{ x := none }] }

def run (j : Bool) (inFuture : Bool) (creator : Option Nat) (p : List Op) : List Obs := Id.run do
  let mut s := if j then startJ inFuture creator else startC inFuture creator
  let mut out : List Obs := []
  for op in p do
    let (o, s') := if j then stepJ s op else stepC s op
    out := out ++ [o]
    -- an exception ends the program
    if (match o with | .threw _ => true | _ => false) then break
    s := s'
  return out

def ops : List Op := [.pushArray 1, .pushHash 1, .pushHash 2, .pop, .deref, .getTB, .countTB]

structure G where
  decisions : Decisions := {}
  deriving Inhabited

instance : Chaotic G where
  decisions g := g.decisions
  setDecisions g d := { g with decisions := d }

def gen (n : Nat) : EStateM Stop G (Bool × Option Nat × List Op) := do
  let fut ← decide (σ := G) "thread.future" 2
  let cr ← if fut == 1 then (do let c ← decide (σ := G) "future.creator-binding" 2; pure (if c == 1 then some 5 else none)) else pure none
  let len ← decide (σ := G) "prog.len" n
  let mut p : List Op := []
  for _ in [0:len + 1] do
    let k ← decide (σ := G) "prog.op" ops.length
    p := p ++ [ops.getD k .deref]
  return (fut == 1, cr, p)

def classify (p : List Op) (j c : List Obs) : String := Id.run do
  let mut i := 0
  for op in p do
    if j[i]? != c[i]? then
      return match op with
        | .pushArray _ => "push-thread-bindings rejects an array map"
        | .pop => "pop-thread-bindings without a matching push"
        | .getTB => "get-thread-bindings holds var_thread_binding boxes, not values"
        | _ => s!"{op.clj} differs"
    i := i + 1
  return "length differs"

def runOne (n : Nat) (aside : List String) (source : Source) : Ended :=
  match (gen n).run { decisions := { source, limit := 1000 } } with
  | .ok (fut, cr, p) g =>
    let j := run true fut cr p
    let c := run false fut cr p
    if j == c then { taken := g.decisions.taken, violation := none }
    else
      let cls := classify p j c
      if aside.contains cls then { taken := g.decisions.taken, violation := none }
      else { taken := g.decisions.taken, violation := some (cls,
        s!"{if fut then s!"in a future (creator binding {cr})" else "main thread"}: {String.intercalate " " (p.map (·.clj))}: jank {String.intercalate ", " (j.map (·.show))}; Clojure {String.intercalate ", " (c.map (·.show))}") }
  | .error _ g => { taken := g.decisions.taken, violation := none }

/-! ## Theorems (for every frame stack) -/

/-- Whenever *x* is thread-bound, jank's `(get (get-thread-bindings) #'*x*)` is not `=` to `*x*`
(it is the box); Clojure's is. -/
theorem getTB_bound_differs (s : St) (n : Nat) (h : bound s = some n) :
    (stepJ s .getTB).1 = .bool false ∧ (stepC s .getTB).1 = .bool true := by
  simp [stepJ, stepC, h]

/-- An array map is rejected by jank for every value and every frame stack; Clojure pushes it. -/
theorem pushArray_rejected (s : St) (n : Nat) :
    (∃ w, (stepJ s (.pushArray n)).1 = .threw w) ∧ (stepC s (.pushArray n)).1 = .ok := by
  simp [stepJ, stepC]

/-- In a future's thread (one conveyed frame), the first pop throws in Clojure and succeeds in
jank, whatever the creator bound. -/
theorem future_pop (cr : Option Nat) :
    (stepJ (startJ true cr) .pop).1 = .ok ∧ ∃ w, (stepC (startC true cr) .pop).1 = .threw w := by
  simp [stepJ, stepC, startJ, startC]

end Jank.R4.Runtime.Bindings4
