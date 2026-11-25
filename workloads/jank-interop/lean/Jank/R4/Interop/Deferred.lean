import Determinismo

/-!
# Round 4: lazily compiled functions (`deferred_cpp_function`)

jank's default eagerness is lazy (util/cli.hpp 141 `compilation_eagerness::lazy`; `--eager` opts
out, cli.cpp 135-139). evaluate.cpp `eval(function)` (522-554) then does not compile a top-level
fn: it boxes a `deferred_cpp_function` holding the generated C++ and `current_def_var`, the var a
`def`/`defn` is binding (evaluate.cpp 327-358 sets it only while evaluating a def's fn value).

`deferred_cpp_function::realize` (runtime/obj/deferred_cpp_function.cpp 45-73), run on the first
call of *that object*, compiles the code, creates the real function and then
`var->bind_root(compiled_fn)` — whatever the var holds by then. So calling an old function object
(captured before its var was redefined, `alter-var-root`ed or `with-redefs`ed) puts that old
function back into the var.

Clojure: a fn is a value; calling one never changes a var (`Var.bindRoot` only from `def`,
`alter-var-root`, `with-redefs`, …).

The replica: vars hold objects; `defn` makes a deferred object owned by its var; `def g f` copies
the root; `alter` sets a root to an already compiled fn; a call through a var derefs it and calls
the object, realizing a deferred one.
-/

namespace Jank.R4.Interop.Deferred

open Determinismo

inductive Obj where
  /-- A compiled fn returning `ret`. -/
  | fn (ret : Nat)
  /-- A deferred fn object `id` returning `ret`. -/
  | deferred (id : Nat) (ret : Nat)
  | unbound
  deriving Repr, BEq, Inhabited

structure St where
  roots : List (String × Obj) := []
  /-- deferred id → (owning var, realized?) -/
  deferreds : List (Nat × String × Bool) := []
  next : Nat := 0
  deriving Inhabited

def St.root (s : St) (v : String) : Obj := (s.roots.lookup v).getD .unbound
def St.setRoot (s : St) (v : String) (o : Obj) : St :=
  { s with roots := (v, o) :: s.roots.filter (·.1 != v) }

inductive Op where
  /-- `(defn v [] ret)` at the top level. -/
  | defn (v : String) (ret : Nat)
  /-- `(def v w)`. -/
  | alias (v w : String)
  /-- `(v)`: a call through the var. -/
  | call (v : String)
  /-- `(alter-var-root #'v (fn [_] (fn [] ret)))`: the new root is created by compiled code. -/
  | alter (v : String) (ret : Nat)
  deriving Repr, BEq, Inhabited

def Op.text : Op → String
  | .defn v r => s!"(defn {v} [] {r})"
  | .alias v w => s!"(def {v} {w})"
  | .call v => s!"({v})"
  | .alter v r => s!"(alter-var-root #'{v} (fn [_] (fn [] {r})))"

/-- jank. A call returns the value, or `none` (an unbound var). -/
def stepJank (s : St) : Op → St × Option Nat
  | .defn v r =>
    let d := s.next
    ({ (s.setRoot v (.deferred d r)) with deferreds := (d, v, false) :: s.deferreds, next := d + 1 }, none)
  | .alias v w => (s.setRoot v (s.root w), none)
  | .alter v r => (s.setRoot v (.fn r), none)
  | .call v =>
    match s.root v with
    | .fn r => (s, some r)
    | .deferred d r =>
      match s.deferreds.find? (·.1 == d) with
      | some (_, owner, false) =>
        -- realize: compile, `var->bind_root(compiled_fn)`, mark realized
        let s' := { (s.setRoot owner (.fn r)) with
          deferreds := s.deferreds.map fun e => if e.1 == d then (d, owner, true) else e }
        (s', some r)
      | _ => (s, some r)
    | .unbound => (s, none)

/-- Clojure: fns are values. -/
def stepClj (s : St) : Op → St × Option Nat
  | .defn v r => (s.setRoot v (.fn r), none)
  | .alias v w => (s.setRoot v (s.root w), none)
  | .alter v r => (s.setRoot v (.fn r), none)
  | .call v => match s.root v with
    | .fn r | .deferred _ r => (s, some r)
    | .unbound => (s, none)

def runBoth (ops : List Op) : List (Op × Option Nat × Option Nat) := Id.run do
  let mut j : St := {}
  let mut c : St := {}
  let mut out := []
  for op in ops do
    let (j', rj) := stepJank j op
    let (c', rc) := stepClj c op
    j := j'
    c := c'
    out := out ++ [(op, rj, rc)]
  return out

def opsUniverse : List Op :=
  [.defn "f" 1, .defn "f" 2, .alias "g" "f", .call "f", .call "g", .alter "f" 3]

/-- The world: a program of `n` top-level forms, each a decision. Property: every call returns
what Clojure's does. -/
structure W where
  decisions : Decisions := {}

instance : Chaotic W where
  decisions w := w.decisions
  setDecisions w d := { w with decisions := d }

def body (n : Nat) : EStateM Stop W Unit := do
  let mut ops : List Op := []
  for i in [0:n] do
    let o ← pick (σ := W) s!"deferred.op{i}" opsUniverse
    ops := ops ++ [o.getD (.call "f")]
  for (op, rj, rc) in runBoth ops do
    if rj != rc then
      violate (σ := W) "calling a fn object leaves every var alone"
        s!"{" ".intercalate (ops.map Op.text)}: at {op.text} Clojure {rc}, jank {rj}"

def run (n : Nat) (source : Source) : Ended :=
  match (body n).run { decisions := { source } } with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }
  | .error (.nodeDown _) w => { taken := w.decisions.taken, violation := none }

/-- In `--eager` mode `defn` compiles at once (`jit_prc.eval`): jank equals Clojure. -/
def stepEager (s : St) : Op → St × Option Nat := stepClj s

/-! ## Proofs -/

/-- A call through a var whose root is the object it realizes changes nothing visible: the root
becomes a compiled fn with the same result. -/
theorem realize_own_root_same_result (s : St) (v : String) (d r : Nat)
    (h : s.root v = .deferred d r) : (stepJank s (.call v)).2 = some r := by
  simp [stepJank, h]
  split <;> rfl

/-- The deviation at its source: after `(defn f [] 1) (def g f) (defn f [] 2) (g)`, `f`'s root is
the old function. -/
theorem old_object_rebinds_var :
    let s0 : St := {}
    let (s1, _) := stepJank s0 (.defn "f" 1)
    let (s2, _) := stepJank s1 (.alias "g" "f")
    let (s3, _) := stepJank s2 (.defn "f" 2)
    let (s4, _) := stepJank s3 (.call "g")
    (stepJank s4 (.call "f")).2 = some 1 ∧ (stepClj {} (.call "f")).2 = none := by
  decide

/-- Clojure's answer for the same program is 2. -/
theorem clojure_keeps_new_root :
    let s0 : St := {}
    let (s1, _) := stepClj s0 (.defn "f" 1)
    let (s2, _) := stepClj s1 (.alias "g" "f")
    let (s3, _) := stepClj s2 (.defn "f" 2)
    let (s4, _) := stepClj s3 (.call "g")
    (stepClj s4 (.call "f")).2 = some 2 := by
  decide

end Jank.R4.Interop.Deferred
