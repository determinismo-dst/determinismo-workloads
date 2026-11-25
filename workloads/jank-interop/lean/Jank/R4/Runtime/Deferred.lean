import Determinismo

/-!
# Round 4, Runtime: lazily compiled functions (deferred_cpp_function), replicated

jank evaluates a top-level form (REPL, nREPL, `jank run`, a module loaded from source) with the
interpreter in evaluate.cpp. A `fn` expression there is JIT-compiled, but by default lazily
(`util::cli::opts.eagerness` defaults to `compilation_eagerness::lazy`, include/cpp/jank/util/
cli.hpp 141; `--eager` / `--lazy` flags, util/cli.cpp 344-351; nothing in the book documents
it). Replicated, upstream-main/compiler+runtime at 7135b7708:

- evaluate.cpp `eval(def)` 333-362: when the value expression is a `fn` (every `defn`: core.jank
  727-800 expands to `(def name (fn name …))`), `current_def_var = var` before evaluating it;
- evaluate.cpp `eval(function)` 522-555: lazy: `make_box<deferred_cpp_function>(meta,
  current_def_var, generated.declaration, …)`, then `current_def_var = jank_nil`; eager: the
  JIT-compiled function itself;
- deferred_cpp_function.cpp `realize` 46-73, called by every `call` arity (75-198): under the
  recursive `compilation_mutex`, if nothing is compiled yet: compile the declaration
  (`jit_prc.eval_string`), `create_function`, `reset_meta`, and **`var->bind_root(compiled_fn)`**
  when the object knows its var (61-69); then the call goes to `compiled_fn`;
- var.cpp `bind_root` 98-104 and `alter_root` 106-112: both take the var's `write_mutex`
  (folly::SharedMutex, exclusive); `alter_root` holds it across `apply_to(f, root …)`;
- deferred_cpp_function.hpp 32-35: behaviors `call` only, no `with_meta`: core/meta.cpp
  `with_meta` 36-59 throws "can't hold any metadata" for it, and `meta` 13-34 gives nil; a
  `jit_function` has `with_meta` (jit_function.hpp 27);
- core.jank `with-redefs-fn` 4549-4566: `var_get_root` of each var, `var_bind_root` of the new
  values, the body, then `var_bind_root` of the old roots in a finally.

Clojure 1.12 (clojure-ref): `defn`'s fn is an ordinary `AFunction` (an `IObj`: `withMeta` works);
calling it never touches a var; `Var.alterRoot`/`bindRoot` are `synchronized` (reentrant).

The world: two vars `a` (0) and `b` (1), and programs of top-level forms and calls. Values are
recorded per object so that `identical?` can be compared.
-/

namespace Jank.R4.Runtime.Deferred

open Determinismo

inductive Fn where
  /-- a var with no root: its unbound root object -/
  | unbound (v : Nat)
  /-- jank: deferred_cpp_function of the k-th fn expression -/
  | deferred (k : Nat)
  /-- jank: the jit_function compiled from deferred k -/
  | compiled (k : Nat)
  /-- Clojure (and jank with --eager): the fn object of the k-th fn expression -/
  | plain (k : Nat)
  /-- `(fn [x] (+ 100 (orig x)))` made by the j-th form, capturing orig -/
  | wrap (j : Nat) (inner : Fn)
  /-- `(fn [] :stub)` made by the j-th form (a closure compiled with its parent) -/
  | stub (j : Nat)
  deriving BEq, Repr, Inhabited

inductive Mode | jankLazy | jankEager | clojure
  deriving BEq, Repr, Inhabited

/-- One deferred object's state: its var (current_def_var when it was made) and whether
`compiled_fn` is set. -/
structure DState where
  var : Option Nat
  compiled : Bool := false
  deriving BEq, Repr, Inhabited

structure St where
  mode : Mode
  roots : Array Fn := #[.unbound 0, .unbound 1]
  defs : Array DState := #[]
  /-- the var whose write_mutex the current thread holds (alter-var-root) -/
  held : Option Nat := none
  /-- the last time a first call rebound a var whose root was another object: what it was -/
  clobbered : Option String := none
  deriving Inhabited

inductive Obs where
  | val (n : Nat)
  | bool (b : Bool)
  | ok
  | threw (why : String)
  | hang (why : String)
  deriving BEq, DecidableEq, Repr, Inhabited

def Obs.show : Obs → String
  | .val n => toString n | .bool b => toString b | .ok => "ok"
  | .threw w => s!"throws ({w})" | .hang w => s!"hangs ({w})"

def Fn.kindStr : Fn → String
  | .unbound _ => "an unbound root" | .deferred _ => "another deferred fn (a redefinition)"
  | .compiled _ => "a compiled fn" | .plain _ => "a fn" | .wrap .. => "a wrapper (alter-var-root)"
  | .stub _ => "a with-redefs stub"

/-- A call's outcome: the value, or an exception, or a hang. -/
inductive R where
  | v (n : Nat)
  | ex (why : String)
  | hang (why : String)
  deriving Inhabited

/-- `deferred_cpp_function::realize` (46-73): compile once, then `var->bind_root(compiled_fn)`.
`bind_root` takes the var's write_mutex: if this thread already holds it (inside
`alter_root`), folly's non-reentrant lock() never returns (round 3's
`exclusive_reentry_blocked`). -/
def realize (s : St) (k : Nat) : Except String St :=
  let d := s.defs[k]!
  if d.compiled then .ok s
  else
    let s := { s with defs := s.defs.set! k { d with compiled := true } }
    match d.var with
    | none => .ok s
    | some u =>
      if s.held == some u then .error s!"bind_root of var {u} while alter_root holds its write_mutex"
      else
        let prev := s.roots[u]!
        let clob := if prev == .deferred k then s.clobbered else some prev.kindStr
        .ok { s with roots := s.roots.set! u (.compiled k), clobbered := clob }

/-- Call a fn value with one argument; a fn made by the k-th form returns k + 1. -/
def callFn (s : St) (f : Fn) : R × St :=
  match f with
  | .unbound v => (.ex s!"var {v} unbound", s)
  | .deferred k =>
    match realize s k with
    | .ok s' => (.v (k + 1), s')
    | .error why => (.hang why, s)
  | .compiled k | .plain k => (.v (k + 1), s)
  | .stub _ => (.v 999, s)
  | .wrap _ inner =>
    -- the wrapper is a closure: (+ 100 (orig x)); orig is the captured value
    match inner with
    | .wrap .. => (.v 0, s)  -- one level of wrapping in this world
    | _ =>
      let (r, s') := (match inner with
        | .unbound v => (R.ex s!"var {v} unbound", s)
        | .deferred k => match realize s k with
          | .ok s'' => (.v (k + 1), s'')
          | .error why => (.hang why, s)
        | .compiled k | .plain k => (.v (k + 1), s)
        | .stub _ => (.v 999, s)
        | .wrap .. => (.v 0, s))
      match r with
      | .v n => (.v (n + 100), s')
      | r => (r, s')

def obsOf : R → Obs
  | .v n => .val n
  | .ex w => .threw w
  | .hang w => .hang w

/-- The forms of the world. `j` numbers the form in the program (fn expressions get their own
numbers from it). -/
inductive Op where
  /-- `(defn v [x] …)`: a fn expression as a def's value -/
  | defn (v : Nat)
  /-- `(def v w)`: the value of w -/
  | defVal (v w : Nat)
  /-- `(v 1)` -/
  | call (v : Nat)
  /-- `(alter-var-root #'v (fn [orig] (fn [x] (+ 100 (orig x)))))` -/
  | alterWrap (v : Nat)
  /-- `(alter-var-root #'v (fn [g] (g 1) g))` -/
  | alterCall (v : Nat)
  /-- `(with-redefs [v (fn [] :stub)] [(w 1) (v 1)])` -/
  | redefsCall (v w : Nat)
  /-- `(with-meta v {:k 1})` -/
  | withMeta (v : Nat)
  /-- `(identical? v w)` -/
  | identical (v w : Nat)
  /-- `(nil? (meta v))` -/
  | metaNil (v : Nat)
  deriving BEq, Repr, Inhabited

def vn (v : Nat) : String := if v == 0 then "a" else "b"

def Op.clj : Op → String
  | .defn v => s!"(defn {vn v} [x] …)"
  | .defVal v w => s!"(def {vn v} {vn w})"
  | .call v => s!"({vn v} 1)"
  | .alterWrap v => s!"(alter-var-root #'{vn v} (fn [orig] (fn [x] (+ 100 (orig x)))))"
  | .alterCall v => s!"(alter-var-root #'{vn v} (fn [g] (g 1) g))"
  | .redefsCall v w => s!"(with-redefs [{vn v} (fn [_] :stub)] [({vn w} 1) ({vn v} 1)])"
  | .withMeta v => s!"(with-meta {vn v} \{:k 1})"
  | .identical v w => s!"(identical? {vn v} {vn w})"
  | .metaNil v => s!"(nil? (meta {vn v}))"

/-- One form, form number `j`. -/
def step (s : St) (j : Nat) (op : Op) : List Obs × St :=
  match op with
  | .defn v =>
    -- eval(def) → eval(function): lazy: a deferred object owning var v; eager / Clojure: the fn
    let k := s.defs.size
    let f : Fn := match s.mode with | .jankLazy => .deferred k | .jankEager => .compiled k | .clojure => .plain k
    let s := { s with defs := s.defs.push { var := some v, compiled := s.mode != Mode.jankLazy } }
    ([], { s with roots := s.roots.set! v f })
  | .defVal v w => ([], { s with roots := s.roots.set! v s.roots[w]! })
  | .call v =>
    let (r, s') := callFn s s.roots[v]!
    ([obsOf r], s')
  | .alterWrap v =>
    -- alter_root: write_mutex held across (f root); f returns the wrapper without calling orig
    ([], { s with roots := s.roots.set! v (.wrap j s.roots[v]!) })
  | .alterCall v =>
    -- alter_root holds v's write_mutex (jank) / v's monitor (Clojure, reentrant) across (f root);
    -- f calls (g 1), then returns g
    let g := s.roots[v]!
    let held := if s.mode == .clojure then none else some v
    let (r, s') := callFn { s with held } g
    match r with
    | .hang w => ([.hang w], s)
    | .ex w => ([.threw w], { s' with held := none })
    | .v _ => ([.ok], { s' with held := none, roots := s'.roots.set! v g })
  | .redefsCall v w =>
    -- with-redefs-fn: old roots read first, new roots bound, body, old roots bound in finally
    let old := s.roots[v]!
    let s1 := { s with roots := s.roots.set! v (.stub j) }
    let (r1, s2) := callFn s1 s1.roots[w]!
    let (r2, s3) := match r1 with
      | .v _ => callFn s2 s2.roots[v]!
      | r => (r, s2)
    let obs := match r1 with
      | .v _ => [obsOf r1, obsOf r2]
      | _ => [obsOf r1]
    match r1, r2 with
    | .hang _, _ | _, .hang _ => (obs, s3)
    | _, _ => (obs, { s3 with roots := s3.roots.set! v old })
  | .withMeta v =>
    match s.roots[v]! with
    | .deferred _ =>
      if s.mode == .jankLazy then ([.threw "can't hold any metadata"], s) else ([.ok], s)
    | .unbound _ => ([.threw "not metadatable"], s)
    | _ => ([.ok], s)
  | .identical v w => ([.bool (s.roots[v]! == s.roots[w]!)], s)
  | .metaNil v =>
    -- jank: a deferred object is not metadatable (meta.cpp 13-34: nil); the compiled fn got
    -- `reset_meta(compiled_fn, meta.get())`, the fn expression's `{:name "ns/f"}`
    -- (processor.cpp analyze_fn 2064-2067; evaluate.cpp 538, 552); closures made in compiled code
    -- carry none. Clojure: a fn made by fn* without a meta'd form has none.
    match s.roots[v]! with
    | .compiled _ => ([.bool false], s)
    | _ => ([.bool true], s)

/-- Run a program; stop at a hang. -/
def run (mode : Mode) (prog : List Op) : List Obs × St := Id.run do
  let mut s : St := { mode }
  let mut out : List Obs := []
  let mut j := 0
  for op in prog do
    let (o, s') := step s j op
    out := out ++ o
    s := s'
    j := j + 1
    if o.any (fun x => match x with | .hang _ => true | _ => false) then break
  return (out, s)

/-- The same runner by structural recursion (for kernel-evaluated examples). -/
def runFrom (s : St) (j : Nat) : List Op → List Obs × St
  | [] => ([], s)
  | op :: rest =>
    let (o, s') := step s j op
    if o.any (fun x => match x with | .hang _ => true | _ => false) then (o, s')
    else
      let (o2, s2) := runFrom s' (j + 1) rest
      (o ++ o2, s2)

def runK (mode : Mode) (prog : List Op) : List Obs := (runFrom { mode } 0 prog).1

/-! ## The world: every program of up to `n` forms -/

def ops : List Op :=
  [.defn 0, .defn 1, .defVal 0 1, .defVal 1 0, .call 0, .call 1, .alterWrap 0, .alterWrap 1,
   .alterCall 0, .alterCall 1, .redefsCall 0 1, .redefsCall 1 0, .redefsCall 0 0, .redefsCall 1 1,
   .withMeta 0, .withMeta 1, .identical 0 1, .metaNil 0, .metaNil 1]

structure G where
  decisions : Decisions := {}
  deriving Inhabited

instance : Chaotic G where
  decisions g := g.decisions
  setDecisions g d := { g with decisions := d }

abbrev GenM := EStateM Stop G

def gen (n : Nat) : GenM (List Op) := do
  let len ← decide (σ := G) "prog.len" n
  let mut p : List Op := []
  for _ in [0:len + 1] do
    let k ← decide (σ := G) "prog.op" ops.length
    p := p ++ [ops.getD k (.call 0)]
  return p

def describe (p : List Op) : String := String.intercalate " " (p.map (·.clj))

/-- The class of a disagreement: the first form whose observation differs, by kind, and (for a
call) what a first call clobbered. -/
def classify (p : List Op) (j c : List Obs) (sj : St) : String := Id.run do
  -- align forms with observations
  let mut i := 0
  let mut s : St := { mode := Mode.jankLazy }
  let mut jj := 0
  for op in p do
    let (o, s') := step s jj op
    let n := o.length
    let jo := (j.drop i).take n
    let co := (c.drop i).take n
    if jo != co then
      let kind := match op with
        | .call _ => "a call"
        | .redefsCall _ _ => "with-redefs"
        | .identical _ _ => "identical?"
        | .withMeta _ => "with-meta"
        | .alterCall _ => "alter-var-root calling its fn"
        | .alterWrap _ => "alter-var-root"
        | .metaNil _ => "meta"
        | _ => "other"
      let hang := jo.any (fun x => match x with | .hang _ => true | _ => false)
      if hang then return s!"{kind}: hangs (the first call's bind_root re-enters the write_mutex alter_root holds)"
      if kind == "with-meta" then return "with-meta of a fn not yet called throws"
      if kind == "meta" then return "meta of a called top-level fn is {:name …}"
      let what := (s'.clobbered.orElse (fun _ => s.clobbered)).getD "its own deferred object"
      return s!"{kind} differs: a first call rebound the var, whose root was {what}"
    i := i + n
    s := s'
    jj := jj + 1
  let _ := sj
  return "other"

/-- One timeline: generate a program, run it in jank (lazy or eager) and Clojure; a violation
when the observations differ (the class is the property), unless its class is set aside. -/
def runOne (n : Nat) (jmode : Mode) (aside : List String) (source : Source) : Ended :=
  match (gen n).run { decisions := { source, limit := 1000 } } with
  | .ok p g =>
    let (j, sj) := run jmode p
    let (c, _) := run .clojure p
    if j == c then { taken := g.decisions.taken, violation := none }
    else
      let cls := classify p j c sj
      if aside.any (fun a => (cls.splitOn a).length > 1) then { taken := g.decisions.taken, violation := none }
      else { taken := g.decisions.taken,
             violation := some (cls, s!"{describe p}: jank {String.intercalate ", " (j.map (·.show))}; Clojure {String.intercalate ", " (c.map (·.show))}") }
  | .error _ g => { taken := g.decisions.taken, violation := none }

/-! ## Theorems -/

/-- The mechanism, for every state: the first call of a deferred fn that knows its var leaves
that var holding the compiled fn, whatever the var held before (unless the thread holds its
write_mutex). -/
theorem realize_rebinds (s : St) (k u : Nat)
    (hv : (s.defs[k]!).var = some u) (hc : (s.defs[k]!).compiled = false) (hh : s.held = none) :
    ∃ s', realize s k = .ok s' ∧ s'.roots = s.roots.set! u (.compiled k) := by
  simp [realize, hc, hv, hh]

/-- Clojure's calls never change a var's root. -/
theorem clojure_call_keeps_roots (s : St) (f : Fn)
    (hd : ∀ k, f ≠ .deferred k) (hw : ∀ j k, f ≠ .wrap j (.deferred k)) :
    (callFn s f).2.roots = s.roots := by
  cases f with
  | unbound v => rfl
  | deferred k => exact absurd rfl (hd k)
  | compiled k => rfl
  | plain k => rfl
  | stub j => rfl
  | wrap j inner =>
    cases inner with
    | deferred k => exact absurd rfl (hw j k)
    | unbound v => rfl
    | compiled k => rfl
    | plain k => rfl
    | stub _ => rfl
    | wrap _ _ => rfl

/-- The hang, for every state: inside alter_root (the write_mutex of var u held), the first call of
a deferred fn owning u never returns. -/
theorem realize_inside_alter_hangs (s : St) (k u : Nat)
    (hv : (s.defs[k]!).var = some u) (hc : (s.defs[k]!).compiled = false) (hh : s.held = some u) :
    ∃ why, realize s k = .error why := by
  simp [realize, hc, hv, hh]

/-- Concrete witnesses (kernel-evaluated). The wrapper is lost after its first call: -/
example : (runK .jankLazy [.defn 0, .alterWrap 0, .call 0, .call 0]) = [.val 101, .val 1] := by decide +kernel
example : (runK .clojure [.defn 0, .alterWrap 0, .call 0, .call 0]) = [.val 101, .val 101] := by decide +kernel
/-- A redefinition is reverted by the first call of the old value: -/
example : (runK .jankLazy [.defn 0, .defVal 1 0, .defn 0, .call 1, .call 0]) = [.val 1, .val 1] := by decide +kernel
example : (runK .clojure [.defn 0, .defVal 1 0, .defn 0, .call 1, .call 0]) = [.val 1, .val 2] := by decide +kernel
/-- identical? changes at the first call: -/
example : (runK .jankLazy [.defn 0, .defVal 1 0, .call 0, .identical 0 1]) = [.val 1, .bool false] := by decide +kernel
example : (runK .clojure [.defn 0, .defVal 1 0, .call 0, .identical 0 1]) = [.val 1, .bool true] := by decide +kernel

end Jank.R4.Runtime.Deferred
