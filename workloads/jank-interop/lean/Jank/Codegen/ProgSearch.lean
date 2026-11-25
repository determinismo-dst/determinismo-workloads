import Jank.Codegen.Pipeline
import Determinismo

/-!
# Searching programs: jank's emitted program must mean what Clojure means

Programs are drawn by decisions (`Determinismo.decide`): small expression trees over `let`,
`loop`/`recur`, `if`, `do`, `fn` (named, closures, `recur`), calls (with effects in the operator
and the operands, logged by `user/log`), `def` with metadata, vars, `letfn`, `try`/`catch`/
`finally`, `case` on integers, vector literals; local names from a pool where distinct names
munge alike (`a-b`, `a_b`). Every drawn program is well formed (`recur` in tail position with the
target's arity, loops bounded).

Each program runs twice: Clojure's meaning (`Spec.run`) and jank's pipeline (`jankRun`: the
analyzer replica, IR, passes, C++ text, C++ compile check, C++ run). The property: same value,
same output, both throw, or neither compiles. `Config` picks the target (eval: JIT, the REPL and
`jank run`; module: AOT), the IR passes (`-O0`, `-O1`, `-O3`) and the runtime (dynamic, static).
-/

namespace Jank.Codegen.ProgSearch

open Jank.Codegen Jank.Analyzer Determinismo
open Jank.Codegen.Spec (Outcome)

structure W where
  decisions : Decisions := {}

instance : Chaotic W where
  decisions w := w.decisions
  setDecisions w d := { w with decisions := d }

abbrev G := EStateM Stop W

def kw (n : String) : Form := .lit (.keyword "" n)
def int (n : Int) : Form := .lit (Obj.ofInt n)

def names : List String := ["x", "a-b", "a_b", "y"]

/-- What a generated expression may use: locals in scope, the recur target's arity when in tail
position, the enclosing named fns. -/
structure Ctx where
  locals : List String := []
  /-- `some n`: tail position of a loop/fn with `n` bindings (recur allowed). -/
  recurArity : Option Nat := none
  fnNames : List String := []
  vars : List String := []
  inTry : Bool := false
  /-- Leave out the productions of the deviations already found (the control search). -/
  clean : Bool := false
  deriving Inhabited

def d (name : String) (n : Nat) : G Nat := decide (σ := W) name n

def pickName (name : String) (c : Ctx := {}) : G String := do
  pure ((← pick (σ := W) name (if c.clean then ["x", "y"] else names)).getD "x")

/-- `[a b]` as a vector expression (helper). -/
def _root_.Jank.Codegen.Form.vector2 (a b : Form) : Form := .vec [a, b]

mutual

/-- An expression (value position unless `tail`). -/
partial def genE (depth : Nat) (c : Ctx) (tail : Bool) : G Form := do
  let leafOnly := depth == 0
  let k ← d "expr.kind" (if leafOnly then 4 else 20)
  match k with
  | 0 => pure (int (← d "expr.int" 3))
  | 1 => pure (kw ((← pick (σ := W) "expr.kw" ["a", "b"]).getD "a"))
  | 2 =>
    match c.locals with
    | [] => pure (int 0)
    | _ => pure (.sym ((← pick (σ := W) "expr.local" c.locals).getD "x"))
  | 3 =>
    -- vector literals the analyzer folds: [] () [[]] [()]
    match (← d "expr.lit" (if c.clean then 2 else 4)) + (if c.clean then 2 else 0) with
    | 0 => pure (.vec [.vec []])
    | 1 => pure (.vec [.lit (.persistentList none [])])
    | 2 => pure (.vec [])
    | _ => pure (.lit (.persistentList none []))
  | 4 => pure (.call (.sym "log") [← genE (depth - 1) c false])
  | 5 => -- a call whose operator has an effect
    if c.clean then pure (.call (.sym "identity") [← genE (depth - 1) c false])
    else pure (.call (.do_ [.call (.sym "log") [kw "op"], .sym "identity"]) [← genE (depth - 1) c false])
  | 6 => pure (.call (.sym "vector") [← genE (depth - 1) c false, ← genE (depth - 1) c false])
  | 7 =>
    let n ← pickName "let.name" c
    let v ← genE (depth - 1) c false
    let body ← genE (depth - 1) { c with locals := n :: c.locals } tail
    pure (.let_ [(n, v)] [body])
  | 8 =>
    let n1 ← pickName "let2.name1" c
    let n2 ← pickName "let2.name2" c
    let v1 ← genE (depth - 1) c false
    let v2 ← genE (depth - 1) { c with locals := n1 :: c.locals } false
    let body ← genE (depth - 1) { c with locals := n2 :: n1 :: c.locals } tail
    pure (.let_ [(n1, v1), (n2, v2)] [body])
  | 9 => -- a bounded loop: (loop [n init] (if (lt n 2) (recur (inc n)) body))
    let n ← if c.clean then pure s!"L{depth}" else pickName "loop.name"
    let init ← d "loop.init" 3
    let c' := { c with locals := n :: c.locals, recurArity := none }
    let body ← genE (depth - 1) c' false
    pure (.loop [(n, int init)] [.if_ (.call (.sym "lt") [.sym n, int 2])
      (.recur [.call (.sym "inc") [.sym n]]) (some body)])
  | 10 =>
    let cond ← genE (depth - 1) c false
    pure (.if_ cond (← genE (depth - 1) c tail) (some (← genE (depth - 1) c tail)))
  | 11 => pure (.do_ [← genE (depth - 1) c false, ← genE (depth - 1) c tail])
  | 12 => genFnCall depth c
  | 13 => -- def with metadata, then read the var and its metadata
    let vname := (← pick (σ := W) "def.name" ["v", "w"]).getD "v"
    let mv : JV ← match ← d "def.meta" 3 with
      | 0 => pure (.int 1)
      | 1 => pure (.list [.sym "" "quote" none, .vec [.sym "" "x" none] none] none)
      | _ => if c.clean then pure (.int 2) else match c.locals with
        | [] => pure (.list [.sym "" "add" none, .int 1, .int 2] none)
        | l :: _ => pure (.sym "" l none)
    let v ← genE (depth - 1) c false
    pure (.do_ [.def_ vname [("k", mv)] (some v),
                .vec [.sym vname, .call (.sym "meta-of") [.varq vname]]])
  | 14 =>
    if c.recurArity.isSome then genE (depth - 1) c tail
    else
      let body ← genE (depth - 1) { c with inTry := true } false
      -- the handler does not use the exception: Clojure's would be a ClassCastException
      let h ← genE (depth - 1) { c with inTry := true } false
      let fin ← d "try.finally" 2
      pure (.try_ [.call (.sym "log") [body], .throw_ (kw "boom")] (some ("e", [h]))
        (if fin == 1 then some [.call (.sym "log") [kw "fin"]] else none))
  | 15 => -- case on integers, tests drawn from a set crossing the i32 boundary
    let v ← d "case.value" (if c.clean then 2 else 4)
    let tests := [0, 2147483647, 2147483648, 4294967296]
    pure (.case_ (int (tests.getD v 0)) [(tests.getD v 0, kw "hit"), (1, kw "one")] (kw "miss"))
  | 16 => -- a loop whose body binds something (maybe an inner loop) before it recurs
    let n ← if c.clean then pure s!"M{depth}" else pickName "loop2.name"
    let c' := { c with locals := n :: c.locals, recurArity := none }
    let z ← genE (depth - 1) c' false
    pure (.loop [(n, int 0)] [.let_ [("z", z)] [.if_ (.call (.sym "lt") [.sym n, int 2])
      (.recur [.call (.sym "inc") [.sym n]]) (some (.sym "z"))]])
  | 17 => pure (.call (.sym "list?") [.call (.sym "first") [← genE (depth - 1) c false]])
  | 18 => -- case whose branches return literals of drawn types (strings, keywords, integers)
    if c.clean then return int 3  -- G16, left out of the control
    let litOf := fun (i : Nat) => match i with
      | 0 => kw "k" | 1 => int 7 | _ => Form.lit (.persistentString "s")
    let v ← d "casemix.value" 3
    let a ← d "casemix.first" 3
    let b2 ← d "casemix.second" 3
    let dv ← d "casemix.default" 3
    pure (.case_ (int (v + 1)) [(1, litOf a), (2, litOf b2)] (litOf dv))
  | _ => -- case with one test
    let v ← d "case1.value" (if c.clean then 2 else 4)
    let tests := [0, 2147483647, 2147483648, 4294967296]
    pure (.case_ (int (tests.getD v 0)) [(tests.getD v 0, kw "hit")] (kw "miss"))

/-- A function literal called on the spot: plain, recursive by `recur`, or a closure over a local. -/
partial def genFnCall (depth : Nat) (c : Ctx) : G Form := do
  match ← d "fn.kind" (if c.clean then 3 else 5) with
  | 0 =>
    let p ← pickName "fn.param" c
    let body ← genE (depth - 1) { c with locals := p :: c.locals, recurArity := none } true
    pure (.call (.fn_ none [p] [body]) [← genE (depth - 1) c false])
  | 1 =>
    -- (fn self [n acc] (if (pos? n) (recur (dec n) (add acc 1)) body)) called with 2 0
    let p ← pickName "fn.param" c
    let q := if p == "acc" then "acc2" else "acc"
    let body ← genE (depth - 1) { c with locals := q :: p :: c.locals, recurArity := none } false
    pure (.call (.fn_ (some "self") [p, q]
      [.if_ (.call (.sym "pos?") [.sym p]) (.recur [.call (.sym "dec") [.sym p], .call (.sym "add") [.sym q, int 1]])
        (some (.vector2 (.sym q) body))]) [int 2, int 0])
  | 2 =>
    -- a closure that refers to its own (possibly hyphenated) name from a nested fn
    let fname := (← pick (σ := W) "fn.name" (if c.clean then ["self"] else ["self", "my-f"])).getD "self"
    pure (.call (.call (.fn_ (some fname) [] [.fn_ none [] [.sym fname]]) []) [])
  | 3 =>
    -- a closure whose parameter has the function's name
    let v ← genE (depth - 1) c false
    pure (.let_ [("cap", v)] [.call (.fn_ (some "f") ["f"] [.sym "cap"]) [int 5]])
  | _ =>
    -- two letfn forms, the first with a forward reference
    let fwd ← d "letfn.forward" 2
    let first := if fwd == 1 then [("f", [], [.call (.sym "g") []]), ("g", [], [int 1])]
                 else [("g", [], [int 1]), ("f", [], [.call (.sym "g") []])]
    pure (.vec [.letfn first [.call (.sym "f") []], .letfn [("h", [], [int 2])] [.call (.sym "h") []]])

end

structure Mode where
  name : String
  cfg : Config
  deriving Inhabited

def modes : List Mode :=
  [{ name := "eval -O0 (JIT, default)", cfg := {} },
   { name := "eval -O1", cfg := { passes := Passes.ofLevel 1 } },
   { name := "eval -O3 (release)", cfg := { passes := Passes.ofLevel 3 } },
   { name := "module, static runtime (AOT default)", cfg := { target := .module, runtime := { dynamic := false } } }]

/-- A deviation's class, from jank's outcome and the program (to keep one counterexample per
class, and to shrink within the class). -/
def classify (prog : String) (c j : Outcome) : String :=
  let has := fun (t : String) => (prog.splitOn t).length > 1
  let jm := j.show
  if jm.startsWith "compile error (use of undeclared identifier 's" then "nested loop: stale recur shadow"
  else if jm.startsWith "compile error (IR pass: std::out_of_range: name_to_info.at())" then "cross-fn self reference by unmunged name"
  else if jm.startsWith "compile error (IR pass: std::out_of_range: name_to_info.at(v" then "deduplicated value still used (case/loop)"
  else if jm.startsWith "compile error (C++ parse error: expected 'catch'" then "hoisted value placed before a catch handler"
  else if jm.startsWith "compile error (C++ parse error" then "C++ syntax error"
  else if jm.startsWith "compile error (redefinition" then "duplicate C++ declaration"
  else if jm.startsWith "compile error (case value" then "case label narrowing"
  else if jm.startsWith "compile error" then "compile error: " ++ String.ofList (jm.toList.take 50)
  else if (match j with | .threw _ => true | _ => false) && has "(case " && !has "meta-of"
       && (match c with | .value .. => true | _ => false) then "case branch converted to another branch's type"
  else if jm.startsWith "crash" then "crash: " ++ String.ofList (jm.toList.take 60)
  else match c, j with
    | .value a o, .value b p =>
      if a.same b && o != p && o.length == p.length then "evaluation order"
      else if has "meta-of" then "def metadata"
      else if has "case" then "case dispatch"
      else if has "a-b" && has "a_b" then "munged names collide"
      else if has "[()]" || has "[[]]" then "constants merged"
      else "value"
    | .threw _, _ | _, .threw _ => if has "meta-of" then "def metadata (throws)" else "throws on one side"
    | _, _ => "other"

def body (cfg : Config) (depth : Nat) (clean : Bool := false) : G Unit := do
  let e ← genE depth { clean } true
  let prog := [e]
  let c := Spec.run prog
  let (j, _) := jankRun prog cfg
  match agree c j with
  | some false =>
    let cls := classify e.code c j
    violate (σ := W) s!"jank's emitted program means what Clojure means [{cls}]"
      s!"{e.code}: Clojure {c.show}, jank {j.show}"
  | _ => pure ()

def run (cfg : Config) (depth : Nat) (source : Source) (clean : Bool := false) : Ended :=
  match (body cfg depth clean).run { decisions := { source, limit := 400 } } with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }
  | .error (.nodeDown _) w => { taken := w.decisions.taken, violation := none }

end Jank.Codegen.ProgSearch
