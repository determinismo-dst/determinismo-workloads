import Determinismo
import Jank.Analyzer.World

/-!
# Searching programs where jank's analysis departs from Clojure

A program is drawn by decisions (`Determinismo.decide`/`pick`) from a grammar of the forms the
analyzer handles: literals of every number/boolean/string kind, locals and shadowing (names drawn
from a pool that includes a macro's and an inline function's name), `if`, `do`, `let*`, `loop*`
with one `recur` round, `fn*` (named or not) applied at once with a `recur` round, `def`, `quote`,
`var`, core calls, the macros `when`, `form-of` (`&form`), `env-count` (`&env`), `mk-vec`,
`mk-map`, `other/secret-of`, and the private `other/secret`.

The property: jank (analysis by the replica, then the IR's meaning of the tree) gives the same
outcome as Clojure (`Outcome.agrees`). Each run also reports the analyzer paths it took
(`tag:*` notes) so findings of an already known class can be set aside.
-/

namespace Jank.Analyzer

open Determinismo

structure GenWorld where
  decisions : Decisions := {}

instance : Chaotic GenWorld where
  decisions w := w.decisions
  setDecisions w d := { w with decisions := d }

abbrev GenM := EStateM Stop GenWorld

def choose (name : String) (n : Nat) : GenM Nat := decide (σ := GenWorld) name n

def literals : List Obj :=
  [I 0, I 1, I (-1), I 2147483647, I 2147483648, D 1.5, D 0.0, B true, B false, .nil, K "k", str "s"]

def namePool : List String := ["x", "f", "when", "inc"]

/-- Features a world may use. -/
structure Features where
  ifs : Bool := true
  lets : Bool := true
  loops : Bool := true
  fns : Bool := true
  macros : Bool := true
  privates : Bool := true
  calls : Bool := true
  cases : Bool := true
  lits : List Obj := literals
  names : List String := namePool

/-- An expression of depth at most `d` with locals `scope` (names) in scope; `tail` when a
`recur` to `target` arity would be legal in Clojure. -/
partial def genExpr (f : Features) (d : Nat) (scope : List String) : GenM Obj := do
  let leaf : GenM Obj := do
    let k ← choose "gen.leaf" (if scope.isEmpty then 2 else 3)
    match k with
    | 0 => pure (f.lits.getD (← choose "gen.literal" f.lits.length) .nil)
    | 1 => pure (f.lits.getD (← choose "gen.literal2" f.lits.length) .nil)
    | _ => pure (S (scope.getD (← choose "gen.local" scope.length) "x"))
  if d == 0 then return ← leaf
  let kinds : List (String × Bool) :=
    [("leaf", true), ("if", f.ifs), ("do", true), ("let", f.lets), ("loop", f.loops), ("fn", f.fns),
     ("macro", f.macros), ("private", f.privates), ("call", f.calls), ("quote", true), ("case", f.cases)]
  let enabled := kinds.filter (·.2)
  let k := (enabled.getD (← choose "gen.kind" enabled.length) ("leaf", true)).1
  match k with
  | "if" =>
    let c ← genExpr f (d - 1) scope
    let t ← genExpr f (d - 1) scope
    if (← choose "gen.if.else" 2) == 0 then pure (L [S "if", c, t])
    else pure (L [S "if", c, t, ← genExpr f (d - 1) scope])
  | "do" => pure (L [S "do", ← genExpr f (d - 1) scope, ← genExpr f (d - 1) scope])
  | "let" =>
    let n := f.names.getD (← choose "gen.let.name" f.names.length) "x"
    let v ← genExpr f (d - 1) scope
    let body ← genExpr f (d - 1) (n :: scope)
    pure (L [S "let*", V [S n, v], body])
  | "loop" =>
    -- (loop* [n init k 0] (if (= k 1) body (recur next 1))): one recur round.
    let n := f.names.getD (← choose "gen.loop.name" f.names.length) "x"
    let init ← genExpr f (d - 1) scope
    let next ← genExpr f (d - 1) (n :: scope)
    let body ← genExpr f (d - 1) (n :: scope)
    pure (L [S "loop*", V [S n, init, S "k", I 0],
      L [S "if", L [S "=", S "k", I 1], body, L [S "recur", next, I 1]]])
  | "fn" =>
    -- ((fn* name? [p k] (if (= k 1) body (recur arg 1))) a 0): one recur round.
    let named ← choose "gen.fn.named" 2
    let fname := f.names.getD (← choose "gen.fn.name" f.names.length) "f"
    let p := f.names.getD (← choose "gen.fn.param" f.names.length) "x"
    let inner := if named == 1 then p :: fname :: scope else p :: scope
    let body ← genExpr f (d - 1) inner
    let next ← genExpr f (d - 1) inner
    let arg ← genExpr f (d - 1) scope
    let fnForm := L ((S "fn*" :: (if named == 1 then [S fname] else [])) ++
      [V [S p, S "k"], L [S "if", L [S "=", S "k", I 1], body, L [S "recur", next, I 1]]])
    pure (L [fnForm, arg, I 0])
  | "macro" =>
    match ← choose "gen.macro" 6 with
    | 0 => pure (L [S "when", ← genExpr f (d - 1) scope, ← genExpr f (d - 1) scope])
    | 1 => pure (L [S "form-of", ← genExpr f (d - 1) scope])
    | 2 => pure (L [S "env-count"])
    | 3 => pure (L [S "meta", L [S "mk-vec", ← genExpr f (d - 1) scope]])
    | 4 => pure (L [S "mk-map", K "k", ← genExpr f (d - 1) scope])
    | _ => pure (L [Obj.sym "other" "secret-of"])
  | "private" => pure (Obj.sym "other" "secret")
  | "call" =>
    match ← choose "gen.call" 5 with
    | 0 => pure (L [S "=", ← genExpr f (d - 1) scope, ← genExpr f (d - 1) scope])
    | 1 => pure (L [S "inc", ← genExpr f (d - 1) scope])
    | 2 => pure (L [S "+", ← genExpr f (d - 1) scope, ← genExpr f (d - 1) scope])
    | 3 => pure (L [S "vector", ← genExpr f (d - 1) scope, ← genExpr f (d - 1) scope])
    | _ => pure (L [K "k", L [S "mk-map", K "k", ← genExpr f (d - 1) scope]])
  | "quote" => pure (L [S "quote", ← genExpr f (d - 1) scope])
  | "case" =>
    -- (case v 1 e1 2 e2 dflt): `case` on integer tests (two clauses or one).
    let v ← match ← choose "gen.case.value" 4 with
      | 0 => pure (I 1) | 1 => pure (I 2) | 2 => pure (I 3)
      | _ => genExpr f (d - 1) scope
    let e1 ← genExpr f (d - 1) scope
    let dflt ← genExpr f (d - 1) scope
    if (← choose "gen.case.clauses" 2) == 0 then pure (L [S "case", v, I 1, e1, dflt])
    else pure (L [S "case", v, I 1, e1, I 2, ← genExpr f (d - 1) scope, dflt])
  | _ => leaf

/-- A program: one top-level expression of depth ≤ `depth`. -/
def genProgram (f : Features) (depth : Nat) : GenM (List Obj) := do
  pure [← genExpr f depth []]

/-- The analyzer path tags of a jank run. -/
def JankRun.tags (j : JankRun) : List String :=
  (j.notes.filter (·.startsWith "tag:")).map (·.drop 4 |>.toString)

/-- Tags read from the program itself: the macros that read `&form`/`&env`. -/
partial def formTags (o : Obj) : List String :=
  let here := match o with
    | .symbol _ "" "form-of" => ["macro-form-env"]
    | .symbol _ "" "env-count" => ["macro-form-env"]
    | _ => []
  here ++ ((o.elems.getD []).flatMap formTags)

/-- One timeline: draw a program, run both sides, compare. `known` tags are set aside. -/
def runOne (f : Features) (depth : Nat) (known : List String) (oracle : Oracle) (source : Source) : Ended :=
  match (genProgram f depth).run { decisions := { source } } with
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }
  | .error (.nodeDown _) w => { taken := w.decisions.taken, violation := none }
  | .ok forms w =>
    let j := runJank forms oracle
    let c := runClojure forms
    let tags := j.tags ++ forms.flatMap formTags
    let isKnown := tags.any known.contains
    if !j.outcome.agrees c && !isKnown then
      { taken := w.decisions.taken,
        violation := some ("jank = Clojure",
          s!"{" ".intercalate (forms.map Obj.pr)} => jank {j.outcome.show}; Clojure {c.show}; tags {tags}") }
    else { taken := w.decisions.taken, violation := none }

/-- Every program of the grammar (depth-first by decisions), counted by outcome class. -/
structure Tally where
  runs : Nat := 0
  agree : Nat := 0
  differ : Nat := 0
  /-- Differences per tag set. -/
  byTags : List (List String × Nat × String) := []
  deriving Inhabited

def tallyAll (f : Features) (depth : Nat) (maxRuns : Nat) (oracle : Oracle := {}) : Tally × Bool := Id.run do
  let mut path : Array Nat := #[]
  let mut t : Tally := {}
  for _ in List.range maxRuns do
    match (genProgram f depth).run { decisions := { source := Source.path path } } with
    | .error _ _ => return (t, false)
    | .ok forms w =>
      let j := runJank forms oracle
      let c := runClojure forms
      let tags := (j.tags ++ forms.flatMap formTags).eraseDups
      t := { t with runs := t.runs + 1 }
      if j.outcome.agrees c then t := { t with agree := t.agree + 1 }
      else
        let ex := s!"{" ".intercalate (forms.map Obj.pr)} => jank {j.outcome.show}; Clojure {c.show}"
        let byTags := match t.byTags.find? (·.1 == tags) with
          | some _ => t.byTags.map fun (ts, n, e) => if ts == tags then (ts, n + 1, e) else (ts, n, e)
          | none => t.byTags ++ [(tags, 1, ex)]
        t := { t with differ := t.differ + 1, byTags }
      match nextPath w.decisions.taken with
      | none => return (t, true)
      | some p => path := p
  return (t, false)

/-- Tally over random programs from seeds `0 .. seeds-1`. -/
def tallySeeds (f : Features) (depth : Nat) (seeds : Nat) (oracle : Oracle := {}) : Tally := Id.run do
  let mut t : Tally := {}
  for seed in List.range seeds do
    match (genProgram f depth).run { decisions := { source := Source.seeded seed } } with
    | .error _ _ => pure ()
    | .ok forms _ =>
      let j := runJank forms oracle
      let c := runClojure forms
      let tags := (j.tags ++ forms.flatMap formTags).eraseDups
      t := { t with runs := t.runs + 1 }
      if j.outcome.agrees c then t := { t with agree := t.agree + 1 }
      else
        let ex := s!"{" ".intercalate (forms.map Obj.pr)} => jank {j.outcome.show}; Clojure {c.show}"
        let byTags := match t.byTags.find? (·.1 == tags) with
          | some _ => t.byTags.map fun (ts, n, e) => if ts == tags then (ts, n + 1, e) else (ts, n, e)
          | none => t.byTags ++ [(tags, 1, ex)]
        t := { t with differ := t.differ + 1, byTags }
  return t

end Jank.Analyzer
