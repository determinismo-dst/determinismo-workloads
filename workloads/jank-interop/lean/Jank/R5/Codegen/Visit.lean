import Jank.R5.Codegen.Sub

/-!
# Round 5, codegen: walking a decision tree, and round 2's verdict on one program

`verdict` is `ProgSearch.body`'s check (ProgSearch.lean 222–231) on a given form: Clojure's
outcome (`Spec.run`), jank's (`jankRun`: analyzer, IR, passes, C++ text, parse, run), `agree`,
and the class of a disagreement (`classify`). `visitFrom` walks a tree depth first from a path,
so a large world runs as resumable segments.
-/

namespace Jank.R5.Codegen

open Jank.Codegen
open Jank.Codegen.Spec (Outcome)

inductive Verdict where
  | agree
  /-- A model gap on one side (`unsupported`): not a result, as in round 2. -/
  | gap (why : String)
  | violate (cls : String) (detail : String)

def verdict (cfg : Config) (e : Form) : Verdict :=
  let c := Spec.run [e]
  let (j, _) := jankRun [e] cfg
  match agree c j with
  | some false => .violate (ProgSearch.classify e.code c j) s!"{e.code}: Clojure {c.show}, jank {j.show}"
  | some true => .agree
  | none => .gap s!"{e.code}: Clojure {c.show}, jank {j.show}"

/-- Depth first from `start` (the leaves before it skipped); `k` returns false to stop before
the leaf, whose path is then returned to resume from. -/
partial def DT.visitFrom {α : Type} : DT α → List Nat → Array Nat → (α → Array Nat → IO Bool) →
    IO (Option (Array Nat))
  | .ret a, _, pre, k => do if (← k a pre) then pure none else pure (some pre)
  | .node _ n f, start, pre, k => do
    let s0 := start.headD 0
    for i in [s0:n] do
      if h : i < n then
        let st := if i == s0 then start.tail else []
        match ← DT.visitFrom (f ⟨i, h⟩) st (pre.push i) k with
        | some p => return some p
        | none => pure ()
    return none

end Jank.R5.Codegen
