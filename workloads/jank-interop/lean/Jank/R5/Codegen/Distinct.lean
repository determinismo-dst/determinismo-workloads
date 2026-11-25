import Jank.R5.Codegen.Gen

/-!
# Round 5, codegen: distinct programs in the clean worlds

Two timelines that draw the same program have the same verdict: `ProgSearch.body` draws the
form `e`, then compares `Spec.run [e]` with `jankRun [e] cfg`, functions of `e` alone. So the
world reduces to its distinct programs. In the clean grammar two timelines draw the same form
only through the leaves: kind 2 with no local in scope is the form `0`, which kind 0 also
draws, and a pick among locals that repeat a name (`(let [x …] (let [x …] x))`). Every other
production puts what it drew into the form (a different kind gives a different head or arity,
names and constants appear in the text). `distinctCount d ls` counts by that rule, with `ls`
the locals in scope; the driver checks it against the forms themselves on every depth-1
timeline and on the small depth-2 partitions.
-/

namespace Jank.R5.Codegen

def dedupNames (ls : List String) : List String := ls.eraseDups

/-- Distinct programs drawn by one production above depth 0 (children counted by `D`). -/
def kindDistinctWith (D : List String → Nat) (depth : Nat) (ls : List String) (k : Nat) : Nat :=
  let xy := ["x", "y"]
  match k with
  | 0 => 3
  | 1 => 2
  | 2 => (dedupNames ls).length
  | 3 => 2
  | 4 => D ls
  | 5 => D ls
  | 6 => D ls * D ls
  | 7 => (xy.map fun n => D ls * D (n :: ls)).sum
  | 8 => (xy.flatMap fun n1 => xy.map fun n2 => D ls * D (n1 :: ls) * D (n2 :: n1 :: ls)).sum
  | 9 => 3 * D (s!"L{depth}" :: ls)
  | 10 => D ls * D ls * D ls
  | 11 => D ls * D ls
  | 12 => (xy.map fun p => D (p :: ls) * D ls).sum + (xy.map fun p => D ("acc" :: p :: ls)).sum + 1
  | 13 => 6 * D ls
  | 14 => 2 * D ls * D ls
  | 15 => 2
  | 16 => D (s!"M{depth}" :: ls)
  | 17 => D ls
  | 18 => 1
  | _ => 2

def distinctCount : Nat → List String → Nat
  | 0, ls => 7 + (dedupNames ls).length
  | d + 1, ls => ((List.range 20).map fun k => kindDistinctWith (distinctCount d) (d + 1) ls k).sum

/-- Distinct programs of one root kind at `depth`, children at `d`. -/
def kindDistinct (d depth : Nat) (ls : List String) (k : Nat) : Nat :=
  kindDistinctWith (distinctCount d) depth ls k

end Jank.R5.Codegen
