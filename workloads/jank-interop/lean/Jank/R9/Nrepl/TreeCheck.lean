import Jank.R9.Nrepl.Tree
import Jank.R3.Nrepl.ThreadSearch

/-!
# Round 9, nREPL: World T's runs as decision trees

- ★ `exhaust_worldT`: `Tree.exhaust_of_treelike` instantiated at round 3's `runTWith` (the sdk's
  `interleavePB`, budget `b`, over `tProg`) and `runT` (the sdk's `interleave`): when World T's run
  function satisfies `Treelike` and has no violation, the sdk's `exhaust` over it completes after
  exactly the leaves of the tree `Tree.build` reads off it.
- `checkTreelike`: the conditions checked on every timeline of a complete depth-first walk (the
  sdk's `nextPath`, as `exhaust`): each decision's value is the path's value modulo its options (0
  beyond the path), at least two options, the decision limit not reached, and causality between
  consecutive timelines (they agree on every decision before the position `nextPath` advanced, and on
  the name and options there), which on a depth-first walk is causality on every pair of timelines
  the walk runs.
-/

namespace Jank.R9.Nrepl.Tree

open Determinismo Jank.R3.Nrepl Jank.R8.Nrepl.Walk

/-- World T's run function on paths (`Source.path`), as lists. -/
def worldRun (sched : Option Nat) (cfg : TConfig) (aside : Aside) (scripts : List (List TReq)) (p : List Nat) :
    List Taken :=
  (runTWith sched cfg aside scripts (Source.path p.toArray)).1.taken.toList

/-- ★ The sdk's `exhaust` over World T (round 3's `runTWith`, either scheduler) completes with the
leaves of the tree read off it, when its run function is `Treelike` and no timeline has a violation. -/
theorem exhaust_worldT (sched : Option Nat) (cfg : TConfig) (aside : Aside) (scripts : List (List TReq))
    (D : Nat) (hT : Treelike (worldRun sched cfg aside scripts) D)
    (hv : ∀ path, (runTWith sched cfg aside scripts (Source.path path)).1.violation = none)
    (maxRuns : Nat) (hm : (build (worldRun sched cfg aside scripts) D []).leaves ≤ maxRuns) :
    exhaust (fun src => (runTWith sched cfg aside scripts src).1) maxRuns =
      .complete (build (worldRun sched cfg aside scripts) D []).leaves :=
  exhaust_of_treelike _ D hT _ (fun path => ⟨by simp [worldRun], hv path⟩) maxRuns hm

structure TCOut where
  runs : Nat := 0
  valueBad : Nat := 0
  optBad : Nat := 0
  limitHit : Nat := 0
  causalBad : Nat := 0
  violations : Nat := 0
  maxDepth : Nat := 0
  example? : Option String := none
  complete : Bool := false
  deriving Inhabited

/-- Walks every timeline depth first (as the sdk's `exhaust`), checking the `Treelike` conditions. -/
def checkTreelike (run : Source → Ended) (limit maxRuns : Nat) : TCOut := Id.run do
  let mut o : TCOut := {}
  let mut path : Array Nat := #[]
  let mut prev : Option (Array Taken) := none
  for _ in [0:maxRuns] do
    let e := run (Source.path path)
    let tk := e.taken
    o := { o with runs := o.runs + 1, maxDepth := max o.maxDepth tk.size }
    if e.violation.isSome then o := { o with violations := o.violations + 1 }
    if tk.size ≥ limit then o := { o with limitHit := o.limitHit + 1 }
    for i in [0:tk.size] do
      let x := tk[i]!
      if x.options < 2 then o := { o with optBad := o.optBad + 1 }
      if x.value != (path.getD i 0) % x.options then
        o := { o with valueBad := o.valueBad + 1, example? := o.example?.orElse fun _ => some s!"run {o.runs}: decision {i} value {x.value}, path {path.getD i 0}, options {x.options}" }
    -- causality against the previous timeline: the path changed first at position j
    if let some pt := prev then
      let j := (List.range (path.size + 1)).find? (fun i => path[i]? != (pt.map (·.value))[i]?) |>.getD path.size
      let mut ok := true
      for i in [0:j] do
        if tk[i]? != pt[i]? then ok := false
      if (tk[j]?.map fun x => (x.name, x.options)) != (pt[j]?.map fun x => (x.name, x.options)) then ok := false
      if !ok then
        o := { o with causalBad := o.causalBad + 1, example? := o.example?.orElse fun _ => some s!"run {o.runs}: differs from the previous timeline before or at position {j}" }
    prev := some tk
    match nextPath tk with
    | none => return { o with complete := true }
    | some q => path := q
  return o

end Jank.R9.Nrepl.Tree
