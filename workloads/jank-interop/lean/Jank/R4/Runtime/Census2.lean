import Determinismo
import Jank.R3.Runtime.Common
import Jank.R3.Runtime.Locks

/-!
# Round 4, Runtime: the two-thread lock census, decided

Round 3's two-thread census (`jank3-runtime census2 2 1 1 0 N 1 k`, 12 partitions by thread 0's
operation, alphabet `Locks.alphabet2`) judged every program with a state search bounded at 20,000
states; 143 of its 37,488 programs exceeded the bound and were left undecided (class
`(search stopped)`). This module walks the same world (the same generator, the same decisions, so
the same programs in the same order) and judges each program with escalating budgets: a program
whose search stops at one budget is searched again at the next, until it is decided or the
budgets run out. Nothing about the replica changes: `Locks.judge` is round 3's.
-/

namespace Jank.R4.Runtime.Census2

open Determinismo Jank.R3.Runtime

/-- Judge with escalating budgets: the class (or `none` when jank has no deadlock that Clojure
lacks), the budget that decided it, or `undecided` when every budget stopped. -/
def judgeEsc (pg : Locks.Program') (budgets : List Nat) : Option String × Nat × Bool :=
  match budgets with
  | [] => (some "(undecided)", 0, false)
  | b :: rest =>
    match Locks.judge pg false b with
    | none => (none, b, true)
    | some (cls, _) =>
      if cls.startsWith "(" then
        if rest.isEmpty then (some cls, b, false) else judgeEsc pg rest
      else (some cls, b, true)

structure Row where
  idx : Nat
  program : String
  firstBudget : Nat
  verdict : String
  budget : Nat
  decided : Bool
  deriving Inhabited

/-- Walk the partition `pfx` of the census world; for every program that round 3's bound (the first
budget) leaves undecided, escalate. Returns the escalated rows and the program count. -/
def walk (threads ops len depth : Nat) (budgets : List Nat) (pfx : Array Nat) (maxRuns : Nat)
    (progress : Nat → Nat → IO Unit := fun _ _ => pure ()) : IO (Array Row × Nat × Bool) := do
  let first := budgets.headD 20000
  let mut path := pfx
  let mut rows : Array Row := #[]
  let mut runs := 0
  let mut complete := false
  for i in [0:maxRuns] do
    let g : Locks.Gen := { decisions := { source := Source.path path, limit := 100000 } }
    let (taken, pg?) := match (Locks.genProgram Locks.alphabet2 threads ops len depth).run g with
      | .ok pg g' => (g'.decisions.taken, some pg)
      | .error _ g' => (g'.decisions.taken, none)
    runs := i + 1
    if let some pg := pg? then
      match Locks.judge pg false first with
      | some (cls, d) =>
        if cls.startsWith "(" then
          let (v, b, ok) := judgeEsc pg budgets.tail
          rows := rows.push { idx := i + 1, program := d, firstBudget := first,
                              verdict := (v.getD "no jank-only deadlock"), budget := b, decided := ok }
          progress (i + 1) rows.size
      | none => pure ()
    match nextPath taken with
    | none => complete := true; break
    | some p =>
      if p.size < pfx.size || p.extract 0 pfx.size != pfx then complete := true; break
      path := p
  return (rows, runs, complete)

end Jank.R4.Runtime.Census2
