import Replica.Prelude

/-!
# Searching: the library's `explore`, `exhaust` and `shrink`, with what this replica prints

Every search prints one line (`search`), every counterexample its shrunk decisions as a tape and
its story.
-/

namespace Replica

open Determinismo

structure Found where
  label : String
  c : Counterexample
  shrunk : Counterexample

def say (line : String) : IO Unit := do
  IO.println line
  (← IO.getStdout).flush

/-- `exhaust`, said: complete, stopped, or the counterexample found (shrunk). -/
def exhaustSaid (label : String) (run : Source → Ended) (maxRuns : Nat) : IO (Option Found) := do
  let start ← IO.monoMsNow
  let result ← IO.lazyPure fun _ => exhaust run maxRuns
  let ms := (← IO.monoMsNow) - start
  match result with
  | .found c =>
    let s ← IO.lazyPure fun _ => shrink run c
    say s!"search exhaust [{label}]: FOUND after {c.runs} timelines ({ms} ms): {c.property}: {s.detail} (shrunk to {s.taken.size} decisions from {c.taken.size})"
    return some { label, c, shrunk := s }
  | .complete n =>
    say s!"search exhaust [{label}]: complete, {n} timelines, none broke it ({ms} ms)"
    return none
  | .stopped n =>
    say s!"search exhaust [{label}]: stopped at {n} timelines, none broke it ({ms} ms)"
    return none

/-- `explore` over seeds `first` to `first + count - 1`, said. -/
def exploreSaid (label : String) (run : Source → Ended) (count : Nat) (first : Nat := 0) :
    IO (Option Found) := do
  let start ← IO.monoMsNow
  let result ← IO.lazyPure fun _ => explore run count first
  let ms := (← IO.monoMsNow) - start
  match result with
  | some c =>
    let s ← IO.lazyPure fun _ => shrink run c
    say s!"search explore [{label}]: FOUND at timeline {c.runs} of seeds {first}..{first + count - 1} ({ms} ms): {c.property}: {s.detail} (shrunk to {s.taken.size} decisions from {c.taken.size})"
    return some { label, c, shrunk := s }
  | none =>
    say s!"search explore [{label}]: {count} timelines (seeds {first}..{first + count - 1}), none broke it ({ms} ms)"
    return none

/-- A counterexample's tape and story, printed. -/
def printFound (f : Found) (story : Source → List String) : IO Unit := do
  say s!"--- counterexample [{f.label}]: {f.shrunk.property}"
  say s!"detail: {f.shrunk.detail}"
  say s!"values: {f.shrunk.values.toList}"
  say "tape:"
  say (tape f.shrunk.taken)
  say "story:"
  for line in story (Source.path f.shrunk.values) do say s!"  {line}"
  say "---"

end Replica
