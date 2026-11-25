import Jank.R3.Codegen.Census
import Jank.R3.Search.Common
import Jank.Codegen.ProgSearch

/-!
# Round 4, widening: round 2's codegen control world at depth 2, run to completion

Round 3 stopped it at 186,717 timelines per mode (≤ 20,000 per partition of the first decision).
Here each partition of the first decision runs with a per-partition bound given on the command
line, so a mode's walk is complete exactly when every partition completes.
-/

namespace Jank.R4.Feedback.Control

open Determinismo Jank.R3.Codegen

def modes : List (String × Jank.Codegen.Config) :=
  [("eval -O0", ({} : Jank.Codegen.Config)),
   ("module (AOT)", { target := .module, runtime := { dynamic := false } })]

def runOf (cfg : Jank.Codegen.Config) : Source → Ended :=
  fun src => Jank.Codegen.ProgSearch.run cfg 2 src true

/-- The number of options of the first decision. -/
def firstOptions (cfg : Jank.Codegen.Config) : Nat :=
  match ((runOf cfg) (Source.path #[])).taken[0]? with | some t => t.options | none => 1

/-- Knuth's estimate of the world's size. -/
def size (cfg : Jank.Codegen.Config) (samples : Nat) : Float × Float :=
  Jank.R3.Search.estimate (runOf cfg) samples

end Jank.R4.Feedback.Control
