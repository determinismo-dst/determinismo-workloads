import Determinismo

/-!
# Shared pieces of the replica

`below`: a uniform decision among `options` without building a list of weights (the library's
`decide` builds `List.replicate options 1`, too slow for the Zig's ranges of 110,001 or 2^32
options). It draws the very value `decide` draws from the same source: `drawWeighted` with all
weights 1 is `randNat gen 0 (options - 1)`. A library gap, said in REPORT.md.
-/

namespace Replica

open Determinismo

/-- `Decisions.next` for a uniform decision of `options` options (no weights list). -/
def nextBelow (d : Decisions) (name : String) (options : Nat) : Except Stop (Nat × Decisions) :=
  if options ≤ 1 then .ok (0, d)
  else if d.taken.size ≥ d.limit then .error .limit
  else
    let position := d.taken.size
    let (value, source) :=
      if h : position < d.source.given.size then (d.source.given[position] % options, d.source)
      else if d.source.random then
        let (v, gen) := randNat d.source.gen 0 (options - 1)
        (v, { d.source with gen := gen })
      else (0, d.source)
    .ok (value, { d with source := source, taken := d.taken.push { name, options, value } })

variable {σ : Type} [Chaotic σ]

/-- A uniform decision among `options` (one option: 0, not recorded). -/
def below (name : String) (options : Nat) : EStateM Stop σ Nat := do
  let s ← get
  match nextBelow (Chaotic.decisions s) name options with
  | .ok (v, d) => set (Chaotic.setDecisions s d); pure v
  | .error e => throw e

/-- The result of one timeline of a replica: its decisions, and the property it broke. -/
def ended (taken : Array Taken) (violation : Option (String × String)) : Ended :=
  { taken, violation }

/-- Which platform commit a model's code is (round 5): 3939448 (rounds 2 to 4, `upstream/`) or
62e06e3 (`upstream-62e06e3/`, the fixes of rounds 2 to 4's findings). Models default to 62e06e3;
a theorem about 3939448's code says so. -/
inductive Ver where
  | v3939448 | v62e06e3
  deriving BEq, Repr, Inhabited, DecidableEq

/-- Swap-remove, as the Zig's `running[index] = running[count - 1]; count -= 1`. -/
def swapRemove {α : Type} [Inhabited α] (a : Array α) (i : Nat) : Array α :=
  if i + 1 == a.size then a.pop else (a.set! i a.back!).pop

end Replica
