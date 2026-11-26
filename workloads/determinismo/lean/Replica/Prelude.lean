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

/-- Which platform commit a model's code is: 3939448 (rounds 2 to 4, `upstream/`), 62e06e3
(round 5, `upstream-62e06e3/`, the fixes of rounds 2 to 4's findings), a7fe05d (round 6,
`upstream-a7fe05d/`, the fixes of round 5's) or df8f08b (round 7, `upstream-df8f08b/`, the fixes
of round 6's) or c4f246e (round 8, `upstream-c4f246e/`, the fixes of round 7's). Models whose
code c4f246e changed default to it since round 8, the others to df8f08b (their code the same at
c4f246e); a theorem about an older commit's code says so. -/
inductive Ver where
  | v3939448 | v62e06e3 | va7fe05d | vdf8f08b | vc4f246e
  deriving BEq, Repr, Inhabited, DecidableEq

/-- 62e06e3 or later: what round 5's fixes brought, kept at a7fe05d unless a7fe05d changed it. -/
def Ver.since62 : Ver → Bool
  | .v3939448 => false
  | _ => true

/-- a7fe05d or later: round 5's findings' fixes, kept at df8f08b unless df8f08b changed them. -/
def Ver.sinceA7 : Ver → Bool
  | .va7fe05d | .vdf8f08b | .vc4f246e => true
  | _ => false

/-- df8f08b or later: round 6's findings' fixes, kept at c4f246e unless c4f246e changed them. -/
def Ver.sinceDf : Ver → Bool
  | .vdf8f08b | .vc4f246e => true
  | _ => false

/-- c4f246e: round 7's findings' fixes. -/
def Ver.sinceC4 : Ver → Bool
  | .vc4f246e => true
  | _ => false

/-- Swap-remove, as the Zig's `running[index] = running[count - 1]; count -= 1`. -/
def swapRemove {α : Type} [Inhabited α] (a : Array α) (i : Nat) : Array α :=
  if i + 1 == a.size then a.pop else (a.set! i a.back!).pop

end Replica
