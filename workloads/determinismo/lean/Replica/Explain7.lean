import Replica.Prelude
import Replica.Searching

/-!
# explain's `--draw <name>=<values>` (df8f08b, round 7; c4f246e, round 8)

`determinismo explain` (src/explain.zig, df8f08b) varies a failure's last faults' details, and
since df8f08b a scenario's own named draws (`--draw <name>`, 154-183 `named_decisions`): each
detail's `m` variants (`--variants`, 6 by default) are the timeline's tape with that draw's pull
answered a fresh value (`random.int(u64)`), or with `--draw <name>=<v>,...` the value set
(512-515: `.value = draw.set orelse random.int(u64)`), replayed from one snapshot to the failure
or a horizon (`Explanation.one`, 328-345). The control: the first other draw after the decision,
varied `m` times (497-502). The verdict (`verdict`, 109-119): needed when none fails and its 90%
Wilson interval lies wholly below the control's; partly with some failing; free when it fails as
often; unclear otherwise.

A set value's `m` variants are one tape: the pull answered `v`, nothing else changed (the removal's
variants vary the control's draw too, 506-511, "so its failures compare with the control's"; a set
value's do not). A replay is deterministic (README_AI.md: every timeline replays
bit-identically): `m` copies of one history, counted as `m` samples.

The model: a timeline whose every history (each distinct tape) fails with probability 5/6,
whatever the named draw's value (a draw that decides nothing), each distinct tape's outcome a
decision taken once; the verdict as the Zig computes it (Wilson's interval in Float).

## c4f246e (round 8, CE57's fix)

`variant_items` (explain.zig:543-597): a set value's `m` variants each vary the control's draw
beside it (`count = 2`, a fresh `random.int(u64)` at the control's pull), as the removal's do;
with no control the value runs once. The control is found among the recorded timeline's draws
(`controls[at]`: the first non-fault draw after the decision, `count > 1`), by its pull number.
A variant's tape answers that pull number whatever draw takes it in the variant's own history
(`variant_tape`, 395-418: overrides by pull). A set value that changes the history before that
pull (the clock step removed: no retry, so no retry jitter) can leave the pull to a draw that
decides nothing, or past the replay's end: then the `m` variants are one history again.
`controlLive` says whether the control's pull still varies the set value's history.
-/

namespace Replica.Explain7

open Determinismo

/-- causality.zig:499-508 `wilson` (z = 1.6448536269514722): the 90% interval. -/
def wilson (failing futures : Nat) : Float × Float :=
  let z : Float := 1.6448536269514722
  let n := futures.toFloat
  let p := failing.toFloat / n
  let denominator := 1 + z * z / n
  let center := (p + z * z / (2 * n)) / denominator
  let half := z * Float.sqrt (p * (1 - p) / n + z * z / (4 * n * n)) / denominator
  (max 0 (center - half), min 1 (center + half))

inductive Verdict where
  | needed | partly | free | unclear
  deriving BEq, Repr, Inhabited, DecidableEq

/-- explain.zig:106-116 `verdict`. -/
def verdict (failing of controlFailing controlOf : Nat) : Verdict :=
  if controlOf == 0 || controlFailing == 0 then .unclear
  else if failing * controlOf ≥ controlFailing * of then .free
  else if (wilson failing of).2 < (wilson controlFailing controlOf).1 then
    (if failing == 0 then .needed else .partly)
  else .unclear

structure S where
  decisions : Decisions := {}
  /-- Each distinct tape's outcome, once replayed (a replay is deterministic). -/
  outcomes : List (List Nat × Bool) := []
  deriving Inhabited

instance : Chaotic S where
  decisions s := s.decisions
  setDecisions s d := { s with decisions := d }

/-- A variant's replay: its tape (the overrides' values) fails or not, decided once per tape. -/
def replay (tape : List Nat) (failOneIn : Nat) : EStateM Stop S Bool := do
  if let some (_, o) := (← get).outcomes.find? (·.1 == tape) then return o
  let o := (← below "history.passes" failOneIn) != 0
  modify fun s => { s with outcomes := s.outcomes ++ [(tape, o)] }
  return o

/-- One explanation of a named draw: the control's `m` variants (fresh values), the detail's
(`set`: the value set, else fresh ones); the verdict. Values: tapes, `1000 + k` the control's,
`2000 + k` a fresh detail's, `v` a set value. -/
def explain (m : Nat) (set : Option Nat) (failOneIn : Nat := 6) (ver : Ver := .vc4f246e) (controlLive : Bool := true) : EStateM Stop S (Nat × Nat × Verdict) := do
  let mut controlFailing := 0
  for k in [0:m] do
    if ← replay [0, 1000 + k] failOneIn then controlFailing := controlFailing + 1
  let mut failing := 0
  for k in [0:m] do
    let tape := match set with
      | none => [2000 + k, 0]
      | some v =>
        -- c4f246e (explain.zig:582-592): the control's pull varied beside the set value; its
        -- override changes the history only when that pull still varies it.
        if ver.sinceC4 then (if controlLive then [v, 3000 + k] else [v, 0]) else [v, 0]
    if ← replay tape failOneIn then failing := failing + 1
  return (failing, controlFailing, verdict failing m controlFailing m)

def property : String := "a detail is called needed only when its value decides the failure (more than the control's histories do)"
def source : String := "src/explain.zig:29-34 (df8f08b: a verdict per detail against its control, by their 90% intervals; \"Six variants once called a wait needed (0 of 6) that another six found half the time (3 of 6)\"), 10-14 (`--draw <name>=0,1000` \"sets it to each value given instead, m times each\")"

def judge (m : Nat) (set : Option Nat) (src : Source) (ver : Ver := .vc4f246e) (controlLive : Bool := true) : Ended :=
  match (explain m set 6 ver controlLive).run { decisions := { source := src } } with
  | .ok (failing, cf, v) s =>
    let how := if set.isNone then "" else if !ver.sinceC4 then s!"set to {set.get!}: its {m} variants one tape, "
      else if controlLive then s!"set to {set.get!}, the control's draw varied beside it, "
      else s!"set to {set.get!}, the control's pull taken in its history by a draw that decides nothing: its {m} variants one history, "
    { taken := s.decisions.taken,
      violation := if v == .needed then
        some (property, s!"every history fails with probability 5/6 whatever the draw's value; {how}{failing} of {m} fail against the control's {cf} of {m}: needed") else none }
  | .error _ s => { taken := s.decisions.taken, violation := none }

/-- Over seeds: how often a draw that decides nothing is called needed, set or fresh. -/
def census (m count : Nat) (ver : Ver := .vc4f246e) (controlLive : Bool := true) : IO Unit := do
  for set in [some 0, none] do
    let mut needed := 0
    for i in [0:count] do
      if (judge m set (Source.seeded i) ver controlLive).violation.isSome then needed := needed + 1
    say s!"census [{reprStr ver}{if set.isSome && ver.sinceC4 then (if controlLive then ", the control's pull live in the set value's history" else ", the control's pull taken by a draw that decides nothing") else ""}; {m} variants, {if set.isSome then "the value set" else "fresh values"}]: {needed} of {count} explanations call a draw that decides nothing needed"

def searchAll (exhaustRuns : Nat) : IO Unit := do
  say s!"== explain property: {property}"
  say s!"   source: {source}"
  for (m, set, ver, live) in [(6, some 0, Ver.vdf8f08b, true), (3, some 0, .vdf8f08b, true), (3, none, .vdf8f08b, true),
      (6, some 0, .vc4f246e, true), (3, some 0, .vc4f246e, true), (3, none, .vc4f246e, true),
      (6, some 0, .vc4f246e, false), (3, some 0, .vc4f246e, false)] do
    let label := s!"{reprStr ver}: {m} variants, {if set.isSome then "a value set" else "fresh values"}{if set.isSome && ver.sinceC4 then (if live then ", the control's pull live in its history" else ", the control's pull taken by a draw that decides nothing") else ""}"
    if let some f ← exhaustSaid s!"{property} / {label}" (fun src => judge m set src ver live) exhaustRuns then
      printFound f (fun _ => [])
  census 6 100000 .vdf8f08b
  census 3 100000 .vdf8f08b
  census 6 100000 .vc4f246e true
  census 6 100000 .vc4f246e false
  census 3 100000 .vc4f246e false

end Replica.Explain7
