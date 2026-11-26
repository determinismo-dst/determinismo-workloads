import Replica.Clock

/-!
# The wall clock's start at 62e06e3: the jump against a token's hour, over the whole timeline
(round 5)

CE15's fix (guest/runtime/composer.zig, 62e06e3): the default cap is 30 minutes (913-914), and the
comment (907-912) and its test (970-979) say: "by default short of what a setup made to last an
hour (a token's hour, the commonest lifetime): the jump and the longest default drive (20
minutes) stay within it, so a timeline failing on the jump, no workload's failure, takes a
credential shorter than that". The test checks `jump_max + drive_ms_max_default < an hour`.

A timeline's wall time after the jump is more than its driver phase:
- a second phase (`drive_again`, 1031-1034): the explorer answers `composer.again` yes once for a
  return to an objective's best (advisor.zig:79-83, `again_left` 1; `--objective-extend` on by
  default, main.zig:540), when the first phase ended before a quarter of the timeline limit (an
  hour by default, main.zig:562): a first phase under 15 minutes, then another up to 20;
- the commands still running at the length's end get 30 s (`length_grace_ns`, 750);
- the ending: an eventually or finally command, up to `ending_ms_max` (20 minutes by default,
  1121) before it is killed;
all of it virtual time under the timeline limit (an hour: a timeline past it is a hang).

A credential the setup issued for an hour (the comment's own example) is used by the drivers and
the ending's check. Without the jump, a timeline that is not a hang never reaches its hour; with
it, any timeline longer than an hour minus its jump does.

The model: the jump drawn as the Zig draws it (its band by name, then plainly), the first phase's
length drawn as `drive_drawn_ns` draws it (`composer.drive_ms` halvings, then plainly), a second
phase when the timeline is an objective's return and the first ended before 15 minutes, a grace
when commands ran past the length, an ending's duration from a menu (the world's). Times in ms.
-/

namespace Replica.Clock5

open Determinismo
open Replica.Clock

def hour : Nat := 3600000

/-- composer.zig:984-990 `drive_drawn_ns`. -/
def driveDrawn (maxMs : Nat) : CM Nat := do
  let top := max 1 (maxMs >>> (← below "composer.drive_ms" 7))
  return top / 2 + (← below "random_below" (top - top / 2 + 1))

structure World where
  label : String
  capMs : Nat := 1800000
  driveMaxMs : Nat := 1200000
  objectiveReturn : Bool := true
  /-- The ending command's run (ms): a quick check, one waiting for the system, one killed at
  its window. -/
  endings : List Nat := [1000, 300000, 600000, 1200000]
  ttlMs : Nat := 3600000
  deriving Inhabited

structure Out where
  jump : Nat
  phases : List Nat
  grace : Nat
  ending : Nat
  deriving Repr, Inhabited

def Out.virtual (o : Out) : Nat := o.phases.foldl (· + ·) 0 + o.grace + o.ending

def timeline5 (w : World) : CM Out := do
  let jump ← clockStartDraw w.capMs
  let first ← driveDrawn w.driveMaxMs
  -- drive_again (1031-1034): not asked past a quarter of the limit since the first phase began.
  let second ← if w.objectiveReturn && first < hour / 4 then do pure [← driveDrawn w.driveMaxMs] else pure []
  let grace := if (← below "world.past_the_length" 2) == 1 then 30000 else 0
  let ending := w.endings[(← below "world.ending_ms" w.endings.length)]!
  return { jump, phases := first :: second, grace, ending }

def property : String := "the default wall clock jump never takes a timeline past what its setup made to last an hour (a token's hour), unless the timeline itself is longer"
def source : String := "guest/runtime/composer.zig:907-912 (62e06e3): \"by default short of what a setup made to last an hour (a token's hour, the commonest lifetime): the jump and the longest default drive (20 minutes) stay within it, so a timeline failing on the jump, no workload's failure, takes a credential shorter than that\"; its test 970-979; 900-901 (\"not past what a setup made to expire\")"

def judge (w : World) (src : Source) : Ended :=
  match (timeline5 w).run { decisions := { source := src } } with
  | .ok o s =>
    let t := o.virtual
    let v := if t < w.ttlMs && t < hour && o.jump + t ≥ w.ttlMs then
        some (property, s!"jump {o.jump} ms; driver phases {o.phases} ms, grace {o.grace} ms, ending {o.ending} ms: {t} ms of virtual time (no hang); the setup's hour token is used {o.jump + t - w.ttlMs} ms past its expiry, never without the jump")
      else none
    { taken := s.decisions.taken, violation := v }
  | .error _ s => { taken := s.decisions.taken, violation := none }

def story (w : World) (src : Source) : List String :=
  match (timeline5 w).run { decisions := { source := src } } with
  | .ok o s => s.log.toList ++ [s!"driver phases (ms): {o.phases}", s!"grace: {o.grace} ms; ending: {o.ending} ms",
      s!"virtual time from the draw to the ending's end: {o.virtual} ms (under the hour's limit)",
      s!"wall time from the token's issue: {o.jump + o.virtual} ms (the token lasts {w.ttlMs} ms)"]
  | .error _ _ => []

def worlds : List World :=
  [ { label := "the defaults: a 30-minute cap, 20-minute phases, an objective's return, endings of 1 s to 20 min" },
    { label := "the defaults, no objective's return (one phase), endings of 1 s to 20 min", objectiveReturn := false },
    { label := "the defaults, one phase, a quick ending (1 s): the fix's own claim", objectiveReturn := false, endings := [1000] } ]

/-- Counted over seeds: how many timelines break it, per world. -/
def census (seeds : Nat) : IO Unit := do
  for w in worlds do
    let mut broke := 0
    for seed in [0:seeds] do
      if (judge w (Source.seeded seed)).violation.isSome then broke := broke + 1
    say s!"census [{property} / {w.label}]: {broke} of {seeds} timelines"

def searchAll (seeds : Nat) : IO Unit := do
  say s!"== clock property: {property}"
  say s!"   source: {source}"
  for w in worlds do
    if let some f ← exploreSaid s!"{property} / {w.label}" (judge w) seeds then
      printFound f (story w)
  census seeds

end Replica.Clock5
