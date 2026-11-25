import Replica.Prelude
import Replica.Searching
import Replica.Composer

/-!
# A timeline's wall clock start, replicated (guest/runtime/composer.zig:895-940, platform 3939448)

`clock_start_draw` (905-927): as a timeline's commands begin, its wall clock (CLOCK_REALTIME) moves
forward by `ms`, log-uniform from a second to `det.clock_start_max_ms=` (explore's
`--clock-start-max`; an hour unless asked, 0 none): a band by name (`composer.clock_start`, one of
`clock_start_bands(max)`), then a plain draw within it (`clock_start_band`, 934-937). The monotonic
clock and the timers' durations stay.

What the comment promises (895-902): "Never back, and not past what a setup made to expire (a
token's hour, a lease): a timeline failing on the jump would be no workload's failure." And the
e2e's `clock-start` check (tools/e2e.zig:8801-8840): "each start a second to an hour past the
guest's own".

The world: a setup that issues a credential valid for `ttl` ms of wall time (a token's hour: the
comment's own example), some time `elapsed` before the timeline's composer draws its start (the
setup's end, the SDK's setup wait, the snapshot: a decision of the world among a menu), and the
drivers' first use of the credential right after the jump. Times in ms.
-/

namespace Replica.Clock

open Determinismo
open Replica.Composer (clockStartBands clockStartBand)

structure CS where
  decisions : Decisions := {}
  log : Array String := #[]
  deriving Inhabited

instance : Chaotic CS where
  decisions s := s.decisions
  setDecisions s d := { s with decisions := d }

abbrev CM := EStateM Stop CS

/-- composer.zig:905-927 `clock_start_draw`: the jump, in ms (0: none). -/
def clockStartDraw (maxMs : Nat) : CM Nat := do
  let bands := clockStartBands maxMs
  if bands == 0 then return 0
  let band ← below "composer.clock_start" bands
  let (low, high) := clockStartBand maxMs band
  let ms := low + (← below "random_below" (high - low + 1))
  modify fun s => { s with log := s.log.push s!"clock_start ms={ms} max_ms={maxMs} (band {band}: {low}..{high})" }
  return ms

/-- A world: the cap, the credential's validity, the time from its issue to the draw. -/
structure CWorld where
  label : String
  maxMs : Nat := 3600000
  ttlMs : Nat := 3600000
  /-- The world's menu for the time between the credential's issue (in the setup) and the draw. -/
  elapsedMenu : List Nat := [0, 1000, 30000]

structure Outcome where
  jump : Nat
  elapsed : Nat
  deriving Inhabited

def timeline (wd : CWorld) : CM Outcome := do
  let elapsed := wd.elapsedMenu[(← below "world.elapsed" wd.elapsedMenu.length)]!
  let jump ← clockStartDraw wd.maxMs
  return { jump, elapsed }

structure CProp where
  name : String
  source : String
  check : CWorld → Outcome → Option String

/-- The comment's promise: the credential the setup issued for `ttl` is still valid when the
drivers first use it, right after the jump (wall time issued + elapsed + jump, before issued + ttl). -/
def notPastSetupExpiry : CProp :=
  { name := "the wall clock's jump never takes it past what the setup made to expire (a token's hour)"
    source := "guest/runtime/composer.zig:900-901 (clock_start_draw's comment): \"Never back, and not past what a setup made to expire (a token's hour, a lease): a timeline failing on the jump would be no workload's failure\"; main.zig:91-93 (--clock-start-max: 1h by default)"
    check := fun wd o =>
      -- Valid before the jump, expired by it.
      if o.elapsed < wd.ttlMs && o.elapsed + o.jump ≥ wd.ttlMs then
        some s!"a credential issued in the setup for {wd.ttlMs} ms, {o.elapsed} ms before the draw: the jump of {o.jump} ms puts the drivers' first use {o.elapsed + o.jump - wd.ttlMs} ms past its expiry"
      else none }

/-- The e2e's claim and "never back": a second to the cap. -/
def withinTheCap : CProp :=
  { name := "the jump is a second to the cap, never back"
    source := "tools/e2e.zig:8801-8840 (check_clock_start: \"each start a second to an hour past the guest's own\"); composer.zig:889 (\"Never back\")"
    check := fun wd o =>
      if clockStartBands wd.maxMs == 0 then (if o.jump == 0 then none else some s!"jump {o.jump} with no band")
      else if o.jump < 1000 || o.jump > wd.maxMs then some s!"jump {o.jump} outside [1000, {wd.maxMs}]" else none }

def allCProps : List CProp := [notPastSetupExpiry, withinTheCap]

def judgeC (p : CProp) (wd : CWorld) (source : Source) : Ended :=
  match (timeline wd).run { decisions := { source } } with
  | .ok o s => { taken := s.decisions.taken, violation := (p.check wd o).map fun d => (p.name, d) }
  | .error _ s => { taken := s.decisions.taken, violation := none }

def cstory (wd : CWorld) (source : Source) : List String :=
  match (timeline wd).run { decisions := { source } } with
  | .ok o s => s.log.toList ++ [s!"the credential: valid {wd.ttlMs} ms from its issue in the setup, issued {o.elapsed} ms before the draw",
                               s!"the drivers' first use: {o.elapsed + o.jump} ms of wall time after its issue"]
  | .error _ _ => []

/-- The Zig's hour (explored), and small caps (exhausted: every band, every ms in it). -/
def cworlds : List CWorld :=
  [ { label := "a cap of 8 s, a credential valid 8 s (the cap's own length, as the hour is the default's)", maxMs := 8000, ttlMs := 8000, elapsedMenu := [0, 1000, 3000] },
    { label := "a cap of 8 s, a credential valid 16 s", maxMs := 8000, ttlMs := 16000, elapsedMenu := [0, 1000, 3000] },
    { label := "the default hour, a token's hour (the comment's example)", maxMs := 3600000, ttlMs := 3600000 },
    { label := "the default hour, a lease of 60 s from the setup", maxMs := 3600000, ttlMs := 60000 } ]

def searchAll (exhaustRuns seeds : Nat) : IO (List Found) := do
  let mut found := []
  for p in allCProps do
    say s!"== clock property: {p.name}"
    say s!"   source: {p.source}"
    for wd in cworlds do
      if wd.maxMs ≤ 16000 then
        if let some f ← exhaustSaid s!"{p.name} / {wd.label}" (judgeC p wd) exhaustRuns then
          printFound f (cstory wd)
          found := found ++ [f]
      else
        if let some f ← exploreSaid s!"{p.name} / {wd.label}" (judgeC p wd) seeds then
          printFound f (cstory wd)
          found := found ++ [f]
  return found

end Replica.Clock
