import Replica.Prelude
import Replica.Searching

/-!
# A session's steps on its tape, and returns into a full tape (round 6)

## Steps (src/core/tape.zig, a7fe05d)

A session's timeline tapes each step it ran at its moment (vm.zig:2205-2208 `step_record`, 2243-2246
`session_end`; main.zig:3750-3759 copies a parent's steps to an extending timeline), by
`write_step` (tape.zig:500-511): the line's head `{"vtime":<ns>,"step":` written at once, then the
step's text as a JSON string into a fixed buffer of 2 * 65,536 bytes with `}\n`; when the string
does not fit, `catch return`: the head stays on the tape, unfinished, and the next line written
continues it. A step is a line of the session's input of any length (vm.zig:2169-2196: no limit);
`det:ask <fifo> <id> <base64 parts>` is one step a REPL message (vm.zig:1895-1899), its whole text
taped.

The replay's parse (tape.zig:596-635): each line a JSON object (`std.json.parseFromSliceLeaky`,
an error otherwise), a step line into a fixed table (`step_parse`, 513-522): at most `steps_max`
(65,536) steps and `step_text_max` (16 MiB) of their text, else TapeTooLong. Nothing on the
recorder's side counts steps (`tape_override`'s cap, vm.zig:3684-3699, counts overrides only).

Property: README_AI.md "every timeline replays bit-identically"; vm.zig:2202-2203 ("A step the
moment runs, on the timeline's own tape at the moment it ran: a replay of the timeline runs it
there again"); CE20's fix's own words (vm.zig:3684-3687): "instead of a tape no replay can read".

## Returns into a full tape (main.zig, a7fe05d)

A timeline's recorder stops taping at override_count_max (1,048,576) overrides and writes
`tape_full` at the next pull (vm.zig:3684-3699); a replay stops there (TapeFull, tape.zig:
310-320). The explorer never reads it (no reference in main.zig): a judgment returns to any
moment of a judged timeline. A node made from a holder at a moment past the marker is the real
state, so its children run; each child's tape `chain`s through the parent up to that moment
(tape.Segment), and its replay alone (README_AI.md: every timeline replays; docs/ANTITHESIS.md,
Branching: "every timeline's path in its record and tape (it replays alone)") stops at the
parent's marker. A node made by replay stops there itself.
-/

namespace Replica.Tape6

open Determinismo

/-! ## Steps -/

structure SC where
  /-- write_step's text buffer (2 * 65,536). -/
  buffer : Nat := 131072
  /-- steps_max (65,536). -/
  stepsMax : Nat := 65536
  /-- step_text_max (16 MiB). -/
  textMax : Nat := 16777216
  /-- The longest step a line's parse reads into the 64 KiB scratch its callers give (main.zig:
  2612, 3332; node.zig:60): std.json's `Value` copies every string (`.alloc_always`), so a step's
  text, grown by an ArrayList's doublings, must fit beside the line's map. Measured with Zig
  0.17's std.json on a copy of a7fe05d's tape.zig: 42,235 bytes (runs6/ce52-zig.txt). -/
  scratchMax : Nat := 42235
  /-- Round 7: the code's version. df8f08b (CE52's fix): `write_step` (tape.zig:512-547) streams a
  step's line whole through a 4 KiB buffer, escaping as it goes; `step_line_parse` (552-609)
  decodes the string straight into the step table (no scratch); `step_record` (vm.zig:2214-2221)
  refuses a step past `step_fits(steps + 1, bytes + "det:over".len, len)` (TapeStepsFull, before
  it runs), room kept for the session's det:over. -/
  ver : Ver := .vdf8f08b
  deriving Repr, Inhabited

/-- What a session tapes, in order. `step len escapes`: a step of `len` bytes, `escapes` of them
written as two (`"`, `\`, a line break). -/
inductive Item where
  | override (pull : Nat)
  | step (len escapes : Nat)
  deriving Repr, BEq, Inhabited

/-- What lands on the tape: a whole line, or a line's head left unfinished. -/
inductive Piece where
  | line (item : Item)
  | head (item : Item)
  deriving Repr, BEq, Inhabited

/-- The JSON string of a step: its bytes, its escapes' second bytes, the two quotes. -/
def jsonLen (len escapes : Nat) : Nat := len + escapes + 2

/-- `det:over`'s length, the room `step_record` keeps (vm.zig:2217). -/
def overLen : Nat := 8

/-- vm.zig:2214-2221 (df8f08b) `step_record`'s cap: tape.zig:499-502 `step_fits(count, used, size)`
= `count < steps_max and used + size <= step_text_max`, asked for one more step and det:over's
bytes. The steps it lets on the tape, in order (a refused step errs, the session's step fails). -/
def accepted (c : SC) (items : List Item) : List Item := Id.run do
  let mut out : Array Item := #[]
  let mut steps := 0
  let mut bytes := 0
  for it in items do
    match it with
    | .override _ => out := out.push it
    | .step len _ =>
      if steps + 1 < c.stepsMax && bytes + overLen + len ≤ c.textMax then
        out := out.push it
        steps := steps + 1
        bytes := bytes + len
  return out.toList

/-- tape.zig:500-511 `write_step` and 400-415 `write_override`. df8f08b: every accepted step's
line written whole. -/
def record (c : SC) (items : List Item) : List Piece :=
  if c.ver.sinceDf then (accepted c items).map .line else
  items.map fun
    | .override p => .line (.override p)
    | .step len esc => if jsonLen len esc + 2 > c.buffer then .head (.step len esc) else .line (.step len esc)

/-- What the recorder wrote whole (what a replay must read back). -/
def written (c : SC) (items : List Item) : List Item :=
  if c.ver.sinceDf then accepted c items else items

/-- The tape's lines as its parse reads them: a head runs on into the next piece. -/
def lines (pieces : List Piece) : List (List Piece) := Id.run do
  let mut out : Array (List Piece) := #[]
  let mut cur : Array Piece := #[]
  for p in pieces do
    cur := cur.push p
    match p with
    | .line _ => out := out.push cur.toList; cur := #[]
    | .head _ => pure ()
  if !cur.isEmpty then out := out.push cur.toList
  return out.toList

/-- tape.zig:596-635 `parse`, 513-522 `step_parse`: the error, or the items it read. -/
def parse (c : SC) (pieces : List Piece) : Except String (List Item) := do
  let mut out : Array Item := #[]
  let mut steps := 0
  let mut text := 0
  for l in lines pieces do
    match l with
    | [.line it] =>
      match it with
      | .step len esc =>
        if !c.ver.sinceDf && len > c.scratchMax then throw s!"OutOfMemory (a step of {len} bytes, {esc} escaped, in the line parse's 64 KiB scratch)"
        if steps == c.stepsMax || text + len > c.textMax then throw "TapeTooLong (steps_max, step_text_max)"
        steps := steps + 1
        text := text + len
      | .override _ => pure ()
      out := out.push it
    | _ => throw s!"the parse's JSON error (a line begun by an unfinished step's head: {reprStr l})"
  return out.toList

def stepsProp : String := "a session's timeline replays from its tape: every step and override the recorder wrote is read back"
def stepsSource : String := "README_AI.md (\"every timeline replays bit-identically\"); src/core/vm.zig:2202-2203 (a7fe05d: \"A step the moment runs, on the timeline's own tape at the moment it ran: a replay of the timeline runs it there again\"), 3684-3687 (\"instead of a tape no replay can read\")"

structure S where
  decisions : Decisions := {}
  deriving Inhabited

instance : Chaotic S where
  decisions s := s.decisions
  setDecisions _ d := { decisions := d }

structure SW where
  label : String
  consts : SC
  items : Nat := 3
  lens : List Nat
  deriving Inhabited

def drawSteps (w : SW) : EStateM Stop S (List Item) := do
  let mut out := []
  let mut pull := 1
  for _ in [0:w.items] do
    match (← below "world.item" (w.lens.length + 1)) with
    | 0 => out := out ++ [.override pull]; pull := pull + 1
    | k => out := out ++ [.step w.lens[k - 1]! 0]
  return out

def judgeSteps (w : SW) (src : Source) : Ended :=
  match (drawSteps w).run { decisions := { source := src } } with
  | .ok items s =>
    let taped := record w.consts items
    { taken := s.decisions.taken,
      violation := match parse w.consts taped with
        | .ok back => if back == written w.consts items then none else some (stepsProp, s!"taped {reprStr (written w.consts items)}, read back {reprStr back}")
        | .error e => some (stepsProp, s!"the session ran {reprStr items}; its tape: {reprStr taped}; the replay's parse: {e}") }
  | .error _ s => { taken := s.decisions.taken, violation := none }

def stepWorlds : List SW :=
  [ { label := "a buffer of 16 bytes, steps of 4 or 20 bytes, overrides, 3 items", consts := { buffer := 16, scratchMax := 1000 }, lens := [4, 20] },
    { label := "a parse scratch of 8 bytes, a buffer of 100, steps of 4 or 12 bytes, overrides, 3 items", consts := { buffer := 100, scratchMax := 8 }, lens := [4, 12] },
    { label := "a step table of 2 steps and 10 bytes, steps of 4 bytes, 4 items", consts := { buffer := 1000, stepsMax := 2, textMax := 10 }, items := 4, lens := [4] },
    -- Round 7: the same three at a7fe05d (CE52 found again there).
    { label := "a7fe05d: a buffer of 16 bytes, steps of 4 or 20 bytes, overrides, 3 items", consts := { buffer := 16, scratchMax := 1000, ver := .va7fe05d }, lens := [4, 20] },
    { label := "a7fe05d: a parse scratch of 8 bytes, a buffer of 100, steps of 4 or 12 bytes, overrides, 3 items", consts := { buffer := 100, scratchMax := 8, ver := .va7fe05d }, lens := [4, 12] },
    { label := "a7fe05d: a step table of 2 steps and 10 bytes, steps of 4 bytes, 4 items", consts := { buffer := 1000, stepsMax := 2, textMax := 10, ver := .va7fe05d }, items := 4, lens := [4] },
    -- Round 7: a table of 3 steps and 20 bytes, steps of 4 or 9 bytes, 5 items (the cap's edges).
    { label := "a step table of 3 steps and 20 bytes, steps of 4 or 9 bytes, 5 items", consts := { buffer := 1000, stepsMax := 3, textMax := 20 }, items := 5, lens := [4, 9] } ]

/-! ## Returns into a full tape -/

structure FC where
  /-- override_count_max (1,048,576). -/
  overrideMax : Nat := 1048576
  deriving Repr, Inhabited

/-- The parent's run: at each pull an override (true) or a plain draw. Its tape: the overrides up
to the cap, then `tape_full` at the next override's pull (vm.zig:3688-3699). -/
def fullAt (c : FC) (overrides : List Bool) : Option Nat := Id.run do
  let mut written := 0
  for (o, pull) in overrides.zipIdx do
    if o then
      if written ≥ c.overrideMax then return some pull
      written := written + 1
  return none

/-- A replay of the parent to moment `m` (its pulls before `m`): stops at TapeFull when a pull at
or past the marker comes first (tape.zig:310-320, vm.zig:3709). -/
def replayTo (full : Option Nat) (m : Nat) : Except String Unit :=
  match full with
  | some at_ => if at_ < m then .error s!"TapeFull at pull {at_}" else .ok ()
  | none => .ok ()

structure FW where
  label : String
  consts : FC
  pulls : Nat := 3
  holders : Bool := true
  /-- Round 7: the code's version. df8f08b (main.zig:4083, 6552-6558 `returns_before_ns`): a judged
  timeline's `last_pull_ns` is also before its tape was full (VM.tape_full_ns), so the frontier's
  and the archive's moments land before the marker. -/
  ver : Ver := .vc4f246e
  /-- Round 7: the parent was cut at its horizon (`--horizon`): `archive_add` (main.zig:7374)
  takes a cut branch's moments to its end (`open = summary.cut or at < summary.last_pull_ns`).
  Round 8, c4f246e (CE58's fix): `open_to_end` (main.zig:6603-6608) is `cut` and no full tape;
  the archive (7502), the frontier (7065) and the extension (7801) read it. -/
  cut : Bool := false
  /-- Round 7: a strategy (a plugin) chooses the moment: `tree_returns` (main.zig:7625-7631)
  bounds it by the timeline's start and end alone. Round 8, c4f246e: offered and bounded by
  `returns_end` (main.zig:6610-6614, 7737, 7760): the end, or the marker if the tape was full. -/
  strategy : Bool := false
  /-- Round 8: the strategy returns to a timeline of an earlier generation (its own archive:
  `planned`, not among this generation's candidates): main.zig:7753-7762 (c4f246e) checks such a
  return against nothing (`else if (!planned.contains(back.branch)) continue;`). -/
  earlier : Bool := false
  deriving Inhabited

structure Return where
  overrides : List Bool
  moment : Nat
  holder : Bool
  deriving Repr, Inhabited

def drawReturn (w : FW) : EStateM Stop S Return := do
  let mut overrides := []
  for _ in [0:w.pulls] do overrides := overrides ++ [(← below "parent.override" 2) == 1]
  -- The judgment's moment: any of the parent's (its returns drawn among them); at df8f08b, an
  -- uncut parent's explorer returns before its tape was full.
  let full := fullAt w.consts overrides
  -- c4f246e: a cut parent's places and a strategy's return to one of this generation's
  -- timelines land before the marker too; a strategy's return to an earlier one is unbounded.
  let bounded := if w.ver.sinceC4 then !(w.strategy && w.earlier)
    else w.ver.sinceDf && !w.cut && !w.strategy
  let bound := if bounded then (full.getD w.pulls) else w.pulls
  let moment ← below "judgment.moment" (bound + 1)
  let holder ← if w.holders then do pure ((← below "node.holder" 2) == 0) else pure false
  return { overrides, moment, holder }

def fullProp : String := "every timeline the tree makes replays alone from its tape and chain"
def fullSource : String := "README_AI.md (\"every timeline replays bit-identically\"); docs/ANTITHESIS.md (Branching: \"every timeline's path in its record and tape (it replays alone)\"); vm.zig:3684-3687 (a7fe05d: a replay stops at the marker)"

def judgeFull (w : FW) (src : Source) : Ended :=
  match (drawReturn w).run { decisions := { source := src } } with
  | .ok r s =>
    let full := fullAt w.consts r.overrides
    -- The node: a holder's state (always made), or a replay of the parent (made or not).
    let nodeMade := r.holder || (replayTo full r.moment).isOk
    let v := if !nodeMade then none else
      match replayTo full r.moment with
      | .error e => some (fullProp, s!"the parent's pulls {r.overrides.map fun o => if o then "override" else "draw"}, its tape full at pull {full.getD 0} (a cap of {w.consts.overrideMax}); the tree returns to its moment {r.moment} from a holder: the child runs; replayed alone, its chain through the parent stops: {e}")
      | .ok () => none
    { taken := s.decisions.taken, violation := v }
  | .error _ s => { taken := s.decisions.taken, violation := none }

def fullWorlds : List FW :=
  [ { label := "a cap of one override, a parent of 3 pulls, holders", consts := { overrideMax := 1 } },
    { label := "a cap of one override, a parent of 3 pulls, no holders (a deciding strategy)", consts := { overrideMax := 1 }, holders := false },
    -- Round 7: a7fe05d (CE53 found again); a parent cut at its horizon (the archive's place);
    -- a strategy's moment.
    { label := "a7fe05d: a cap of one override, a parent of 3 pulls, holders", consts := { overrideMax := 1 }, ver := .va7fe05d },
    { label := "a cap of one override, a parent of 3 pulls cut at its horizon, holders (the archive)", consts := { overrideMax := 1 }, cut := true },
    { label := "a cap of one override, a parent of 3 pulls, holders, a strategy's moment", consts := { overrideMax := 1 }, strategy := true },
    -- Round 8: df8f08b's cut and strategy worlds (CE58 found again there), and a strategy's
    -- return to a timeline of an earlier generation at c4f246e.
    { label := "df8f08b: a cap of one override, a parent of 3 pulls cut at its horizon, holders (the archive)", consts := { overrideMax := 1 }, cut := true, ver := .vdf8f08b },
    { label := "df8f08b: a cap of one override, a parent of 3 pulls, holders, a strategy's moment", consts := { overrideMax := 1 }, strategy := true, ver := .vdf8f08b },
    { label := "a cap of one override, a parent of 3 pulls cut at its horizon, holders, a strategy's moment", consts := { overrideMax := 1 }, cut := true, strategy := true },
    { label := "a cap of one override, a parent of 3 pulls, holders, a strategy's moment in a timeline of an earlier generation", consts := { overrideMax := 1 }, strategy := true, earlier := true },
    { label := "a cap of two overrides, a parent of 5 pulls cut at its horizon, holders", consts := { overrideMax := 2 }, pulls := 5, cut := true },
    { label := "a cap of two overrides, a parent of 5 pulls, holders", consts := { overrideMax := 2 }, pulls := 5 } ]

def searchAll (exhaustRuns : Nat) : IO Unit := do
  say s!"== tape property: {stepsProp}"
  say s!"   source: {stepsSource}"
  for w in stepWorlds do
    if let some f ← exhaustSaid s!"{stepsProp} / {w.label}" (judgeSteps w) exhaustRuns then
      printFound f (fun _ => [])
  -- The Zig's sizes: one REPL message of 96 KiB as det:ask's base64 (4/3 of it, 131,072 bytes).
  let ask : Item := .step 131072 0
  say s!"the Zig's buffer, a det:ask step of 131,072 bytes (a 96 KiB message in base64), then the session's end: {reprStr (parse {} (record {} [ask, .step 7 0]))}"
  say s!"the Zig's scratch, a det:ask step of 42,236 bytes (a 31 KiB message in base64): {reprStr (parse {} (record {} [.step 42236 0, .step 7 0]))}; of 42,235 bytes: {reprStr ((parse {} (record {} [.step 42235 0, .step 7 0])).toOption.isSome)}"
  say s!"the Zig's buffer, a step of 70,000 bytes of Clojure with 61,072 quotes and line breaks: {reprStr (parse {} (record {} [.step 70000 61072]))}"
  say s!"the Zig's table, 65,537 steps of 10 bytes: {match parse {} (record {} (List.replicate 65537 (.step 10 0))) with | .ok _ => "read" | .error e => e}"
  say s!"== tape property: {fullProp}"
  say s!"   source: {fullSource}"
  for w in fullWorlds do
    if let some f ← exhaustSaid s!"{fullProp} / {w.label}" (judgeFull w) exhaustRuns then
      printFound f (fun _ => [])

end Replica.Tape6
