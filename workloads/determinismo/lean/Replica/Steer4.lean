import Replica.Prelude
import Replica.Searching

/-!
# The tree's steering: a targeted run's report (src/main.zig, src/changed.zig, platform 3939448)

A targeted run (`--changed`) counts, for each hunk of the change, the timelines that ran its
lines and the first of them (`tree_judge_begin`, main.zig:6363-6381: over `done`, the timelines
of the generations judged now), and at the run's end prints each hunk "ran in <count>/<timelines>
timelines" or "NEVER RAN" (`Change.summarize`, changed.zig:66-85, with `state.next_index` as the
timelines; recorded as `{"changed":...}`, main.zig:4383-4391).

What is judged (main.zig:4100-4370): generations of `size` timelines, judged when that many ended
(`judge_count`, 4614-4620); at the loop's end, a last partial generation only while the run is
not past its budget and has timelines left to plan (4360-4363: `!late and
batch.summaries.count > 0 and state.next_index < state.total`). With one generation planned ahead
(`--pipeline 1`), each judgment plans the next `size` (its returns and the fresh fill, up to
`total`), so `next_index` is `min(total, size * (judged generations + 1))`.

The world: each timeline runs some of the hunks; timelines end in index order; the budget may
end after any of them (`late`).
-/

namespace Replica.Steer4

open Determinismo

structure SCfg where
  label : String
  size : Nat := 2
  total : Nat := 3
  hunks : Nat := 1
  budget : Bool := false
  /-- Round 6: main.zig as at a7fe05d (every ended timeline counted, `change_count`) unless a
  theorem about 3939448 says so. -/
  ver : Ver := .vdf8f08b
  deriving Inhabited

structure SS where
  decisions : Decisions := {}
  deriving Inhabited

instance : Chaotic SS where
  decisions s := s.decisions
  setDecisions _ d := { decisions := d }

abbrev SM := EStateM Stop SS

structure Targeted where
  /-- Each timeline's hunks, for those that ran. -/
  ran : List (List Nat)
  /-- The hunks' counts and the timelines figure, as the report prints them. -/
  counts : List Nat
  timelines : Nat
  judged : Nat
  deriving Repr, Inhabited

def runOf (cfg : SCfg) : SM Targeted := do
  let mut ran : List (List Nat) := []
  let mut judged := 0
  let mut batch := 0
  let mut generations := 0
  let mut late := false
  let mut counts := List.replicate cfg.hunks 0
  for i in [0:cfg.total] do
    -- Planned yet? (pipeline 1: the next generation is planned at each judgment).
    let nextIndex := min cfg.total (cfg.size * (generations + 1))
    if i ≥ nextIndex then break
    let mut mine := []
    for h in [0:cfg.hunks] do
      if (← below "timeline.hunk" 2) == 1 then mine := mine ++ [h]
    ran := ran ++ [mine]
    batch := batch + 1
    -- main.zig:4280-4285: a complete generation judged (one judgment of the whole ones).
    if batch ≥ cfg.size then
      let whole := cfg.size * (batch / cfg.size)
      for t in ran.drop judged |>.take whole do
        counts := counts.zipIdx.map fun (c, h) => if t.contains h then c + 1 else c
      judged := judged + whole
      batch := batch - whole
      generations := generations + whole / cfg.size
    if cfg.budget then
      if (← below "budget.over" 2) == 1 then
        late := true
        break
  let nextIndex := min cfg.total (cfg.size * (generations + 1))
  -- main.zig:4360-4363: the last partial generation, unless late or every timeline planned.
  if !late && batch > 0 && nextIndex < cfg.total then
    for t in ran.drop judged do
      counts := counts.zipIdx.map fun (c, h) => if t.contains h then c + 1 else c
    judged := judged + batch
  -- a7fe05d (main.zig:4462-4464, 6426-6445; changed.zig:69-70): the batch's summaries no judgment
  -- took counted at the end too, and "ran in n/N" divides by the timelines counted (CE39's fix).
  if cfg.ver.sinceA7 then
    for t in ran.drop judged do
      counts := counts.zipIdx.map fun (c, h) => if t.contains h then c + 1 else c
    return { ran, counts, timelines := ran.length, judged := ran.length }
  return { ran, counts, timelines := nextIndex, judged }

def reportLine (t : Targeted) (h : Nat) : String :=
  let c := t.counts[h]!
  if c == 0 then s!"NEVER RAN  hunk {h}" else s!"ran in {c}/{t.timelines} timelines  hunk {h}"

def property : String := "a targeted run reports each hunk in as many timelines as ran it, NEVER RAN only for one none ran"
def source : String := "docs/AGENTS.md:319-322 (\"reports which hunks ran in how many timelines and which never did\"); README_AI.md:319-320 (\"says which of them ran, in how many timelines, and which never did\"); docs/ANTITHESIS.md:131"

def check (t : Targeted) : Option String := Id.run do
  for h in [0:t.counts.length] do
    let truly := (t.ran.filter (·.contains h)).length
    if truly != t.counts[h]! then
      return some s!"{t.ran.length} timelines ran (hunks {t.ran}), {t.judged} of them judged; the report: \"{reportLine t h}\"; {truly} timelines ran hunk {h}"
  return none

def judgeS (cfg : SCfg) (src : Source) : Ended :=
  match (runOf cfg).run { decisions := { source := src } } with
  | .ok t s => { taken := s.decisions.taken, violation := (check t).map (property, ·) }
  | .error _ s => { taken := s.decisions.taken, violation := none }

def storyS (cfg : SCfg) (src : Source) : List String :=
  match (runOf cfg).run { decisions := { source := src } } with
  | .ok t _ =>
    [s!"generations of {cfg.size}, {cfg.total} timelines; each timeline's hunks: {t.ran}",
     s!"judged (counted): the first {t.judged}; the rest ended in a last partial generation never judged"] ++
    ((List.range cfg.hunks).map fun h => s!"  {reportLine t h}")
  | .error _ _ => []

def sworlds : List SCfg :=
  [ { label := "generations of 2, 3 timelines, one hunk" },
    { label := "generations of 2, 4 timelines, one hunk, a budget", total := 4, budget := true },
    { label := "generations of 16, 20 timelines, one hunk", size := 16, total := 20 },
    { label := "generations of 4, 8 timelines, two hunks", size := 4, total := 8, hunks := 2 },
    { label := "3939448: generations of 2, 3 timelines, one hunk", ver := .v3939448 } ]

def searchAll (exhaustRuns seeds : Nat) : IO Unit := do
  say s!"== steering property: {property}"
  say s!"   source: {source}"
  for cfg in sworlds do
    if let some f ← exhaustSaid s!"{property} / {cfg.label}" (judgeS cfg) exhaustRuns then
      printFound f (storyS cfg)
    if let some f ← exploreSaid s!"{property} / {cfg.label}" (judgeS cfg) seeds then
      printFound f (storyS cfg)

end Replica.Steer4
