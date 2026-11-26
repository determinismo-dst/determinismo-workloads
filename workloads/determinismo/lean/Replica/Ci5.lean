import Replica.Ci
import Replica.Junit

/-!
# determinismo-ci at 62e06e3: a shard's xargs runs and their reports merged (round 5)

`shard_command` (src/products/ci.zig:526-561, 62e06e3), the `{tests}` mode with `junit`: each
xargs run of the runner is `sh -c '<run>; s=$?; if [ -f <junit> ]; then mv <junit>
<junit>.determinismo-ci-part.$$; fi; exit $s' sh <names...>` (539-547): the run line as written,
`{tests}` replaced by `"$@"`, then the move appended after a `;`. After xargs (548-554): `set --
<junit>.determinismo-ci-part.*; if [ -e "$1" ]; then cat "$@" > <junit>; rm -f "$@"; fi`: the
parts, when any, become the report `det-assert junit` reads (ci.zig:229-233); else the file at
the path stays as the last run left it.

The appended move runs only when the shell gets past the run line. A run line that leaves the
shell itself never reaches it:
- one ending in `exit` (examples/ci-demo/ci-capped.json:6, the repository's own: `...; exit
  $status`),
- one that `exec`s its runner (`cd /app && exec pytest {tests}`),
- one whose last word is a `#` comment (the appended text is the comment's),
- one under `set -e` whose runner failed (the shell exits at the failing command).

What the documentation and the fix promise: docs/CI.md (`junit`): "each test gets its own verdict
across its shard's timelines"; ci.zig:528-531: "with a report each run's is moved aside and all of
them make the report ...: every test of the shard gets its verdict, not only the last run's (CE21)".

The model: a shard's names, xargs's runs of them (`Junit.xargsBatches`, GNU's rule), each run's
runner writing a fresh report of its own names at the path and exiting 0 or 1 (the world's
decision), the shell's control flow by the run line's form.
-/

namespace Replica.Ci5

open Determinismo

/-- How a run line ends the shell it runs in. -/
inductive RunLine where
  /-- `cd /app && pytest --junitxml /tmp/junit.xml {tests}`: falls through. -/
  | plain
  /-- `...; exit $status` (examples/ci-demo/ci-capped.json). -/
  | exits
  /-- `cd /app && exec pytest ... {tests}`. -/
  | execs
  /-- `pytest ... {tests}  # the slow ones too`. -/
  | comment
  /-- `set -e; cd /app; pytest ... {tests}`. -/
  | setE
  deriving BEq, Repr, Inhabited, DecidableEq

def RunLine.show : RunLine → String
  | .plain => "cd /app && python -m pytest --junitxml /tmp/junit.xml {tests}"
  | .exits => "cd /app && python -m pytest ... --junitxml /tmp/junit.xml {tests}; status=$?; python -c ...; exit $status (ci-capped.json)"
  | .execs => "cd /app && exec python -m pytest --junitxml /tmp/junit.xml {tests}"
  | .comment => "python -m pytest --junitxml /tmp/junit.xml {tests}  # all of them"
  | .setE => "set -e; cd /app; python -m pytest --junitxml /tmp/junit.xml {tests}"

/-- Whether the shell reaches the appended move after a run of the runner that exited `failed`. -/
def RunLine.reachesMove (r : RunLine) (failed : Bool) : Bool :=
  match r with
  | .plain => true
  | .setE => !failed
  | _ => false

/-- One xargs run: its names, and whether its runner failed. -/
structure Run where
  names : List String
  failed : Bool
  deriving Repr, Inhabited

/-- The file system's part of it: the report at the path, and the parts moved aside. -/
structure Files where
  report : Option (List String) := none
  parts : List (List String) := []
  deriving Repr, Inhabited

/-- One xargs run (ci.zig:539-547, 62e06e3): its report written fresh at the path, then moved
aside when the shell gets there. 3939448 (ci.zig:226-233): no move. -/
def step (ver : Ver) (line : RunLine) (f : Files) (r : Run) : Files :=
  if ver = .v62e06e3 ∧ line.reachesMove r.failed = true then { report := none, parts := f.parts ++ [r.names] }
  else { f with report := some r.names }

/-- After xargs (ci.zig:548-554): the parts concatenated over the path, when any. Returns the
names in the report `det-assert junit` reads. -/
def judged (ver : Ver) (line : RunLine) (runs : List Run) : List String :=
  let f := runs.foldl (step ver line) {}
  let f := if ver = .v62e06e3 ∧ f.parts ≠ [] then { report := some f.parts.flatten, parts := [] } else f
  f.report.getD []

structure S where
  decisions : Decisions := {}
  deriving Inhabited

instance : Chaotic S where
  decisions s := s.decisions
  setDecisions _ d := { decisions := d }

structure World where
  label : String
  lines : List RunLine := [.plain, .exits, .execs, .comment, .setE]
  testsMax : Nat := 4
  lengths : List Nat := [5, 12, 20]
  buffer : Nat := 48
  base : Nat := 16
  ver : Ver := .v62e06e3

structure Drawn where
  line : RunLine
  runs : List Run
  deriving Inhabited

def draw (w : World) : EStateM Stop S Drawn := do
  let line := w.lines[(← below "world.run_line" w.lines.length)]!
  let n := 1 + (← below "world.tests" w.testsMax)
  let mut names := []
  for i in [0:n] do
    let len := w.lengths[(← below "world.name_length" w.lengths.length)]!
    let stem := s!"t{i}_"
    names := names ++ [stem ++ String.ofList (List.replicate (len - min len stem.length) 'x')]
  let mut runs := []
  for b in Junit.xargsBatches w.buffer w.base names do
    runs := runs ++ [{ names := b, failed := (← below "world.runner_fails" 2) == 1 }]
  return { line, runs }

def property : String := "every test of a shard gets its verdict, however many runs xargs splits the list into"
def source : String := "docs/CI.md (`junit`: \"each test gets its own verdict across its shard's timelines\"); src/products/ci.zig:526-531 (62e06e3, CE21's fix: \"with a report each run's is moved aside and all of them make the report ...: every test of the shard gets its verdict, not only the last run's\")"

def judge (w : World) (src : Source) : Ended :=
  match (draw w).run { decisions := { source := src } } with
  | .ok d s =>
    let names := d.runs.flatMap (·.names)
    let got := judged w.ver d.line d.runs
    let lost := names.filter (!got.contains ·)
    { taken := s.decisions.taken,
      violation := if lost.isEmpty then none else
        some (property, s!"run line `{d.line.show}`, {d.runs.length} xargs runs ({d.runs.map fun r => if r.failed then "failing" else "passing"}): {lost.length} of {names.length} tests never judged: {lost}") }
  | .error _ s => { taken := s.decisions.taken, violation := none }

def story (w : World) (src : Source) : List String :=
  match (draw w).run { decisions := { source := src } } with
  | .ok d _ =>
    [s!"the run line: {d.line.show}"] ++
    (d.runs.zipIdx.map fun (r, i) =>
      s!"xargs run {i + 1}: {r.names}, its runner {if r.failed then "exits 1" else "exits 0"}; the move {if w.ver == .v62e06e3 && d.line.reachesMove r.failed then "runs" else "never runs (the shell is gone)"}") ++
    [s!"det-assert junit reads: {judged w.ver d.line d.runs}"]
  | .error _ _ => []

def worlds : List World :=
  [ { label := "a plain run line (as ci-junit.json), up to 4 tests, an xargs buffer of 48 bytes", lines := [.plain] },
    { label := "every run line's form, up to 4 tests, an xargs buffer of 48 bytes" },
    { label := "3939448: a plain run line", lines := [.plain], ver := .v3939448 } ]

def searchAll (exhaustRuns : Nat) : IO Unit := do
  say s!"== ci property: {property}"
  say s!"   source: {source}"
  for w in worlds do
    if let some f ← exhaustSaid s!"{property} / {w.label}" (judge w) exhaustRuns then
      printFound f (story w)
  -- At GNU's real size: 2,000 names of 80 bytes (two xargs runs), each form, the runners passing.
  let names : List String := (List.range 2000).map fun i =>
    let stem := s!"tests/test_{i}"
    stem ++ String.ofList (List.replicate (80 - stem.length) 'x')
  let batches := Junit.xargsBatches 131072 64 names
  for line in [RunLine.plain, .exits, .execs, .comment, .setE] do
    for failing in [none, some 0] do
      let runs := batches.zipIdx.map fun (b, i) => ({ names := b, failed := failing == some i } : Run)
      let got := judged .v62e06e3 line runs
      say s!"at GNU's 131,072 bytes, 2,000 names of 80 bytes, {batches.length} xargs runs, {if failing.isSome then "the first run's runner failing" else "every runner passing"}: `{line.show}`: {got.length} of 2,000 tests judged"

end Replica.Ci5
