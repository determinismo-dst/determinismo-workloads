# A Lean replica of determinismo

determinismo's own code, replicated in Lean 4 function by function from the Zig, blind (from the
code and its docs only), and searched against what the docs promise: the parts that decide what a
run's verdict means. The composer (guest/runtime/composer.zig), the fault injector's rules
(guest/runtime/faults.zig), verdicts (src/core/events.zig, src/report.zig, src/main.zig, serve's
properties), and tapes and replay (src/core/tape.zig, src/core/vm.zig), at platform commit 0dea225.

How rounds are run, findings confirmed and fixes verified: [METHODOLOGY.md](../../../METHODOLOGY.md).

## Round 1

[REPORT.md](REPORT.md): 13 counterexamples (CE1-CE13), a minor one (CE14) and notes, each with
its minimal case, Zig path and how to drive it on the platform; 29 properties, 20 theorems; the
searches in `runs/`. On the platform:
- **CE13** confirmed by a unit test that fails on 0dea225's tape.zig
  ([confirm/ce13_test.zig](confirm/ce13_test.zig)); CE1-CE4, CE6, CE7, CE9-CE12 confirmed by
  reading the code; CE8 is the docs' wording (a scenario's injected faults start in quiet periods
  by design).
- **Fixes:** CE6 is on the platform's `next` (94204e8). CE1-CE5, CE7 and CE9-CE13 are fixed and
  wait for their checks, each with a test that fails on the old code (e2e fork-replay,
  workload-singleton, length-bounds, quiet-stop, ending-killed; unit tests for the tape's
  checkpoints and the outage cap). CE14 can't happen in practice.

## Round 2

[REPORT-2.md](REPORT-2.md), at platform commit 3939448 (newer than round 1's):
- **Round 1 rechecked:** CE1, CE3, CE6, CE7, CE9-CE14 fixed; CE2 fixed for exit codes but not for
  a start's own SIGKILL under `--min-drive 0`; CE4 fixed for serial drivers and `--timeline` (a
  drawn length still doesn't bound a singleton, by design per the code, not per schema.zig's
  doc); CE5 half fixed (a start waiting for a slot still begins past the stop); CE8 is now the
  docs' wording.
- **New, CE15-CE22**, each with a regression test in `tests/`:
  - CE15: the wall clock start's last band reached its cap (an hour), so an hour token a setup
    issued expired as the drivers began. Confirmed by a unit test red at the hour and fixed on
    `next` (eed20cd: a 30-minute default).
  - CE16: a passing JUnit case whose captured output in CDATA holds `<error` or `<failure` is
    judged failing (junit.zig searches the whole case).
  - CE17: partial persistence can keep a later range of a fresh sparse file and lose an earlier
    one, the hole the docs rule out.
  - CE18, CE22: a message declared under two kinds: an unmet `sometimes` passes, and the verdict
    depends on which kind the catalog noted first.
  - CE19: a run serve adopted across a restart takes its status from the summary, not the
    explorer's exit (a catalog failure then reads "passed").
  - CE20: a tape past 65,536 overrides is recorded whole but refused on replay.
  - CE21: `{tests}` through xargs splits a large shard into runner runs that overwrite each
    other's JUnit report, so only the last batch is judged.
- 38 properties, 35 theorems (three for every input); the searches in `runs2/`.

## Round 3

[REPORT-3.md](REPORT-3.md), at 3939448: the explorer's tree (frontier, archive, returns,
generations, strategies' answers), determinismo-ci end to end, serve's resume, coverage gate
and sessions, disk faults over a model of Linux's page cache, clock skews. CE23-CE31, each with a
regression test in `tests/`:
- CE23: a timeline a strategy seeded is returned to with the tree's planned seed, so its children
  replay another parent.
- CE24: the same seed grows another tree with another number of workers.
- CE25: the archive returns to repeats. CE26: a generation returns twice to one moment.
- CE27: determinismo-ci reports a hung timeline as the job's "error", "failing in 0 of 3".
- CE28: a session opened on a CI job's run changes its shard verdicts.
- CE29: a resumed run's state ignores the timelines recorded before its stop.
- CE30: the coverage gate stops instrumented runs whose first timelines only repeat their setup's
  code.
- CE31: `corrupt_reads`, documented as keeping what is stored intact, stores a corrupted byte (a
  partial write to an uncached page reads it through the corrupting table first).
- 28 properties, 19 theorems; the searches in `runs3/`.

## Round 4

[REPORT-4.md](REPORT-4.md), at 3939448: a resumed tree, holders, durability points, disk faults
over the page cache with Linux's writeback-error reporting, determinismo-ci's per-shard reports
and the coverage gate on CI jobs, targeted runs, clocks with restarts. CE32-CE39, each with a
regression test in `tests/`:
- CE32-CE34: a resumed tree renumbers its timelines (returns rebuilt from recorded timelines
  alone; a last generation planned ready returns first; a filler taken between plans cuts a whole
  record), so recorded timelines are judged under another plan and unrun ones start elsewhere
  than their paths say.
- CE35: a sync_stall and a durable_crash on one node share the guest module's one arm.
- CE36: under lost_writes, a page evicted under memory pressure reads back stale before any
  crash.
- CE37: determinismo-ci counts missing JUnit reports over the run, not per shard.
- CE38: the coverage gate turns a passing CI job with an uncovered runner (docs/CI.md's Jest
  example) into "error", depending on the host.
- CE39: a targeted run reports a hunk NEVER RAN when only its last, unjudged timelines ran it.
- 20 properties, 16 theorems; the searches in `runs4/`.

## Building and running

    lake update && lake build
    .lake/build/bin/replica composer <exhaust> <seeds> <drawn-seeds> [<property>]
    .lake/build/bin/replica faults|verdicts|tape <exhaust> [<seeds>]
    .lake/build/bin/replica2 clock|junit|persist <exhaust> [<seeds>]
    .lake/build/bin/replica3 tree|treecensus|jobs|ci|serve|disk|skew|ce2 ...
    .lake/build/bin/replica4 resume|resumecensus|durable|ci|steer|clock|holders ...

`lakefile.toml` takes determinismo's Lean library (`sdk/lean`) from the platform's 3939448.

## Keeping it current

The replica cites the platform's lines at 0dea225. As the platform changes (these fixes among the
first), [../../lean-drift.py](../../lean-drift.py) lists the citations whose lines changed:

    workloads/lean-drift.py --replica workloads/determinismo/lean --repo <platform clone> \
      --base 0dea225 --new <commit> --changed-only

A fix shows as changed lines under its counterexample's citations; the next round re-runs those
searches against the fixed code, where the counterexample should be gone.

## Round 5

[REPORT-5.md](REPORT-5.md): CE1-CE39 rechecked at next 62e06e3 (most fixed; CE4, CE13, CE15, CE19,
CE20, CE21 and CE29 partly, with remainders numbered anew; CE23-CE26, CE30, CE32-CE34, CE38, CE39
still there), and CE40-CE48. CE40, CE41 and CE48 fail as Zig tests on copies of 62e06e3's ci.zig,
junit.zig and tape.zig; the rest are the model's, each with its regression test in tests/.

## Round 6

[REPORT-6.md](REPORT-6.md): CE1-CE48 rechecked at next a7fe05d (CE40, CE42, CE43, CE46-CE48
fixed; CE41 partly, its remainder CE49; CE45 still there, and with CE47 fixed a complete resume
now reads "passed"), and CE49-CE55: captured JUnit output that prints `</testcase>` makes tests of
its own and hides failures (CE49), the coverage gate stopping an instrumented run started from a
snapshot (CE50), a command-line run's analyses booting other inputs than its tapes' (CE51), a
session step over about 41 KiB making its tape unreadable (CE52), returns past a full tape's marker
(CE53), an aimed corrupt_reads naming a byte its read never had changed (CE54), and a test runner
exiting 255 stopping xargs before the shard's later tests (CE55). CE49, CE52 and CE55 fail as Zig
tests on copies of a7fe05d's junit.zig, tape.zig and ci.zig; each has its regression test in tests/.

## Round 7

[REPORT-7.md](REPORT-7.md): every counterexample rechecked at next df8f08b, with Zig tests
(`tests/r7_*.zig`) red on a7fe05d and green on df8f08b for CE49, CE50, CE51, CE52, CE53, CE54,
CE55, CE45 (a complete run resumed again) and the composer's `drivers_stopped`; CE25 and CE32-CE34
closed. Five new, each with a test failing on df8f08b: the coverage gate's end label on a run from
a snapshot (CE56), explain's `--draw <name>=<v>` counting one replay as m samples (CE57), returns
past a full tape's marker from a cut timeline or a strategy (CE58), `returns_earlier` putting two
returns on one moment (CE59), and a command-line run's injector reaching its analyses under its
kept copy's name (CE60). All five, and CE45's remaining paths, are fixed on the platform's next
(7abcbbf, db50882, dbca564, 8ee80ba, 4af1750, c4f246e), each with a regression test that failed
first.

## Round 8

[REPORT-8.md](REPORT-8.md): round 7's fixes rechecked at next c4f246e (each closes its
counterexample on the paths it targets; Zig tests red on df8f08b and green on c4f246e), and six
new, each with a test failing on c4f246e (`tests/r8_*.zig`): a drained run's catalog line taken
as the verdict of a later resume (CE61), explain's control pull left to a draw that decides
nothing, so a set value's variants are one history again (CE62), a `--scenario all` run's
request rewritten with its first scenario and the explorer's own fields (CE63), `podman_cpuset`
reading 512 bytes of the user manager's cpuset (CE64), a tree's declared lines written once per
timeline instead of once per run (CE65), and a bundle that leaves the run's injectors on the
recording host (CE66). CE62 and CE66 are fixed on the platform's next (7c5bc6f, c6c995e), each
with a regression test that failed first; the others are in progress.
