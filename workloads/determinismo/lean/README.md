# A Lean replica of determinismo

determinismo's own code, replicated in Lean 4 function by function from the Zig, blind (from the
code and its docs only), and searched against what the docs promise: the parts that decide what a
run's verdict means. The composer (guest/runtime/composer.zig), the fault injector's rules
(guest/runtime/faults.zig), verdicts (src/core/events.zig, src/report.zig, src/main.zig, serve's
properties), and tapes and replay (src/core/tape.zig, src/core/vm.zig), at platform commit 0dea225.

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

## Building and running

    lake update && lake build
    .lake/build/bin/replica composer <exhaust> <seeds> <drawn-seeds> [<property>]
    .lake/build/bin/replica faults|verdicts|tape <exhaust> [<seeds>]
    .lake/build/bin/replica2 clock|junit|persist <exhaust> [<seeds>]

`lakefile.toml` takes determinismo's Lean library (`sdk/lean`) from the platform's 3939448.

## Keeping it current

The replica cites the platform's lines at 0dea225. As the platform changes (these fixes among the
first), [../../lean-drift.py](../../lean-drift.py) lists the citations whose lines changed:

    workloads/lean-drift.py --replica workloads/determinismo/lean --repo <platform clone> \
      --base 0dea225 --new <commit> --changed-only

A fix shows as changed lines under its counterexample's citations; the next round re-runs those
searches against the fixed code, where the counterexample should be gone.
