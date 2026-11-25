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

## Building and running

    lake update && lake build
    .lake/build/bin/replica composer <exhaust> <seeds> <drawn-seeds> [<property>]
    .lake/build/bin/replica faults|verdicts|tape <exhaust> [<seeds>]

`lakefile.toml` takes determinismo's Lean library (`sdk/lean`) from the platform's 0dea225.

## Keeping it current

The replica cites the platform's lines at 0dea225. As the platform changes (these fixes among the
first), [../../lean-drift.py](../../lean-drift.py) lists the citations whose lines changed:

    workloads/lean-drift.py --replica workloads/determinismo/lean --repo <platform clone> \
      --base 0dea225 --new <commit> --changed-only

A fix shows as changed lines under its counterexample's citations; the next round re-runs those
searches against the fixed code, where the counterexample should be gone.
