# How these findings are made

Three ways of finding bugs, all ending the same way: a test that the real system fails, run
again by anyone.

1. **determinismo hunts**: the system runs in determinismo's deterministic VMs under drawn faults
   (crashes, partitions, clock steps, disk faults, thread pauses) while a test program drives it
   and checks properties. A failing timeline replays exactly. The workloads under `workloads/`
   are these programs.
2. **Lean replicas**: the system is written again in Lean 4 from its own source, function by
   function, without looking at its tracker. Then it is searched for departures from what its
   documentation promises. Each departure becomes a test for the real system.
3. **Generated differential tests**: random programs run on the system and on a reference
   implementation, and every disagreement is shrunk to a minimal case. So far this is jank
   against Clojure ([jank-interop/gen](workloads/jank-interop/gen/README.md)).

## A Lean replica, round by round

**The round's writer** is a coding agent (Claude) working blind in a directory of its own.
- **It reads:**
  - the system's source at a pinned commit;
  - its documentation and its own tests;
  - Lean's library and determinismo's Lean SDK (`sdk/lean`).
- **It never reads:** the system's issues, PRs or git history, or our earlier findings. Each
  round's tool calls are audited afterwards.
- It commits nothing and runs nothing on the real system.

**What it writes:**
- The replica. Each modeled function cites the upstream `file:lines` it copies, at the pinned
  commit.
- **Properties.** Each one quotes the documentation sentence it comes from: no property without a
  documented promise.
- **Searches:**
  - exhaustive enumeration of small programs (bounded entities, calls, threads), and random
    exploration beyond that;
  - every choice is a named decision on a tape (`name=value/options`), so a counterexample replays
    and shrinks;
  - theorems with no `sorry` where a claim covers every input.
- **For each counterexample:**
  - the minimal case;
  - the property and its source;
  - the code path with line numbers;
  - the replica's story of what happens, and its tape;
  - a test in the system's own language. The test asserts the documented result, so it fails on
    the real system exactly when the prediction holds. A control beside it must pass.
- **A report** (`REPORT-<n>.md`) with these sections:
  - counterexamples;
  - what was seen again, and what was not counted (with why);
  - what is replicated, what is not exact, and the assumptions;
  - properties, search runs and theorems;
  - model errors corrected;
  - the list for the next round.

**The next round** starts from the real system's answers to the last one: confirmed, not
reproduced, or failing another way. The model is corrected where the real system disagreed, and
then the list goes on.

**Keeping a replica current:** [workloads/lean-drift.py](workloads/lean-drift.py) maps every
citation through upstream's diff and lists the ones whose lines changed. That list starts the
next round.

## Confirming on the real system

The coordinator does this, never the replica's writer.

- **Where to run, in this order:**
  1. on a workstation first;
  2. on Linux (a container, or GitHub's hosted runners) for Linux-only paths;
  3. under determinismo only when the bug needs a fault, an interleaving, a crash window or a
     cluster.
- **Versions:** the latest release, and main built from source.
- **Check the expected values independently.** The reference must run the same version the docs
  describe. Run jank's tests on Clojure; take SQLite's answers from the SQLite release the system
  claims to match, not from whatever `sqlite3` a language bundles. Two predictions were withdrawn
  over exactly this.
- **Confirmed** means the test fails the predicted way and its control passes. Otherwise it is
  filed as "not reproduced", "failed another way" or "withdrawn", with the reason, and goes back to
  the replica.
- **States the docs allow but a plain test can't reach** (a power loss between two writes, a
  process killed inside a critical section):
  - the test forges that on-disk state;
  - it checks the layout around the forged bytes first, so a format change fails the test instead
    of passing it;
  - it names the determinismo drive that would reach the state for real.
- **Search the tracker** (issues and PRs, by mechanism and by error text) before filing. Record the
  date and any related issue.
- **Record:** each project's `REPROS.md` lists the findings by kind (crash, hang, wrong value,
  error). Each entry has a self-contained repro, its tracker line, and a box ticked only once an
  upstream issue describes that finding itself.

## Fixes

- A proposed fix is a diff against the pinned commit, under `fixes/`.
- It counts as verified when the finding's test fails on the stock build, passes on the patched
  build, and the project's own suites give the same results as before.
- Findings that are design or documentation questions are marked as such, with the docs change
  proposed instead.
- A fix inside a replica is a switch, off by default: the replica stays the system as written.

## Running them again

- [flecs-lean](.github/workflows/flecs-lean.yml) runs every flecs test on GitHub's Linux runners
  against the tagged release.
- [jankifier](https://github.com/pfeodrippe/jankifier) runs every jank test daily on Linux and
  macOS against jank's main, and ticks a finding once jank behaves like Clojure. Its
  `specs/repros.md` orders the findings by harm.
- Each replica's README says how to build it and rerun its searches.

## By kind of project

**C libraries** ([flecs/lean](workloads/flecs/lean/README.md)):
- Each test is a standalone C program linked against the release's amalgamated source, with
  asserts on. An abort confirms a "no internal assert" prediction.
- Uninitialized reads run under valgrind and MemorySanitizer. Races are built without asserts, run
  under ThreadSanitizer, and also run as is.
- Allocation and reuse bugs use the library's OS API hooks: guard bytes after each block, and freed
  blocks kept and poisoned.
- Fixes are patched into the amalgamation, and the library's own suites run after each one.

**Language runtimes and compilers** ([jank-interop/lean](workloads/jank-interop/lean/README.md),
[gen](workloads/jank-interop/gen/README.md)):
- The tests are the language's own `deftest`s, each asserting the reference language's result,
  each run in its own process.
- Every compilation path is a separate case: a literal inlined natively, a `let`-bound value, a
  value passed through a function, and the core function called as a value.
- Before filing, each example is run on both implementations, and the values observed are written
  down, not the values predicted.
- Generated tests add cases nobody wrote, shrunk to a minimal form and grouped by cause.

**Checkers** ([elle/lean](workloads/elle/lean/README.md)):
- The checker's verdicts are compared with a specification built from the definitions (for Elle,
  Adya's dependency graphs over every interpretation of a history), not from its code.
- Each counterexample history runs through the checker's own test suite.
- Fixes go into the deployed copy as switches.

**Storage engines and databases:**
- The tests use the system's client library, on the release and on main.
- Failed `fsync`s and short writes come from an `LD_PRELOAD` shim that fails a chosen call.
- Power-loss and crash windows are forged on-disk states (above), and determinismo drives reach
  them for real.
- Replication and sync are tested against the system's own local server.

**Distributed systems:**
- A workload under `workloads/` runs the system's real cluster under drawn faults. Its hunts are
  trees: they return to rare states and branch from them.
- **For a failing timeline,** determinismo's causality forks futures at moments before the failure
  and reports the fraction that still fail. The jump in that curve is where the outcome was
  decided.
- **Explain** redraws the details of the last faults before the failure, one at a time. It varies
  only the fault injector's draws, not a fault the scenario requests itself.
- A replica's prediction about timing becomes a drive: futures with one fault's details changed,
  each with the fraction expected to fail.

**determinismo itself** ([determinismo/lean](workloads/determinismo/lean/README.md)):
- The composer, fault injector, verdicts and tapes are replicated.
- Each confirmed counterexample becomes a regression test in the platform. The test is committed
  before the fix, fails on the old code and passes with the fix.
