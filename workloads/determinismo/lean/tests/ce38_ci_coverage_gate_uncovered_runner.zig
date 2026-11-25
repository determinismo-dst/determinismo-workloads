// CE38: determinismo-ci posts its job's run with no "coverage" asked (ci.zig:254-270); serve's
// coverage gate (src/serve.zig:690-752) stops any running run whose first 4 ended timelines
// carry no `coverage` event. A run command covers only JVMs (the agent: classes instrumented as
// they load on JDK 24 or later, or jars instrumented ahead of time) and Python 3.12 or later
// (the sitecustomize): det-nodes exec --coverage, guest/runtime/nodes.zig:3744-3752. A job whose
// tests run on Python 3.11, on JDK 17 to 23 with jars as built, on Node.js (docs/CI.md's own
// example config: `npx jest --ci --shard={shard}/{shards}`), Go without determinismo-toolexec,
// is stopped after 4 ended timelines; its shards lack timelines (ci.zig:285: "error") and the
// job exits 1 though every test passed. Whether it is stopped depends on the host: a job whose
// timelines all end between two of the watcher's looks (one ingest) ends before the gate stops
// it, and passes (an `uncovered` file only).
// Promise: docs/CI.md (Coverage: "An older Python or JVM runs uncovered and says so on standard
// error"; Running it: "Exit status 0 when every shard passes"); the config example in docs/CI.md.
// Minimal case (Replica/Ci4.lean, theorems ce38_jest_job_errors and
// ce38_same_job_passes_on_a_bigger_host): 8 shards of 3 timelines, Jest, every test passing;
// the watcher ingests one ended timeline a look: stopped after 4, shards 1 to 4 with 1 timeline
// each and 5 to 8 with none: error, exit 1. Every timeline ended before the first look: pass.

// Unit test, in src/serve.zig beside coverage_gate (as CE30's), through serve's test server: a
// run directory whose request.json is determinismo-ci's (it has "ci":{...} and
// "checkpoint_exec"), events/ with 4 ended timelines, none with a coverage event, the run going.
// run_update(server, id). Assert: no `stopped` file (a CI job's run is judged by its shards; its
// tests' runtime may run uncovered, as docs/CI.md says), and an `uncovered` file once it ends.
// At 3939448: `stopped` holds "no coverage in its first 4 timelines: its system runs without its
// language's instrumentation".
test "a CI job's run is not stopped for coverage its runner cannot give" {
    try serve_ci_run_uncovered_not_stopped();
}

// e2e: examples/ci-demo with its Dockerfile's base image python:3.11-slim (pytest 8.3.3), its
// ci.json (3 shards of 12 timelines), on a host where it runs fewer than 36 timelines at once:
// assert exit status 1 for the wrong test only (shard 3 "fail", shard 1 "pass", shard 2 "flaky")
// and a "runs uncovered" note. At 3939448: "serve stopped run N: no coverage in its first 4
// timelines", every shard "error".
