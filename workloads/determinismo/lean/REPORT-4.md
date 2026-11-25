# determinismo in Lean: round 4

## What this is

Round 4 of the Lean 4 (v4.36.0) replica of determinismo at platform commit 3939448 (`upstream/`), written from the Zig function by function and searched against what the docs, the skills and the code's own comments promise. Rounds 1 to 3's models were not found wrong this round.

New files:
- `Replica/Resume4.lean`: a resumed tree. The interrupted run's judgment as the run's loop makes it, the stop and its record, `resume_read`'s keys, `rejudge_load`, `recorded_returns`, the resumed judgment.
- `Replica/Holders4.lean`: a timeline's holders (`Owner`: spacing, period, arming at new behaviors, `drop`) and `Registry.take`.
- `Replica/Durable.lean`: durability points (the two fault layers, `node_admits`, `durable_arm`/`durable_disarm`, the guest module's one arm per cgroup). Also disk failures over Linux's page cache with `errseq_t` error reporting and eviction.
- `Replica/Ci4.lean`: `tests_judge`'s per-shard reports, the `{shard}` mode's line, and serve's coverage gate on a CI job, with each runner's agent.
- `Replica/Steer4.lean`: a targeted run's hunk report.
- `Replica/Clock4.lean`: nodes restarted during their clock skews.
- `Replica/Theorems4.lean`: 16 theorems.
- `Main4.lean`: the `replica4` executable.
- `tests/ce32_*.zig` to `tests/ce39_*.zig`: the regression tests.
- `runs4/`: every search's output.
- `scratch/round4.sh`: the script that ran them.

Commands:

    lake build
    .lake/build/bin/replica4 resume <exhaust> <seeds>
    .lake/build/bin/replica4 resumecensus <seeds>
    .lake/build/bin/replica4 durable <exhaust> <seeds>
    .lake/build/bin/replica4 ci <exhaust> <seeds>
    .lake/build/bin/replica4 steer <exhaust> <seeds>
    .lake/build/bin/replica4 clock <exhaust> <seeds>
    .lake/build/bin/replica4 holders <exhaust> <seeds>

## Counterexamples

### CE32: a resumed tree rebuilds a judgment's returns from its recorded timelines, and renumbers them

**Property.**
- main.zig:242-244, the `--resume` usage: "continue that run, its recorded timelines skipped".
- main.zig:4643-4645, `tree_rejudge`: "the queue is then the interrupted run's".
- main.zig:4552-4561, `queue_take`: "so that every index keeps its timeline".
- main.zig:4136-4139: "a resumed run judges the same generations again".
- README_AI.md: "every timeline replays bit-identically".

**Minimal case** (`runs4/resume.txt`; theorem `ce32_dropped_return`).
- Generation 0 is timelines 0 to 3. Its returns are to #0 at 10 ms, #1 at 20 ms and #2 at 30 ms, one branch each. They are numbered 4, 5 and 6, and the fill is 7.
- The run stops after timeline 6 alone finished.
- On resume, `recorded_returns` gives only [#2 at 30 ms]. #2's return is `ready`, since its one timeline is recorded.
- The resumed tree plans 4 as #2's child, and 5, 6 and 7 as fresh.
- So timeline 6's summary is judged as a fresh timeline's (`archive_add` stores that plan).
- Timeline 4 never ran. It now starts from the setup snapshot while its path, its events' header and its tape's chain say it begins inside #2 at 30 ms.

Second case (theorem `ce32_merged_returns`). Two returns to one moment (CE26) have one key. Their children 4 and 5, then #2's child 6, become #0's 4, #2's 5, and 6 fresh.

**Consequences.**
- A later return to a recorded timeline replays another timeline. `maker_begin` (7704-7714) and `node_make_start` (7480-7520) replay the plan's `parent.path` with `parent.seed`, so the node is a state that timeline never had.
- The children of that node inherit the wrong lineage.
- A ready return's unrecorded timeline does not replay from its tape.
- The same renumbering follows from a recorded return whose node the resumed run does not make: the memory cap (6439-6517) or a failed maker (6552-6556). It also follows from one the interrupted run did not make and the resumed one does.

**How likely.** Any stop of a tree after a judgment, unless every timeline of every return had finished. Serve resumes stopped runs (serve.zig:5630-5633). In the model's census, the stop records each later timeline with probability 1/2 (`runs4/resume-census.txt`):
- 3 returns of 1 branch: 49,915 of 100,000 resumed runs judge a recorded timeline under another plan.
- With two returns at one moment: 29,063 of 37,386.
- The default shape (16, 4 branches, 3 returns): 85,602 of 100,000.

**Zig path** (src/main.zig):
- 2152-2163: `resume_read` keys each recorded timeline by (generation, path's last branch, moment): `children`, `first_child`.
- 6820-6841: `recorded_returns`, one return per key that has a recorded child, in first-child order.
- 6427-6431: `tree_judge_begin` takes them for a judged-again generation.
- 6455-6466: a key with `children` recorded timelines is `ready`, its snapshot the setup's.
- 6263-6310: `judge_plan_one` numbers from `next_index`.

**Regression test.** `tests/ce32_resume_recorded_returns.zig`:
- Unit tests beside `test recorded_returns` (main.zig, after 6859). Three returns, one with no recorded child, must come back three; two at one moment must stay two. The first needs the record to carry each judgment's returns (the test's generation line carries them; 3939448 ignores the field).
- e2e: a tree of 64 killed after 24 record lines, then resumed with `--verify-replays 100`. Every timeline's path before its parent's place must equal the parent's own record line's path, and every replay must verify.

### CE33: a resumed tree's last generation is planned as its nodes come, ready returns first

**Property.** As CE32's, plus docs/ANTITHESIS.md, Branching: "every timeline's path in its record and tape (it replays alone)".

**Minimal case** (theorem `ce33_ready_first`; world "nodes made again in the makings' order").
- Generation 0 is timelines 0 to 4. Its returns are to #0 at 10 ms and #1 at 20 ms, two branches each: 5 and 6 are #0's, 7 and 8 are #1's, 9 is the fill.
- The run stops after 6, 7 and 8 finished.
- On resume, `recorded_returns` gives [#0, #1] in the record's order.
- #1 is ready (both of its timelines are recorded). #0 is made by a replay.
- The run's loop judges this last recorded generation (`.last`). Its first poll plans the ready #1's timelines at 5 and 6, and #0's node, once made, gets 7 and 8.
- So timeline 5 never ran, and it starts at the setup snapshot as #1's child.
- Timeline 6 (#0's) is judged as #1's. Timelines 7 and 8 (#1's) are judged as #0's.
- This holds even with the resumed nodes made in the interrupted run's order. With the host's timing drawn, any other order of made nodes renumbers too.

**How likely.** In the model (every return with a recorded timeline, and the same node order), 12,415 of 56,205 resumed runs. It needs the last recorded generation to have a return whose timelines all finished after an earlier return whose timelines did not. That is common with parallel workers: one slow timeline in the earlier return is enough.

**Zig path** (src/main.zig):
- 4720-4723: `rejudge_load`'s `.last`, left to the loop.
- 4283: `tree_judge_begin(..., !state.rejudge_last)`.
- 6219-6233: `tree_judge_poll`, the first poll before any worker frees up.
- 6254-6261: `judge_plan_ready`, which plans made nodes as they come, in the makings' order among them.
- 6455-6466: `ready`, with `.snapshot = state.setup`.
- 6288-6309: the children's `.snapshot = snapshot`.
- 3552-3560: the events' header `{"path": lineage}`.

**Regression test.** `tests/ce33_resume_ready_first.zig`:
- Unit test beside rejudge_load's (main.zig, after 4772), on judge_plan_ready's choice made `plan_next(makings, in_order)`. In a resumed generation nothing is planned while an earlier making is unmade.
- e2e: CE32's, plus each resumed timeline's first event at or after its path's last moment.

### CE34: a filler taken between a judgment's plans makes a resume cut the record

**Property.**
- main.zig:4643-4646: "A resumed run's recorded generations judged again ... A generation whose summaries the interruption cut ends it".
- main.zig:4665-4669, `Rejudged.cut`: "Not the plan its record was made with, or cut by the interruption".
- main.zig:4692: "The fresh timelines taken while it was judged, before its plan as they were".

**Minimal case** (theorem `ce34_filler_cut`).
- Generation 0 is timelines 0 to 4. Its returns are to #0 and #1, two branches each.
- #0's node is made, so 5 and 6 are planned. Two workers take them. A third worker frees up with nothing queued and takes filler 7. Then #1's node is made, giving 8 and 9, and the fill is 10.
- The record says `{"fresh":{"generation":0,"index":7}}`.
- On resume, `rejudge_load` queues recorded fillers first, at `next_index`. 7 is not 5, so the resume is `.cut` although the record is whole and this plan's.
- The loop takes the recorded members from the queue, judges generation 0 again and records a second generation line for it. It numbers with the resumed host's timing: #0's 5 and 6, #1's 7 and 8, 9 fresh.
- So the recorded filler 7, run from the setup snapshot, is judged as #1's child.
- The record's later generations are never judged again. The loop forms generations from the queue order instead of the record's finishing order.

**How likely.** In the model with up to 3 fillers, 8,300 of 100,000 resumed runs are cut. In the default shape (16, 4 branches) with up to 6 fillers, 356 of 100,000 are cut. A filler is taken whenever the queue drains while a judgment's later nodes are still being made, which is the case `judge_plan_ready`'s comment (6243-6249) and queue_take's (4549-4561) describe in hunts.

**Zig path** (src/main.zig):
- 4562-4574: `queue_take`'s fresh filler, recorded.
- 6254-6261: plans as nodes come.
- 4693-4698: `rejudge_load`'s fillers first, `.cut`.
- 4646-4661: tree_rejudge ends.
- 4303-4310: recorded timelines taken from the queue with the resumed plan.
- 4283: the generation judged again, recording.

**Regression test.** `tests/ce34_resume_filler_cut.zig`:
- Unit test with rejudge_load's own test state (main.zig, after 4772): fresh [7] while `next_index` is 5 must give `.last`, never `.cut`.
- e2e: no generation line twice in a resumed record, and CE32's lineage check.

### CE35: a sync_stall and a durable_crash on one node share the module's one arm

**Property.**
- ARCHITECTURE.md:364-366: "While a `sync_stall` or `durable_crash` fault lasts, each of its syncs is a decision (one randomness pull), and one in a few is picked".
- docs/ANTITHESIS.md:57, Durability points.
- faults.zig:53-60: "while the fault lasts, the guest module makes each of the node's fsyncs and sync writes a decision".

**Minimal cases** (theorems `ce35_crash_replaces_stall`, `ce35_stall_end_disarms_crash`).
- A sync_stall begins, then a durable_crash over it (the overlap drawn). The node's sync while the sync_stall lasts is a crash_before decision: no stall.
- A durable_crash begins, then a sync_stall over it, and the sync_stall ends. The node's next sync while the durable_crash lasts is no decision at all, yet its fault events say it is under way.

**How likely.** In timelines of 8 steps with the regime's overlap drawn 0 to 8 eighths, 13,190 of 100,000 have a sync that is not its fault's decision. Both kinds began in 49,660 of them. sync_stall is on by default, durable_crash comes with `+crash`, and `fault.overlap_eighths` is drawn per regime, so any run with `+crash` meets it.

**Zig path.**
- faults.zig:1580-1585: `layer_of`, sync_stall a condition and durable_crash a process fault.
- faults.zig:1633-1641: `node_admits`, an overlap drawn across layers.
- faults.zig:3225-3254: `durable_arm`, both arm the node's cgroup.
- faults.zig:3256-3268: `durable_disarm`.
- faults.zig:2245-2250: either fault's end disarms.
- guest/module/det_guest.c:461-497: one arm a cgroup, "Replaced (or disarmed)" (469).
- guest/module/det_guest.c:404-439: `det_durability` decides by the armed mode only.

**Regression test.** `tests/ce35_durability_one_arm.zig`:
- Selftest scenario: an injected 4 s durable_crash, then a 1 s sync_stall, on a node fsyncing every 10 ms. Between 1 s and 4 s, its syncs must be decisions. The reverse order is checked for `sync_stalled` events.
- Unit test (faults.zig, beside the layer test) on the arm a node should have, made `durability_arm_of(process, condition)`.

### CE36: lost writes read back stale before any crash

Round 3 noted this without a model. It is modeled and searched now.

**Property.**
- docs/ANTITHESIS.md:56: "writes acknowledged and never stored (gone at the next crash, synced or not)".
- nodes.zig:1932-1933: "a crash after loses them although they were synced".

**Minimal case** (theorem `ce36_lost_write_read_back`).
- The node writes 1, then 2, to a page. The disk starts dropping writes.
- The flusher writes the page back; the write is dropped and the page is left clean.
- Memory pressure evicts the clean page.
- The node's read returns 0. No crash came.

Without eviction, the same steps never break it (exhausted: 326,577 timelines).

**How likely.** Any lost_writes fault on a node whose page cache is reclaimed while it lasts: a guest under memory pressure, a JVM's heap growing. The same happens to a node that exited during the fault, since disk_heal unmounts it (nodes.zig:2192-2196). The node reads its own acknowledged, synced write as gone mid-run, a state a crash never shows (a crash restarts it). Its own logs then say "corruption" where the docs promise a loss at the next crash.

**Zig path.**
- nodes.zig:1972-1976: `drop_writes`.
- nodes.zig:2179-2198: `disk_heal`, which leaves a running node's cache and unmounts an exited one.
- Linux: dm-flakey's `drop_writes` ("All write I/O is silently ignored"); clean pages are reclaimable.

**Regression test.** `tests/ce36_lost_writes_evicted.zig`: a selftest disk scenario (write and fsync under lost_writes, `POSIX_FADV_DONTNEED`, read). Or the docs' fix: "or once the kernel drops the page".

### CE37: tests_judge counts missing JUnit reports over the whole run, not per shard

**Property.**
- ci.zig:436-439, tests_judge: "\"error\" when a timeline stated no test (the run command died before its report)".
- ci.zig:473: "<k> timelines without their JUnit report".
- docs/CI.md: "each test gets its own verdict across its shard's timelines".

**Minimal case** (theorem `ce37_unreported_missed`, and the general `unreported_zero_of_one_full`).
- Three tests, two shards of 2 timelines, `junit`. Shard 1 passes in both.
- Shard 2's runner dies before its report in one timeline.
- tests_judge says "0 timelines without their JUnit report". Shard 2's test reads "pass" (over its one report). The job is flaky (exit 2).
- The same timeline in a one-shard job: error (exit 1).

The general theorem: any one test reported in a whole shard's timelines makes `unreported` 0, whatever the other shards' timelines did.

**How likely.** Any job of two shards or more where one shard's runner dies before its report in some timelines while another shard reports in all of its own.

**Zig path.** src/products/ci.zig:440-485 (454 `reported = @max(...)` over every test of the run; 470 `unreported += timelines -| reported`, `timelines` being one shard's; 473, 475).

**Regression test.** `tests/ce37_ci_unreported_per_shard.zig`:
- A store test (beside CE28's) on a count made SQL: the run's timelines that stated the shard property and no "test passes:" assertion must be 1.
- e2e: ci-demo in the `{shard}` mode with a runner that exits before writing its report.

### CE38: the coverage gate turns a passing CI job with an uncovered runner into "error", depending on the host

**Property.**
- docs/CI.md:90: "An older Python or JVM runs uncovered and says so on standard error".
- docs/CI.md: "Exit status 0 when every shard passes".
- docs/CI.md:36: the config example, `npx jest --ci --shard={shard}/{shards}`.

**Minimal case** (theorems `ce38_jest_job_errors`, `ce38_same_job_passes_on_a_bigger_host`).
- docs/CI.md's own Jest config: 8 shards of 3, every test passing.
- Its run command reports no coverage: `det-nodes exec --coverage` covers JVMs and Python 3.12+ only.
- The watcher ingests one ended timeline a look. After 4, serve stops the run ("no coverage in its first 4 timelines: its system runs without its language's instrumentation").
- Shards 1 to 4 have 1 timeline each and shards 5 to 8 none. Every shard is "error"; exit 1.
- When all 24 timelines end before the gate's first look, the same job passes (exit 0, an `uncovered` file only).
- The same holds for Python 3.11, JDK 17 to 23 with jars as built, and Go without determinismo-toolexec (the search's first case: Python 3.11, 2 shards of 3).

**How likely.** Every CI job whose test runtime has no automatic coverage, on any host where its timelines do not all end between two looks of serve's watcher (once a second): Node.js, Ruby, PHP, shell, older Python and JVMs, uninstrumented Go and Rust. Examples/ci-demo (Python 3.12) is not affected: 1,000,000 timelines exhausted and 100,000 seeds explored.

**Zig path.**
- src/serve.zig:703-752: `coverage_gate`, which applies to every run unless request.json says `"coverage": "off"`.
- src/serve.zig:650-678: the watcher's looks.
- src/products/ci.zig:254-270: the run is posted without `coverage`.
- src/products/ci.zig:286: a shard with fewer than `timelines` is "error".
- guest/runtime/nodes.zig:3744-3752: what `--coverage` covers (`java_options`, `python_options` only).
- sdk/java/DeterminismoCoverage.java:9-12 (JDK 24); guest/runtime/python/sitecustomize.py:14-23 (3.12).

**Regression test.** `tests/ce38_ci_coverage_gate_uncovered_runner.zig`:
- A serve test (beside coverage_gate, as CE30's): a CI request.json and 4 ended uncovered timelines must leave no `stopped` file.
- e2e: ci-demo on python:3.11-slim must end with the wrong test's "fail" only.

### CE39: a targeted run reports a hunk "NEVER RAN" when only its last timelines ran it

**Property.**
- docs/AGENTS.md:319-322: "reports which hunks ran in how many timelines and which never did".
- README_AI.md:319-320: "says which of them ran, in how many timelines, and which never did".
- docs/ANTITHESIS.md:131.

**Minimal case** (theorem `ce39_never_ran`).
- Generations of 2, 3 timelines. Timeline 2 alone runs the hunk.
- Generation 0 (timelines 0 and 1) is judged. Timeline 2 ends with every timeline planned, so it is never judged.
- The report says "NEVER RAN".
- With `--generation 16` and 20 timelines, the last 4 are uncounted. With a time budget, every timeline since the last judgment is uncounted.
- "ran in c/N timelines" divides by `next_index`, which counts timelines planned past the budget and never run.

**How likely.** Every targeted run whose timeline count is not a multiple of its generation, or that ends by its budget, as hunts do. A hunk reached late, which is where a change's deep paths are, is the one reported unreached.

**Zig path** (src/main.zig):
- 6363-6391: hunks counted over `done`, the judged timelines.
- 4371: `if (!late and batch.summaries.count > 0 and state.next_index < state.total)`, so the last partial generation is judged only then.
- 4383: `target.summarize(state.next_index)`.
- src/changed.zig:66-85: "NEVER RAN".

**Regression test.** `tests/ce39_targeted_unjudged_timelines.zig`:
- Unit test beside `test judge_count` on the counting made a function of the run's summaries at its end.
- e2e: the `changed` check with `--branches 20 --generation 16`, against the coverage events.

## Other findings (not counterexamples)

- **Holders for new behaviors are the ones `drop` removes** (Holders4.lean; theorem `new_behavior_holder_dropped`; `runs4/holders.txt`).
  - Owner.behaviors makes a hold point just after a new behavior unless one is within `spacing` (holders.zig:1029-1046).
  - Past 8 kept holders, `drop` removes the one closest to the one before it (1275-1293). That is usually the new behavior's holder, a little past a periodic one.
  - The frontier's return then replays from the periodic holder. In a 640 ms timeline (spacing 10 ms, period 80 ms), the return just after the behavior at 11,001 µs replays 10,002 µs from 1,000 µs; another case replays 16,000 µs.
  - Cost only: nodes stay exact (replays with the timeline's tape). The comment's promise, "so the replays from a holder to a later moment stay short wherever the moment is" (29-30), holds for random moments, not for the tree's returns.
- **One holder serves one return.** With CE26's double returns, the second node is a replay from the parent's start, or from a periodic holder 73 ms back (holders' search). The log line classifies it correctly ("its holders before it taken or gone").
- **The `{shard}` mode's line.** A shard's "<n> tests" is computed by list position modulo the shards (ci.zig:281-285) whatever the runner does. Against a runner splitting in blocks, 125 lines of the shard counts 1 to 12 differ (the first: 4 tests, 3 shards, shard 2 says 1 test, the runner ran 2). ci-shard.json's awk deals modulo, as the line counts.
- **CE30 extends to the JVM agent and Python.**
  - Their per-process report sets (`queued`/`reported` in DeterminismoCoverage.java:126-177; `reported` in determinismo.py:641-656) are in a setup snapshot's process memory. A JVM or Python node started in the setup whose timelines rerun its setup's lines reports nothing, and the gate stops it as uninstrumented.
  - A CI run command's new processes report normally.
- **write_errors keeps fsync's error reporting.** A writeback error is reported by the next fsync of each open description, and a description opened later sees an unseen one (errseq). The platform's own syncfs (`writeback_s`) reads the superblock's errseq, not the file's. disk_heal leaves a running node as it is. So a write whose fsync returned 0 with no error since is stored (1,000,000 timelines exhausted and 100,000 seeds, one and two pages).
- **durable_crash's two sides.**
  - A crash_before task released into the freeze returns `-ERESTARTNOINTR` without syncing (det_guest.c:431-438), and partial persistence writes only what a flusher could have.
  - crash_after parks after the filesystem's fsync returned.
  - Read, not searched: both hold as documented.
- **Extensions of cut timelines** (read).
  - An extension lands at `min(end - 1 ms, last pull - 1 µs)` (main.zig:7279-7296).
  - Its children's horizon is drawn from that moment (`at + horizon_drawn`, 6299-6304). An extension of a timeline whose last pull came well before its cut may stop before its parent did, while its `why` says "Extended #i from where it stopped".
- **Ladders** (read). A property's first failing timeline gets its holders written only when its generation is judged, and only the holders no return took (main.zig:6611-6614, 5440-5461). A failure in CE39's unjudged tail gets no ladder.
- **Steering on tapes** (read).
  - The configuration bandit's answers and the novelty steering's driver phase length are written on the tape as they are taken (vm.zig:3819-3846; bandit.zig:12-13).
  - Holders and replays load the timeline's tape (main.zig:7382-7404; node.zig:16-40).
  - The bandit never touches a verdict. Replays hold.
- **Clocks.** A node restarted during its skew starts at offset 0 while its fault still counts as under way, and a strobe's next flip skews the new namespace again. Every two nodes stay within the maximum, and no node falls more than the maximum below what the clocks remember (3 worlds, each 1,000,000 timelines exhausted and 100,000 seeds). The bookkeeping is conservative: it counts a restarted node's skew as still applied.

## What was replicated, and what is not exact

Replicated with file and lines:
- `resume_read`'s keys, `rejudge_load`, `recorded_returns`, the ready check, `judge_plan_ready`/`judge_plan_one`'s numbering, `tree_judge_poll`'s first poll, `queue_take`'s recorded fillers, and `tree_judge_end`'s fill.
- `Owner.spacing`, `period`, `behaviors`, `reached`, `drop`, and `Registry.take` with `replay_why`'s classes.
- `layer_of`, `node_admits`, `durable_arm`/`durable_disarm` and the faults' ends; the module's arm table and `det_durability`'s choice.
- `disk_fail`'s tables (healthy, `error_writes`, `drop_writes`), `disk_heal` for a running node, and Linux's page cache with errseq.
- `tests_judge`, the shard line's count, `coverage_gate`, the watcher's looks, and what `det-nodes exec --coverage` covers.
- Tree_judge_begin's hunk counts, the loop's last judgment, and `Change.summarize`.
- `skew_clamp`, `skew_begin`, strobe flips and skew ends with restarts.

Not exact:
- The resumed tree's judgment returns are the world's (the model does not judge). One generation is judged before the stop. Holders, memory caps and sessions are left out of the resume model.
- Holders' memory pressure, disk holders and `--holders-retain` are left out. Time is in µs with a 640 ms timeline.
- One node and its module are modeled. A sync is one decision with `one_in` 1 (every sync picked). Partial persistence and the crash's freeze are read, not modeled.
- Pages are one value each, with one file.
- The coverage gate assumes timelines end in index order (round-robin shards). Hangs are CE27's, so every timeline passes here.
- The targeted run model has pipeline 1, timelines ending in index order, and hunks drawn per timeline.

## Assumptions

- Linux's page cache and writeback errors, as Documentation/filesystems/vfs.rst ("Handling errors during writeback"), lib/errseq.c and fsync(2) describe them:
  - a failed writeback leaves the page clean with its data;
  - each open description is told once;
  - a description opened later sees an error nobody saw (since 4.16);
  - clean pages are reclaimable.
- dm-flakey's `drop_writes` ignores writes and `error_writes` fails them.
- The guest module's arm table and `det_durability` are as in det_guest.c at 3939448.
- A CI runner's processes start in each timeline. JDK 24+ (agent) and Python 3.12+ (sitecustomize) report coverage, and nothing else does.
- Serve's watcher looks once a second, and a run's timelines may end between looks in any grouping.
- A stop records any subset of the timelines that ran, in any order. The next generation is not judged before it.
- Rounds 1 to 3's assumptions hold.

## Properties, with sources (20)

**A resumed tree (4).**
1. Every recorded timeline keeps its plan in the resumed tree (main.zig:242-244, 4643-4645, 4552-4561, 4136-4139): fails (CE32, CE33, CE34).
2. Every timeline the resumed tree runs starts where its path says (README_AI.md; ANTITHESIS.md; main.zig:6458-6460): fails (CE32, CE33).
3. Every index keeps its timeline (main.zig:4552-4561): fails (CE32, CE33, CE34).
4. A resume judges again every generation its record has whole (main.zig:4643-4646, 4665-4669, 4692): fails (CE34).

**Holders (2).**
5. A return just after a new behavior starts from a holder at most `spacing` before it (holders.zig:1029-1032, 29-35): fails by `drop` (cost only).
6. One holder serves one return, and the second's replay is named as such (main.zig:6482-6498): holds, with a long replay.

**Durability and disks (4).**
7. While a sync_stall or durable_crash lasts, each sync is that fault's decision (ARCHITECTURE.md:364-366; ANTITHESIS.md:57; faults.zig:53-60): fails (CE35).
8. With disk_lost_writes off, a write whose fsync returned 0 with no error since is stored (schema.zig:514-519; Linux): holds.
9. Lost writes are gone at the next crash, and readable until then (ANTITHESIS.md:56; nodes.zig:1932-1933): fails with eviction (CE36).
10. durable_crash crashes just before or just after the sync's data reaches the disk (ANTITHESIS.md:57): holds (read).

**CI (5).**
11. tests_judge counts every timeline that stated no test (ci.zig:436-439, 473): fails (CE37).
12. A shard's failures give the same exit whatever a passing shard beside it reports (CI.md): fails (CE37).
13. A CI job whose tests all pass exits 0, an uncovered runner running uncovered (CI.md:90, 36): fails (CE38).
14. A shard's line counts the tests its runner ran (CI.md; ci.zig:288-291): fails in the `{shard}` mode against a block-splitting runner (cosmetic).
15. The gate stops only runs without instrumentation, the JVM agent and Python included (SDKS.md:101-105; serve.zig:731-733): fails (CE30's case).

**Steering (3).**
16. A targeted run reports each hunk in as many timelines as ran it, and NEVER RAN only for one none ran (AGENTS.md:319-322; README_AI.md:319-320): fails (CE39).
17. The bandit's and novelty steering's answers are on the tape, so replays and nodes repeat them (vm.zig:3819-3846; bandit.zig:12-13): holds (read).
18. Steering never changes a verdict: holds (read).

**Clocks (2).**
19. Every two nodes stay within the maximum, restarts during skews included (faults.zig:1701-1709): holds.
20. No node falls more than the maximum below what the clocks remember, restarts included (faults.zig:1704-1709; 1572-1573): holds.

## Search runs (`runs4/`)

- `resume.txt`: 4 properties over 7 worlds, each exhausted (to 1,000,000) and explored over 100,000 seeds.
- `resume-census.txt`: 100,000 seeds per world, each property counted.
- `durable.txt`: the durability property over 3 worlds (overlap 0: complete at 6,444; overlap 8 and 4: found), its census (100,000 seeds), and the disk properties over 4 worlds (exhausted to 1,000,000 or complete, 100,000 seeds).
- `ci.txt`: the per-shard properties over 3 worlds (exhausted, one-shard complete at 343) and the gate over 3 worlds (the Python 3.12 world: 1,000,000 exhausted, 100,000 seeds, none). Also the `{shard}` line over 1 to 12 tests, and the JVM and Python report sets.
- `steer.txt`: 4 worlds (the two-hunk, whole-generations world complete at 65,536: none).
- `clock.txt`: 3 worlds, 1,000,000 exhausted and 100,000 seeds each: none.
- `holders.txt`: 3 worlds: found.

## Theorems (16, `Replica/Theorems4.lean`)

General:
- `spacing_ge_min`
- `period_eight`
- `foldl_max_ge`
- `foldl_max_mem`
- `unreported_zero_of_one_full` (CE37's mechanism for every input)

By computation:
- Holders: `new_behavior_holder_dropped`.
- CE32: `ce32_dropped_return`, `ce32_merged_returns`.
- CE33: `ce33_ready_first`.
- CE34: `ce34_filler_cut`.
- CE35: `ce35_crash_replaces_stall`, `ce35_stall_end_disarms_crash`.
- CE36: `ce36_lost_write_read_back`.
- CE37: `ce37_unreported_missed`.
- CE38: `ce38_jest_job_errors`, `ce38_same_job_passes_on_a_bigger_host`.
- CE39: `ce39_never_ran`.

## Library gaps

- Lean's `(← x)` hoisting (round 3's gap) was avoided by drawing every conditional decision in its own `do` block. A `decideIf` would still help.
- `exhaust` changes the last decisions first. Worlds whose interesting case sits behind an early decision (a runner menu) were explored too, and the dedicated worlds were narrowed.
- A census over several properties at once (one run, every property counted) was written by hand again (`Resume4.census`). The library's `census` counts one violation a timeline.
- Page-cache, errseq, module-arm and SQL-count models were built by hand.

## Left for round 5

- Run CE32 to CE39 on the platform, with CE23 to CE31.
- The tree:
  - a resumed tree's later generations after a cut (finishing order lost);
  - the memory cap and failed makers in a resume;
  - `--holders-retain` and disk holders' chains (`kept_trim`);
  - novelty steering's driver lengths (`Novelty.choose`) against its documented curve.
- Disks:
  - partial persistence modeled (files, delalloc runs, the commit);
  - durable_crash with partial persistence and the journal.
- CI: xargs batches with `junit` (CE21) per test; the setup's stale JUnit file read by a timeline whose runner died before writing its own.
- Coverage: Node.js and .NET coverage paths (`coverageStart`, `determinismo-dotnet-instrument`) against the gate.
- Clocks: skips with restarts (round 3's skew-and-skip finding), and a node's persisted hybrid clock across a crash.
