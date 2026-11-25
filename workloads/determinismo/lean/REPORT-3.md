# determinismo in Lean: round 3

## What this is

Round 3 of the Lean 4 (v4.36.0) replica of determinismo at platform commit 3939448 (`upstream/`), written from the Zig function by function. It is searched against what the docs, the skills and the code's own comments promise. Rounds 1 and 2's models were not found wrong this round.

New files:
- `Replica/Tree.lean`: the explorer's tree, function by function: `generation_for`, `roots`, `nodes`, `fits`, `judge_count`, `frontier_choose`, `candidate_before`, `archive_add`, `objective_place`, `memory_forget`, `archive_ranked`, `archive_returns`, `tree_returns` with a strategy's answer, `answer_parse`, `returns_earlier`, `returns_branches`.
- `Replica/TreeRun.lean`: a tree run. It has the queue, judgments in order, nodes (made by a holder or a replay), the worker's start of a timeline with a strategy's `branch` reply, and tapes, over a model system.
- `Replica/TreeProps.lean`: 13 properties, the worlds, the searches, a census and the `--jobs` comparison.
- `Replica/Ci.lean`: determinismo-ci end to end (shard SQL, `tests_judge`, verdict, exit status), with hangs, runner deaths and sessions.
- `Replica/Serve3.lean`: resume of a stopped run, the coverage gate, and `properties_sql` with sessions.
- `Replica/Disk.lean`: disk faults (dm-flakey and dm-delay tables, the heal, crashes) over a model of Linux's page cache, and `writeback_s`'s drawn flusher.
- `Replica/Skew.lean`: clock skews (`skew_clamp`, `clock_leaves`, strobes) and skips.
- `Replica/Ce2Drawn.lean`: CE2's remainder in drawn worlds made for it.
- `Replica/Theorems3.lean`: 19 theorems.
- `Main3.lean`: the `replica3` executable.
- `tests/ce23_*.zig` to `tests/ce31_*.zig`: the regression tests.
- `runs3/`: every search's output.
- `scratch/round3.sh` and `scratch/round3-after.sh`: the scripts that ran them.

Commands:

    lake build
    .lake/build/bin/replica3 tree <exhaust> <seeds>
    .lake/build/bin/replica3 treecensus <seeds>
    .lake/build/bin/replica3 jobs <exhaust> <seeds>
    .lake/build/bin/replica3 ci <exhaust>
    .lake/build/bin/replica3 serve <exhaust>
    .lake/build/bin/replica3 disk <exhaust>
    .lake/build/bin/replica3 skew <exhaust> <seeds>
    .lake/build/bin/replica3 ce2 <seeds>

## Counterexamples

### CE23: a timeline seeded by its strategy is returned to with the tree's planned seed

**Property.**
- README_AI.md: "every timeline replays bit-identically".
- docs/ANTITHESIS.md (Branching): "every timeline's path in its record and tape (it replays alone)".
- docs/PLUGINS.md (`branch`): a seed given there is "another random future: its tape's header says it, so its replay needs no plugin".
- docs/PLUGINS.md (`returns`): "Nodes replay their parents with their tapes, so what the strategy decided there stays".

**Minimal case** (`runs3/tree.txt`; theorems `strategy_seed_tape_replays_another` and `strategy_seed_node_elsewhere`).
- `plugins/python/same_seed.py 0x42` has `decides` false, so holders are on. It gives every timeline seed 0x42.
- Timeline 0's plan says `branch_seed(base, 0)`.
- The judgment returns to timeline 0. The node comes from its holder, so it is the real state.
- Child 4's tape header says seed 0x42. Its `chain` says timeline 0 with the planned seed.
- Replayed alone, child 4 runs another prefix: it ran `[2,0,2,2,0,1]`, and its tape replays `[1,2,2,2,0,1]`.
- Without a holder, the node itself is a replay with the planned seed: "a return to #0 at 15 µs replayed [1]; #0 had [2] there". This covers a deciding strategy, an archive return to an earlier generation, and a moment before the first holder.

**How likely.** It happens in any tree run with a strategy that gives seeds. In the census (5,000 runs per world):
- with same_seed.py, 3,029 runs break the tape replay and 3,958 build a node from a state the parent never had;
- with a deciding strategy that seeds some timelines, 2,687 runs build such a node.

The e2e check `branch-seeds` runs three flat branches only (tools/e2e.zig:2148-2178).

**Zig path** (src/main.zig):
- 3474-3486, the worker: `if (choice.seed) |seed| place.seed = seed;`.
- 3835-3937: `Summary` and `Summaries.note` carry `jitter_seed`, not the seed.
- 6362-6365: only the jitter is copied back into the plan.
- 6280-6286: `judge_plan_one`'s segment `.seed = parent.seed`.
- 7704-7712 and 7485: `maker_begin` loads the parent with `parent.seed`.
- src/core/node.zig:30-39 and 165-180: `Recorded.load` and `chain` use the seed they are given.
- 3754-3780: `branch_announce` writes the strategy's `branch_seed` and the plan's `chain`.

**Regression test.** `tests/ce23_tree_strategy_seed.zig`:
- unit test "a judged timeline's plan has the seed it ran with: its children's chain replays it", beside "a plugin's returns are kept whole..." (main.zig, after 5917);
- e2e `check_branch_seeds_tree`: same_seed.py in a tree of 64 timelines, a returned timeline replayed from its tape, the events hash compared.

### CE24: the same seed grows another tree with another number of workers

**Property.**
- README_AI.md: "`--jobs`, same timelines as one worker".
- ARCHITECTURE.md §9: "(a seed gives the same tree)".
- The code's own comment, main.zig:3955-3960, says the opposite.

**Minimal cases** (`runs3/jobs.txt`; theorems `generation_for_workers`, `same_seed_other_tree`, `finishing_order_other_tree`).
- One worker plans generations of 16; 32 workers plan generations of 32. With the pipeline of 3, timeline 48 is generation 0's first return (from #0 at 23 µs) with one worker, and a fresh start with 32.
- With `--generation 4` given, 2 workers and pipeline 2: timeline 0 finishes last, generation 0 is timelines 1 to 4, and timeline 9 starts from #2 instead of #1.

**How likely.** Certain whenever the worker count differs: another host, `--jobs`, or serve's default. A failure at one index is not at the same index in a rerun elsewhere. Each timeline still replays from its own tape.

**Zig path.** main.zig:3973-3975 and 8883 (generation size from the workers); 4158-4166 and 5309-5341 (generations by finishing order); 4614-4620 (`judge_count`).

**Regression test.** `tests/ce24_tree_jobs.zig`:
- unit test "a seed's tree does not depend on the workers", beside `test generation_for` (main.zig:3977);
- e2e: the records' paths of `--jobs 1` and `--jobs 8` with `--generation 16`, compared index by index.

### CE25: the archive returns to repeats

**Property.** ARCHITECTURE.md §9: "a timeline whose whole trace equals an earlier one's is never returned to".

**Minimal case** (`runs3/tree.txt`; theorem `repeat_is_a_place`).
- Timeline 1's trace equals timeline 0's, and the judgment skips it as a candidate.
- `archive_add` already made it the second place of timeline 0's cells.
- `Cell.place` takes places in turn, so the cell's next return goes to #1, the repeat.

**How likely.** Repeats were returned to in 208 of 15,000 judgments with few randomness pulls, and in 1,159 of 15,000 with same_seed.py. Each one costs a node and its branches for a state the tree already has.

**Zig path.** main.zig:6366 (`archive_add` runs before the repeat check at 6400); 7016-7026 (a place added for a behavior another timeline reached); 5826-5829 (`Cell.place`).

**Regression test.** `tests/ce25_archive_repeat.zig`: "a repeat is no archive cell's place", beside "the archive returns first to a cell whose returns paid" (main.zig, after 5880).

### CE26: a generation returns twice to one moment

**Property.**
- docs/AGENTS.md: "A generation of 16 is 4 fresh starts and 3 moments with 4 branches each".
- main.zig:7077-7080: "seldom returned to ...; each return counts".
- docs/PLUGINS.md: the explorer's fill goes to "other timelines than those chosen".

**Minimal case** (theorem `frontier_and_archive_one_moment`, at the Zig's default shape of 16 with 4 branches).
- Only #0 made `sometimes "zero"` true.
- Its frontier return lands just after it and is kept.
- The behavior's cell is new: its count of timelines is still 0 when ranked, because `visits` is updated later (6431-6435). So it ranks first, and its one place is the same moment.
- The frontier's return carries no `cell`, so the archive does not know the moment was just returned to, and returns there again.
- Result: 8 timelines from one moment, 2 distinct moments instead of 3, and a second node replayed from the parent's start.
- Strategy case: the archive fill went to the timeline a strategy chose, because 7106 skips only the strategy's matched cell (1,310 of 5,000 runs).

**How likely.** 1,322 of 15,000 judgments (8.8%) in the default-shape world with no strategy.

**Zig path.** main.zig:7323-7339, 7081-7123, 7134-7165, 7106.

**Regression test.** `tests/ce26_two_returns_one_moment.zig`: "a generation never returns twice to one moment", beside "a plugin's returns are kept whole..." (main.zig, after 5917).

### CE27: determinismo-ci reports a hang as the job's "error", "failing in 0 of 3 timelines"

**Property.** docs/CI.md:
- "failing in every timeline, fail; in some, flaky; in none, pass";
- `run`: "exit status 0 when they pass";
- exit status "0 when every shard passes, 1 when one fails, 2 when one is flaky (`--flaky-passes` counts flaky as passing)".

**Minimal case** (`runs3/ci.txt`; theorem `hang_is_an_error`).
- One shard with 3 timelines: two pass, and the third deadlocks and is cut at its limit, stating nothing.
- determinismo-ci prints `shard 1: error ... failing in 0 of 3 timelines` and exits 1, with or without `--flaky-passes`.
- The docs say flaky: exit 2, or 0 with `--flaky-passes`.
- With `junit`, a runner that dies before its report does the same, through `tests_judge`'s `unreported`.
- "error" appears in no doc.

**How likely.** Every hang or runner crash in a job: the races and crashes the product exists to show, reported as the job's own failure.

**Zig path.** ci.zig:250, 273-275, 286, 288-291; `tests_judge` 440-485 (lines 470 and 475).

**Regression test.** `tests/ce27_ci_hang_error.zig`:
- unit test "a shard whose tests hang in one timeline of three is flaky, failing in that one", beside "a shard's verdict line read" (ci.zig, after 524), on line 286 made a function;
- e2e: ci-demo with a test that deadlocks in some schedules.

### CE28: a session opened on a CI job's run changes its shard verdicts

**Property.**
- docs/CI.md: a shard's verdict is its timelines'.
- store.zig:676-679: "What a run found is judged over these" (sessions excluded). `properties_sql` and the UI's CI page already exclude them.

**Minimal case** (theorem `session_turns_a_failing_job_green`).
- A shard fails in all 3 timelines.
- A session (a REPL fix) passes before the verdict is read.
- `shard_sql` reads `timeline_events`, which includes the session: "flaky", exit 0 with `--flaky-passes`.
- The other way: a passing shard plus a failing session reads flaky.

**How likely.** It needs a session opened while the job runs whose run reaches the shard's det-assert before the verdict is read. Jobs take minutes, and a failing timeline's page offers a REPL.

**Zig path.** ci.zig:273-275 (`FROM timeline_events`; `explored_timeline_events`, store.zig:684-686, would exclude sessions) and 286.

**Regression test.** `tests/ce28_ci_session_verdict.zig`: a store.zig test, "a CI shard's verdict counts the run's timelines, never a session's" (after 1990), with ci.zig's `shard_sql` made pub.

### CE29: a resumed run's state ignores timelines recorded before its stop

**Property.**
- serve.zig:5912: "A failing property fails the run, as explore exits".
- serve.zig:5630-5633: resume "Continues a run that ended before its end".
- main.zig:242-244, the `--resume` usage text.

**Minimal cases** (`runs3/serve.txt`; theorems `resumed_reads_passed`, `resumed_reads_failed`).
- The one timeline failed, and the run was stopped after its record line. On resume, `resume_read` says "the run is complete" and exits 0: "passed", while its properties fail.
- Two timelines: the first fails before the stop, the second passes after. The explorer judges only the second: "passed".
- The other way: a `sometimes` made true only before the stop ends "failed", while its properties pass.

**How likely.** Any resumed run with a failure, or with its only true `sometimes`, before the stop. A stop during the end's replays loses every failure.

**Zig path.** main.zig:2103-2194 (2186-2192 exit 0); 3460-3462 (recorded timelines skipped, nothing absorbed); 1106-1170; serve.zig:6226-6235.

**Regression test.** `tests/ce29_resume_verdict.zig`:
- unit test "a resumed run's verdict counts the timelines its record has" (main.zig, after 2380), on `resume_read`'s parse made a function;
- serve e2e: stop after a failing timeline, resume, check "failed".

### CE30: the coverage gate stops instrumented runs whose first timelines repeat their setup's code

**Property.**
- docs/SDKS.md:101-105: "a run whose first 4 ended timelines report none is stopped".
- The stop's reason (serve.zig:731-733): "its system runs without its language's instrumentation".
- docs/CI.md: "serve can tell a job that ran from one that did not".

**Minimal case** (theorem `instrumented_run_stopped`).
- The setup ran edge 2, and each of the first 4 timelines runs edge 2 again.
- The coverage bits are a tmpfs in the setup's snapshot (init.zig:214-223; sdk/zig/determinismo.zig:2122-2200), so nothing new is reported.
- The run is stopped and called uninstrumented.
- Also: `count(*) FROM timelines` includes sessions, so one run timeline plus three sessions stops a run.

**How likely.** Systems whose setup exercises the drivers' paths (warm-ups, readiness probes, nodes started in the setup), when the first timelines reach no new path. The stop sends users to rebuild a workload that is already instrumented.

**Zig path.** serve.zig:703-752 (722 and 728); voidstar.zig:244-260.

**Regression test.** `tests/ce30_coverage_gate_setup_edges.zig`: a serve test beside `coverage_gate`. With coverage in the setup's events and none in 4 timelines, no `stopped` file is written.

### CE31: corrupt_reads, a failure that "keeps what is stored", stores a corrupted byte

**Property.**
- schema.zig:515-519: with `disk_lost_writes` off, "Its other failures leave what is stored intact, so durability stays judgeable".
- nodes.zig:1936-1937: "what is stored is intact".
- ANTITHESIS.md: the disk fails "for a while".

**Minimal case** (theorem `corrupt_read_stored`).
- A page stores `[0,1]`. During corrupt_reads (byte 1 reads 1), the node writes byte 1 = 0.
- The page is not cached, so the kernel reads it first through the corrupting table: `[1,1]`, then the write makes `[1,0]`.
- After the heal, `[1,0]` is stored: a byte the node never wrote.
- A page read during the fault stays corrupted in the cache after the heal (2191 leaves a running node's cache as it is).

**How likely.** Any corrupt_reads fault on a node that partially writes a page it does not hold in its cache: a log appended after a restart, a page updated in place. errors, write_errors and lost_writes never stored a foreign byte (each world exhausted: 663,552 timelines).

**Zig path.** nodes.zig:1979-1983, 2179-2198; faults.zig:916-922, 955-964.

**Regression test.** `tests/ce31_disk_corrupt_reads_stored.zig`: a selftest disk scenario (beside nodes.zig:1382). A cold page gets one byte written during corrupt_reads, is synced and healed, and the device is read with O_DIRECT. A page read during the fault is read again after the heal.

## Other findings (not counterexamples)

- **Return offsets.** With the default `--return-offsets` (0,0,0,1s,5s,30s; main.zig:6893-6918), half the returns land before what they were chosen for. That includes a `sometimes` made true (2,177 of 5,000 runs) and an optimize bucket's best (3,106 of 5,000). AGENTS.md says "the tree returns there"; the usage text documents the offsets. The comment "Never before its branch's start: just after then" leaves out that a return that cannot move stays where it was (6907).
- **Strategy returns past the last pull.** A strategy's return past its timeline's last randomness pull is accepted (7247-7250 checks only the span), so its children are one timeline (ARCHITECTURE.md §9).
- **Extensions of cut timelines.** A cut timeline's extension lands at its last pull, not where it stopped (7279-7296), unlike frontier_choose's "open to its end" (6731-6733). Read, not modeled.
- **writeback_s.** ANTITHESIS.md:52 says a crash loses "only the last window's unsynced writes". But nodes.zig:2811-2858 draws the flusher off half the time ("strict when off", AGENTS.md:234), and a crash at 30 s with a 5 s window lost 30 s (theorem `writeback_off_loses_all`).
- **Lost writes before a crash.** ANTITHESIS.md says lost writes are "gone at the next crash". A node that exited during the fault is unmounted at the heal (nodes.zig:2192-2196), so its synced writes are gone without any crash. So are pages evicted under memory pressure.
- **Skews and skips.** `skew_clamp` (faults.zig:1728-1739) bounds skews by `clock_high_ns`, which clock skips never raise. A skew of -1 beside one of +1, then a permanent skip back of the maximum: one node 5 below what clocks remember, against a maximum of 4. Both features are off by default. With skews alone the bounds hold (1,000,000 timelines exhausted plus 100,000 seeds; theorem `skewClamp_within`).
- **CE2's remainder, drawn.** In worlds drawn around it, 315 of 20,000 timelines broke "a command that ended on its own is judged by its exit". All 315 had `min_drive` 0: 315 of 9,928 (3.2%).

## What was replicated, and what is not exact

Replicated with file and lines:
- the tree's shape, the frontier, the candidates' order, `tree_returns`, `answer_parse` and `Strategies.returns`;
- the archive (`archive_add`, `objective_place`, `memory_forget`, `archive_ranked`, `archive_returns`, `archive_offered`), `returns_earlier`, `judge_plan_one` and the fresh fill;
- the queue (planned timelines before filler), generations by finishing order, `generation_for`;
- the worker's seed choice, tape headers, and nodes made by a holder or by `Recorded.load` and `chain`;
- determinismo-ci's SQL, `tests_judge`, verdicts and exit statuses;
- `properties_sql` statuses with sessions;
- `resume_read`, system_run's verdict and serve's `state`;
- `coverage_gate` and the Zig SDK's coverage reporting;
- `disk_fail`, `disk_failures_kept`, `disk_heal` and `writeback_loop`;
- `skew_clamp`, `skew_begin`, strobes, `clock_leaves` and `clock_shift`.

Not exact:
- The tree runs a model system. Judgments are made at once (the Zig keeps starting queued filler while nodes are made). Holders are a decision per return. Memory caps, the bandit, novelty steering, horizons, targeted runs, severity, history and ladders are left out. `branch_seed` and trace hashes are a stand-in mix.
- `archive_ranked`'s order is weighted sampling without replacement, the distribution the Zig's keys give, not its PRNG. The other generation draws are named decisions.
- Return offsets are scaled to 0, 0, 0, 7, 15 and 33 µs.
- CI outcomes, disk steps and clock events are world decisions. The resume model is a flat run with no catalog. Disk pages are 2 or 3 bytes.

## Assumptions

- Linux's page cache: a buffered partial write to an uncached page reads it first; a read keeps the page clean; a failed writeback leaves the page clean; an unmount or crash drops the cache; clean pages can be evicted. dm-flakey's `corrupt_bio_byte r` changes read data.
- Coverage is the Zig SDK's, the C SDK's and libvoidstar's: an event the first time a process of the timeline runs an edge, setup included. The JVM and Python agents are not modeled.
- A session is a row of `timelines` with `extends` set, its events past its moment its own.
- A hung CI timeline states nothing after its run command.
- Code comments state the promise where the docs are silent (CE26, CE31, the skew clamp).
- Rounds 1 and 2's assumptions hold.

## Properties, with sources (28)

**The tree (13).**
1. Every timeline replays alone from its tape (README_AI.md; ANTITHESIS.md; PLUGINS.md): fails (CE23).
2. A node made by a replay is its parent's state (PLUGINS.md; ARCHITECTURE.md): fails (CE23).
3. A repeat is never returned to (ARCHITECTURE.md §9): fails (CE25).
4. A generation's returns are distinct moments, each counted (AGENTS.md; main.zig:7077-7080): fails (CE26).
5. The fill goes to other timelines than a strategy's (PLUGINS.md): fails (CE26).
6. The explorer's returns lie inside their timeline, before its last pull (ARCHITECTURE.md §9): holds.
7. Every branch point, a strategy's too, comes before its timeline's last pull (ARCHITECTURE.md §9): fails (noted above).
8. A judgment plans as many timelines as it judged, its returns within the budget (AGENTS.md; PLUGINS.md): holds.
9. A timeline's frontier is a sometimes made true when it has an open new one (AGENTS.md; usage): holds.
10. A return for a sometimes made true lands after it (AGENTS.md): fails by the offsets.
11. An optimize bucket's cell keeps the best state so far (AGENTS.md): holds.
12. A return to an optimize bucket lands at its best (AGENTS.md): fails by the offsets.
13. The same timelines whatever `--jobs` (README_AI.md; ARCHITECTURE.md): fails (CE24).

**CI (4).**
14. The job's verdict is the documented one (CI.md): fails (CE27, CE28).
15. A shard's line counts every timeline that did not pass: fails (CE27).
16. The exit status is the documented one: fails (CE27).
17. A shard's verdict excludes sessions (store.zig:676-679): fails (CE28).

**Serve (4).**
18. A resumed run's state is its timelines' verdict: fails (CE29).
19. The coverage gate stops only runs without instrumentation: fails (CE30).
20. The gate judges the run's own first 4 timelines: fails (CE30).
21. A session never changes a property's status (`properties_sql`): holds, every kind, exhausted.

**Disk (4).**
22. With `disk_lost_writes` off, no foreign byte is stored: fails (CE31).
23. After the heal, reads return what is stored: fails (CE31).
24. Lost writes are gone at the next crash, not before: fails (noted above).
25. With `writeback_s`, a crash loses only the last window: fails (noted above).

**Clock (2).**
26. Every two nodes stay within the maximum: holds, and is proven for one clamp.
27. Every node stays within the maximum of what clocks remember: holds with skews alone, fails with skips.

**The composer (1).**
28. Round 1's 13th property, in CE2's drawn worlds: fails, 315 of 20,000.

## Search runs (`runs3/`)

- `tree.txt`: 12 properties over 7 worlds, each exhausted to 20,000 runs and explored over 10,000 seeds.
- `tree-census.txt`: 5,000 seeds per world, every property counted per run.
- `jobs.txt`: the `--jobs` property; the timing world exhausted to 20,000 and explored over 5,000 seeds, the default generation explored.
- `ci.txt`: 4 properties over 6 worlds, exhausted.
- `serve.txt`: resume over 1 to 3 timelines, the gate over 3 worlds, sessions over 5 kinds, all exhausted.
- `disk.txt`: 3 properties over 6 worlds (4 complete at 663,552 timelines; 2 exhausted to 1,000,000 and explored over 100,000 seeds), plus `writeback_s`.
- `skew.txt`: 3 worlds exhausted to 1,000,000 and explored over 100,000 seeds.
- `ce2.txt`: 20,000 seeds.

`ci`, `serve`, `tree` and `treecensus` were run again after fixing the model, so that a decision behind a condition is no longer drawn every time. Lean lifts `(← x)` out of `a && (← x)`. The fix changes tapes and the size of the spaces, not what the properties see.

## Theorems (19, `Replica/Theorems3.lean`)

General:
- `generationFor_ge_base`
- `judgeCount_le`
- `fits_shape`
- `clamp_fold`
- `skewClamp_within`

By computation:
- CE24: `generation_for_workers`, `same_seed_other_tree`, `finishing_order_other_tree`.
- CE23: `strategy_seed_tape_replays_another`, `strategy_seed_node_elsewhere`.
- CE25: `repeat_is_a_place`.
- CE26: `frontier_and_archive_one_moment`.
- CE27, CE28: `hang_is_an_error`, `session_turns_a_failing_job_green`.
- CE29: `resumed_reads_passed`, `resumed_reads_failed`.
- CE30: `instrumented_run_stopped`.
- CE31: `corrupt_read_stored`.
- `writeback_s`: `writeback_off_loses_all`.

## Library gaps

- `(← x)` inside `a && (← x)` is hoisted, so a conditional decision is drawn unconditionally. A `decideIf`, or a lint, would prevent it.
- When the world's state holds the decisions, a `set { s with ... }` after a decision drops the decisions taken since `s` was read. The skew model lost its skips' decisions this way until it used `modify`. Keeping decisions apart from the world's state would make this impossible.
- There is no weighted sampling without replacement.
- `exhaust` changes the last decisions first, so a world whose first decision picks the case never reaches its other cases. Fixed worlds were used here.
- Page-cache, time-namespace and SQL-view models were built by hand.

## Left for round 4

- Run CE23 to CE31 on the platform.
- The tree:
  - holders: spacing, and one holder per return;
  - the node memory cap, and horizons and extensions of cut timelines;
  - targeted runs, steering, the bandit and ladders;
  - a resumed tree's `rejudge_load` and `recorded_returns`.
- CI: per-shard `reported` counts; the `{shard}` runner mode.
- Disk:
  - write_errors with fsync's error reporting after the heal;
  - sync_stall and durable_crash with partial persistence;
  - eviction under lost_writes.
- Clock: a node restarted during its skew gets a fresh time namespace.
- The coverage gate with the JVM and Python agents.
