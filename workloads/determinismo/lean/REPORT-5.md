# determinismo in Lean: round 5

## What this is

Round 5 of the Lean 4 (v4.36.0) replica of determinismo. The platform's next branch is now 62e06e3, a plain copy in `upstream-62e06e3/` (its commit in `.commit`). Round 4's baseline, 3939448, stays in `upstream/`, so each verdict cites both versions' lines as `3939448 → 62e06e3`. The models now follow 62e06e3 by default. Each changed function takes a version (`Ver`, in `Replica/Prelude.lean`), and the theorems about 3939448's code pass `.v3939448` explicitly. The SDK is still the one at `upstream/sdk/lean`.

Changed models:
- `Composer.lean`: `kill_all` reaps first; the slot wait is bounded by the stop; the clock is drawn before `composer_start` with a 30-minute cap; the explorer answers `composer.again` yes once.
- `Junit.lean`: `element_index`.
- `Persist.lean`: a fresh file is written back from its first range.
- `Verdicts.lean`: the catalog keyed by kind; serve's `ended_status`.
- `Tape.lean`: the recorder's cap and its `tape_full` marker; `passed` and `past_full`; idle ingress polls never taped.
- `Ci.lean`, `Ci4.lean`: `shard_verdict`, sessions left out, the per-timeline `unreported_sql`, `tests_judge` without its count.
- `Durable.lean`: two arms per node.

New files:
- `Replica/Ci5.lean`: `shard_command`'s xargs runs and their merged reports, by the run line's form.
- `Replica/Resume5.lean`: the resumed verdict at 62e06e3 (record lines' properties, their room, the complete path) and serve's `runs_adopt`.
- `Replica/Clock5.lean`: the default jump against a token's hour over a whole timeline.
- `Replica/Disk5.lean`: corrupt_reads's tracefs reader, the heal, and a later fault's reader.
- `Replica/Theorems5.lean`: 29 theorems.
- `Main5.lean`: the `replica5` executable.
- `tests/ce40_*.zig` to `tests/ce48_*.zig`: the regression tests.
- `runs5/`: the searches' output and the Zig test runs.
- `scratch/round5.sh`: the searches.
- `scratch/zig5/`: copies of 62e06e3's `ci.zig`, `junit.zig` and `tape.zig` with the new tests appended. They are compiled and run outside the platform's tree.

Commands:

    lake build
    .lake/build/bin/replica5 composer|cworld|cdrawn ...
    .lake/build/bin/replica5 junit|persist|verdicts|tape|resume <exhaust>
    .lake/build/bin/replica5 ci|durable|disk <exhaust> <seeds>
    .lake/build/bin/replica5 clock <seeds>

## The recheck of CE1 to CE39 at 62e06e3

"Searched" means round 2 to 4's searches were run again on 62e06e3's model, in `runs5/`. "Theorem" names one in `Theorems5.lean` that runs the old minimal case on the new code.

- **CE1** (a finally after a signal): **fixed**, as since 3939448. composer.zig:534-539 → 541-547; reap's `by_kill` 331-340 → 331-337. kill_all's new first reap does not reopen it. Searched: world 4 complete at 1,394; 5,000 drawn.
- **CE2** (an exit hidden as killed with min_drive 0): **fixed**. kill_all reaps what ended on its own before killing (composer.zig:401-407 → 401-412). Searched: worlds 2, 13 and 16 complete (512, 41,472 and 41,472 timelines); 5,000 drawn. Theorem `ce2_own_sigkill_judged`. A death in the few instructions between that reap and the kill is still taken as the composer's.
- **CE3** (workload marking keeps no driver; panic): **fixed**, unchanged (composer.zig:223-235, 686-692 → 221-283, 693-699).
- **CE4** (the length doesn't bound serial or singleton drivers): **partly fixed**, unchanged. Serial drivers and `--timeline` are bounded. A drawn length still doesn't bound a singleton, by design (composer.zig:712-714 → 718-721), against the comment at schema.zig:643-648 → 648-653.
- **CE5** (a driver starts past half the limit): **fixed** on both paths. Quiet stretches: composer.zig:792-803 → 799-808. The slot wait is now bounded by the stop: 849-851, 875-890 → 809-813, 883-898. Searched: world 14 complete (5); world 12 explored. Theorem `ce5_slot_wait_stops`. A second driver phase is new (CE42).
- **CE6** (fault exclusions miss links): **fixed**, unchanged (faults.zig:1484-1489).
- **CE7** (an outage ignores the recovery window): **fixed**, unchanged (faults.zig:2122-2132, 3095-3109).
- **CE8** (injected faults in quiet periods): **fixed in the docs**, unchanged since round 2 (ANTITHESIS.md:60-61; faults.zig:392, 4590).
- **CE9** (one message with two kinds, order-dependent): **fixed**, unchanged (events.zig:56-61 → 59; report.zig:520-523 → 610). Searched: the order property holds in all 10 verdict worlds.
- **CE10** (a sometimes true in another scenario): **fixed**, unchanged (report.zig:367-407 → 417-456; main.zig:1149-1155 → 1151-1156).
- **CE11** (messages sharing 192 bytes): **fixed**, unchanged (events.zig:1483-1501 → 1486-1504).
- **CE12** (replays lose the fork and serve events): **fixed**, unchanged (vm.zig:3691-3694, 3805-3806 → 3750-3753, 3876). Searched.
- **CE13** (a passed-over checkpoint stops all checks): **fixed, with round 2's remainder**: a replay that parts inside its tape's last checkpoint interval is never stopped by a checkpoint (tape.zig:223-233 → 265-277). Searched: found again in `runs5/tape.txt`.
- **CE14** (thinning overflows the checkpoint table): **fixed**, unchanged (tape.zig:593-608 → 666-683).
- **CE15** (the wall clock jump reaches what the setup made to expire): **partly fixed**. The cap went from an hour to 30 minutes (composer.zig:903 → 913-914). The new test checks the jump plus one 20-minute phase (970-979). A whole timeline is longer than that (CE44). Theorem `ce15_thirty_minute_bands`.
- **CE16** (captured output fails a passing test): **fixed** for CDATA output (junit.zig:32 → 32, 58-87). Searched: round 2's world complete at 961. Theorem `ce16_captured_error_passes`. Output that prints its element's own closing tag is new (CE41).
- **CE17** (a fresh file keeps a later range and loses an earlier one): **fixed** (nodes.zig:942-953 → 828-830, 859-864, 945-954). Searched: "no hole before a kept page of a fresh file" holds (1,000,000 timelines and 284,650 complete). Theorem `ce17_fresh_file_from_its_first_range`. Files with allocated pages still wrap, which contradicts ANTITHESIS.md:53's "ascending run" wording: found in 2,868 timelines. The code comment says the wrap is by design.
- **CE18** (a sometimes hidden by another kind): **fixed** (report.zig:125-145 → 143-173; main.zig:1150-1155 → 1151-1156). Searched. Theorem `ce18_ce22_catalog_by_kind`.
- **CE19** (an adopted run reads "passed"): **partly fixed**. `ended_status` reads `exit` in discovery and in the adopted reap (serve.zig:5757-5762, 5983 → 5756, 5903-5909, 6017). Theorem `ce19_adopted_reads_exit`. `runs_adopt` still deletes `exit` and reads the record (5821 → 5806-5815): CE47.
- **CE20** (a tape over 65,536 overrides never replays): **partly fixed**.
  - Fixed: the replay's table is sized from the tape (tape.zig:8, 554-556 → 11, 139-187, 593). The recorder stops at `override_count_max` with a `tape_full` marker (vm.zig:3684-3699; tape.zig:406-414), and a replay stops there (300-308). Idle polls are never taped (vm.zig:3806-3815, 3837).
  - Searched: "a replay has its recorded history to where its recorder stopped taping, and stops there" holds in the three full-tape worlds (one complete at 65,536, two exhausted to 1,000,000).
  - Theorem `ce20_full_tape_stops_its_replay`.
  - The reason table is unchanged (tape.zig:117 → 120, 639): CE48.
- **CE21** (only the last xargs batch judged): **fixed for a run line that falls through** (ci.zig:221-245 → 526-563). Proven for every list of runs: `ce21_plain_keeps_every_run`. A run line that leaves its shell undoes it (CE40).
- **CE22** (the catalog's verdict depends on order): **fixed** (report.zig:131-138 → 143-166). Searched. Theorem `ce18_ce22_catalog_by_kind`.
- **CE23** (a strategy's seed replays another prefix): **still there**, unchanged (main.zig:3484 → 3523; the plan's seed and segments 6280-6286 → 6319-6325).
- **CE24** (the same seed grows another tree with other workers): **still there**, unchanged (main.zig:3973-3975 → 4012-4014; 4614-4620 → 4653-4659).
- **CE25** (the archive returns to repeats): **still there**, unchanged (main.zig:6366, 7016-7026, 5826-5829 → 6405, 7055-7065, 5865-5868).
- **CE26** (two returns to one moment): **still there**, unchanged (main.zig:7081-7123, 7323-7339 → 7120-7162, 7362-7378).
- **CE27** (a hang reported as the job's "error"): **fixed**. `shard_verdict` counts a silent timeline as failing (ci.zig:286 → 316-320). Searched: the job, line and exit properties hold. Theorem `ce27_hang_is_flaky`. "error" is still printed, and still missing from docs/CI.md, in two cases: a shard that passed without a report (289), and a run serve stopped (292).
- **CE28** (a session changes the shard verdicts): **fixed** (ci.zig:273-275 → 340-342, `explored_timeline_events`). Searched. Theorem `ce28_session_left_out`.
- **CE29** (a resumed run ignores what was recorded before its stop): **partly fixed**. Record lines now carry each timeline's evaluated properties, merged on resume (report.zig:28-45, 513-531, 593-608; main.zig:2023-2036, 2170-2176, 2212-2229, 2828-2829). Searched: holds for evaluated always and sometimes. Theorem `ce29_recorded_failure_counts`. Two remainders: a complete resume judges no catalog (CE45), and properties past a line's room are not counted (CE46).
- **CE30** (the coverage gate stops instrumented runs that repeat their setup's code): **still there**, unchanged (serve.zig:703-752).
- **CE31** (corrupt_reads stores a foreign byte): **fixed by declaring it**. The byte is still stored, now documented as a real disk's behavior, and every read the fault corrupts is to be named (schema.zig:515-519 → 520-524; nodes.zig:1936-1937 → 1983-1986; the tracer 2052-2060, 2152-2324). Reads go unnamed or are misnamed: CE43.
- **CE32** (a resumed tree renumbers a judgment's returns): **still there**, unchanged (main.zig:6820-6841 → 6859-6880; 6455-6466 → 6494-6505).
- **CE33** (a resumed generation is planned as nodes come): **still there**, unchanged (main.zig:6254-6261 → 6293-6300; 4720-4723 → 4759-4762).
- **CE34** (a filler between a judgment's plans cuts a resume): **still there**, unchanged (main.zig:4562-4574, 4693-4698 → 4601-4613, 4732-4737).
- **CE35** (sync_stall and durable_crash share one arm): **fixed** (det_guest.c:249, 284-307, 404-447, 461-523; faults.zig:2245-2250, 3256-3290, 3325). Searched: 6 steps at 4 eighths complete at 446,792. The census has 0 of 100,000, with both kinds begun in 49,660. Theorem `ce35_two_arms`.
- **CE36** (lost writes read back stale before a crash): **fixed in the docs**. ANTITHESIS.md:56 now says "or sooner once the kernel drops the page from its cache"; nodes.zig:1932-1933 → 1977-1980. The model still finds the old wording's case, which is now documented.
- **CE37** (missing reports counted over the whole run): **fixed** (ci.zig:440-485 → 296-308, 483-513). Searched: the per-timeline count holds in 3 worlds. Theorem `ce37_unreported_counted`.
- **CE38** (an uncovered CI job errors, depending on the host): **still there**. serve.zig:703-752 is unchanged, and the run is still posted without `coverage`. ci.zig now prints serve's reason and sets "error" on purpose (251-256, 292). docs/CI.md:90 still says an older runtime "runs uncovered". Searched: found in all three worlds. The never-run shards now print "fail, failing in 3 of 3 timelines".
- **CE39** (a targeted run reports "NEVER RAN"): **still there**, unchanged (main.zig:4371, 4383, 6363-6391 → 4410, 4422, 6402-6430).

## New counterexamples

### CE40: a run line that leaves its shell undoes CE21's fix

**Property.**
- docs/CI.md (`junit`): "each test gets its own verdict across its shard's timelines".
- ci.zig:526-531, the fix: "with a report each run's is moved aside and all of them make the report ...: every test of the shard gets its verdict, not only the last run's".

**Minimal case** (`runs5/ci.txt`; theorems `ce40_exit_run_line_keeps_the_last_run` and `ce40_set_e_drops_the_failing_run`; general theorem `ce40_leaving_keeps_only_the_last`).
- Two xargs runs, of ["a", "b"] and ["c"].
- The run line is examples/ci-demo/ci-capped.json's form: `...; status=$?; python -c ...; exit $status`.
- Each run's `sh -c` exits at `exit $status`, before the appended `; s=$?; if [ -f <junit> ]; then mv ...`.
- The second report overwrites the first, no part exists, and the merge (`set -- <junit>.determinismo-ci-part.*`) finds none.
- So "a" and "b" never get a verdict.
- The same happens for `exec` and for a trailing `# comment`.
- Under `set -e`, a run whose runner fails exits before its move. Its report is overwritten by the next run's, or by the merged parts. The failing tests are the ones without a verdict.

**On the code.** Appended to a copy of 62e06e3's `ci.zig` and run (`runs5/ce40-zig.txt`). The upstream CE21 test passes; both new tests fail:
- `exit`: 20,000 names, 5,000 judged.
- `set -e`, the first run failing: 15,000 judged.

The model at GNU's 131,072 bytes, 2,000 names of 80 bytes: 383 of 2,000 judged for `exit`, `exec` and a comment, and for `set -e` with the first run failing.

**How likely.** Any `{tests}` job with `junit` whose shard list passes xargs's buffer, which is about 1,600 names of 80 bytes. The run line must end its shell in one of these ways. ci-capped.json is the repository's own example of the `exit` form, and `exec` and `set -e` are common in CI scripts.

**Zig path.** src/products/ci.zig:533-563 `shard_command`: 539-547 append the move after the run line as written; 548-554 merge the parts.

**Regression test.** `tests/ce40_ci_run_line_leaves_shell.zig`, beside the CE21 test (after ci.zig:658). It compiles and fails at 62e06e3.

### CE41: captured output that prints its element's closing tag fails a passing test

**Property.**
- junit.zig:2-6: a case fails by "whether it holds a `<failure>` or an `<error>`".
- 62e06e3's own test name: "a test case's captured output never fails it".
- docs/CI.md, Verdicts per test.

**Minimal case** (`runs5/junit.txt`; theorem `ce41_closing_tag_fails_a_passing_test`):

    <testcase classname="junit.ReportTest" name="renders_an_error"><system-out><![CDATA[</system-out><error message="x"/>]]></system-out></testcase>

- `element_index` skips from `<system-out>` to the first `</system-out>` after its tag, which is the one inside the CDATA.
- It goes on scanning there and meets `<error`.
- The test is judged failing in every timeline.
- `<system-err>` behaves the same.

**On the code.** Appended to a copy of 62e06e3's `junit.zig` (`runs5/ce41-zig.txt`): the four upstream tests pass and the new one fails.

**How likely.** Any test that prints JUnit XML: the tests of a reporter, a CI tool, or a test framework's own suite. Surefire, jest-junit and go-junit-report write such output in CDATA as is. Rare, but certain for those suites: the job fails in every timeline.

**Zig path.** guest/runtime/junit.zig:62-87 `element_index`, the skip at 72-81.

**Regression test.** `tests/ce41_junit_closing_tag_in_cdata.zig`, beside "a test case's captured output never fails it" (after junit.zig:205). It compiles and fails.

### CE42: a second driver phase starts drivers past half the timeline's limit

**Property.** composer.zig:792-795: "No driver starts past half the timeline's limit".

**Minimal case** (`runs5/stop-world17.txt`; theorem `ce42_second_phase_starts_past_half`).
- One parallel driver, one at a time, a 600 ms limit, no length.
- Phase 1 starts at 0, 10, 20 and 30 ms; the fourth start runs 270 ms.
- At 30 ms, `drive_again` asks (under a quarter of the limit) and the explorer answers yes once.
- Phase 2's `run_drivers` sets its stop at 30 + 300 = 330 ms.
- Its drivers start at 300 and 310 ms, past 300.

**How likely.** Every return to an objective's best is asked for a second phase (advisor.zig:79-83; `--objective-extend` on by default, main.zig:540). The stop exists with a timeline limit (an hour by default) and no length (`--drive-max none`). Starts can then come up to three quarters of the limit after the drivers began.

**Zig path.** composer.zig:797 (`stop_ns = now_ns() + limit_ns / 2`, per phase), 1025-1028 (`drive_again`), 521-525 (the phases).

**Regression test.** `tests/ce42_composer_second_phase_stop.zig`: a selftest scenario and its explore line.

### CE43: corrupt_reads's last reads are never named, or are named under the next fault

**Property.**
- sdk/zig/schema.zig:520-524: "Every read it corrupts is an event (`disk_corrupt_read` ...): a loss outside every such read is the system's".
- nodes.zig:2052-2055: "a read just before is named too: never one missed".
- nodes.zig:2415: "After the table heals: a read just before it is named too".

**Minimal case** (`runs5/disk.txt`; theorem `ce43_read_before_the_heal_unnamed`).
- corrupt_reads #0 begins and its reader process starts.
- A read is queued; its line waits in the instance's ring buffer.
- The heal comes before the reader is scheduled. The reader is SIGKILLed, so the read is never named in fault #0.
- `rmdir(instance)` fails with EBUSY while the dying reader still holds `trace_pipe`, so the instance stays.
- The node's next corrupt_reads reuses the instance (`mkdir` ignored). Its reader names read 0 under fault #1, with fault #1's `corrupt_byte`: a byte fault #1 never changed.

**How likely.** Any read just before a corrupt_reads fault ends. The heal (a device-mapper suspend, then the kill) runs in the injector, and nothing waits for the reader to drain. The second half needs a later corrupt_reads on the same node.

**Zig path.** guest/runtime/nodes.zig:
- 2173-2229 `disk_reads_trace_start` (2186 `mkdir` ignored; 2203 the pipe opened);
- 2232-2266 `disk_reads_read`;
- 2309-2324 `disk_reads_trace_stop` (2316 the kill, 2323 `rmdir` unchecked);
- 2412-2415 `disk_heal`.

**Regression test.** `tests/ce43_corrupt_reads_unnamed.zig`: a guest test beside `test bio_read_line`. It needs root, tracefs and device-mapper; run it in the selftest's disk node.

### CE44: the default jump takes a whole timeline past a token's hour

**Property.** composer.zig:907-912 (62e06e3): "by default short of what a setup made to last an hour ...: the jump and the longest default drive (20 minutes) stay within it, so a timeline failing on the jump, no workload's failure, takes a credential shorter than that". Also 900-901.

**Minimal cases** (`runs5/clock.txt`; theorems `ce44_second_phase_past_the_hour` and `ce44_ending_past_the_hour`).
- An objective's return:
  - a jump at the 30-minute cap;
  - a first phase of 899,999 ms and a second of 20 minutes;
  - a 1 s ending.
  - That is 35 minutes of virtual time, with no hang. The setup's hour token is used 5 minutes past its expiry.
- One phase:
  - a jump of 1,624,445 ms;
  - a 760,404 ms phase, the 30 s grace, and an ending that ran its 20-minute window.
  - The token is used 14.8 s past its expiry.

Without the jump, a timeline under the hour's limit never reaches its token's expiry.

**How likely.** In the census:
- 4,452 of 1,000,000 drawn objective-return timelines (endings of 1 s to 20 minutes);
- 1,315 of 1,000,000 with one phase;
- 0 of 1,000,000 with one phase and a 1 s ending, which is what the fix's test checks.

The failure lands in the ending's check or in the second phase: an auth failure that is no workload's.

**Zig path.** composer.zig:913-914 (the cap), 970-979 (its test), 1025-1028 (`drive_again`), 751 (the grace), 1113 (`ending_ms_max_default`), main.zig:562 (the limit).

**Regression test.** `tests/ce44_clock_start_whole_timeline.zig`, beside the fix's test (after composer.zig:979).

### CE45: a resume that finds every timeline recorded judges no catalog

**Property.**
- main.zig:2213-2214: "Judged from its record, as the run that recorded it would have been".
- CE29's property: a resumed run's state is its timelines' verdict.
- serve.zig:5630-5633.

**Minimal case** (`runs5/resume.txt`; theorem `ce45_complete_resume_skips_the_catalog`).
- Two timelines declare `reachable "r"` and never reach it. Both are recorded, and the run is stopped before its end.
- Uninterrupted, the run exits 3.
- The resume says "the run is complete", judges `failing_properties` over the record lines, exits 0 and writes `exit` "0". Serve shows "passed".
- A record line keeps only evaluated properties (`hits > 0`), so the catalog is in no line.
- The comment "A catalog's assertions no timeline reached are judged by the runs that ran timelines" (2215-2216) assumes that run reached its end.

**How likely.** Any run stopped after its last record line and before its end: during the end's replays, the summary or coverage, or a deploy's serve restart. The failing property must be a catalogued assertion no timeline reached, such as "test command started: X" for a command never started, or a `reachable`.

**Zig path.** src/main.zig:2210-2229; src/report.zig:513-517.

**Regression test.** `tests/ce45_resume_complete_catalog.zig`, beside main.zig's state_format test. It needs the complete path made a function, `resumed_verdict`.

### CE46: properties past a record line's room are not judged on resume

**Property.** main.zig:2023-2025: "counted in the resumed run's verdict as its own timelines' are"; 2828.

**Minimal case** (`runs5/resume.txt`; theorem `ce46_failure_past_the_room`).
- A record line has room for one property (40 KiB in the Zig).
- Timeline 0 evaluates `always "a"` true, then `always "b"` false.
- The line keeps "a" with `properties_all` false.
- Resumed, the run exits 0; uninterrupted it exits 3.
- The resume says how many lines were partial, "their verdicts not counted" (2207-2208), and passes.

**How likely.** A timeline with more properties than the room holds: about 230 of 50-byte messages, or 128 of 192-byte ones (`name.len + 128` each). Examples: a CI shard with `det-assert junit` (one property a test), or a workload with a property a key or a node. The first ones in the table's order are kept, so a late failing one is lost.

**Zig path.** src/report.zig:42-45, 513-531; src/main.zig:2170-2176, 2205-2208, 2030-2036.

**Regression test.** `tests/ce46_record_line_room.zig`, beside `recorded_merge`: a record line of 400 properties, the last failing, read back and merged.

### CE47: serve deletes a command-line resume's `exit` and shows its record's status

**Property.**
- serve.zig:5898-5902 (`ended_status`: "How a run's explorer ended: its `exit` ...").
- serve.zig:5912: "A failing property fails the run, as explore exits".
- CE19's property.

**Minimal case** (theorem `ce47_adopted_resume_reads_its_record`).
- A run whose only failure is a catalog's `reachable` is resumed from a command line.
- Its explorer notes the adoption (main.zig:1287-1294), exits 3 and writes `exit`.
- The watcher's next look runs `runs_adopt`, finds the explorer gone, deletes `exit` (5806-5810) and takes `recorded_status(record)` (5815). The resume's summary has no catalog, so serve shows "passed".
- A complete resume (CE45's path) ends in milliseconds and always loses its `exit` this way. It then shows "interrupted", or the interrupted run's summary.

**Zig path.** src/serve.zig:5795-5822 `runs_adopt`; 5939-5951 `recorded_status`.

**Regression test.** `tests/ce47_runs_adopt_exit.zig`, beside "a run's end is its explorer's exit, then its record's summary" (after serve.zig:5937).

### CE48: a timeline of 1,025 outside connections still records a tape no replay can read

**Property.**
- README_AI.md: "every timeline replays bit-identically".
- vm.zig:3684-3687 (CE20's fix): "instead of a tape no replay can read".

**Minimal case** (`runs5/tape.txt`; theorem `ce48_reasons_past_the_table`).
- Three decisions carry a reason, against a reason table of two (1,024 in the Zig).
- The recorder writes all three, with no marker, since `tape_override` counts overrides only.
- The replay's parse refuses the tape: `TapeTooLong (reason_count_max)`.

**On the code.** 1,025 `det.egress_channel` overrides, as the egress proxy tapes them. Appended to a copy of 62e06e3's `tape.zig`: CE20's 70,560-poll test passes and the new test fails with TapeTooLong (`runs5/ce48-zig.txt`).

**How likely.** The guest's egress proxy asks its channel at each connection (guest/runtime/egress.zig:42-58), each a decision with `egress_channel_reason` (vm.zig:3514, 3756-3761). So does every fork (`fork_reason`) and every reasoned strategy override. A system that opens 1,025 outside connections in a timeline, such as an HTTP client calling an API, gets a tape that cannot replay. Its node replays and its children's chains fail at the parse too.

**Zig path.** src/core/tape.zig:120 (`reason_count_max`), 635-644; vm.zig:3687-3699.

**Regression test.** `tests/ce48_tape_reason_table.zig`, beside CE20's test (after tape.zig:937). It compiles and fails.

## Other findings (not counterexamples)

- **Full tapes and holders on disk.** The explorer never reads `tape_full` (main.zig has no reference to it). A node made from a disk holder exactly at its moment does no replay (node.zig:143). So a return past a full tape's marker can be made, and its children's chains then stop at TapeFull. Read, not searched.
- **Idle polls.** A replay answers "nothing" for a status pull its tape lacks. A session that runs past its tape's last override without the extend step gets "nothing" for its connections instead of a reset (vm.zig:3806-3815). Consistent for the guest: read, not a promise broken.
- **The clock's order.** The clock is drawn before `composer_start` (composer.zig:491-496). A return or session at `composer_start`'s moment now inherits its parent's jump instead of drawing its own. That is by design (the comment), and other returns always did. Tapes, replays and forks are unaffected: no new pull, and pulls keep their order.
- **Slot wait at the stop.** A slot freed in the last poll before the stop is reaped at the stop's wake, and the start comes one wake past it (composer.zig:386-397). The model counts it as at the stop.
- **The durability arms.** The table holds 64 slots, two arms for each of 32 nodes, the same reach as before. A node's cgroup survives its restarts (nodes.zig:3558, no rmdir), so an arm stays valid.

## What was replicated, and what is not exact

Replicated with file and lines at 62e06e3:
- composer: `kill_all`, the stop-bounded `driver_start_by`, the clock's order and cap, the explorer's single `again`;
- junit: `element_index`;
- persistence: the fresh file's first range;
- verdicts: the catalog by kind, `made_true(.sometimes)`, `ended_status`;
- tapes: the recorder's cap and marker, `passed`, `past_full`, idle polls;
- CI: `shard_verdict`, `shard_sql` over explored timelines, `unreported_sql`, `tests_judge`, the stop's "error", and `shard_command`'s shell (by the run line's form);
- durability: two arms per node and `det_durability`'s order;
- resume: record lines' properties and room, `merge_into`, the complete path, `runs_adopt`;
- corrupt_reads: the tracer's start, reads, heal and instance.

Not exact:
- The shell model draws a run line's form and each run's exit. Batches are GNU xargs's rule.
- The record line's room is a count of properties, not bytes.
- The tracer's scheduling is a decision, and so is the dying reader holding its pipe at `rmdir`.
- The clock model draws the jump and phase lengths as the Zig does; the ending's duration comes from a menu, and other parts of a timeline are left out.
- Round 1 to 4's simplifications still hold.

## Assumptions

- sh semantics: `exit` and `exec` end the shell; text after `#` is a comment; `set -e` exits at a failing simple command.
- GNU xargs splits past 131,072 bytes; macOS's xargs splits too, at its own size (seen in the Zig run).
- Linux tracing:
  - `trace_pipe` consumes what it returns;
  - a reader is woken by an irq_work and scheduled like any task;
  - `kill(2)` returns before the target exits;
  - removing an instance with an open pipe fails with EBUSY, and the buffer stays.
- The explorer answers `composer.again` yes once for an objective's return, and no otherwise.
- A setup's credential lasts an hour of wall time from its issue.
- A run's catalog is declared in each timeline's table, with `hits == 0` until reached.
- serve's watcher looks about once a second.
- Rounds 1 to 4's assumptions hold.

## Properties, with sources (16 new or restated)

1. Every test of a shard gets its verdict, however many xargs runs (CI.md; ci.zig:526-531): fails (CE40).
2. A test case's captured output never fails it (junit.zig's test; junit.zig:2-6): fails (CE41).
3. No driver starts past half the timeline's limit (composer.zig:792-795): fails with a second phase (CE42); holds otherwise.
4. A command that ended on its own is judged by its exit (ANTITHESIS.md): holds (CE2 fixed).
5. A finally only after every command completed, the length's kills aside: holds.
6. Every read a corrupt_reads fault corrupts is named in that fault (schema.zig:520-524; nodes.zig:2052-2055, 2415): fails (CE43).
7. A disk_corrupt_read names its own fault's byte: fails (CE43).
8. The default jump never takes a timeline past a token's hour unless the timeline is longer (composer.zig:907-912): fails (CE44).
9. A resumed run's verdict is the uninterrupted run's (main.zig:2023-2025, 2213-2214, 2828): fails (CE45, CE46); holds for evaluated always and sometimes.
10. A run's state is its explorer's exit, reaped, adopted or resumed (serve.zig:5898-5912): fails through runs_adopt (CE47).
11. Every timeline replays from its tape, up to a full tape's marker (README_AI.md; vm.zig:3684-3687): fails through the reason table (CE48).
12. A full tape's replay has the recorded history and stops at the marker: holds.
13. While a sync_stall or durable_crash lasts, each sync is that fault's decision: holds (CE35 fixed).
14. A shard's verdict, line and exit are as documented (CI.md): hold (CE27, CE28 fixed).
15. Timelines without their report counted each (ci.zig:296-308): holds (CE37 fixed).
16. No hole before a kept page of a fresh file: holds (CE17 fixed); "an ascending run" fails for non-fresh files, by the code's design.

## Search runs (`runs5/`)

Composer:
- `ce2-world{2,13,16}.txt`: complete at 512, 41,472 and 41,472 timelines; 5,000 seeds each; none.
- `ce5-world14.txt`: complete at 5; 2,000 seeds; none.
- `ce5-world12.txt`: 5,000 timelines (the swarm, stopped) and 2,000 seeds; none.
- `ce1-world4.txt`: complete at 1,394; 5,000 seeds; none.
- `stop-world17.txt`: found after 4 timelines (CE42).
- `drawn-{2,12,13}.txt`: 5,000 drawn scenarios each, the Zig's constants; none.

Other areas:
- `junit.txt`: 4 worlds; the new one found (CE41), the others complete (up to 961).
- `persist.txt`: no hole: 1,000,000 timelines and 284,650 complete. Ascending: found in non-fresh files.
- `verdicts.txt`: 6 properties over 10 worlds, all complete (up to 29,282 timelines): none.
- `tape.txt`: 4 properties over 11 worlds. Found: the reason table (CE48) and CE13's last interval. The full-tape property holds in three worlds (one complete at 65,536, two exhausted to 1,000,000).
- `ci.txt`: round 3's 4 properties over 6 worlds and the per-timeline count over 3: none. The gate is found (CE38). The merge is found (CE40), plus GNU-size lines.
- `durable.txt`: the durability property, 3 worlds complete (up to 446,792) plus 100,000 seeds; its census 0 of 100,000. The disk properties as in round 4.
- `resume.txt`: 4 worlds. Found: CE45, CE46, and CE29 at 3939448.
- `clock.txt`: 3 worlds × 1,000,000 seeds, with a census.
- `disk.txt`: 2 properties × 3 depths, exhausted and 100,000 seeds: found (CE43).
- `ce40-zig.txt`, `ce41-zig.txt`, `ce48-zig.txt`: the Zig tests run on copies of 62e06e3's files.

## Theorems (29, `Replica/Theorems5.lean`)

General:
- `plain_parts`
- `ce21_plain_keeps_every_run`: for every list of xargs runs, a run line that falls through judges every name.
- `leaving_parts`
- `ce40_leaving_keeps_only_the_last`: for every list of runs, `exit`, `exec` or a comment leaves only the last run's names.

The recheck, by computation (62e06e3 passes round 2 to 4's minimal cases):
- `ce2_own_sigkill_judged`
- `ce5_slot_wait_stops`
- `ce15_thirty_minute_bands`
- `ce16_captured_error_passes`
- `ce17_fresh_file_from_its_first_range`
- `ce18_ce22_catalog_by_kind`
- `ce19_adopted_reads_exit`
- `ce20_full_tape_stops_its_replay`
- `ce21_plain_run_line_judges_every_run`
- `ce27_hang_is_flaky`
- `ce28_session_left_out`
- `ce29_recorded_failure_counts`
- `ce35_two_arms`
- `ce37_unreported_counted`

New counterexamples, by computation:
- `ce40_exit_run_line_keeps_the_last_run`
- `ce40_set_e_drops_the_failing_run`
- `ce41_closing_tag_fails_a_passing_test`
- `ce42_second_phase_starts_past_half`
- `ce43_read_before_the_heal_unnamed`
- `ce44_second_phase_past_the_hour`
- `ce44_ending_past_the_hour`
- `ce45_complete_resume_skips_the_catalog`
- `ce46_failure_past_the_room`
- `ce47_adopted_resume_reads_its_record`
- `ce48_reasons_past_the_table`

Rounds 2 to 4's theorems about fixed code now state `.v3939448` (Theorems2: 6, Theorems3: 2, Theorems4: 3), and all build.

## Library gaps

- A model of two versions needs a version threaded through each changed function. The library has no notion of a "model variant" to search both against one property.
- Proofs about `for` loops in `Id.run` need the loop rewritten as `List.foldl` first (done for `Ci5.judged`). A `forIn`-to-`foldl` simp set would help.
- `simp` does not reduce a derived `BEq`'s `a == a` on an enum; `=` with `DecidableEq` had to replace it in proved code.
- A census over seeds was again written by hand (`Clock5.census`).
- Shell, tracefs and resume-record models were built by hand.

## Left for round 6

- Run CE40 to CE48 on the platform. CE40, CE41 and CE48 already fail against copies of 62e06e3's files.
- Still open from earlier rounds: CE23 to CE26, CE30, CE32 to CE34, CE38, CE39.
- Full tapes and the tree: returns past a marker, disk holders at exact moments, chains through a full parent.
- corrupt_reads: the 4,096-event cap, readahead across aimed extents, and a fault aimed at a file whose extents move.
- The resume: CE45 with sessions; record lines dropped whole past 128 KiB (deep tree paths plus properties).
- CI: the `{shard}` mode with `junit` and xargs-free runners; `explored_timeline_events` against resumed and rerun timelines.
