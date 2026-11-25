# determinismo in Lean: round 2

## What this is

This is round 2 of the Lean 4 (v4.36.0) replica of determinismo, now built against platform commit 3939448 (`upstream/`). Round 1's copy at 0dea225 is `upstream-0dea225/`. The replica is written function by function from the Zig, with file and lines for each. It is searched against what the docs, the skills and the code's own comments promise. The SDK is `upstream/sdk/lean`, a path dependency.

Files:
- Round 1's modules, updated to 3939448: `Replica/Composer.lean`, `ComposerProps.lean`, `ComposerSearch.lean`, `Faults.lean`, `Verdicts.lean` (now also covers serve's adoption of a run), `Tape.lean`, `Theorems.lean`.
- New modules:
  - `Replica/Clock.lean`: the timeline's wall clock start.
  - `Replica/Junit.lean`: JUnit cases, det-assert, xargs and `tests_judge`.
  - `Replica/Persist.lean`: partial persistence.
  - `Replica/Theorems2.lean`: round 2's theorems.
- Two executables: `Main.lean` builds `replica` (round 1's searches) and `Main2.lean` builds `replica2` (the new areas).
- `tests/`: the regression tests: `ce02_composer_own_sigkill.zig`, `ce05_composer_slot_wait.zig`, and `ce15_` to `ce22_*.zig`.
- `runs2/`: every round 2 search's output. Round 1's outputs stay in `runs/`.
- `scratch/round2-ce1-14.sh`, `scratch/round2-new.sh`, `scratch/round2-after.sh`: the scripts that ran the searches.

Commands:

    lake build
    .lake/build/bin/replica composer <exhaust> <seeds> <drawn-seeds> [<property>]
    .lake/build/bin/replica cworld <property> <world> <exhaust> <seeds> <first-seed>
    .lake/build/bin/replica cdrawn <property> <seeds> <first-seed>
    .lake/build/bin/replica faults <exhaust> <seeds>
    .lake/build/bin/replica verdicts <exhaust>
    .lake/build/bin/replica tape <exhaust>
    .lake/build/bin/replica2 clock <exhaust> <seeds>
    .lake/build/bin/replica2 junit <exhaust>
    .lake/build/bin/replica2 persist <exhaust>

## The SDK at 3939448

The lakefile already pointed at `upstream/sdk/lean`. With the new copy there, nothing broke: the whole replica built unchanged against it (67 jobs) before any round 2 edit.

What changed in the SDK:
- `decide` now draws uniformly without building a weights list (`Decisions.nextOf`, Decide.lean 145-151). It draws the same values `Replica.below` does, so `below` stays and round 1's tapes keep their meaning.
- New: `Bounds` (depth and per-name caps), `Census` (counts per property, resumable segments, a time budget, iterative deepening, Knuth's size estimate), `permutation`, `subset`, `composition`, and a shrink that also drops chunks from the middle of a path.
- Round 1's library gaps about bounded search, progress and counts are closed by this.
- Round 2 still uses `exhaust`/`explore` so both rounds' outputs read alike. The new shrink is used throughout.

## Round 1's counterexamples at 3939448

Each fixed counterexample's round 1 decisions now give a passing timeline. This is proven by computation in `Replica/Theorems.lean` under the names below. All of round 1's searches were run again (`runs2/`).

### CE1 — fixed

- `guest/runtime/composer.zig:534-539`: the length's kill saves `composer.interrupted` before `kill_all` and restores it after. The `if (bounded)` reset is gone.
- `composer.zig:331-340`: a command reaped by `kill_all` counts as the composer's kill only when SIGKILL ended it.
- The selftest's new `ending_signal` scenario covers it.
- Theorem `finally_after_a_signal_fixed`.
- Search: "a finally only after every command completed, the length's kills aside" holds in every world, exhausted and over 2,000 seeds, and in 5,500 drawn scenarios.
- Remainder (a one-poll race, not reached in the replica): a SIGKILL death after `wait_until`'s last reap and before `kill_all` is counted as the length's kill.

### CE2 — fixed for exit codes; still there for SIGKILL

- `composer.zig:335-340` (`by_kill`): round 1's case, a start exiting 1, is now judged. Theorem `failing_exit_judged`.
- Still there: with `--min-drive 0`, `min_drive` returns at once (853-856), so nothing reaps the starts before `kill_all` (401-407).
- A start that died of its own SIGKILL (the OOM killer, a kill from outside the composer) is then reaped with `killed = true`. It is reported killed: no "test commands exit successfully" false, no "completed".
- Found in small world 16, exhausted and explored (`runs2/ce2-world16.txt`). drive#3 dies of its own SIGKILL at 2 ms and is reaped by the eventually ending's `kill_all` at 3 ms as killed. Theorem `own_sigkill_reported_killed`.
- With any `min_drive`, `wait_until` would have reaped it first and judged it 137.
- Regression: `tests/ce02_composer_own_sigkill.zig` (a selftest scenario, its assertion, the explore command).

### CE3 — fixed

- `composer.zig:223-235`: a workload counts as marked only among the swarm's commands.
- `rescue_counts` (686-692, its test 693-705) counts the marked commands, else the drivers, else the anytime commands.
- Theorems `singleton_marked_goes_on` and `five_anytime_go_on`.
- General theorem `rescue_counts_only_swarm_commands`: the rescue never counts a singleton, a first or an ending.
- Search: "never panics" and "keeps one marked driver among its commands" hold everywhere.
- A marked singleton now simply isn't a swarm command. The skill says a singleton is not for running beside nemeses, so no promise breaks.

### CE4 — fixed for serial drivers and `--timeline`; a drawn length still doesn't bound a singleton

- `composer.zig:413-419` (`run_alone_until`) and 881 bound a serial driver. Theorem `serial_bounded_by_the_length`.
- `run_singleton` (715-737) returns the length's end under `--timeline`.
- Still there:
  - With `drive_ms_max` (or `--drive-max`, 20 minutes by default) and no `--timeline`, a singleton timeline draws no length.
  - Its singleton runs to its end: 712-714 says "a drawn length doesn't, a singleton running alone to its end by design".
  - `sdk/zig/schema.zig:643-648` says `drive_ms_max` makes "a timeline's length no longer follows how slow its commands are".
- New property 15 fails:
  - in world 15 (a 60 ms `drive_ms_max`, a 200 ms singleton): theorem `singleton_past_drive_max`;
  - in drawn scenarios (`runs2/drawn-14.txt`): `drive_ms_max` 30 s, a 100 s singleton.
- This is a documentation mismatch.

### CE5 — half fixed: quiet stretches stop, slot waits don't

- `composer.zig:792-803`: the stop is checked after quiet stretches. Theorem `quiet_stretches_stop_at_half_the_limit`.
- Still there: the stop is checked before `driver_start` (849-851). `driver_start_by` (875-890) then waits for a slot with no deadline: `wait_below(parallelism, maxInt)` reaps with hang, and a serial driver uses `wait_below(1, maxInt)`. It then starts the command, whatever the time.
- Drawn-scenario case (`runs2/composer-13.txt`, `drawn-13.txt`): parallel_max 1, a 600 s limit (so the stop is at 300 s). A 400 s start holds the only slot. The next start begins at 400,010 ms, and only then is `drivers_stopped` logged.
- World 14: theorem `slot_wait_past_half_the_limit`.
- This is the pattern the comment at 786-790 names (Redpanda's run 177 hangs).
- Regression: `tests/ce05_composer_slot_wait.zig`.

### CE6 — fixed

- `guest/runtime/faults.zig:1484-1489`, with its test at 5076-5106.
- Theorem `excluded_node_unlisted`.
- Search: "an excluded node is in no drawn fault" holds: worlds exhausted to 100,000 timelines (one complete at 92,224) and 5,000 seeds.

### CE7 — fixed

- `faults.zig:3095-3109`, `outage_down_already` 2122-2132 with its test.
- Search: both caps (the literal one and the one counting recovering nodes) hold.

### CE8 — the docs changed to match the code

- The code is unchanged: `faults.zig:392` checks quiet periods for drawn faults only, and `inject` applies at once.
- `docs/ANTITHESIS.md:60-61` and `docs/AGENTS.md:394-395` now say an injected fault starts in a quiet period and on a node the exclusions leave out.
- The strict properties still fail; the documented ones (drawn faults only) hold.

### CE9 — fixed in the explorer; the catalog keeps the first kind

- `src/core/events.zig:56-61` `Property.same`; `src/report.zig:520-523` `aggregate_find`; test 882-894.
- Theorem `verdict_same_in_either_order`.
- The catalog across scenarios (`report.zig:125-138`) is still keyed by message alone, with the first kind noted. This gives CE18 and CE22.

### CE10 — fixed

- `report.zig:367-371` `unmet_here`, 389-396 `failing_violations`, 399-407 `sometimes_unmet`, 142-145 `made_true`; `src/main.zig:1106-1156`.
- Theorem `sometimes_across_scenarios_fixed`. The fix brings CE18.

### CE11 — fixed

- `events.zig:1483-1501`: a cut message keeps the whole message's hash.
- `identity` (49-54) and `same` use it; test 1882-1897.
- Theorem `long_messages_apart`. Wyhash collisions are not modeled.

### CE12 — fixed

- `src/core/vm.zig:3691-3694` (fork) and 3805-3806 (serve).
- Search: "a replay has its recorded history" holds in the fork and serve worlds (65,536 timelines each, complete).

### CE13 — fixed

- `src/core/tape.zig:223-233`; tests 1006-1027.
- Theorems `check_below_waits` and `check_past_stops`, for every input.
- Remainder: a replay that parts within its tape's last checkpoint interval is never stopped by a checkpoint. The search shows it (a 10-event replay parting at event 8, with a checkpoint every 4 events).
- The run's verification replays catch it by the final events hash (`src/replays.zig`), but not where it parted.

### CE14 — fixed

- `tape.zig:593-608`; test 641-660.
- Theorem `thinning_no_longer_overflows`.

### Round 1's notes

- An anytime command started beside the singleton (`composer.zig:720-726`) is unchanged, and the searches still find it.
- `schema.zig:647` still says "4 to 63" starts. With the swarm on, `starts_draw` gives 2 to 63 (`composer.zig:749-753`).

## New counterexamples

### CE15: a timeline's wall clock start reaches what the setup made to expire

**Property.** `guest/runtime/composer.zig:900-901` (`clock_start_draw`'s comment): "Never back, and not past what a setup made to expire (a token's hour, a lease): a timeline failing on the jump would be no workload's failure". The default cap is an hour (903; `main.zig:91-93`).

**Minimal cases** (`runs2/clock.txt`):
- An 8 s cap and an 8 s credential, exhausted: band 3 jumps 8,000 ms, and the first use lands at the expiry.
- The default hour and a token's hour: found at seed 676. The jump is 3,587,530 ms and the token was issued 30 s before the draw, so the first use is 17.5 s past expiry.
- A 60 s lease from the setup: broken by the first seed (a jump of 128 s).

**Why.**
- `clock_start_band(max, last).high == max` for every cap of a second or more. Proven for all caps as `last_band_reaches_the_cap`, and for the hour as `hour_bands`.
- The time between the credential's issue and the draw comes on top.
- A token used throughout a 20-minute drive expires in about 1/12 × 1,200/1,552 ≈ 6% of timelines. None of them would expire it without the jump.

**Zig path.** `composer.zig:903`, 905-927 (`clock_start_draw`), 929-932 (`clock_start_bands`), 934-937 (`clock_start_band`).

**Regression test.** `tests/ce15_composer_clock_start.zig`. It goes beside `test clock_start_bands` in `guest/runtime/composer.zig`: test "a timeline's drawn wall clock start never reaches what a setup made to expire". It fails on band 11.

### CE16: a passing test whose captured output mentions an error element is judged failing

**Property.** `guest/runtime/junit.zig:2-6`: a test case fails by "whether it holds a `<failure>` or an `<error>` (skipped ones pass)". docs/CI.md, Verdicts per test.

**Minimal case** (`runs2/junit.txt`, 3 decisions):

    <testcase classname="tests.test_app" name="test_1" time="0.1"><system-out><![CDATA[<error code="503"/>]]></system-out></testcase>

- `det-assert junit` states `always(false) "test passes: tests.test_app::test_1"` in every timeline. The job's verdict is "fail", exit 1.
- The same output escaped (as pytest writes it) passes: theorem `escaped_output_passes`. In CDATA (Surefire, jest-junit, go-junit-report) it fails: theorem `captured_error_fails_the_test`.

**Zig path.** `junit.zig:32` searches the whole body for `<failure` or `<error`, `system-out`/`system-err` included; `assert_main.zig:43-51`.

**Regression test.** `tests/ce16_junit_captured_output.zig`, beside `junit.zig`'s tests (after line 149): test "a test case's captured output never fails it".

### CE17: a fresh file keeps a later range of new data and loses an earlier one

**Property.** docs/ANTITHESIS.md:53: "its new data ... as an ascending run from the start of one of its new ranges, as the flusher writes it (no hole before a kept page of a fresh file)". `guest/runtime/nodes.zig:761-765`: "never a page before an earlier one of a fresh file".

**Minimal case** (`runs2/persist.txt`; theorem `fresh_file_hole_before_kept`):
- A fresh sparse file: new, hole, new.
- The run starts at drawn range 1, so page 2 is written back and page 0 is not.
- With the journal committed, page 2 is kept and page 0 reads zeros under the file's size.
- With more pages left, the run wraps to range 0 after range 1, so "new data is written back as an ascending run" fails too.

**Zig path.**
- `nodes.zig:841-873` (`unallocated_of`) joins ranges only when adjacent.
- 942-953: `var range = random.uintLessThan(u32, unallocated.ranges)` and the wrap.
- On a host, a fresh file's first writeback starts at its first page.
- The selftest's 30 fresh files are one range each, so it can't see this.

**Regression test.** `tests/ce17_partial_fresh_file.zig`, beside "partial persistence draws the same files and pages from the same seed, nested ones too" (after `nodes.zig:1382`).
- Test: "a fresh file's new data is written back from its first range".
- Pages 0 and 4 written, `partial_file` run over 64 seeds, FIEMAP read after each.
- It must never find page 4 written back while page 0 is not.

### CE18: a sometimes never true passes when its message is reached under another kind

**Property.** ANTITHESIS.md (Judged as Antithesis does). `events.zig:56-61` (CE9's fix: "a message with two kinds in two timelines is two properties, each judged as its kind"). The workload skill: "one never true fails the run".

**Minimal case** (`runs2/verdicts.txt`, 3 decisions; theorem `sometimes_hidden_by_another_kind`):
- One scenario. One timeline evaluates `sometimes(false, "m")`, the other `always(true, "m")`.
- The explorer exits 0. Serve lists the sometimes as failing, and the docs fail it.
- A `reachable` or an `always_or_unreachable` reached under the same message hides it too, in the same scenario or another one.

**Zig path.**
- `report.zig:389-407`: the unmet sometimes is left out of `failing_violations`, and its identity goes to `sometimes_unmet`.
- `catalog_reached` (752-765) and `Catalog.note` (131-138) OR `reached` under one identity, whatever the kind.
- `main.zig:1150-1155` then passes it because `made_true` (142-145) is true.

**How likely.** Same as CE9. Literal call sites are catalogued at startup, and two kinds fail there. This needs messages computed at run time.

**Regression test.** `tests/ce18_sometimes_other_kind.zig`, beside "one message with two kinds is two properties, whichever timeline came first" (after `report.zig:894`).

### CE19: a run adopted across a serve restart ends "passed" when its explorer failed it

**Property.**
- docs/AGENTS.md: "A restarted `serve` adopts the runs still going".
- `main.zig:1166-1170`: the `exit` file exists because serve judged adopted runs "from their timelines' failing always properties alone".
- `serve.zig:5912`: "A failing property fails the run, as explore exits".

**Minimal case** (`runs2/verdicts.txt`, 2 decisions; theorem `adopted_run_reads_passed`):
- One timeline declares `reachable "m"` and never reaches it. The explorer exits 3 and writes `3 exited with status 3`.
- If serve reaped the run itself: "failed".
- If serve was restarted during the run and adopted it: "passed".
- At the next serve start, `runs_discover` reads `exit` and the run turns "failed".
- The opposite also happens. With CE18's timelines the explorer exits 0, but the summary line says `"failing":true`: reaped "passed", adopted "failed".

**Zig path.**
- `serve.zig:5983` (`runs_reap`, adopted branch) and 5821 (`runs_adopt`) both take `recorded_status(record)`. Only `runs_discover` (5757-5762) reads `exit`.
- `recorded_status` (5904-5918) uses the summary's `"failing":true` lines.
- That flag is `aggregate.failing()` (`report.zig:830`), which is false for an assertion the scenario never reached. The catalog judges those across scenarios (`main.zig:1157-1164`).

**How likely.** High. Any catalogued `sometimes`, `reachable` or `always` that no timeline reaches will do, for example "test command started: X" for a command never started, on any run that is running while serve is redeployed.

**Regression test.** `tests/ce19_serve_adopted_status.zig`, beside `recorded_status` (after `serve.zig:5918`).
- Unit test "an adopted run's status is its explorer's, a catalog's failure included".
- Plus an e2e: restart serve during a run, then compare `GET /runs/<id>` with the `exit` file.

### CE20: a timeline with more than 65,536 overrides is recorded whole and never replays

**Property.** README_AI.md: "replay any timeline exactly", "every timeline replays bit-identically". `vm.zig:3729-3731`: "a replay's history is the run's".

**Minimal case** (`runs2/tape.txt`, a table of 4; theorem `polls_past_the_table`). Five ingress polls are recorded, each answer on the tape. The replay's parse refuses the fifth with `TapeTooLong`. Strategy reasons past a table of 2 fail the same way; the Zig's table holds 1,024.

**At the Zig's size.**
- `tape.zig:98-103`: a session relaying connections polls 84 times a virtual second, each answer on the tape. 65,536 overrides is 13 virtual minutes.
- Egress and ingress replies take one override per 64 bytes (`sdk/zig/determinismo.zig:282-290`), so 4 MiB fills the table.
- `sdk.serve` replies of 16 KiB fill it in 256 calls.
- A tree's return to such a timeline is dropped (`main.zig:7697-7712`).

**Zig path.** `tape.zig:8` (`override_count_max`), 117 (`reason_count_max`), 554-556 and 565-567. The recording side has no bound (`vm.zig:3730`, 3766, 3803, 3831).

**Regression test.** `tests/ce20_tape_override_table.zig`, beside "a relayed session's polls, thousands of ingress answers, parse: their reason is their kind" (after `tape.zig:844`). It parses 70,560 polls.

### CE21: determinismo-ci judges only the last xargs batch of a shard's tests

**Property.** docs/CI.md (`junit`): "each test gets its own verdict across its shard's timelines". (`run`): "`{tests}` (the shard's names, as arguments ...)".

**Minimal case** (`runs2/junit.txt`; theorem `xargs_loses_the_first_batch`):
- Two names past a 48-byte buffer: two runner runs, and only the second test is judged.
- At GNU's real default (131,072 bytes), 2,000 names of 80 bytes make two runs; the first run's 1,617 tests get no verdict.
- The job still fails when one of those fails (xargs exits 123), but the per-test lines say "0 failing".

**Zig path.** `src/products/ci.zig:221-233` builds the shard command, and 236-245 reads the report once at the end.

**Regression test.** `tests/ce21_ci_xargs_batches.zig`, beside "a shard's verdict line read" (after `ci.zig:524`). It runs ci.zig's pipeline over 3,000 names and checks the report covers them all.

### CE22: the catalog's verdict depends on the order its kinds were noted

**Property.**
- ARCHITECTURE.md M9: "parallel = sequential".
- README_AI.md: "--jobs, same timelines as one worker".
- `report.zig:546`: "the summary does not depend on which worker finished first".
- CE9's fix: two kinds are two properties.

**Minimal case** (`runs2/verdicts.txt` and `verdicts-after.txt`; theorem `catalog_kind_order`):
- One timeline declares `reachable "m"`, another `always_or_unreachable "m"`, and neither is reached.
- If the reachable's timeline ended first: exit 3. If the other ended first: exit 0. The docs fail the reachable.

**Zig path.** `report.zig:131-138` keeps an identity's first kind; `judge` (149-170) uses that kind; the notes are made in merge order (752-765).

**How likely.** Low, as for CE18.

**Regression test.** `tests/ce22_catalog_kind_order.zig`, beside `test Catalog` (after `report.zig:189`).

## Other findings (not counterexamples)

- **CI's missing-report count.** `ci.zig:446-470` counts "timelines without their JUnit report" from the most any test was hit in, across every shard. One shard's missing report is hidden by another shard that reported everywhere (theorem `missing_report_hidden_by_another_shard`). The shard's own property still fails the job.
- **No clock start in CI timelines.** CI runs hold the scenario (`serve.zig:2817-2830` `--hold-scenario`; `main.zig:1665`), so there is no composer and no clock start. Every timeline of a job reads the same wall time, which is the very thing the clock start was added to avoid (composer.zig:895-898).
- **JUnit attributes.** They are found by `" name=\""`. An indented line break passes (searched). An unescaped `>` inside an attribute, which is legal XML, cuts the tag and drops the case (not searched).
- **The explorer's tree.** `returns_earlier` (`main.zig:6893-6925`), `objective_place` (7047-7055) and `archive_returns` (7081-7123) were read but not replicated.

## What was replicated, and what is not exact

3939448's changes are replicated, each marked with its lines:
- composer: `rescue_counts`, `by_kill`, `run_alone_until`, the singleton's length, the stop after quiet stretches, the length's kill keeping earlier interruptions, and the clock start's draws (only under `irrelevantDraws`);
- faults: the excluded peer in `links_collect`, `outage_down_already`;
- verdicts: `Property.same`, message hashes, `unmet_here` / `failing_violations` / `sometimes_unmet` / `made_true`;
- tape: fork and serve events, the new `check`, the thinning loop.

New:
- serve's `recorded_status`;
- `clock_start_draw` and its bands;
- `junit.zig`'s `cases`/`attribute`/`unescape`, `det-assert junit`, GNU xargs batching, `tests_judge`'s count;
- `partial_file` and `unallocated_of`;
- the tape's two table sizes.

Not exact:
- Persistence: a file is a list of page states. The 64-extent FIEMAP cap is not modeled. The generator's draws are named `partial.*` decisions here (in the Zig, one platform decision seeds a generator). Syncing a hole or a clean page writes nothing.
- Clock: the credential and the time from its issue to the draw are world decisions. Time namespaces are not modeled.
- JUnit: text search as `std.mem` does it; messages not modeled; xargs per GNU's rule, ignoring the environment's size.
- Serve: only a run's status.
- As in round 1: processes are world decisions, time is in ms, and small worlds use small constants.

## Assumptions

- Where the docs say nothing, a code comment states the promise (CE5, CE15, CE17's in nodes.zig).
- A setup credential is valid until a wall time fixed at the setup.
- Serve's "passed"/"failed" is its verdict on the run.
- JUnit producers write a case's captured output in `system-out`/`system-err`, either in CDATA or escaped.
- GNU xargs's default buffer is 131,072 bytes.
- Round 1's assumptions still hold.

## Properties, with sources (38)

**Composer (15).**
1. One ending command per timeline (skill): holds.
2. An eventually runs with every other command ended: holds.
3. A finally only after every command completed, the length's kills aside: holds (CE1 fixed).
4. The same, strict: fails by design (the length's kills).
5. A singleton alone among parallel and serial drivers: holds.
6. A singleton alone, anytime counted: fails (round 1's note).
7. A serial driver alone: holds.
8. parallel_max respected: fails only through note 6.
9. Faults in the driver phase only: holds.
10. The swarm keeps a marked driver: holds.
11. No panic on a valid scenario: holds.
12. A timeline's length bounds the drivers: holds.
13. Own exits are judged: fails (CE2's remainder).
14. No start past half the limit: fails (CE5).
15. With drive_ms_max, no driver past its longest length and grace (schema.zig:643-648): fails (CE4's remainder, by design).

**Fault injector (7).**
1. Exclusions, strict (0dea225's docs, no longer promised): fails through injected faults.
2. Exclusions for drawn faults: holds.
3. The literal nodes-down cap: holds.
4. The nodes-down cap with recovering nodes counted: holds.
5. Quiet periods, strict (no longer promised): fails through injected faults.
6. Quiet periods for drawn faults: holds.
7. Nothing lasts past the stop: holds.

**Verdicts and serve (6).**
1. Order independence: fails (CE22).
2. The explorer as documented: fails (CE18, CE22).
3. Serve as documented: holds.
4. The explorer agrees with serve: fails (CE18, CE22).
5. Events are not properties: holds (theorem).
6. A run's state is the same reaped or adopted: fails (CE19).

**Tape (3).**
1. A replay has the recorded history: fails (CE20).
2. The n-th pull gets the n-th answer: holds.
3. A replay stops where it diverges: holds, except within the tape's last interval.

**Clock (2).**
1. Not past what the setup made to expire: fails (CE15).
2. One second to the cap, never back: holds.

**CI (3).**
1. Failure or error decides a test's verdict: fails (CE16).
2. Every test case is a test: holds.
3. Every test of a shard is judged: fails (CE21).

**Persistence (2).**
1. No hole before a kept page of a fresh file: fails (CE17).
2. New data written back as an ascending run: fails (CE17).

## Search runs (`runs2/`)

- **Composer.** 15 properties over 17 worlds:
  - worlds without the swarm exhausted to the end (4 to 9,728 timelines);
  - worlds with the swarm exhausted to 5,000 timelines (their trees have no end) and explored over 2,000 seeds;
  - drawn scenarios with the Zig's constants over seeds 0–5,499.
  - The 5,000-seed drawn run for property 13 was stopped after 8 minutes without output (most likely its shrink). World 16 covers that property.
- **Faults.** 7 properties over 6 worlds, exhausted to 100,000 timelines (one world complete at 92,224), plus 5,000 seeds.
- **Verdicts.** 6 properties over 10 worlds, all complete (up to 29,282 timelines). Rerun after fixing the order property to treat an error in either order as the same outcome.
- **Tape.** 3 properties over 9 worlds: complete up to 65,536 timelines, three stopped at 1,000,000.
- **Clock.** The 8 s worlds exhausted (21,003 timelines each); the hour explored over 20,000 seeds.
- **JUnit and CI.** Every world complete.
- **Persistence.** Exhausted.

Every counterexample was shrunk; its tape and story are in these files.

## Theorems (35)

`Replica/Theorems.lean` (21):
- General: `foldlM_drops_events`, `events_are_not_properties`, `check_below_waits`, `check_past_stops`, `rescue_keeps_one`, `rescue_counts_only_swarm_commands`, `literal_le_counted`.
- By computation: `rescue_keeps_the_rest`, `singleton_marked_goes_on`, `excluded_node_unlisted`, `verdict_same_in_either_order`, `sometimes_across_scenarios_fixed`, `long_messages_apart`, `thinning_no_longer_overflows`, `thinning_usual`, `finally_after_a_signal_fixed`, `serial_bounded_by_the_length`, `quiet_stretches_stop_at_half_the_limit`, `anytime_beside_the_singleton`, `five_anytime_go_on`, `failing_exit_judged`.

`Replica/Theorems2.lean` (14):
- General: `last_band_reaches_the_cap`.
- By computation: `hour_bands`, `captured_error_fails_the_test`, `escaped_output_passes`, `xargs_loses_the_first_batch`, `fresh_file_hole_before_kept`, `sometimes_hidden_by_another_kind`, `catalog_kind_order`, `adopted_run_reads_passed`, `polls_past_the_table`, `own_sigkill_reported_killed`, `slot_wait_past_half_the_limit`, `singleton_past_drive_max`, `missing_report_hidden_by_another_shard`.

## Library gaps

The SDK closed round 1's search gaps. Still built here:
- models of processes, file extents, tape tables and serve;
- text search from a position (Lean's `String` has no `indexOfPos`);
- per-property counts in `exhaust` (`census` has them; not used, to keep round 1's output format);
- `native_decide` for concrete counterexamples, and `DecidableEq` (or `==` with `BEq`) for statements about structures.

## Left for round 3

- **The explorer's tree:** `tree_returns`, `archive_add`/`archive_returns` (objectives' best places), `returns_earlier`, `memory_forget`, generation shapes with a strategy's `branches`/`fill`, and the plugin protocol's promises.
- **CI end to end:** missing reports, the shard SQL, and a hung CI timeline reported as "error".
- **Serve:** `properties_sql` with sessions, the coverage gate, resume.
- **Disk faults:** `disk` (dm-flakey, lost writes), `sync_stall`, `durable_crash`, `writeback_s`.
- **Clock skew and skips:** against the clock start's `clock_settime`.
- **CE2's remainder** in drawn worlds made for it.