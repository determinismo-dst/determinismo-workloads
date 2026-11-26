# determinismo in Lean: round 6

## What this is

Round 6 of the Lean 4 (v4.36.0) replica of determinismo. The platform's next branch is now a7fe05d, a plain copy in `upstream-a7fe05d/` (its commit in `.commit`). Round 5's baseline, 62e06e3, stays in `upstream-62e06e3/`, so verdicts cite both as `62e06e3 → a7fe05d`. The models now follow a7fe05d by default. `Ver` (`Replica/Prelude.lean`) gained `.va7fe05d`, with `Ver.since62` and `Ver.sinceA7`. Theorems about older code pass `.v62e06e3` or `.v3939448` explicitly. The SDK is still the one at `upstream/sdk/lean`.

Changed models (each change threads the version):
- `Composer.lean`: `run_drivers` takes the drivers' start, and every phase stops at half the limit from it (CE42).
- `Junit.lean`: `captured_end` (CE41's fix); a new property, "the tests judged are the report's test cases"; a world whose captured output prints test cases.
- `Ci5.lean`: the run line in its own subshell (CE40's fix); a runner's exit 255 stops xargs (`xargsRuns`).
- `Tape.lean`: the reason table sized from the tape (CE48's fix).
- `Disk5.lean`: the heal's drain, with its marker, 2 s waits, kill, `rmdir` and the next start's clear (CE43's fix). New: the "or said" property, and a world where `pidfd_open` may fail.
- `Resume5.lean`: no room in record lines (CE46's fix); `runs_adopt` keeps the resume's own `exit` (CE47's fix); a session's timeline holding one of the run's numbers.
- `Serve3.lean`: the coverage gate's `setup_covered` and `explored` (CE30's fix); runs that start from a snapshot.
- `Ci4.lean`: CI jobs are exempt from the gate (CE38's fix).
- `Steer4.lean`: every ended timeline is counted (CE39's fix).
- `TreeRun.lean`: `plan_adopt_ran` (CE23's fix).

New files:
- `Replica/Request6.lean`: a run's recorded request and machine against the inputs its analyses boot.
- `Replica/Tape6.lean`: a session's steps on its tape, and returns into a full tape.
- `Replica/Aimed6.lean`: the byte an aimed corrupt_reads names.
- `Replica/Theorems6.lean`: 27 theorems.
- `Main6.lean`: the `replica6` executable.
- `tests/ce49_*.zig` to `tests/ce55_*.zig`: the regression tests.
- `runs6/`: the searches and the Zig runs.
- `scratch/round6.sh`: the searches.
- `scratch/zig6/`: copies of a7fe05d's `ci.zig`, `junit.zig` and `tape.zig`, with round 6's tests appended.

Commands:

    lake build
    .lake/build/bin/replica6 composer|cworld|cdrawn ...
    .lake/build/bin/replica6 junit|persist|verdicts|tape|resume|serve|request|tape6 <exhaust>
    .lake/build/bin/replica6 ci|durable|disk|tree|steer|aimed <exhaust> <seeds>
    .lake/build/bin/replica6 clock|treecensus <seeds>

## The recheck of CE1 to CE48 at a7fe05d

"Searched" means the round 2 to 5 searches were rerun on a7fe05d's model; the output is in `runs6/`. A theorem named here runs the old minimal case on a7fe05d's code. Theorems that call a model without a version run its default, which is now a7fe05d, and all of them build. Theorems in `Theorems5` about 62e06e3 are pinned to `.v62e06e3`.

### Composer, faults, verdicts (CE1 to CE15)

- **CE1** (a finally after a signal): **fixed**. composer.zig 541-547 → 545-551 (reap's `by_kill` 331-337 → 334-341). Searched: world 4 is complete at 1,394; 5,000 drawn. Theorem `finally_after_a_signal_fixed` (Theorems).
- **CE2** (an exit hidden as killed): **fixed**. composer.zig 401-412 → 405-416. a7fe05d adds `composer_kills` and the upstream test "kill_all judges a start that died of its own SIGKILL". Searched: worlds 2, 13 and 16 are complete (512, 41,472 and 41,472 timelines); 5,000 drawn. Theorems `ce2_own_sigkill_judged` (Theorems5) and `failing_exit_judged` (Theorems).
- **CE3** (workload marking keeps no driver): **fixed**, unchanged. composer.zig 221-283 → 224-286; 693-699 → 697-703. Theorems `singleton_marked_goes_on` and `five_anytime_go_on`.
- **CE4** (the length doesn't bound singleton drivers): **partly fixed**, unchanged. The remainder is by design. composer.zig 718-721 → 722-725. Theorems `serial_bounded_by_the_length` (fixed part) and `singleton_past_drive_max` (Theorems2: still true).
- **CE5** (a driver starts past half the limit): **fixed**. composer.zig 799-808 → 806-815 and 809-813 → 816-820. Searched: world 14 is complete (5); world 12 stopped at 5,000 with none found. Theorems `quiet_stretches_stop_at_half_the_limit` and `ce5_slot_wait_stops`.
- **CE6, CE7** (fault exclusions, an outage's recovery window): **fixed**. faults.zig is identical. Theorem `excluded_node_unlisted` (CE6).
- **CE8** (injected faults in quiet periods): **fixed in the docs**. Unchanged.
- **CE9, CE10, CE11** (verdict order, scenarios, 192-byte messages): **fixed**. events.zig is identical; report.zig 610 → 642 and 417-456 → 457-496; main.zig 1151-1156 → 1154-1159. Searched: verdicts, 6 properties × 10 worlds, all complete. Theorems `verdict_same_in_either_order`, `sometimes_across_scenarios_fixed` and `long_messages_apart`.
- **CE12** (replays lose fork events): **fixed**. vm.zig is unchanged for this. Searched (tape).
- **CE13** (a passed-over checkpoint): **fixed, with round 2's remainder still there**. tape.zig 265-277 → 276-288. Searched: the last-interval case was found again in `runs6/tape.txt` ("replays perturbed": the replay ran to its end past the checkpoint at 8). The general theorems `check_below_waits` and `check_past_stops` still hold.
- **CE14** (thinning overflows the table): **fixed**. tape.zig 666-683 → 678-695. Theorem `thinning_no_longer_overflows`.
- **CE15** (the wall clock's jump): **partly fixed**, unchanged. composer.zig 913-914 → 924-925. Theorem `ce15_thirty_minute_bands`. The remainder is CE44.

### CI, JUnit, persistence, verdicts, tapes (CE16 to CE22)

- **CE16** (captured output fails a test): **fixed**. junit.zig 58-87 → 58-103. Theorem `ce16_captured_error_passes`. Searched: complete at 961.
- **CE17** (a fresh file's ranges): **fixed**. nodes.zig 945-954 is unchanged. Theorem `ce17_fresh_file_from_its_first_range`. Searched: "no hole" holds over 1,000,000 timelines, plus 284,650 complete. The "ascending run" wording is still broken for non-fresh files (2,868), as the code intends.
- **CE18, CE22** (the catalog by kind): **fixed**. report.zig 143-173 → 183-213. Theorem `ce18_ce22_catalog_by_kind`.
- **CE19** (an adopted run reads "passed"): **fixed**. Its remainder, CE47, is fixed. serve.zig 5903-5909 → 5936-5942; 5756 → 5788; runs_adopt 5795-5822 → 5827-5855, which now reads `ended_status` (5848). Theorems `ce19_adopted_reads_exit` and `ce47_adopted_resume_keeps_its_exit`.
- **CE20** (a tape over the override table): **fixed**, with its remainder CE48 fixed. tape.zig 139-187 → 138-198; 300-308 → 311-319; 406-414 → 417-425. Theorems `ce20_full_tape_stops_its_replay` and `ce48_reasons_sized_from_the_tape`. Searched: the full-tape property holds in three worlds. The explorer still never reads `tape_full`: CE53.
- **CE21** (only the last xargs batch judged): **fixed**. ci.zig 526-563 → 526-568. Theorems `ce40_subshell_keeps_every_run` (for every run line form and every list of runs) and `ce21_ce27_ce28_ce29_still_fixed`.

### The tree (CE23 to CE26)

- **CE23** (a strategy's seed replays another prefix): **fixed**. main.zig: `plan_adopt_ran` 6404-6416, called at 6490. `Summary.seed` sits in the summary header with state_format 4 (2282, 2378-2379, 2414, 3985; runs.zig:13-17). Theorem `ce23_strategy_seed_adopted`. Tree census (`runs6/tree-census.txt`, 2,000 seeds a world): "every timeline replays alone" and "a node made by a replay is its parent's state" break in 0 runs in every world. With same_seed.py, round 3 had 3,029 and 3,958 of 5,000.
- **CE24** (the same seed grows another tree with other workers): **still there**, unchanged. main.zig 4012-4014 → 4052-4054; 4653-4659 → 4695-4701. Theorems `same_seed_other_tree` and `finishing_order_other_tree` (Theorems3) run on the default tree, now a7fe05d's.
- **CE25** (the archive returns to repeats): **still there**. main.zig 6405 → 6491; 7055-7065 → 7123-7133. Theorem `repeat_is_a_place`. Census: 369 of 2,000 same_seed.py runs.
- **CE26** (two returns to one moment): **still there**. main.zig 7120-7162 → 7188-7230; 7362-7378 → 7430-7446. Theorem `frontier_and_archive_one_moment`. Census: 528 of 2,000 runs in the first world.

### CI, serve, resume, durability (CE27 to CE39)

- **CE27** (a hang reported as "error"): **fixed**. ci.zig 316-320 is unchanged. Theorem `ce21_ce27_ce28_ce29_still_fixed`. As in round 5, "error" is still printed in two cases (289, 292) and is missing from docs/CI.md:124-126.
- **CE28** (a session changes shard verdicts): **fixed**. ci.zig 340-342. Same theorem.
- **CE29** (a resume ignores what was recorded): **fixed for evaluated properties**. main.zig 2864-2865. Same theorem, and `ce46_every_property_recorded`. CE45, the catalog, is still there.
- **CE30** (the coverage gate stops instrumented runs): **partly fixed**. serve.zig 703-752 → 703-784 adds `setup_covered` (707-727, 750) and counts `explored` (755). Theorem `ce30_setup_covered_not_stopped`. Searched: the instrumented world is complete at 320; the sessions worlds hold. The remainder is new: a run that starts from a snapshot (CE50).
- **CE31** (corrupt_reads stores a foreign byte): **fixed by declaring it**. nodes.zig 1983-1986 is unchanged. Its naming was CE43 (now fixed). CE54 is new.
- **CE32, CE33, CE34** (a resumed tree's returns, its ready-first plan, a filler's cut): **still there**, unchanged. main.zig 6859-6880 → 6927-6948; 6494-6505 → 6562-6573; 6293-6300 → 6335-6342; 4759-4762 → 4801-4804; 4601-4613 → 4643-4655; 4732-4737 → 4774-4779. Theorems `ce32_dropped_return`, `ce32_merged_returns`, `ce33_ready_first` and `ce34_filler_cut` (Theorems4; the model has no version because the code didn't change).
- **CE35** (sync_stall and durable_crash share an arm): **fixed**. Theorem `ce35_two_arms`. Searched: the census has 0 of 100,000, with both kinds begun in 49,660. a7fe05d's selftest change (durability_both_kinds) applies each request before sending the next.
- **CE36** (lost writes read back stale): **fixed in the docs**. Unchanged; the model still finds the documented case.
- **CE37** (missing reports counted over the run): **fixed**. Theorem `ce37_unreported_counted`.
- **CE38** (an uncovered CI job errors): **fixed**. serve.zig 765-773: a request with `ci` is never stopped. docs/CI.md:90-92 now says such a job "runs uncovered: the job runs to its end, never stopped by serve's coverage gate". Theorem `ce38_ci_job_runs_uncovered`. Searched: three worlds hold. The 62e06e3 world is found again.
- **CE39** (a targeted run reports "NEVER RAN"): **fixed**. main.zig: `change_count` 6429-6445, the end's count 4462-4464; changed.zig 25-27 and 69-70. Theorem `ce39_last_timeline_counted`. Searched: four worlds hold (one stopped at 1,000,000); 3939448's world is found again.

### Round 5's findings (CE40 to CE48)

- **CE40** (a run line that leaves its shell): **fixed**. ci.zig 539-547 → 537-552: `(\n<run line>\n); s=$?; ...`. Theorems:
  - `ce40_exit_run_line_judges_every_run` and `ce40_set_e_judges_the_failing_run` (the old cases);
  - `ce40_subshell_keeps_every_run`, general: for every form and every non-empty list of runs, every name is judged.

  Searched: every form is complete at 3,390; at GNU's size, 2,000 of 2,000 names are judged for each form. Upstream's three tests pass on a copy of a7fe05d's ci.zig (`runs6/recheck-ce40-zig.txt`). A runner's exit 255 is new (CE55).
- **CE41** (captured output with its own closing tag): **partly fixed**. junit.zig 72-81 calls `captured_end` (92-103). Theorem `ce41_closing_tag_in_cdata_passes`. Searched: round 5's world is complete at 961. Upstream's test passes (`runs6/recheck-ce41-zig.txt`). The remainder, a printed `</testcase>`, is CE49.
- **CE42** (a second phase's stop): **fixed**. composer.zig 797 → 804: `drive_start_ns + limit_ns / 2`, with `run_drivers` taking the drivers' start (767, 527-529). Theorem `ce42_second_phase_stops_at_half`. Searched: world 17 is complete at 18; 5,000 seeds; 5,000 drawn scenarios.
- **CE43** (corrupt_reads's last reads unnamed or misnamed): **fixed**. nodes.zig 2309-2324 → 2329-2364: the event disabled, the end marker written (2353), the reader waited for 2 s (2354), killed and waited for again if it hasn't exited, `rmdir` checked (2360-2362); the reader stops at the marker (2264); a leftover instance is cleared (2200-2205). Theorems:
  - `ce43_drained_at_the_heal`: the old case, with the reader scheduled within 2 s, is named.
  - `ce43_starved_reader_said`: a reader not scheduled within 2 s leaves the read unnamed, but the fault says "drain", and the next fault names nothing of the old.

  Searched: "named, or said" holds (100,000 seeds × 3 depths), and so does "named under its own fault". The strict wording ("every read ... is an event") still fails when the drain is cut, and the fault says so. See other findings for when `pidfd_open` fails.
- **CE44** (the jump past a token's hour): **still there, now documented**. Only the comment changed (composer.zig 900-914 → 913-925); it now names CE44 and the census. The promise it broke ("so a timeline failing on the jump ... takes a credential shorter than that") was withdrawn. Theorem `ce44_still_past_the_hour`. Census, unchanged: 4,452 and 1,315 of 1,000,000; 0 for the fix's own case.
- **CE45** (a complete resume judges no catalog): **still there**. main.zig 2212-2229 → 2242-2259 is unchanged. Theorem `ce45_complete_resume_still_skips_the_catalog`. a7fe05d's CE47 fix now *keeps* this resume's `exit` "0", so serve shows "passed". Round 6 also found the same through a session (the item left for round 6):
  - a session's timeline takes one of the run's numbers;
  - `resume_read` skips its line (main.zig:2200), so the run is never "complete";
  - the resume goes the explorer's way, passes that number over, and runs nothing;
  - it then judges the catalog of the recorded aggregates alone (2865), which hold only evaluated properties: exit 0.

  Found in `runs6/resume.txt`; same theorem, third conjunct.
- **CE46** (properties past a record line's room): **fixed**. report.zig 42-45 → 40-44, and 513-531 → 553-563: every evaluated property is recorded, and a line past 128 KiB is written whole from the heap (`line_write_large` 62-70, `line_bytes_write` 72-78). Theorem `ce46_every_property_recorded`. Searched: the old world (a room of 1) holds at a7fe05d and is found at 62e06e3.
- **CE47** (serve deletes a resume's `exit`): **fixed**. main.zig 1293-1297: the resume removes its last end's `exit` as it begins. serve.zig 5839 no longer deletes `exit`, and 5848 uses `ended_status`. Theorem `ce47_adopted_resume_keeps_its_exit`.
- **CE48** (the reason table): **fixed**. tape.zig 120 (removed) → 146-149, 186-198, 605 and 651: the table is sized from the tape's count of `,"reason":"`. Theorem `ce48_reasons_sized_from_the_tape`. Searched: "a table of 2 reasons" is complete at 65,536. Upstream's 1,025-connection test passes (`runs6/recheck-ce48-zig.txt`).

## New counterexamples

### CE49: captured output that prints test cases makes tests of its own and hides failures (CE41's remainder)

**Property.**
- junit.zig:2-6: each `<testcase>`'s classname and name, "whether it holds a `<failure>` or an `<error>`".
- a7fe05d's own test name: "captured output that prints its own closing tag never fails its test".
- docs/CI.md (Verdicts per test).

**Minimal case** (`runs6/junit.txt`, both properties found; theorem `ce49_printed_cases_judged`). The test `junit.WriterTest::writes_a_report` passes and prints a JUnit report in its `<system-out>`'s CDATA:

    <testcase classname="printed" name="ok"></testcase><testcase classname="printed" name="bad"><failure message="x"/></testcase>

- `cases` (junit.zig:14-20) ends the case's body at the first `</testcase>`, the one in the CDATA.
- It looks for the next `<testcase` from there and finds `printed::bad`, judged failing in every timeline. The job fails.
- A real test whose output printed `</testcase>` before its own `<failure>` is judged passing: the cut body never reaches the failure, and `captured_end` finds no closing tag in it.
- A printed name equal to a real test's adds its verdict to that test.

**How likely.** The same suites as CE41: any test of something that writes JUnit XML (a reporter, a CI tool, a test framework's own tests). Surefire, jest-junit and go-junit-report write output in CDATA as is. go-junit-report writes a package's whole output into the suite's `<system-out>`, where a printed `<testcase` is read the same way.

**Zig path.** guest/runtime/junit.zig:14-20 (`cases`: `indexOfPos(report, at, "</testcase>")`, then `<testcase` from there), 73-78.

**Regression test.** `tests/ce49_junit_printed_testcase.zig`, beside CE41's test (after junit.zig:240). It fails on a copy of a7fe05d's junit.zig: "expected 2, found 3" (`runs6/ce49-zig.txt`).

### CE50: the coverage gate stops an instrumented run started from a snapshot (CE30's remainder)

**Property.**
- docs/SDKS.md:101-105: the gate is for a run without coverage.
- The stop's reason: "its system runs without its language's instrumentation".
- serve.zig:703-706, CE30's fix: "timelines repeating the setup's paths report none, and the gate stopped instrumented runs as uninstrumented".

**Minimal case** (`runs6/serve.txt`; theorem `ce50_snapshot_run_stopped`). Round 3's draws, on a run whose setup ran in the snapshot it starts from:
- The setup ran edge 2. The run's own events/setup.jsonl is empty: main.zig:2690-2703 opens it, then sends the events to fork.jsonl or nowhere.
- The first 4 timelines run edge 2 again. Its bit is in the snapshot, so nothing is reported.
- `setup_covered` finds nothing, and the request has no `ci`. The run is stopped as uninstrumented.

**How likely.** Every run serve starts from a machine's checkpoint (`checkpoint`, POST /machines/<id>/checkpoint), other than CI: a fast VM's explore-here, a sandbox, a developer's REPL. Also a session fork's futures (`from_snapshot`). Each of these, if instrumented, is stopped when its first four timelines reach no line the machine hadn't run. That is likely when the developer set the system up and exercised it in the machine. The machine's own events (`<data>/machines/<m>/events.jsonl`, serve.zig:3424) hold the coverage it reported.

**Zig path.** src/serve.zig:707-727 (`setup_covered` reads only `runs/<id>/events/setup.jsonl`), 750, 773 (only `ci` exempt); src/main.zig:2690-2703.

**Regression test.** `tests/ce50_coverage_gate_checkpoint_run.zig`, beside "an instrumented run whose first timelines repeat its setup's code is not stopped as uncovered" (after serve.zig:6007). It needs the platform's tree (duckdb).

### CE51: a command-line run's analyses boot other inputs than its tapes' (a7fe05d's fix, partly)

**Property.**
- main.zig:1402-1405, a7fe05d's fix: "In the guest's command line too: left out, serve's analyses of a run started with --clock-start-max 0 booted another guest line, and its tapes were refused".
- Its test: "a run's request keeps what its guest's command line needs".
- The request's own comments: "In the guest's command line: replays need it".
- serve.zig:5583-5590.

**Minimal case** (`runs6/request.txt`; theorem `ce51_analysis_boots_other_inputs`). A run started from a command line with `--timeline-limit 30s`, and nothing else:
- Its tapes' inputs include `det.timeline_limit_ms=30000`.
- `run_request_write` records no `timeline_limit`.
- An analysis (`replay_argv`: machine.json, then `system_arguments(request.json)`) boots `det.timeline_limit_ms=3600000`. The inputs differ (`inputs_hash`, main.zig:8676-8705), so every tape is refused with TapeInputsDiffer.

The same holds alone for each of these:
- `--no-swarm` (`swarm` is written at its default, true);
- `--epoch`, `--timer-slack-us`, `--timer-landing-permille` (machine.json keeps none of them);
- `--injector` (no `injectors` in the request; the initramfs differs).

A run recorded by 62e06e3's explorer with `--clock-start-max 0` stays refused by a7fe05d's serve, since no request from before has the field. Runs serve starts record the posted request and serve's machine, so the property holds for every input (`serve_run_boots_its_inputs`, proved).

**How likely.** Any run started from a terminal with one of these flags. `--timeline-limit` is documented (docs/AGENTS.md:299) and the e2e passes it to explore nine times; `--no-swarm` is the comparison mode. Then every analysis of that run fails: causality, explain, sessions, replays.

**Zig path.** src/main.zig:1374-1487 (`run_request_write`: no `.timeline_limit`, `.swarm` or `.injectors`; machine.json without `--epoch`, `--timer-slack-us` or `--timer-landing-permille`), 9142-9143 (`--timeline-limit` keeps no text), 1835-1908, 8676-8705; src/serve.zig:2865-2880, 5565-5600.

**Regression test.** `tests/ce51_request_keeps_machine_inputs.zig`, beside a7fe05d's request test (after main.zig:1369). It rebuilds the analysis's argv from request.json and machine.json and compares `cmdline_build`, the epoch and the timers. It needs the platform's tree.

### CE52: a session step over about 41 KiB makes its timeline's tape unreadable

**Property.**
- README_AI.md: "every timeline replays bit-identically".
- vm.zig:2202-2203: "A step the moment runs, on the timeline's own tape at the moment it ran: a replay of the timeline runs it there again".
- vm.zig:3684-3687 (CE20's fix): "instead of a tape no replay can read".

**Minimal case** (`runs6/tape6.txt`, `runs6/ce52-zig.txt`; theorem `ce52_long_step_unreadable`). Two bounds, neither on the recorder's side:
- **The parse.** Every caller parses a tape line into a 64 KiB scratch (main.zig:2612, 3332; node.zig:60). std.json's `Value` copies every string (`.alloc_always`, std/json/dynamic.zig:88). The longest step that parses is 42,235 bytes, measured on a copy of a7fe05d's tape.zig. A `det:ask` step (vm.zig:1895-1899: one REPL message in base64) of 42,236 bytes, a 31 KiB message, fails with OutOfMemory.
- **The recorder.** `write_step` (tape.zig:500-511) writes the line's head, then stringifies the step into 128 KiB. Past that it returns (`catch return`), leaving the head unfinished, so the next line runs on from it. A 96 KiB message gives UnexpectedEndOfInput.
- **The table.** Past 65,536 steps or 16 MiB of step text, the parse refuses the tape (TapeTooLong, 513-522). Nothing caps steps when recording.

**On the code.** Three tests appended to a copy of a7fe05d's tape.zig (its `write_all` uses libc's write so it runs on macOS) all fail:
- a 131,072-byte `det:ask`: UnexpectedEndOfInput;
- a 45,000-byte one, written whole: OutOfMemory;
- an 80,000-byte shell step with 40,000 quotes: OutOfMemory.

**How likely.** A REPL session that sends a message over 31 KiB: nREPL's `load-file` of a medium namespace (CIDER's load-buffer sends the whole file), or one large form or pasted script. The session's timeline then can't be replayed. Neither can its saved checkpoints' replays or the sessions opened on it later. Steps are any length (vm.zig:2169-2196 reads lines without a bound).

**Zig path.** src/core/tape.zig:500-511 (`write_step`), 513-522 (`step_parse`), 612-620 (each line parsed in the scratch); src/main.zig:2612, 3332; src/core/node.zig:60; src/core/vm.zig:2205-2208.

**Regression test.** `tests/ce52_tape_long_session_step.zig`, beside "a session's steps on its timeline's tape parse back, with their moments" (after tape.zig:906). It has three tests and needs only std and a temporary file.

### CE53: a return past a full tape's marker makes timelines that never replay

**Property.**
- README_AI.md: "every timeline replays bit-identically".
- docs/ANTITHESIS.md (Branching): "every timeline's path in its record and tape (it replays alone)".

**Minimal case** (`runs6/tape6.txt`; theorem `ce53_child_of_a_full_tape_never_replays`).
- A cap of one override (1,048,576 in the Zig). The parent's pulls are a draw and two overrides, so its tape is full at pull 2.
- The tree returns to its moment 3 from a holder, which is the real state, so the child runs.
- The child's chain goes through the parent to moment 3. Replayed alone, it stops at the parent's marker (TapeFull), and so do its failures' replays.
- Without holders (a deciding strategy), the node itself is a replay that stops; the search is complete with none found.

**How likely.** Rare: a timeline must make 1,048,576 overrides, for example an hours-long timeline of outside connections or ingress answers. The explorer never reads `tape_full` (main.zig has no reference to it). `archive_add` (7096-7140) and the frontier take every moment before `last_pull_ns`.

**Zig path.** src/core/vm.zig:3684-3699; src/core/tape.zig:310-320; src/main.zig:7096-7108 (the moments), 3910-3926 (`Summary.last_pull_ns`: nothing about the tape).

**Regression test.** `tests/ce53_return_past_full_tape.zig`, beside "the archive returns first to a cell whose returns paid" (main.zig:5918). It needs the platform's tree. It names `Summary.tape_full_ns`, the moment the fix would keep.

### CE54: an aimed corrupt_reads names a byte its read never had changed

**Property.**
- sdk/zig/schema.zig, `corrupt_reads`: "Every read it corrupts is named (`disk_corrupt_read`: node, file, sectors, the byte ...), so a durability judge excludes those pages, or flags a loss inside one, without guessing".
- nodes.zig:2278: `.byte = read.sector * 512 + corrupt_byte - 1, // The device's byte the fault changed.`

**Minimal case** (`runs6/aimed.txt`; theorem `ce54_named_byte_not_the_changed_one`; general theorem `read_inside_an_extent_named_right`).
- The aimed file's only extent is block 1, and block 0 is a hole.
- During the fault the hole is written at ext4's goal (`ext4_ext_find_goal`: the extent's block less the distance), which is block 0.
- A read of both blocks is one bio. device-mapper splits it at the segment boundary, and dm-flakey changes the byte at the start of the flakey part: block 1's.
- The event names block 0's byte, which the fault never changed.
- With two aimed extents and the hole between them filled (the left extent's block plus one), two bytes are changed and one is named.

The general theorem shows the naming is right for every read inside one extent. That covers a page read to merge a write, which is CE31's case.

**How likely.** An aimed fault (half of disk faults, faults.zig:928-931) on a file whose holes are written during the fault, then read across. Databases with sparse or preallocated files written out of order do this (bbolt/etcd grows its file with truncate; LMDB). In the model's uniform world: 2,483 of 37,102 reads through an aimed extent (3 blocks) and 2,167 of 31,930 (4 blocks).

**Zig path.** guest/runtime/nodes.zig:2375-2410 (`file_extents` at the fault's start), 2415-2434 (`aimed_record`'s segments), 2270-2280 (one byte per bio).

**Regression test.** `tests/ce54_aimed_corrupt_read_byte.zig`, beside `test aimed_record` (after nodes.zig:2445). It needs only std. It names `read_changed_bytes`, the function the fix would make of the inline naming.

### CE55: a runner that exits 255 stops xargs, and the shard's later tests are never judged

**Property.**
- docs/CI.md (`junit`): "each test gets its own verdict across its shard's timelines".
- ci.zig:529-533 (a7fe05d): "every test of the shard gets its verdict ..., whatever the run line does with its shell (CE40)".

**Minimal case** (`runs6/ci.txt`; theorem `ce55_255_stops_the_shard`).
- Two xargs batches. The first run's runner exits 255. The subshell keeps that status, and the move then runs `exit $s`.
- xargs stops: GNU's and BSD's "exits immediately ... if an invocation exits with a value of 255".
- The second batch never runs and its tests get no verdict. Nothing but the shard's failure says so.
- This holds at every version.

**On the code.** Appended to a copy of a7fe05d's ci.zig: 5,000 of 20,000 judged (`runs6/ce55-zig.txt`).

**How likely.** Rare but certain for some runners:
- mocha's exit status is its failure count, capped at 255;
- `System.exit(-1)`, `os.Exit(-1)` and `exit -1` all exit 255.

The shard list must also be long enough to split.

**Zig path.** src/products/ci.zig:537-552 (`exit $s` after the move), 553-555 (the xargs line).

**Regression test.** `tests/ce55_ci_xargs_exit_255.zig`, beside a7fe05d's CE40 tests (after ci.zig:714). It needs /bin/sh and xargs.

## Other findings (not counterexamples)

- **The drain when `pidfd_open` fails** (nodes.zig:2348-2362). If it fails, nothing waits for or kills the reader. `rmdir` runs at once and fails, which is said ("rmdir"). If the next fault starts before the stray reader reads the marker, the start's clear erases the marker. The old reader then shares the pipe and names the new fault's reads under the old fault's byte, which is CE43's second half (`runs6/disk.txt`, "pidfd_open may fail"). `pidfd_open` is used elsewhere in the guest (nodes.zig:718, 3422), so this is unlikely.
- **A reader that already exited at the heal.** If the reader died during the fault (the OOM killer), reads after its death are never named and nothing says so: `pidfd_open` returns ESRCH, so there is no "drain" event, and `rmdir` succeeds. If its pid was reused, the heal waits 2 s and SIGKILLs the stranger. 62e06e3 killed the stored pid at once too. Read, not modeled.
- **The 4,096-event cap.** nodes.zig:2162 and 2268-2272 cap events per fault; the cap is said with `disk_corrupt_reads_capped`, but schema.zig's "every read it corrupts is named" doesn't mention it. A non-aimed fault on a node that reads a few thousand bios during the fault reaches it.
- **Aimed extents reused by another file.** When the aimed file is deleted or rewritten during the fault and ext4 gives its old blocks to another file (after the freeing transaction commits), that file's reads are corrupted and named with the aimed file's name. The sectors are right. Read, not modeled.
- **trace_clock.** The reader stops at the marker in trace_pipe's merge order, which uses the instance's default `local` clock. Linux documents that clock as possibly unsynchronized across CPUs. A read traced earlier on another CPU with a later stamp would come after the marker. The heal swaps the table first, so such a read was mapped before the heal. Read; it depends on the guest's per-CPU clocks.
- **CE40's subshell.** A run line's variables no longer reach the appended part, which uses only `$?`. An EXIT trap now runs before the move. That helps a trap that writes the report (`go-junit-report` at EXIT), whose report 62e06e3 moved too late. A run line ending in `&` used to be a syntax error (`&;`). It now backgrounds the runner, and the move races it. Read.
- **CE42's stop.** The limit is read from the same command line in every phase, and a returned timeline keeps its parent's composer, so its drivers' start. Phases with a length are bounded by the length, not the half. Holds (world 17 complete).
- **CE48's count.** The count runs over the whole tape text, so it can only over-count: a step line, a header, or a reason of another kind. The platform's only writer, `write_override`, always writes `,"reason":"`. A hand-written tape with `"reason"` first or spaced would be refused. Read.
- **Records since CE29 and CE46.** A record line now holds every evaluated property, at any size. serve reads `record.jsonl` whole through `run_file`, capped at 256 MiB (serve.zig:173, 6789-6793) for:
  - the run's page (`run_show`, 2338);
  - `recorded_status` (6075);
  - `summary_workers` (6490).

  At about 15 KB a line (100 properties of about 150 bytes), a run of about 17,000 timelines passes the cap. Its page then has no run, summary or changed line. An explorer that died before its exit reads "interrupted", and `exploration_judge` reads 0 workers. Arithmetic, not modeled.
- **CE45 and CE47 together.** With CE47 fixed, a complete resume's `exit` "0" is kept, and serve shows "passed" for a run failing a catalog assertion (CE45).
- **The `{shard}` mode with `junit`.** There is no xargs and one report, so it holds. The shard line's test count is the list's modulo, not the runner's own split (`runs6/ci.txt`: 125 lines differ), as in round 3.
- **`explored_timeline_events` with resumed timelines.** Counts are `count(DISTINCT timeline)` (ci.zig:340-342, 296-300). A timeline the resume runs again is the same deterministic timeline, so its statements repeat and nothing changes. Holds by reading.
- **The older models still in the searches.** Round 2's `Junit.testsJudged` (3939448's last-batch xargs) and Serve3's resume model (3939448) are found again in `runs6/junit.txt` and `runs6/serve.txt`. They model old code, superseded by Ci5 and Resume5.

## What was replicated, and what is not exact

Replicated at a7fe05d, with file and lines:
- composer: the stop from the drivers' start;
- junit: `captured_end`, and `cases`' `</testcase>` search as is;
- CI: the subshell, `exit $s`, xargs's 255 stop, and the gate's `ci` exemption;
- tapes: the sized reason table, `write_step`, `step_parse`, the parse scratch, and `tape_full` against returns;
- corrupt_reads: the drain (marker, waits, kill, `rmdir`, clear), and aimed naming against dm's split;
- resume: no room, the kept `exit`, and a session's number;
- serve: `setup_covered`, `explored`, and runs from snapshots;
- the tree: `plan_adopt_ran`;
- the targeted count;
- a run's request and machine against `inputs_hash`.

Not exact:
- The drain's scheduling is a decision. So are whether a killed reader exits within 2 s and whether `pidfd_open` fails.
- Inputs are a list of the words and machine fields that `inputs_hash` covers, not a hash. The kernel and initramfs are named, not built.
- Steps carry their length and escapes only. The parse scratch's bound is the measured 42,235 bytes; the model doesn't run std.json.
- The aimed model is in blocks, with `corrupt_byte` 1. ext4's allocator is reduced to its goal. Bios are runs of a file's consecutive blocks.
- The full-tape model is one parent and one return.
- Rounds 1 to 5's simplifications still hold.

## Assumptions

- sh: a subshell's `exit`, `exec` and `set -e` end only the subshell, and its EXIT trap runs at its end.
- xargs (GNU findutils and BSD) stops when a command exits 255.
- Linux:
  - device-mapper splits a bio at target boundaries;
  - dm-flakey's `corrupt_bio_byte` counts from each clone's start;
  - `ext4_ext_find_goal` places a hole's block next to its logical neighbour;
  - writing 0 to an event's `enable` stops new trace lines before the marker;
  - pidfd polling is readable once the process exited and closed its files.
- std.json (Zig 0.17, the platform's minimum) copies every string of a `Value`.
- A command-line run's analyses boot machine.json, then `system_arguments(request.json)` (serve.zig `replay_argv`).
- Rounds 1 to 5's assumptions hold.

## Properties, with sources (13 new or restated)

1. Every test of a shard gets its verdict, whatever the run line does with its shell (ci.zig:529-533). Holds for every form (CE40 fixed). Fails at a 255 (CE55).
2. The tests judged are the report's test cases, each with its own verdict (junit.zig:2-6). Fails (CE49).
3. A test case's captured output never fails it (a7fe05d's test). Holds for closing tags (CE41 fixed).
4. No driver starts past half the timeline's limit (composer.zig:798-804). Holds (CE42 fixed).
5. Every read corrupt_reads corrupts is named in its fault (schema.zig): fails only when the drain is cut, which is said. "Named, or said" holds. "Named under its own fault" holds (CE43 fixed) unless `pidfd_open` fails.
6. A disk_corrupt_read names the byte its read had changed, and every changed byte is named (schema.zig; nodes.zig:2278). Fails (CE54).
7. The coverage gate stops only runs without instrumentation (SDKS.md:101-105). Holds for runs whose setup ran in them (CE30 fixed). Fails for runs from a snapshot (CE50).
8. An analysis of a run boots the inputs its tapes were recorded with (main.zig:1402-1405). Fails for command-line runs (CE51).
9. A session's timeline replays from its tape (vm.zig:2202-2203). Fails (CE52).
10. Every timeline the tree makes replays alone (ANTITHESIS.md). Fails past a full tape (CE53); holds for the strategy's seeds (CE23 fixed).
11. A resumed run's verdict is the uninterrupted run's (main.zig:2244-2246). Fails for the catalog (CE45), including through a session's number; holds for evaluated properties of any number (CE46 fixed).
12. A run's state is its explorer's exit, adopted or not (serve.zig:5931-5945). Holds (CE47 fixed).
13. A targeted run reports each hunk in as many timelines as ran it (AGENTS.md). Holds (CE39 fixed).

## Search runs (`runs6/`)

Composer:
- `ce2-world{2,13,16}.txt`: complete at 512, 41,472 and 41,472; 5,000 seeds each; none found.
- `ce5-world14.txt`: complete at 5. `ce5-world12.txt`: stopped at 5,000. Both had 2,000 seeds; none found.
- `stop-world17.txt`: complete at 18, plus 5,000 seeds; none found (CE42 fixed).
- `ce1-world4.txt`: complete at 1,394, plus 5,000 seeds.
- `drawn-{2,12,13}.txt`: 5,000 drawn scenarios each; none found.

Other areas:
- `junit.txt`: 3 properties × 5 worlds. The printed-cases world is found (CE49); the others are complete, up to 961.
- `persist.txt`, `verdicts.txt`, `durable.txt`, `clock.txt`: as in round 5. Nothing new is found; CE44 is found again.
- `tape.txt`: 4 properties × 11 worlds. The reason table holds (complete at 65,536). CE13's last interval is found again.
- `ci.txt`:
  - the gate holds in 3 worlds; 62e06e3's is found;
  - every run line form holds (complete at 3,390); 62e06e3's is found (CE40);
  - the 255 world is found (CE55);
  - at GNU's size, 2,000 of 2,000 for each form.
- `resume.txt`: the catalog (CE45) and the session world are found. The room world holds; 62e06e3's is found.
- `disk.txt`: 3 properties × 3 versions × 3 depths.
- `serve.txt`: the gate. The snapshot world is found (CE50); the plain and sessions worlds hold; 3939448's are found.
- `steer.txt`: 4 worlds hold; 3939448's is found.
- `tree-census.txt`: 7 worlds × 2,000 seeds. CE23's properties are at 0; CE25 and CE26 remain.
- `request.txt`: found for command-line runs (a7fe05d's and 62e06e3's recordings); complete at 256 for serve's runs.
- `tape6.txt`: the steps' three worlds are found; the full tape is found with holders, complete without.
- `aimed.txt`: found in both worlds, plus a census.

The Zig runs used Zig 0.17.0's global cache:
- `ce49-zig.txt`, `ce52-zig.txt`, `ce55-zig.txt`: the new tests fail on copies of a7fe05d's files.
- `recheck-ce4{0,1,8}-zig.txt`: upstream's tests for CE40, CE41 and CE48 pass.

## Theorems (27, `Replica/Theorems6.lean`)

General (for every input):
- `subshell_parts`
- `ce40_subshell_keeps_every_run`: for every run line form and every non-empty list of xargs runs, a7fe05d judges every name.
- `serve_run_boots_its_inputs`
- `read_inside_an_extent_named_right`: a read inside one aimed extent is named with the byte it had changed.

The recheck, by computation:
- `ce40_exit_run_line_judges_every_run`
- `ce40_set_e_judges_the_failing_run`
- `ce41_closing_tag_in_cdata_passes`
- `ce42_second_phase_stops_at_half`
- `ce43_drained_at_the_heal`
- `ce43_starved_reader_said`
- `ce44_still_past_the_hour`
- `ce45_complete_resume_still_skips_the_catalog`
- `ce46_every_property_recorded`
- `ce47_adopted_resume_keeps_its_exit`
- `ce48_reasons_sized_from_the_tape`
- `ce23_strategy_seed_adopted`
- `ce30_setup_covered_not_stopped`
- `ce38_ci_job_runs_uncovered`
- `ce39_last_timeline_counted`
- `ce21_ce27_ce28_ce29_still_fixed`

New counterexamples, by computation:
- `ce49_printed_cases_judged`
- `ce50_snapshot_run_stopped`
- `ce51_analysis_boots_other_inputs`
- `ce52_long_step_unreadable`
- `ce53_child_of_a_full_tape_never_replays`
- `ce54_named_byte_not_the_changed_one`
- `ce55_255_stops_the_shard`

Earlier rounds' theorems now pin their version where the code changed:
- Theorems5: 5, to `.v62e06e3` (CE41, CE42, CE43, CE47, CE48; CE46 already was).
- Theorems3: 2, to `.v3939448` (the CE23 world and the CE30 gate).
- Theorems4: 2 (CE38 to `.v62e06e3`, CE39 to `.v3939448`).

Round 5's proofs about `Ci5.step` build unchanged against the three-version step. All 174 build jobs succeed.

## Library gaps

- Model variants: a third version meant replacing each `== .v62e06e3` with "since 62e06e3" by hand. A `Ver` ordered by commit, and properties searched over a version list, would help.
- The library has no model of a byte stream with line framing; the tape's text was modeled as pieces. A JSON-lines writer/reader model would cover `write_step` and similar writers.
- A census over seeds was again written by hand (`Aimed6.census`), although `Determinismo/Census.lean` exists in a7fe05d's SDK (the replica still builds against `upstream/sdk/lean`).
- The parse scratch's bound came from running Zig. Lean has no model of std.json's allocation.
- `simp` needed `List.filterMap_cons` spelled out to reduce a one-element `filterMap` under a hypothesis.

## Left for round 7

- Run CE49, CE52 and CE55 on the platform (they already fail against copies of a7fe05d's files), and CE50, CE51, CE53 and CE54 in its tree or guest.
- Still open from earlier rounds: CE4's singleton (by design), CE24 to CE26, CE32 to CE34, CE44 (decision pending) and CE45.
- corrupt_reads: the reader killed by the OOM killer, and pid reuse at the heal; aimed extents reused by another file; per-CPU trace clocks.
- Records past 256 MiB: serve's page and status, measured on a long run's record.
- The tree with a full tape: holders at the marker's exact moment, and archive returns to earlier generations past their marker.
- A run line ending in `&` under the subshell; xargs's other stops (a command killed by a signal, under `exec` at 62e06e3).
- The SDK: build against a7fe05d's `sdk/lean` (Relation.lean, Census.lean).
