# determinismo in Lean: round 7

## What this is

Round 7 of the Lean 4 (v4.36.0) replica of determinismo. The platform's next branch is now df8f08b, a plain copy in `upstream-df8f08b/` (its commit in `.commit`); round 6's baseline a7fe05d stays in `upstream-a7fe05d/`. The 19 commits change 11 files: `guest/runtime/{composer,junit,nodes}.zig`, `src/core/{tape,vm}.zig`, `src/{explain,main,runs,serve}.zig`, `src/products/ci.zig`, `tools/e2e.zig`. Each diff is in `scratch/r7/*.diff`.

df8f08b carries changes for eight of round 6's counterexamples: CE45, CE49, CE50, CE51, CE52, CE53, CE54 and CE55. It also carries the composer's `drivers_stopped`, the `planned` record lines (CE32 to CE34), the repeats and one-moment fixes (CE25, CE26), and explain's `--draw`.

The models follow df8f08b by default:
- `Ver` (`Replica/Prelude.lean`) gained `.vdf8f08b`. `Ver.sinceA7` holds for a7fe05d and df8f08b, and `Ver.sinceDf` is new.
- Every model's default moved from `.va7fe05d` to `.vdf8f08b`.
- Round 6's theorems about a7fe05d's code are pinned to `.va7fe05d` (Theorems6, Theorems4, Theorems3).

Changed models (each change threads the version):
- `Junit.lean`: `caseIndex`, and `capturedEndDf` (comment-aware); a world with comments in a case's body.
- `Ci5.lean`: `xargsRunsV` (a 255 passed on as 254).
- `Tape6.lean`: `write_step`'s stream, `step_line_parse` (no scratch bound), `step_record`'s cap (`accepted`); returns before the marker, and the cut and strategy worlds.
- `Aimed6.lean`: `read_corrupted_parts` in blocks (`namedDf`) and in sectors (`readCorruptedParts`, `changedB`).
- `Serve3.lean`: the checkpoint and snapshot exemption; the end's `uncovered` file (`Gate.labeled`), with a property of its own.
- `Request6.lean`: df8f08b's request and machine; the injector's kept name.
- `Resume5.lean`: the catalog line; whether the run reached its end before its stop.
- `Resume4.lean`: `planned` lines, `child_indices`, `index_settle`, a stop while the judgment plans, and two lines under one key.
- `Tree.lean`, `TreeRun.lean`: `archive_add_judged`'s repeats; `archive_returns`' one moment.
- `Composer.lean`, `ComposerProps.lean`: `driver_start_by` returns whether it started; property 15, `stopSaid`; worlds 18 and 19 (a7fe05d).
- `Disk5.lean`: a reader that dies during its fault, and pid reuse at the heal.

New files:
- `Replica/Explain7.lean`: explain's verdicts (Wilson's interval) for a named draw.
- `Replica/Disk7.lean`: the searches for a dying reader.
- `Replica/Theorems7.lean`: 25 theorems.
- `Main7.lean`: the `replica7` executable.
- `tests/r7_*.zig`: round 7's Zig tests.
- `scratch/zig7/`: the harnesses (copies of both versions' files, shims, `tools/extract.py`, `run-all.sh`).
- `scratch/sdk7/`: the replica built against df8f08b's `sdk/lean`.
- `scratch/round7.sh`, `scratch/round7b.sh`: the searches.
- `runs7/`: their output.

Commands:

    lake build
    .lake/build/bin/replica7 composer|cworld|cdrawn ...
    .lake/build/bin/replica7 junit|persist|verdicts|tape|resume|serve|request|tape6|explain <exhaust>
    .lake/build/bin/replica7 ci|durable|disk|disk7|resume4|tree|steer|aimed <exhaust> <seeds>
    .lake/build/bin/replica7 clock|treecensus|resume4census <seeds>
    scratch/zig7/run-all.sh

## How the Zig tests run

Each test is in the platform's form: a Zig `test` block. It runs against a copy of a7fe05d's and of df8f08b's file, built with Zig 0.17.0 through the job slots.

The copies come in two forms:
- Standalone files are copied whole and the test is appended: `junit.zig`, `ci.zig`, and `tape.zig` (its `write_all` uses libc's write so it runs on macOS).
- Other files are copied in part: the declarations a test needs are copied verbatim by `scratch/zig7/tools/extract.py`, each marked with its file and lines, after a shim header (`scratch/zig7/shims/`). This covers `nodes.zig`, `serve.zig` and `main.zig`, which are Linux-only and need duckdb.

What the shims replace:
- `linux` syscalls, through libc;
- `sdk.event`, kept in memory;
- duckdb's two counts;
- `runs.artifact_keep`, which names a kept copy as the platform does;
- `report.record`, kept in memory.

Two harnesses wrap statements taken from inside larger functions; each such statement keeps its line numbers:
- the summary's `last_pull_ns` line;
- the run end's catalog lines.

The explain harness is a copy of df8f08b's `explain.zig` with its scratch directory moved under the replica's. It runs with a shell script standing in for `determinismo explore`.

`runs7/<harness>-<a7|df>-zig.txt` hold the outputs. "Red" means the test fails on that version; "green" means it passes.

## The changed counterexamples at df8f08b

### CE45 (a complete resume judges no catalog): closed for a complete run resumed again; three paths remain

**The change.** At the run's end the catalog's verdict is recorded (main.zig:1170-1175, `{"catalog":{"failing":n}}`). `resume_read` reads the last such line (2297). `complete_verdict` (2148-2154) fails the run for it.

**Model** (`Resume5.resumedExit`, `ended`):
- Theorem `ce45_closed_for_a_complete_run`: two timelines declaring `reachable "r"`, never reaching it. The run exits 3, and the complete resume now exits 3.
- The same theorem shows two paths still exit 0:
  - a stop after the last timeline's record line but before the run's end (no catalog line yet);
  - a session's timeline holding one of the run's numbers (round 6's path). `resume_read` never finds the run complete. The explorer's way judges the catalog from nothing; `catalog_failing` is read in `complete_verdict` alone. It then records `{"catalog":{"failing":0}}`, the line a later resume reads.
- The search found a third path: a run stopped after its first timeline's line, resumed, with its new timelines not declaring "r". The record lines keep evaluated properties only (report.zig), so the declaration is lost and the resumed run exits 0 (theorem `ce45_interrupted_run_loses_declarations`; `runs7/resume.txt`).
- All three follow from one gap: a record line keeps no timeline's declared-but-unreached catalog entries.

**Zig** (`tests/r7_ce45_resume.zig`): the run's own end lines (each version's) write the record, and `resume_read` runs verbatim in a child process (it ends the process with the status).
- "a complete run resumed again fails for its catalog as the run did": red on a7fe05d (0), green on df8f08b (3).
- "so does one whose missing number a session's timeline took": red on both (status 100: not complete, the explorer's way).

### CE49 (printed test cases): closed

**The change.**
- `cases` finds each case with `case_index` (junit.zig:62-83: no `<testcase` inside a CDATA section or a comment).
- It ends each body with `captured_end` (115-131), which now skips comments too.

**Model.**
- Theorem `ce49_closed`: round 6's two reports are judged right.
- The searches (`runs7/junit.txt`): every df8f08b world is complete (up to 961 timelines); a7fe05d's printed-cases world is found.

**Zig** (`tests/r7_ce49_junit.zig`): red on a7fe05d ("expected 2, found 3"), green on df8f08b.

**What it leaves.** `element_index` (85-112), the failure search inside a body, skips CDATA and captured output but not comments. A passing case whose body holds `<!-- <failure .../> -->` is judged failing at both versions:
- theorem `df_comment_in_a_body_fails_its_case`;
- the comment world is found in `runs7/junit.txt`.

I know of no JUnit writer that puts comments inside a test case, so this is a note, not a counterexample.

### CE50 (the coverage gate stops a run from a snapshot): closed for the stop; CE56 remains

**The change.** serve.zig:779-783: a request with `checkpoint` or `from_snapshot` returns before the stop. Both fields are written by `run_create` (1921-1924), the machine's checkpoint action (3486-3488) and the session's futures (4033).

**Model.**
- Theorem `ce50_closed_ce56_said`: round 3's draws on a run from a snapshot are not stopped.
- Searches: the gate property holds in every df8f08b world, and a7fe05d's snapshot world is found.

**Zig** (`tests/r7_ce50_coverage_gate.zig`, `coverage_gate` and `setup_covered` verbatim):
- "a run from a machine's checkpoint or a fork's snapshot is not stopped as uninstrumented": red on a7fe05d, green on df8f08b;
- its control, an ordinary run without coverage stopped: green on both.

**What it leaves** (CE56 below): the same gate, once such a run ends, writes its `uncovered` file.

### CE51 (a command-line run's analyses boot other inputs): closed for five flags; CE60 remains

**The change.**
- `run_request_write` records `timeline_limit` as given, `swarm` and `injectors` (main.zig:1441-1453).
- machine.json gains `--epoch`, `--timer-slack-us` and `--timer-landing-permille` (1519-1522).
- `system_arguments` gives all of them back (serve.zig:5595-5602).

**Model.**
- Theorem `ce51_closed`: for every command-line run without an injector of its own, the analysis boots the run's inputs.
- `runs7/request.txt`: each flag alone boots its inputs at df8f08b, except `--injector`.
- Runs recorded by a7fe05d's or 62e06e3's explorer stay refused by df8f08b's serve, since their requests have none of the fields.

**Zig** (`tests/r7_ce51_request.zig`; `run_request_write`, `RunRequest` and `system_arguments` verbatim):
- "a command-line run's analyses are given every input flag of its command line and machine": red on a7fe05d, green on df8f08b;
- its control, `--clock-start-max`: green on both.

**What it leaves** (CE60 below): the injector reaches the analysis under its kept copy's name.

### CE52 (a long session step makes the tape unreadable): closed

**The change.**
- `write_step` streams each line whole through a 4 KiB buffer, escaping as it goes (tape.zig:512-547).
- `step_line_parse` decodes the string straight into the step table (552-609; called at 717), so there is no 64 KiB scratch.
- `step_record` refuses a step past `step_fits(steps + 1, bytes + "det:over".len, len)` with TapeStepsFull, before it runs (vm.zig:2214-2221).
- `session_end` asserts det:over's room (2255-2263).
- An extending timeline counts the steps it copies (main.zig:3846-3852).

**Model.**
- Theorem `ce52_closed`: the 131,072-byte `det:ask`, the 42,236-byte one and the 70,000-byte step with 61,072 escapes all read back, and a table of 2 steps keeps one, with room for det:over.
- `runs7/tape6.txt`: df8f08b's four step worlds are complete, including a table of 3 steps and 20 bytes over 5 items (243 timelines); a7fe05d's three are found.

**Zig** (`tests/r7_ce52_tape.zig`, round 6's three tests): red on a7fe05d (UnexpectedEndOfInput, OutOfMemory, OutOfMemory), green on df8f08b.

**What it leaves** (read, not a counterexample). An extending timeline copies every parent step before its moment, `det:over` included, with no check. A parent tape filled to `steps_max` (65,535 steps of its own and its det:over), or to within 8 bytes of 16 MiB, then makes any later session on it hit `session_end`'s `assert(tape.step_fits(...))`. That is a panic in a safe build. It needs a session at the cap exactly.

### CE53 (a return past a full tape's marker): closed for the explorer's moments; CE58 remains

**The change.**
- `VM.tape_full_ns` (vm.zig:3712).
- A judged timeline's `last_pull_ns` is `returns_before_ns(last pull, checks' start, tape_full_ns)` (main.zig:4083, 6556-6558).

**Model.**
- Theorem `replay_before_the_marker`: for every marker and moment, a moment at or before the marker's pull replays.
- Theorem `ce53_closed`: round 6's draws.
- `runs7/tape6.txt`: the uncut worlds hold (complete at 52 and 324 timelines); a7fe05d's is found.
- A return at the marker's exact moment never happens: the archive needs `at < last_pull_ns` (7374) and the frontier is clamped to `end_ns - return_after_ns` (7670-7686).

**Zig** (`tests/r7_ce53_archive.zig`: the summary statement of each version, then `archive_add` verbatim):
- "the archive keeps no place past where a timeline's tape was full": red on a7fe05d, green on df8f08b.

**What it leaves** (CE58 below): a cut timeline's archive places, and a strategy's moments.

### CE54 (an aimed corrupt_reads names an unchanged byte): closed

**The change.** `disk_reads_read` names one part per aimed extent a read overlaps, through `read_corrupted_parts` (nodes.zig:2269-2285, 2301-2318). Each part's byte is counted from the part's start, and there is none for a part shorter than `corrupt_byte`.

**Model.**
- Theorem `ce54_closed`: for every aimed table and read, df8f08b names exactly the blocks whose byte dm changed.
- Theorem `ce54_parts_are_the_changed_bytes`, in sectors for every `corrupt_byte`: `read_corrupted_parts`' bytes are dm-flakey's, byte `cb` of each clone over an extent. Both theorems are general.
- `runs7/aimed.txt`: df8f08b's worlds of 3 and 4 blocks are complete (2,280 and 59,840 timelines), and 5 blocks stopped at 200,000 with none found.
  - Census: 0 wrong of 7,417, 6,444 and 5,668 reads through an aimed extent.
  - a7fe05d: 532 of 7,417.
- The kernel's side was reread for the cases the fix's assumptions cover:
  - dm splits a bio only at target boundaries: `max_io_len` is 0 for flakey and linear.
  - The remainder resubmitted by `dm_split_and_process_bio` keeps `BIO_TRACE_COMPLETION`, so `block_bio_queue` traces a read once.
  - `file_extents` joins adjacent extents in logical order only, so two physically adjacent extents stay two segments, two clones, and two named bytes, which agrees.

**Zig** (`tests/r7_ce54_aimed_reader.zig`: the reader itself, `disk_reads_read` verbatim, fed a pipe of `block_bio_queue` lines and the heal's marker):
- "an aimed corrupt_reads names the bytes the fault changed, and only those": red on a7fe05d (names 47,108 = 92 × 512 + 4, not 51,204), green on df8f08b;
- its control, a read inside one extent: green on both.

### CE55 (a runner's 255 stops xargs): closed

**The change.** Every `{tests}` run line runs in its subshell, junit or not, and `if [ $s -eq 255 ]; then s=254; fi; exit $s` (ci.zig:543-555).

**Model.**
- Theorem `ce55_closed`, general: for every run line form and every non-empty list of runs, 255s included, every name is judged.
- `runs7/ci.txt`: a7fe05d's 255 world is found.

**Zig** (`tests/r7_ce55_ci.zig`): red on a7fe05d (5,000 of 20,000 on macOS's xargs), green on df8f08b.

### The composer's `drivers_stopped` (ba609dd): closed

**The change.** `driver_start_by` returns false when its slot wait reached the stop with no slot free. `run_drivers` then says `drivers_stopped` and ends the phase (composer.zig:820-827, 897-916).

**Model.**
- New property 15, "a timeline whose drivers' stop cut a start says drivers_stopped" (`ComposerProps.stopSaid`).
- Theorem `drivers_stop_said`: world 14 (a 400 ms driver holding the only slot, a 600 ms limit), decisions `[1, 1, 0]`.
  - Three starts are made and the fourth's wait reaches the stop at 300 ms.
  - a7fe05d says nothing; df8f08b says it.
  - No start comes past half the limit at either version.
- Searches:
  - a7fe05d's worlds 18 and 19 are found (`runs7/stopsaid-world18.txt`, `-world19.txt`);
  - df8f08b's worlds 14 and 17 are complete (5 and 18 timelines);
  - world 12 stopped at 20,000;
  - 5,000 drawn scenarios found nothing (`runs7/stopsaid-drawn.txt`).
- "No driver starts past half the limit" still holds: world 17 complete at 18, world 14 complete at 5, 5,000 drawn scenarios.
- No Zig test: the composer is the guest's, and the model was asked for here.

## CE32 to CE34, CE25, CE26 at df8f08b

### CE32 to CE34 (a resumed tree's numbers): closed by the `planned` lines; CE59's key collision remains

**The change.**
- `judge_plan_one` records each return's children's numbers as it plans them (main.zig:6492-6545).
- On resume, `Resumed.plan_note` keeps them under (generation, parent, moment) (2114-2118).
- `child_indices` gives them again whatever order the nodes come in (4765-4775).
- `index_settle` passes over every planned number (4754-4761).
- `return_recorded` makes no node when all of a return's numbers are recorded (2122-2127).
- `recorded_returns` reads the lines (7096-7111).

**Model** (`Resume4`, `ver := .vdf8f08b`).
- Theorem `ce32_ce33_ce34_closed`: round 4's minimal cases hold.
- Census (`runs7/resume4-census.txt`, 2,000 seeds a world): every property breaks in 0 runs in every df8f08b world, including two new ones where the stop comes while the judgment still plans. (a7fe05d's world breaks 1,079, 398, 1,472 and 155 of 2,000.)
- The model takes the last recorded generation as `rejudge_last` does: its returns are the judgment's own again, the planned keys keep their numbers, and the others take fresh ones.
- What remains is round 4's CE26 world, two returns to one moment. Two `planned` lines go under one key, and `plan_note`'s `put` keeps the last. Both makings get its numbers; the first's are passed over and never planned.
  - 491 of 730 runs keep a recorded timeline under another plan.
  - Theorem `ce59_one_key_two_plans_on_resume`.
  - Since CE26's fix this needs CE59's offsets.

### CE25 (the archive returns to repeats): closed

`archive_add_judged` (main.zig:7308-7314) keeps a repeat out of the cells.
- Theorem `ce25_ce26_closed`, first conjunct.
- Tree census, same_seed.py's world: "never returned to a repeat" breaks in 0 of 1,000 runs (round 6: 369 of 2,000).

### CE26 (two returns to one moment): closed in archive_returns; CE59 remains

`archive_returns` passes over a place the generation returns to already (main.zig:7482-7486).
- Theorem `ce25_ce26_closed`, second conjunct.
- Tree census (the first world): "distinct moments" breaks in 34 of 1,000 runs (round 6: 528 of 2,000). same_seed.py's world: 88 of 1,000 (round 6: 850 of 2,000).
- Every remaining case moves through `returns_earlier` (CE59).

## The recheck of the other counterexamples at df8f08b

`lake build` evaluates every earlier theorem against its model. Those not pinned to an older version now run on df8f08b's code, and all of them build:
- `ce43_drained_at_the_heal`, `ce43_starved_reader_said`, `ce44_still_past_the_hour`, `ce46_every_property_recorded`, `ce47_adopted_resume_keeps_its_exit` and `ce48_reasons_sized_from_the_tape`;
- CE1, CE2, CE3, CE5, CE9 to CE11, CE14, CE16, CE17, CE21, CE23, CE27 to CE30, CE35, CE37 to CE42.

Rounds 2 to 6's searches on code df8f08b did not change were rerun (`runs7/persist.txt`, `verdicts.txt`, `durable.txt`, `clock.txt`, `steer.txt`, `disk.txt`, `ce1-world4.txt`, `ce2-world16.txt`, `drawn-12.txt`, `ce5-world14.txt`, `stop-world17.txt`, `drawn-13.txt`). Each finds what round 6 found and nothing new:
- the documented non-fresh ascending-run wording;
- CE36's documented lost-writes case;
- CE44's census;
- 3939448's steering world;
- the drain's strict wording.

Status by number:
- **Fixed, code unchanged:** CE1 to CE3, CE5 to CE23, CE27 to CE31, CE35 to CE43, CE46 to CE48.
- **Fixed by df8f08b:** CE25, CE32 to CE34, CE49, CE52, CE54, CE55. CE45, CE50, CE51 and CE53 are fixed in part (above).
- **Still there:**
  - CE4's singleton (by design);
  - CE24: the same seed grows another tree with other workers or timing. df8f08b's e2e now works around it: the `tree` subcheck went to 192 timelines because "a tree's shape varied with the host's timing: 128 timelines steered 25 once and none the next time" (e2e.zig:6945-6949), and `changed` runs with 4 workers (9788-9791);
  - CE26's remainder (CE59);
  - CE44 (documented).

## New counterexamples (CE56 on)

### CE56: the coverage gate says an instrumented run from a snapshot runs uninstrumented (CE50's remainder)

**Property.**
- docs/SDKS.md:101-105: the gate is for a run without coverage.
- serve.zig:756-757, the remedy it writes: "its system runs without its language's instrumentation (coverage always); build its workload with it".
- serve.zig:779-782 (CE50's fix): such a run is "judged at its end, never stopped as uninstrumented".

**Minimal case** (theorems `ce50_closed_ce56_said` and `ce56_snapshot_run_said_uninstrumented`; `runs7/serve.txt`). Round 3's draws on an instrumented run from a snapshot:
- The setup ran edge 2 in the machine. The run's events/setup.jsonl is empty.
- Its 4 timelines repeat edge 2 and report no coverage. They are not stopped, since the run is exempt.
- When the run ends, `coverage_gate`'s `!going` branch (762-772) comes before the exemption. It finds no coverage in the store and none in setup.jsonl, and writes `uncovered`: "no coverage in its 4 timelines: its system runs without its language's instrumentation ... build its workload with it, or ask "coverage": "off" for a self-test".

The run's page and client show that line.

**How likely.** Runs from a snapshot are usually short. A fork's futures (`forks.asked` timelines from a session's moment) or a sandbox's replay (`checkpoint_steps`) whose timelines run only lines the machine had run before the snapshot report no coverage. Each of those gets the label.

**Zig path.** src/serve.zig:762-772 (before 776-783's exemptions), 707-727 (`setup_covered`).

**Test.** `tests/r7_ce50_coverage_gate.zig`, "round 7, CE56: a run from a checkpoint that ended is not said to run uninstrumented": red on both versions. Its control, a run of its own that ended without coverage is said uncovered: green on both.

### CE57: explain's `--draw <name>=<values>` counts one replay as m samples

**Property.**
- explain.zig:10-14: "`--draw <name>=0,1000` sets it to each value given instead, m times each".
- 29-34: a verdict per detail against its control by their 90% intervals. "Six variants once called a wait needed (0 of 6) that another six found half the time (3 of 6)."
- README_AI.md: every timeline replays bit-identically.

**Minimal case** (theorems `ce57_verdicts` and `ce57_one_history_needed`; `runs7/explain.txt`).
- A set value's m variants are the timeline's tape with one pull answered `v`, nothing else changed (explain.zig:509-516). They replay from one snapshot.
- So they are m copies of one deterministic history, and step 5's Wilson interval counts them as m samples.
- In a timeline where any history fails with probability 5/6, whatever the draw's value:
  - the control's 6 histories fail 5 times;
  - a set value whose one history does not fail reads "0 of 6: needed".
- `verdict(0, 1, 5, 6)`, the honest count, is "unclear".
- The removal's variants vary the control's draw too, "so its failures compare with the control's" (506-511). The set values' do not.

**How often.** Census over 100,000 seeds, a draw that decides nothing:
- 6 variants: needed in 15,507 with a value set, 2 with fresh values. Exactly: 1/6 × P(the control fails at least 4 of 6) ≈ 15.6%, against (1/6)^6 × 0.94 for fresh values.
- 3 variants: 9,659 against 279.

Any `--draw name=...` on a timeline whose failure is not certain once its history parts is affected: the doc's own use, Datomic's #3 clock step "removed, or under twice the interval".

**Zig path.** src/explain.zig:513 (`.value = draw.set orelse random.int(u64)`, one override), 109-119 (`verdict`), 328-345 (`Explanation.one`).

**Tests.** `tests/r7_ce57_explain_draw_set.zig`, against a copy of df8f08b's explain.zig with `fake-explorer.sh`, a timeline whose every history fails 5 times in 6:
- "each of a set value's m variants is a history of its own": red on df8f08b (1 distinct tape of 6);
- "a value whose one history does not fail is not called needed": red on df8f08b (set 8: "failing 0 of 6, verdict needed" against the control's 5 of 6);
- control, fresh values, 6 distinct tapes: green.

### CE58: a return past a full tape's marker from a cut timeline's archive or a strategy (CE53's remainder)

**Property.** As CE53: README_AI.md, every timeline replays bit-identically; docs/ANTITHESIS.md (Branching), "every timeline's path in its record and tape (it replays alone)"; main.zig:6552-6555 (df8f08b), "Past a full tape's marker a child's chain stops there and never replays".

**Minimal case** (theorem `ce58_cut_or_strategy_past_the_marker`; `runs7/tape6.txt`).
- A cap of one override; the parent's pulls are a draw and two overrides, so its tape is full at pull 2.
- Two ways to a return at moment 3:
  - the parent was cut at its horizon, and `archive_add` takes a cut timeline's moments to its end (main.zig:7374: `open = summary.cut or at < summary.last_pull_ns`, whatever `last_pull_ns` now holds);
  - a strategy's return is bounded by the timeline's start and end alone (7632). Its candidates are offered `end_ns`, not `last_pull_ns` (7606-7617).
- The child of a holder there runs, and its chain stops at the marker.

**How likely.** Rare, as CE53: 1,048,576 overrides before a horizon cut, or a plugin strategy.

**Zig path.** src/main.zig:7374, 7632, 7606-7617.

**Test.** `tests/r7_ce53_archive.zig`, "round 7, CE58: nor in a timeline cut at its horizon": red on both versions.

### CE59: two returns at one moment again through `returns_earlier` (CE26's remainder), and one key on resume

**Property.**
- df8f08b's test "a generation never returns twice to one moment" (main.zig:6072).
- CE26's fix's comment (7482-7486).
- On resume, "every index keeps its timeline" (Resume4's properties).

**Minimal case** (theorems `ce59_offsets_meet` and `ce59_one_key_two_plans_on_resume`; `runs7/tree-dup.txt`).
- CE26's fix compares archive places with the returns already listed. The list is then moved by `returns_earlier` (6699, 7207-7226).
- A return with `earliest_ns` lands earlier by an offset from `--return-offsets` (0 half the time, else 1, 5 or 30 s). That covers the frontier's and every archive cell's (7498).
- Two distinct moments of one timeline that differ by 1, 4, 5, 25, 29 or 30 s become one. The census world's seed 20: archive places #0@23 and #0@8; the first moves 15 µs (the model's scale): both at #0@8.
- Two nodes and their branches at one moment follow. So do two `planned` lines under one key, of which a resume keeps the last: the first making's numbers are passed over and never planned, and the second's are queued twice.

**How likely.** Uncommon. Two returns on one timeline whose moments differ by exactly one of those sums, to the nanosecond. In deterministic VMs with periodic timers and no CPU modulation, events exactly N seconds apart are plausible. The tree census still finds 34 of 1,000 runs in its scaled world.

**Zig path.** src/main.zig:6697-6699, 7207-7226, 7498; 2114-2118 (`plan_note`'s `put`).

**Test.** `tests/r7_ce59_returns_earlier.zig` (`returns_earlier`, `TreeReturn`, `return_offsets_default` verbatim):
- "a generation's returns, moved earlier, never meet at one moment": a frontier return and an archive place 5 s apart on #0, over 64 seeds. Red on both versions: 6 of 64 meet.
- Control, 3 s apart: green.

### CE60: a command-line run's injector reaches its analyses under another name (CE51's remainder)

**Property.** As CE51:
- main.zig:1443-1446 (df8f08b): "in the guest's command line or its initramfs, so an analysis of a run started with one booted other inputs and was refused";
- docs/PLUGINS.md:149-151: injectors "go on the system disk (`/det/injectors/<name>`, part of the run's inputs)".

**Minimal case** (theorem `ce60_injector_by_another_name`; `runs7/request.txt`). A command-line run with `--injector ./chaos`:
- The run boots `chaos` as given. Its system disk holds `/det/injectors/chaos`, and the disk's name hashes each injector's basename (prepare.zig:195-199, 1464-1471).
- `run_request_write` records the kept copy, `<hash>-chaos` (runs.zig:217-219), and changes nothing of what the run boots.
- The analysis's `--injector` is the kept copy. It builds another system disk with another basename, which inputs_hash covers (main.zig:8967-8969). Every tape is refused (TapeInputsDiffer), as before the fix.

serve's own runs keep the copy before they start and are unaffected.

**How likely.** Any command-line run with an injector of its own (docs/PLUGINS.md's `--injector`, the e2e `injectors` check). Then every analysis of that run fails: causality, explain, sessions, replays.

**Zig path.** src/main.zig:1449-1453; src/runs.zig:212-219; src/prepare.zig:195-199, 1464-1471.

**Test.** `tests/r7_ce51_request.zig`, "round 7, CE60: an injector reaches the analysis under the name the run's system disk has": red on both versions ("the run's injector: chaos; the analysis's: 056e8453348f0063-chaos").

## Round 6's list

### corrupt_reads

**The reader dies during its fault** (`Disk5.readerDies`, `Disk7`; theorem `dead_reader_unsaid_or_stranger_killed`; `runs7/disk7.txt`).
- The heal's `pidfd_open` fails with ESRCH (`watched` false). Nothing waits, kills or is said; `rmdir` succeeds, and the reads after the death are never named. "Named, or said" is found.
- If another process took the pid, the heal waits 2 s for it, says "drain", and SIGKILLs it. The new property "a heal kills its own reader and no other process" is found. 62e06e3 killed a stored pid at once too.
- With a reader that lives, both properties hold at df8f08b: complete at 396 and 8,856 timelines.

How likely: low. The reader is in det-faults' process group, which `faults_stop` signals by pid alone (composer.zig:368-375). A cgroup OOM stays in its node's cgroup. A guest-wide OOM picks by badness, and the reader is a few hundred KB. So only a guest-wide OOM with nothing larger could kill it, and pid reuse needs the pids to wrap meanwhile. Not counted as a counterexample.

**Aimed extents reused by another file** (read). `disk_corrupt_read` names the aimed file for every read inside the extents captured at the fault's start (nodes.zig:2276-2283). A file that gets those blocks after the aimed one is deleted or truncated has its reads named under the aimed file's name; ext4 reuses freed blocks once their transaction commits. An LSM store compacting during the fault does that. The sectors and bytes are right, and no judge in the platform reads `file` (only the e2e counts the events: e2e.zig:7514). So this is a note.

**Per-CPU trace clocks** (read). Deterministic VMs have one vCPU (`vcpus: u32 = 1`, main.zig:414; vm.zig:403). One per-CPU buffer means the marker is ordered after every line traced before it, so the property holds. Fast VMs (several vCPUs) inject no corrupt_reads in their own runs. If one did, `enable` = 0 is written after a synchronize, and the marker after that, with KVM's stable clock across vCPUs.

### Records past 256 MiB (read; no long run's record here)

`run_file` reads with `.limited(256 << 20)` (serve.zig:173, 6832-6836). Past it, each read fails and is caught as "":
- `run_show` (2348) shows no run, summary or changed line;
- `ended_status` (5942-5952), without an `exit`, reads "interrupted";
- `summary_workers` (6533) reads 0 workers.

df8f08b adds a `planned` line a return and a `catalog` line a run end, a few hundred bytes each. A record line holds every evaluated property (CE46's fix). With 100 properties of about 150 bytes, a run passes the cap at about 17,000 timelines; with a CI shard's 2,000 tests, at about 870. serve.zig's own comment cites a 360 MB summaries file for Kafka run 1919. I had no long run's record to measure, so this stays arithmetic.

### The tree with a full tape

- Returns land strictly before the marker: archive `<`, frontier clamp (CE53 above). The marker's exact moment never gets a return.
- An archive cell's place from an earlier generation took that generation's `last_pull_ns`, which now includes its `tape_full_ns`, unless the timeline was cut. The cut case and a strategy's return remain: CE58.

### A run line ending in `&`, and xargs's other stops

Zig, `tests/r7_ci_other_stops.zig`:
- **A runner killed by a signal** (xargs stops at a command terminated by a signal). Test "an exec'd runner killed by a signal leaves every test of the shard judged":
  - red on 62e06e3 (5,000 of 20,000: the exec'd runner was xargs's command);
  - green on a7fe05d and df8f08b (the subshell's 137 goes to xargs as a status).
  - Only a runner that kills its whole process group (`kill 0`) would stop xargs now.
- **A run line ending in `&`.** The move runs before the backgrounded runners write, every runner writes the same path, and the last batch's report is what the command leaves:
  - 5,000 of 20,000 names at a7fe05d and df8f08b;
  - 0 at 62e06e3 (`&;` is a syntax error).
  - Such a run line is broken under any CI, and the job's unreported timelines are counted (CE37's fix). This is a note.

### The SDK against df8f08b's `sdk/lean`

df8f08b's `sdk/lean` differs from the replica's `upstream/sdk/lean` in these places:
- `Relation.lean` (Plus/Star closures), which is new;
- `Disk.lean`: corrupt records, misdirected writes, `Write.covers`;
- `Determinismo.lean`, the tests and the README.

`Census.lean` was already there. `scratch/sdk7/` builds the whole replica, `Replica` and `replica7`, against df8f08b's `sdk/lean`: 153 jobs, all succeed (`runs7/sdk7-build.txt`). The replica uses neither `Disk` nor `Relation`, so nothing needed changing. The main build stays on `upstream/sdk/lean`.

## Other findings (not counterexamples)

- **A comment in a test case's body** fails the case: `element_index` skips no comment (CE49 above).
- **An extended session at a full parent tape** asserts in `session_end` (CE52 above).
- **The catalog line of a run of several scenarios** goes to the last scenario's record only. `report.record` after the scenario loop (main.zig:1175) writes to whichever record is open. A resume of an earlier scenario's complete run reads no catalog. Read, not modeled.
- **CE24 in the e2e.** df8f08b's e2e raised the steered subcheck from 128 to 192 timelines, and gave `changed` 4 workers, because the tree's shape varied with the host's timing. That is CE24's symptom in the platform's own checks.

## What was replicated, and what is not exact

Replicated at df8f08b, with file and lines:
- the composer's stop said on a cut start;
- junit's `case_index` and comment-aware `captured_end`;
- CI's 255 → 254;
- tapes: `write_step`'s stream, `step_line_parse`, `step_record`'s cap with det:over's room, returns before the marker;
- corrupt_reads: `read_corrupted_parts`, and a reader's death with pid reuse;
- serve: the gate's exemption and its end label;
- the request's fields and machine flags;
- the record's catalog line;
- the tree: `planned` lines, `child_indices`, `index_settle`, `return_recorded`, `archive_add_judged`, archive_returns' one moment;
- explain's named draws and verdicts.

Not exact:
- The resumed tree's model judges one generation and takes the last recorded one as `rejudge_last` does. Earlier generations replaced by `recorded_returns` are not modeled.
- Explain's model has one detail and one control. Each distinct tape's outcome is a decision, not a system.
- The reader's death is a step of its own, and pid reuse is a decision.
- The Zig harnesses copy declarations verbatim but shim what they call (listed above). Two of them wrap statements taken from larger functions.
- Rounds 1 to 6's simplifications still hold.

## Assumptions

- dm-flakey changes byte `corrupt_bio_byte` of each read clone over its segment. dm splits a bio only at target boundaries (`max_io_len` 0 for flakey and linear). `block_bio_queue` traces a bio once (`BIO_TRACE_COMPLETION` kept by `bio_trim`).
- xargs (GNU, BSD, busybox) stops at a command that exits 255 or is killed by a signal; a subshell's 128 + n is an ordinary status to it.
- A replay is deterministic: identical tapes from one snapshot are one history.
- A tracepoint's `enable` = 0 returns after in-flight handlers finished.
- `pidfd_open` of an exited process that was reaped fails with ESRCH.
- Rounds 1 to 6's assumptions hold.

## Properties, with sources (7 new or restated)

1. A timeline whose drivers' stop cut a start says `drivers_stopped` (composer.zig:820-823, docs/AGENTS.md:300-302). Fails at a7fe05d; holds at df8f08b.
2. The coverage gate says a run's system runs without its instrumentation only when it does (serve.zig:756-757, 779-782). Fails (CE56).
3. A detail is called needed only when its value decides the failure more than the control's histories do (explain.zig:29-34). Fails for set values (CE57).
4. A generation never returns twice to one moment (main.zig:6072). Fails through `returns_earlier` (CE59).
5. An analysis boots the inputs its tapes were recorded with (main.zig:1443-1446). Holds for five flags; fails for `--injector` (CE60).
6. A corrupt_reads heal kills its own reader and no other process (nodes.zig:2383). Fails when the reader died and its pid was reused (read as unlikely).
7. A resumed run's verdict is the run's, its catalog's included (main.zig:2336-2338). Holds for a complete run resumed again; fails for a stop before the end, a session's number, and an interrupted run's lost declarations (CE45).

## Search runs (`runs7/`)

- `junit.txt`: 3 properties × 7 worlds. The df8f08b worlds are complete (up to 961). a7fe05d's printed-cases world is found, and so is the comment world. The old 3939448 last-batch model is found again, as in round 6.
- `tape6.txt`: steps (7 worlds) and full tapes (6 worlds). df8f08b's step worlds and uncut tape worlds are complete. a7fe05d's worlds and the cut and strategy worlds are found.
- `aimed.txt`: df8f08b complete at 2,280 and 59,840, stopped at 200,000 for 5 blocks, with the censuses (0 wrong); a7fe05d found (532 of 7,417 wrong).
- `ci.txt`: the 255 world holds at df8f08b and is found at a7fe05d; every run line form holds; 62e06e3's and 3939448's worlds are found.
- `serve.txt`: the stop holds at df8f08b and is found at a7fe05d; the label (CE56) is found at every version; sessions hold.
- `request.txt`: df8f08b's command-line world is found through `--injector` alone (CE60); serve's runs are complete at 256; older recordings are found.
- `resume.txt`: df8f08b's catalog worlds are found through CE45's remaining paths; the evaluated-property worlds hold.
- `resume4.txt`, `resume4-census.txt`: every df8f08b world holds but the CE26 world (CE59 on resume); a7fe05d's are found.
- `tree-census.txt`, `tree-dup.txt`: CE25 at 0; CE26 from 528 of 2,000 to 34 of 1,000 (CE59).
- `disk7.txt`: a dying reader found for both properties; a reader that lives holds.
- `explain.txt`: found for set values, and the censuses.
- `stopsaid-world18.txt`, `-world19.txt` (a7fe05d) found; `stopsaid-world14.txt`, `-world17.txt`, `-world12.txt` and `stopsaid-drawn.txt` hold; `stop-world17.txt`, `ce5-world14.txt` and `drawn-13.txt` hold.
- `persist.txt`, `verdicts.txt`, `durable.txt`, `clock.txt`, `steer.txt`, `disk.txt`, `ce1-world4.txt`, `ce2-world16.txt`, `drawn-12.txt`: as in round 6.

The Zig runs (`scratch/zig7/run-all.sh`, `runs7/*-zig.txt`), Zig 0.17.0 with the global cache:
- CE45: red a7 (0) / green df.
- CE49: red a7 / green df.
- CE50: red a7 / green df (control green).
- CE51: red a7 / green df (control green).
- CE52: 3 tests, red a7 / green df.
- CE53: red a7 / green df.
- CE54: red a7 / green df (control green).
- CE55: red a7 (5,000) / green df.
- Red on df8f08b: CE45's session path; CE56; CE57 (two tests, control green); CE58; CE59 (control green); CE60.
- xargs's signal stop: red 62e06e3 / green a7 and df.
- A run line ending in `&`: red on all three (a note).

## Theorems (25, `Replica/Theorems7.lean`)

General (for every input):
- `replay_before_the_marker`
- `ce54_closed`
- `ce54_parts_are_the_changed_bytes`
- `subshell_parts_df`
- `ce55_closed`
- `ce51_closed`

The fixes, by computation:
- `ce49_closed`
- `ce52_closed`
- `ce53_closed`
- `ce54_minimal_cases_named`
- `ce45_closed_for_a_complete_run`
- `ce50_closed_ce56_said`
- `drivers_stop_said`
- `ce32_ce33_ce34_closed`
- `ce25_ce26_closed`

What the fixes leave, and new counterexamples, by computation:
- `df_comment_in_a_body_fails_its_case`
- `ce45_interrupted_run_loses_declarations`
- `ce56_snapshot_run_said_uninstrumented`
- `ce57_verdicts`
- `ce57_one_history_needed`
- `ce58_cut_or_strategy_past_the_marker`
- `ce59_offsets_meet`
- `ce59_one_key_two_plans_on_resume`
- `ce60_injector_by_another_name`
- `dead_reader_unsaid_or_stranger_killed`

Pinned this round:
- Theorems6: CE49, CE50, CE52 and CE53 to `.va7fe05d`.
- Theorems4: CE32 to CE34 to `.va7fe05d`.
- Theorems3: CE26 to `.va7fe05d`.

Theorems5's proofs about `Ci5.step` needed `Ver.sinceA7` in their simp sets. All 187 build jobs succeed; against df8f08b's SDK, all 153.

## Library gaps

- Moving a model's default version meant pinning every theorem that read the default and whose code changed. A version-indexed theorem set, or a check that lists theorems whose result changes with the default, would make this mechanical.
- `native_decide` on Float (Wilson's interval) works, but the SDK has no exact interval or binomial arithmetic. A rational Wilson bound would let `ce57_verdicts` be a `decide` proof.
- `Determinismo.census` (the SDK's) counts an exhaustive space. A census over seeds with per-property counts (Aimed6, Explain7, Resume4) is still written by hand each round.
- Proving `parse (record items) = written items` for the tape needs loop invariants over `for ... in` with mutable state. There are no lemmas for `Id.run do` loops, so the steps' fix is checked by exhaustive search, not proved.

## Left for round 8

- Run round 7's tests in the platform's tree. The excerpt harnesses for serve.zig and main.zig shim their callers; the platform's own form needs duckdb and Linux.
- CE45: record each timeline's declared catalog entries, then recheck the three paths.
- CE56, CE57, CE58, CE59, CE60, and the comment in a case's body.
- The resumed tree's earlier generations replaced by `recorded_returns`, and whether a pipelined judgment can be cut before all its returns are planned.
- Records past 256 MiB on a real long run's record.
- Still open from earlier rounds: CE4's singleton (by design), CE24, CE44 (documented).

## What I couldn't do

- Run any test in the platform's tree or on Linux. Every Zig test ran on the Mac against copies of the files: whole files for junit, ci and tape; verbatim declarations with shims for nodes, serve and main; explain with a stand-in explorer.
- Measure a long run's record: I had none in my directory, so records past 256 MiB stay arithmetic.
- Model the resumed tree's earlier generations (`recorded_returns` replacing a judgment's returns).
