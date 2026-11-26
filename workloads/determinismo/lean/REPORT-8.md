# determinismo in Lean: round 8

## What this is

Round 8 of the Lean 4 (v4.36.0) replica of determinismo. The platform's next branch is now c4f246e, a plain copy in `upstream-c4f246e/` (its commit in `.commit`). Round 7's baseline df8f08b stays in `upstream-df8f08b/`.

The 7 commits change 8 files: `src/{cpus,explain,main,prepare,report,runs,serve,strategy}.zig`. Each diff is in `scratch/r8/*.diff`. No file under `guest/`, `src/core/`, `src/products/` or `sdk/` changed, so the models of junit, CI, the composer, the fault injector, tapes' steps, corrupt_reads and the clock are c4f246e's code as they stand.

The models follow c4f246e where its code changed:
- `Ver` (`Replica/Prelude.lean`) gained `.vc4f246e`. `Ver.sinceA7` and `Ver.sinceDf` hold for it; `Ver.sinceC4` is new.
- These defaults moved to `.vc4f246e`: Serve3, Explain7, Tape6, Tree, TreeRun, Resume5 and Request6. The other models keep `.vdf8f08b`, whose code is c4f246e's.
- Round 7's theorems about df8f08b's code of those models are pinned to `.vdf8f08b` (Theorems7).

Changed models (each change threads the version):
- `Serve3.lean`: the end's label skips a run from a checkpoint or a fork's snapshot (CE56's fix). New property: an uninstrumented run that ends is said uncovered.
- `Explain7.lean`: `variant_items`, where a set value's variants vary the control's draw. New: `controlLive`, whether the control's pull still varies the value's history.
- `Tape6.lean`: `open_to_end` and `returns_end`. New world: a strategy's return to a timeline of an earlier generation.
- `Tree.lean`, `TreeRun.lean`: `returns_earlier` never lands on a taken moment.
- `Resume5.lean`: `declared` lines, `catalog_seen`, a drained run resumed twice (`resumedExitAfterDrain`), and a run of two scenarios (`resumedExitScenarios`).
- `Request6.lean`: `injectors_keep`. Injector paths are now lists of parts, so the closing theorem is general.

New files:
- `Replica/Theorems8.lean`: 9 theorems.
- `Main8.lean`: the `replica8` executable.
- `tests/r8_*.zig`: round 8's Zig tests.
- `scratch/zig8/`: the harnesses (`build-*.sh`, shims, `run-all.sh`).
- `scratch/round8.sh`: the searches.
- `runs8/`: their output.

Commands:

    lake build
    .lake/build/bin/replica8 resume|serve|request|tape6|explain <exhaust>
    .lake/build/bin/replica8 treecensus <seeds>
    scratch/round8.sh
    scratch/zig8/run-all.sh

## How the Zig tests run

As in round 7: a Zig `test` block, run against copies of df8f08b's and c4f246e's files, built with Zig 0.17.0 through the job slots. Outputs are in `runs8/<harness>-<df|c4>-zig.txt`. "Red" means the test fails on that version; "green" means it passes.

Harnesses:
- **Copied whole:**
  - `explain.zig`, with its scratch directory moved under the replica's and shell scripts standing in for `determinismo explore`;
  - `bundle.zig`, with its `core` import (cpuid, kvm, vm) shimmed. The test's run names its own `--cpuid`, so the shim is never called.
- **Declarations copied verbatim** by `scratch/zig8/tools/extract.py` after a shim header, each marked with its file and lines:
  - `main.zig`: resume, the archive, `returns_earlier`, `run_request_write`, `run_scenario`;
  - `serve.zig`: the coverage gate, `RunRequest`, `system_arguments`;
  - `runs.zig` (c4f246e): `artifact_keep`, `artifact_keep_named`, `keep_once`, `injectors_keep`;
  - `cpus.zig` (c4f246e): `podman_cpuset`, `cpuset_within`, `given`, `set_add`, `set_has`.
- **Statements taken from inside functions, keeping their line numbers:**
  - main.zig:1170-1175, the run end's catalog lines;
  - main.zig:4125-4126, the summary's `last_pull_ns` and `tape_full_ns`;
  - report.zig:553-568, the declared lines;
  - report.zig:658-688, three `Multiverse` methods (`aggregate_known`, `aggregate_find`, `merge`).

What the shims replace:
- `linux` calls, through libc;
- the record, kept in memory;
- report.zig's `Multiverse` and `Catalog` in the resume harness: the catalog as `catalog_reached` and `Catalog.judge` decide it, for the kinds used;
- `Events.Property`.

## The recheck of round 7's counterexamples at c4f246e

### CE45 (a resume's catalog): closed on its three remaining paths; CE61 and CE63 remain

**The change.**
- report.zig:553-568: a declaration no earlier timeline of the worker had is written as `{"declared":...}`.
- main.zig:2323: `resume_read` collects them.
- main.zig:2136: `merge_into` merges them with hits 0, so they are in the catalog and reached only where a timeline reached them.
- main.zig:2319-2322, 2364: a complete resume short-circuits only when the record has a catalog line (`catalog_seen`). Otherwise it ends as a run does.

**Model.** Theorem `ce45_paths_closed`: at c4f246e each path exits 3, as the run does:
- a complete run resumed again;
- a stop after the last timeline's line and before the run's end;
- a session's timeline holding one of the run's numbers;
- a run stopped after its first timeline, the rest not declaring "r".

Searches (`runs8/resume.txt`) at c4f246e:
- Each world is complete with none broken: 768, 768, 486, 1,536 and 1,024 timelines.
- The new world drawing every path at once is complete at 156,250 timelines: three timelines, a reachable and a sometimes declared, a session, the stop before or after the end.
- df8f08b's paths are found again.

**Zig** (`tests/r8_ce45_resume.zig`). Each version's run writes its own record (c4f246e's with its `declared` lines). `resume_read` runs verbatim in a child process; when the run is not complete, the child goes on the explorer's way (`merge_into`, then the catalog and the run's end lines, verbatim).
- The complete run resumed again: green on both.
- The session path, the stop before the end and the interrupted run: red on df8f08b (0), green on c4f246e (3).

**What the recheck asked for:**
- **Resumes of resumes.** The record keeps every line of every resume, so a later resume merges all of them. One case fails: a run whose earlier end wrote a catalog line over part of its timelines. That is CE61 (a drain).
- **A run stopped before its first worker reported.** Nothing is recorded but the run line, so every timeline runs again. This is the model's `recorded = 0`; it holds.
- **A catalog line written before the run's end.** A drained run's end writes one (CE61). After the run's end: the catalog line of a run of several scenarios goes to the last scenario's record alone, and each scenario's run is resumed as that scenario alone (CE63).
- **Sessions.** Sessions write no `declared` lines. An extending timeline sets `report.record_branches_only` (main.zig:2794), and `record` writes only `branch` lines then (report.zig:46-48). So a session's declarations never reach a resume's catalog.
- **A tree.** Its declared lines are written once per timeline, not once per run (CE65).

### CE56 (the gate's end label on a run from a snapshot): closed

**The change.** serve.zig:766-770: the end returns before the label for a request with `checkpoint` or `from_snapshot`.

**Model.**
- Theorem `ce56_closed_and_its_note`, first conjunct: round 7's draws are not labeled at c4f246e. The second conjunct shows df8f08b labels them.
- `runs8/serve.txt`: the label property is complete at c4f246e (46,042 timelines) and found at df8f08b and a7fe05d. The stop property is unchanged.

**Zig** (`tests/r7_ce50_coverage_gate.zig`, round 7's): CE56's test is red on df8f08b and green on c4f246e. Its control and CE50's tests are green on both.

**What it leaves** (a note; the gate cannot tell). A run from a checkpoint or a fork's snapshot of an uninstrumented system is never said to run blind.
- Its timelines report no coverage, but the end returns before the label.
- CE50's exemption comment (serve.zig:784-787) still says such a run is "Judged at its end, never stopped as uninstrumented". At c4f246e it is judged nowhere.
- The new property, "a run of an uninstrumented system that ends unstopped is said uncovered at its end" (serve.zig:692-694), is found in `runs8/serve.txt` and is the third conjunct of the theorem.
- The machine or run the snapshot came from had its own setup.jsonl, which the gate could read instead.

### CE57 (explain's set values): closed when the control's pull still varies the value's history; CE62 remains

**The change.** explain.zig:543-597 (`variant_items`): each of a set value's m variants varies the control's draw beside it (`count = 2`). With no control, the value runs once.

**Model.**
- Theorem `ce57_closed_ce62_left`: a value set with 6 variants replays 7 histories at df8f08b and 12 at c4f246e.
- Census (`runs8/explain.txt`, 100,000 seeds, a draw that decides nothing, 6 variants): "needed" in 2 explanations at c4f246e, the same as with fresh values. df8f08b: 15,507.
- The 6-variant search stopped at 100,000 timelines with none broken.
- With 3 variants, the "found" is the same for fresh values (279 per 100,000). That is 3 variants' own limit, not this.

**Zig** (`tests/r7_ce57_explain_draw_set.zig`, round 7's three tests, on a copy of c4f246e's explain.zig): all green on c4f246e. On df8f08b the two counterexample tests are red and the control is green.

**What it leaves:** CE62 below.

### CE58 (returns past a full tape's marker): closed for the archive, the frontier, an extension, this generation's strategy, and resumes; a strategy's return to an earlier generation remains (a note)

**The change.**
- main.zig:6606-6614: `open_to_end` is `cut and no full tape`; `returns_end` is the end, or the marker if the tape was full.
- They are read by the frontier (7065), the archive (7502), the extension (7801), and the strategy's offer and check (7737, 7760).
- main.zig:4126: Summary keeps `tape_full_ns`.
- main.zig:2394-2408, 2502-2503, 2539: SummaryHeader carries it, so a resumed tree's summaries know it (state_format 7).

**Model** (`Tape6`, `runs8/tape6.txt`).
- At c4f246e every world is complete with none broken: the uncut parent with and without holders, the cut parent, this generation's strategy, a cut parent with a strategy, a cap of two overrides over 5 pulls cut or not (52 to 324 timelines).
- df8f08b's cut and strategy worlds are found again.
- Theorem `ce58_closed_but_earlier_generations`.

**Every path, read.**
- The frontier clamps to `min(end_ns, last_pull_ns) - return_after_ns`, and `last_pull_ns` already stops at the marker.
- `objective_place` only moves a place earlier.
- `returns_earlier` only moves returns earlier.
- The archive's places need `open_to_end or at < last_pull_ns`.
- A resumed tree loads `tape_full_ns` with each summary.
- The tree census at c4f246e (`runs8/tree-census.txt`): "every branch point comes before its timeline's last randomness pull" breaks in 0 runs in each world without a strategy that answers returns. It still breaks where a strategy answers returns, as in round 7 (330 and 358 of 1,000).

**Zig** (`tests/r7_ce53_archive.zig`, round 7's, with c4f246e's two summary statements): CE58's test is red on df8f08b and green on c4f246e. CE53's is green on both.

**What it leaves** (a note).
- tree_returns (main.zig:7753-7762) checks a strategy's return against the timeline's span only when the timeline is among this generation's candidates. A return to a timeline of an earlier generation passes `planned.contains`, unchecked.
- The model's world "a strategy's moment in a timeline of an earlier generation" is found.
- In the platform, the node there is made by a replay, which stops at the marker (no node), or from a holder on disk at or past the marker with no pull before the moment (`disk_node`, main.zig:8071-8085).
- So it needs a strategy, a full tape (1,048,576 overrides) and such a holder. I did not trace how long an earlier generation's disk holders live, so this stays a note.

### CE59 (two returns at one moment): closed, on resume too

**The change.** main.zig:7258-7290: `returns_earlier` never moves a return onto a moment another return of that timeline has, taken from the list as moved so far.

**Model.**
- Theorem `ce59_closed`: the census world's seed 20 holds at c4f246e and breaks at df8f08b.
- Tree census (`runs8/tree-census.txt`): "distinct moments" breaks in 0 of 1,000 runs in all seven worlds, strategies included. Every census header says "0 with two returns at one moment". Round 7: 34, 49, 88, 63, 18 and 27 of 1,000.
- The returns that stayed put shift "a return to an optimize bucket lands at its best state" by a few runs (for example 637 to 632). That property breaks by design, since returns land earlier.

**On resume.** The planned-key collision (round 7's `ce59_one_key_two_plans_on_resume`) needs two returns at one moment.
- Without a strategy, the list before `returns_earlier` has none: the fill takes one return per timeline, and `archive_returns` passes over places already listed. `returns_earlier` no longer makes one.
- `recorded_returns` builds its returns from the planned keys, which are distinct.
- A tree with a strategy does not resume (main.zig:2277-2281).
- So the Resume4 world (two returns at one moment by construction) no longer arises. Its model's code (`plan_note`) is unchanged.

**Zig:**
- `tests/r7_ce59_returns_earlier.zig` (round 7's): red on df8f08b (6 of 64), green on c4f246e.
- New, `tests/r8_ce59_returns_earlier_many.zig`: 2,000 lists of 2 to 6 returns on two timelines at whole seconds 30 to 41, moved or not, a seed each. 104 lists meet on df8f08b; 0 on c4f246e (green).

**Left as it was** (a note). A strategy's returns are never moved (`earliest_ns` null) and never checked against each other. A plugin that lists one moment twice still gets two nodes there. A plugin asks for several branches at one moment through `branches`, so this is the plugin's mistake, and such a tree never resumes.

### CE60 (a command-line run's injector): closed

**The change.** runs.zig:227-262: `injectors_keep` keeps each injector as `<data>/artifacts/<hash>/<name>` (`artifact_keep_named`). main.zig:1449 uses it.

**Model.** Theorem `ce60_closed`, general: for every command-line run, c4f246e's analyses boot the inputs its tapes were recorded with. The system disk hashes each injector's basename and content (prepare.zig:196-200), and the kept copy keeps the basename. In `runs8/request.txt`, c4f246e's command-line and serve worlds are complete at 256; df8f08b's is found.

**Zig** (`tests/r7_ce51_request.zig`, round 7's, with c4f246e's keeps verbatim): CE60's test is red on df8f08b ("056e8453348f0063-chaos") and green on c4f246e ("chaos").

**Read, no new case:**
- Two injectors with one basename are one file on the run's own disk too (prepare.zig:1470-1475: the second overwrites). The kept copies keep both names and contents in order, so the hash agrees.
- The guest picks among the names sorted (composer.zig:72-77). A serve run's names are `<hash>-<name>` (serve.zig:2139-2149, unchanged), so its order can differ from a command-line run's with the same files. Each run's own analyses agree.
- What still leaves the run's injectors behind is a bundle (CE66).

## The new code

### `src/cpus.zig`'s `podman_cpuset` (cf7587a)

It reads `/sys/fs/cgroup/user.slice/user-<uid>.slice/user@<uid>.service/cpuset.cpus.effective`, intersects it with the process's affinity (`given()`, read before any pin narrows it), and gives the list to `podman build --cpuset-cpus` (prepare.zig:1345-1346) and to an `image:` strategy's `podman run` (strategy.zig:193-199).

What I checked:
- The path buffer of 160 bytes holds two 10-digit uids (93 bytes).
- `cpus_max` (1,024) bounds the ranges parsed, and `linux.cpu_set_t` holds 1,024 CPUs.
- strategy.zig's comptime check leaves the two argument slots.
- `given()` is cached before a pin (cpus.zig:1462), so a pinned worker still gives its run's CPUs.
- Malformed ranges are skipped.

Findings:
- **CE64** (below): one 512-byte read.
- **srv4's case is unchanged, by design.** The function's own test, and the isolation in infra/host/isolate.sh, put the user slice on the reserved CPUs. The hunt's CPUs and the user manager's are disjoint, so the result is null and builds still run on the sessions' CPUs. The function says so ("the build runs where the slice lets it").
- **No file is not no cap** (an assumption about cgroup v2, unverified here). The file exists only where the cpuset controller is enabled at the user manager's cgroup. On srv4, isolate.sh's `service.d` drop-in and its `set-property` on every active unit enable it.
  - On a host without isolation (serve.sh with no reserved cores), nothing enables it. The code reads "no cap" and passes the process's whole CPU list.
  - The cap, where there is one, belongs to the nearest cpuset-enabled ancestor, not necessarily the user manager.
  - What rootless podman (or buildah, under `podman build`) does with `--cpuset-cpus` when the cpuset controller is not delegated is outside my copies. If it refuses, every image build on such a host fails; if it warns and drops the flag, nothing changes. A check on a host without isolate.sh would settle it: `cat /sys/fs/cgroup/user.slice/user-$UID.slice/user@$UID.service/cgroup.controllers`, then `podman build --cpuset-cpus 0 ...`.

### The state formats 7 and 8

**An older run resumed by this build.**
- **Through serve.** `core_same` (serve.zig:2824-2831) compares the run's `state_format` with the server's, so a run of format 6 or 7 resumes and replays on its own kept explorer (`explorer_of`, 2810-2819; `run_resume` and `resume_note`).
- **From a command line.** `resume_read` reads no format. A flat run's record lines only gained optional fields, so it resumes as before.
- **A tree's summaries.** The format byte is at offset 41 in both layouts, and `summary_format` (2) did not move when SummaryHeader grew from 64 to 72 bytes:
  - The first summary is read 8 bytes long.
  - The second header is read 8 bytes into the first record's behaviors, so its format byte is the first record's `jitter_seed` byte 1.
  - That is almost always another value than 2, so the resume ends with `SummariesOfAnotherBuild`. A lone summary is not indexed, so its timeline runs again.
  - The refusal holds by that misaligned byte, not by a check of the format. Bumping `summary_format` with SummaryHeader, or checking `state_format` in `resume_read`, would make it hold by design.

**A run of this build read by serve's ingest.**
- `store.ingest` reads `timelines.jsonl` (store.zig:839-907), whose columns did not change. Serve does not read the summaries file, beyond checking that it exists (serve.zig:5703-5707).
- The record's new `declared` lines:
  - `run_show` copies only lines starting with `run`, `summary`, `snapshot` or `changed` (serve.zig:2408-2414);
  - `recorded_status` and `summary_workers` look for `{"summary":`, which a declared line's JSON-escaped message cannot contain unescaped.
- So ingest reads a c4f246e run as before. The only effect is the record's size (CE65).

## New counterexamples (CE61 on)

### CE61: a drained run's catalog line is taken as a complete run's verdict (CE45's remainder)

**Property.**
- main.zig:2365-2367 (c4f246e): "Judged from its record, as the run that recorded it would have been".
- RecordLine.catalog (main.zig:2266-2268): "the run's catalog judged ... the last such line the run's verdict".
- docs/ANTITHESIS.md's catalog: an assertion no timeline reached fails the run.

**Minimal case** (theorem `ce61_drained_catalog_line`; `runs8/resume.txt`). Three timelines; the first two declare reachable "r", the third reaches it.
1. The run is drained after two timelines (serve's `?drain=1`: SIGUSR2, `drain_requested`, main.zig:5234-5272: no timeline starts, the explorer ends as a run does). Its end judges the catalog over those two, so "r" is unreached, and writes `{"catalog":{"failing":1}}` (main.zig:1170-1175).
2. serve marks a drained run stopped, so it is resumable (`drained_mark`, serve.zig:5666-5675; `run_resume`, 5681-5694).
3. The resume runs the third timeline, which reaches "r", and is interrupted after that timeline's line and before its end. It writes no catalog line of its own.
4. Resumed again, every timeline is recorded and `catalog_seen` is true from the drain's line. The short-circuit exits with that line's count: 3. The run's verdict is 0.

The search also finds the other direction. Drained after none of its timelines, the line says 0; every later timeline declares "r" unreached; the run's verdict is 3 and the resume's 0.

**How likely.** It needs a drain (serve's drain, used to empty a host), then a resume interrupted in the window between its last record line and its end, then another resume. The window is the same as CE45's first path. The drain makes the earlier line exist. df8f08b reads the same line (theorem's third conjunct).

**Zig path.** src/main.zig:2319-2322 (any catalog line sets `catalog_seen`, the last one wins), 2364-2373, 1170-1175; src/serve.zig:5642-5675.

**Test.** `tests/r8_ce45_resume.zig`, "round 8, CE61: a run drained, resumed and interrupted before its end is judged by its last timelines too":
- red on c4f246e and df8f08b ("expected 0, found 3");
- its control, the same resume reaching its own end: green on both.

### CE62: explain's set value can leave the control's pull to another draw, its variants one history again (CE57's remainder)

**Property.**
- explain.zig:10-15 (c4f246e): `--draw <name>=<v>` runs "m times each with the control's draw varied beside it (one tape replays one history)".
- explain.zig:582-588: "so each is a history of its own that compares with the control's".
- explain.zig:29-34: step 5's verdict against the control by 90% intervals.
- README_AI.md: every timeline replays bit-identically.

**Minimal case** (theorems `ce57_closed_ce62_left` and `ce62_one_history_needed`; `runs8/explain.txt`).
- The control is found among the *recorded* timeline's draws: the first non-fault draw with `count > 1` after the decision, by its pull number (explain.zig:548-551).
- A variant's tape answers that pull number, whatever draw takes it in the variant's own history (`variant_tape`, 395-418, overrides by pull).
- A set value that changes the history before that pull can leave it to a draw that decides nothing, or to none before the horizon. The doc's own example does this: "the step removed" (clock_step.ms 0) means no retry, so no retry jitter. c4f246e's own test uses `retry.jitter-ms` as the control.
- Then the m variants are one history, counted m times, as at df8f08b. With a timeline whose histories fail 5 times in 6 whatever any draw is, the step removed has one history that does not fail: "0 of 6: needed" against the control's 5 of 6.

**How often.** Census (100,000 seeds, 6 variants): 15,507 "needed" when the control's pull is taken by an inert draw, the same as df8f08b, against 2 when it stays live. Whether a set value takes the control's pull away depends on the system: values that remove a step, a retry or a timeout are the ones `--draw name=v` is for.

**Zig path.** src/explain.zig:548-551 (the control by pull number), 569-592 (the set value's variants), 395-418 (`variant_tape`).

**Test.** `tests/r8_ce62_explain_control_pull.zig`, against a copy of each version's explain.zig. The stand-in explorer (`fake-explorer-retry.sh`) draws the jitter at pull 40 only when a step makes a retry; with the step removed, pull 40 is a request id.
- "each of its variants a history of its own" (`--draw clock_step.ms=0`): red on c4f246e (1 history) and df8f08b.
- "not called needed": red on c4f246e (0 of 6 against 5 of 6: needed) and df8f08b.
- Control, a value that keeps the retry (8): 6 histories, green on c4f246e, red on df8f08b.

### CE63: a run of several scenarios records the explorer's request in place of the one it was asked

**Property.**
- serve.zig:5677-5680 (run_resume): "Continues a run that ended before its end (stopped, or its explorer interrupted): its explorer again, as it was asked".
- main.zig:1197-1200: a run's request is "what serve replays and continues it with".
- main.zig:1164-1165: "Catalogs span scenarios ... judged once all ran".

**Minimal case** (theorem `ce63_scenario_resumed_alone`; `runs8/resume.txt`; the Zig test).
- serve starts a run as posted, `--scenario all` among its fields, and writes that request (serve.zig:2125-2175).
- The explorer explores each scenario as a run of its own. The first keeps the run already claimed, "its request now naming the scenario" (main.zig:1121, 1329-1359 `run_scenario`).
- `run_request_write` writes request.json again from the explorer's own arguments (main.zig:1411-1534). What follows:
  - **Its `scenario` is the first scenario's name.** A resume passes `--scenario <that name>` (serve.zig:2249), so it explores that scenario alone. Interrupted in the first scenario, the run's other scenarios are never explored: no run of theirs was claimed yet, and nothing resumes them. Interrupted in any scenario, the resumed run's catalog is judged over one scenario (main.zig:1166-1170: `every_scenario` false, so nothing fails). A `sometimes` reached and never made true in it fails the resumed run, though another scenario would make it true.
  - **Every field serve alone records is gone:** `return_branches`, `holders_budget`, `holders_on_disk`, `prefer_*`, `ranges`, `decide`, `egress`, `automations`, `ci`, `checkpoint*`, `from_*`, `strategy_asked`, `history`, `repeat`. For a tree asked with `return_branches`, the resume is refused as "the record of another run" (main.zig:2290-2301: the record's run line says 2, the resume's default is `tree.children`). A CI job loses the coverage gate's exemption (serve.zig:783).
  - The next scenarios' runs are written the same way (main.zig:1348).
- Two scenarios, each one timeline declaring reachable "r", never reaching it: the run exits 3. Its last scenario's run resumed exits 0; its first scenario's run resumed exits 0, and the second scenario is never explored.

**How likely.** Any `--scenario all` run that is stopped, drained or interrupted, then resumed. A program with several scenarios run as `all` is the README's first example (README_AI.md:267-268).

**Zig path.** src/main.zig:1121, 1329-1359, 1411-1534, 1164-1170, 2290-2301; src/serve.zig:2125-2175, 2228-2230, 2249, 5681-5760.

**Test.** `tests/r8_ce63_scenarios_request.zig`, "a run of several scenarios keeps the request it was asked": serve's request (`scenario: all`, `return_branches: 2`, a CI job's), then `run_scenario` verbatim for the first scenario. Red on both versions ("scenario transfer, return_branches null, ci gone").

### CE64: `podman_cpuset` reads 512 bytes of the user manager's cpuset

**Property.**
- cpus.zig:977-982 (c4f246e): "its own CPUs, as far as the user manager's cpuset reaches".
- The function's own test (1043-1058).

**Minimal case** (the Zig test).
- The process runs on the even CPUs 0 to 598, and the user manager's cpuset is the same 300 CPUs: a list of 1,145 bytes.
- One read into `reach_buffer: [512]u8` (cpus.zig:987-994) keeps the first 512 bytes. The rest is dropped, and the last number is cut short (here "28" of "28x").
- podman is given 142 of the 300 CPUs. A cut number can also name a CPU the cpuset never had ("…,254" read as "25").

**How likely.** Low. The kernel prints ranges, so it takes about 128 or more separate CPUs or ranges: one hyperthread a core where siblings are numbered side by side, on a host of 256 CPUs or more. srv4's list is "0-8,44-52".

**Zig path.** src/cpus.zig:987-994.

**Test.** `tests/r8_ce64_podman_cpuset.zig`, on c4f246e's declarations verbatim, with the cgroup file read from the test's own file:
- red on c4f246e (512 bytes, ending "…,280,282");
- its control, the function's own lists ("0-8,44-52", "0-52", no file): green.

### CE65: a tree records each unreached declaration once per timeline, not once per run

**Property.**
- report.zig:553-557 (c4f246e): "its declaration a record line of its own (once a run; a worker's)".
- main.zig:2264: "An assertion declared and not reached, the first time the run saw it".

**Minimal case** (the Zig test).
- The line is skipped when the multiverse already knows the property (`aggregate_known`, report.zig:658-663).
- A tree's timeline runs in a process of its own: `timeline_start` (main.zig:5327-5363) calls `worker_run` for one timeline. Its multiverse starts empty (main.zig:3394, `mine.multiverse.* = .{}`).
- So every tree timeline writes a line for every declaration it did not reach. A flat run's worker keeps one multiverse and writes each once.

**How likely.** Every tree run. The catalog is declared in the setup, so each timeline carries every declaration (report.zig:553-568 reads `vm.events.properties`).
- A line is 90 bytes plus the message.
- 30 unreached declarations of 40 characters over 10,000 timelines add 37 MiB.
- 100 over 20,000 add 248 MiB, about serve's whole read limit: `run_file`'s `.limited(256 << 20)`. Past it, `run_show` shows no summary and `ended_status` without an `exit` reads "interrupted" (round 7's arithmetic).
- A resume reads the record whole and merges every line (`recorded_merge`, each a linear search of the aggregates).

**Zig path.** src/report.zig:553-568, 658-663; src/main.zig:3394, 5327-5363, 2323, 2136.

**Test.** `tests/r8_ce65_declared_once.zig`: the declared statement and three `Multiverse` methods verbatim. Four timelines each declaring reachable "r":
- a tree's (a fresh multiverse each): red on c4f246e ("expected 1, found 4");
- a flat worker's: green.

### CE66: a bundle leaves the run's injectors on the recording host

**Property.**
- bundle.zig:2-9: "one timeline of a run with everything it replays on ... how someone else replays a finding's timeline exactly".
- docs/INSPECT.md:3-5, 9-12: "they open it on their own machine ... exactly as it did where it was recorded"; "The run's inputs: kernel, initramfs, the test program, the system's images, its pinned guest CPU, and the run's own explorer".
- docs/PLUGINS.md:149-151: injectors go on the system disk, "part of the run's inputs".

**Minimal case** (the Zig test).
- A run with `--injector` (a command-line run's request names `<data>/artifacts/<hash>/chaos`, CE60's kept copy; a serve run's names `<data>/artifacts/<hash>-chaos`) is bundled.
- bundle.zig rewrites the kernel and initramfs (72-95), the program and the explorer (111-133), and the pin's images (135-147).
- The request's `injectors` keep the recording host's paths, and nothing puts them in the bundle or in its store's STORED.
- The bundle's replay, `explore --run . --branch <n>`, reads the request (verify.zig:204-209, `serve.system_arguments`, serve.zig:5601-5602: `--injector <path>`) and builds the system disk from it.
- On any other host the file is not there, so the replay fails. Where a file of that path differs, the disk differs and every tape is refused.

**How likely.** Every bundle of a run with an injector of its own: docs/PLUGINS.md's `--injector`, and serve's `injectors` (uploads by `@<name>`). An inspection machine (docs/INSPECT.md, infra/aws/inspect.sh) cannot open them.

**Zig path.** src/bundle.zig:111-133 (only `program` and `explorer` rewritten); src/verify.zig:204-209; src/serve.zig:5601-5602.

**Test.** `tests/r8_ce66_bundle_injectors.zig`, on a copy of c4f246e's bundle.zig, a run bundled with a store:
- red on c4f246e (the request names `.../data/artifacts/3333333333333333/chaos`, "the recording host's, not in the bundle");
- its control, a run without an injector: green.

## Round 7's list

- **Round 7's tests in the platform's tree.** Not possible here (Linux and duckdb). Round 7's tests were rerun on copies of c4f246e's files: CE57's, CE58's, CE59's, CE60's, CE56's and CE45's (as round 8's form) are green there.
- **CE56 to CE60.** Above.
- **The comment in a case's body.** junit.zig is unchanged, so `element_index` still skips no comment. Still a note.
- **The resumed tree's earlier generations and `recorded_returns`** (read).
  - Only the generation being judged again takes the record's returns (main.zig:6757-6762, generation + 1). Earlier generations are not made again.
  - `recorded_returns` (7152-7174) builds each return from its planned key, with `why` "Recorded" and `branches` its count. It drops the archive cell a return was credited to (`cell`), so on resume a cell's branches no longer credit it, and later generations rank the archive as the uninterrupted run would not have. Nothing claims the resumed tree's later generations are the uninterrupted one's, so this is a note.
  - A judgment cut before all its returns were planned keeps only the planned ones. The rest are not chosen again: their numbers were never recorded, and round 7's census of that world (0 broken) stands, since the code is unchanged.
- **Records past 256 MiB.** CE65 makes them likelier; still arithmetic, with no long run's record here.
- **Still open from earlier rounds:** CE4's singleton (by design), CE24, CE44 (documented).

## New areas

What rounds 1 to 7 covered:
- the composer and the fault injector (CE1 to CE8, CE15, CE42);
- verdicts and the catalog (CE9 to CE11, CE18, CE22);
- checks' checkpoints (CE13, CE14);
- serve: adoption, sessions, the coverage gate (CE12, CE19, CE28, CE30, CE38, CE47, CE50, CE56);
- tapes: overrides, steps, reasons, full tapes (CE20, CE48, CE52, CE53, CE58);
- disks: persistence, durability, corrupt_reads (CE17, CE31, CE35, CE36, CE43, CE54);
- the clock (CE15, CE44);
- CI and JUnit (CE16, CE21, CE27, CE37, CE40, CE41, CE49, CE55);
- the tree explorer and its resume (CE23 to CE26, CE32 to CE34, CE59);
- targeted runs (CE39);
- resume verdicts (CE29, CE45 to CE47);
- analyses' inputs (CE51, CE60);
- explain (CE57);
- steering and holders (round 4's searches).

Round 8's new areas:
- **Runs of several scenarios**, and what their resumes and requests do (CE63).
- **Bundles** (CE66).

Not covered by any round: causality's futures, shrink, merge, query, mutate, verify's replays, the bandit and advisor, quint and tla, wasm plugins, compose and Kubernetes prepare, egress.

## Other findings (not counterexamples)

- **CE56's remainder.** An uninstrumented system's run from a snapshot is never said uncovered, and CE50's comment "Judged at its end" no longer holds.
- **CE58's remainder.** A strategy's return to an earlier generation's timeline is not bounded by its marker.
- **CE59.** A strategy may list one moment twice; never moved, never resumed.
- **podman_cpuset.** No file is read as no cap; whether rootless podman takes `--cpuset-cpus` without a delegated cpuset is unverified; srv4's case returns null by design.
- **summary_format** did not move with SummaryHeader's growth. A command-line resume of an older tree is refused by a misaligned byte, not by a check.
- **`recorded_returns`** drops each return's archive cell.
- **main.zig:7375** is an orphaned doc line ("A judged timeline, kept for returns from later generations ..."), followed by `doomed_at`'s.

## What was replicated, and what is not exact

Replicated at c4f246e, with file and lines:
- the gate's end exemption;
- explain's `variant_items`;
- `open_to_end`, `returns_end` and a strategy's bound;
- `returns_earlier`'s landing check;
- declared lines, `catalog_seen` and `merge_into`'s declarations;
- a drain's end;
- a run of several scenarios' resume;
- `injectors_keep`.

Not exact:
- Resume5's declared lines are all of a recorded timeline's declarations. The platform writes one per worker per property, which is the same catalog, since a worker's timelines run in turn.
- The scenario model resumes one scenario's run alone; serve's other fields (CE63) are in the Zig test only.
- Explain's model takes "the control's pull taken by an inert draw" as a world (`controlLive`), not as a system's code.
- The Tape6 earlier-generation world assumes a holder at the moment.
- The Zig harnesses copy declarations verbatim and shim what they call (listed above). Three wrap statements taken from larger functions. The resume harness's catalog shim covers the kinds the tests use. The explain harness's stand-in explorer is mine.
- Rounds 1 to 7's simplifications still hold.

## Assumptions

- A replay is deterministic: identical tapes from one snapshot are one history (round 7's).
- A drained run's explorer ends through main's end (main.zig:5234-5272: no timeline starts; the scenario loop and the catalog lines follow).
- cgroup v2: a cgroup has `cpuset.cpus.effective` only where its parent enables the cpuset controller; an ancestor's cpuset still caps it. Not checked on a host here.
- Rounds 1 to 7's assumptions hold.

## Properties, with sources (7 new or restated)

1. A resumed run's verdict is the run's, its catalog's included (main.zig:2365-2367; RecordLine.catalog 2266-2268). At c4f246e it holds for CE45's three paths. It fails after a drain (CE61) and for a run of several scenarios (CE63).
2. Each of a set value's m variants is a history of its own (explain.zig:10-15, 582-588). Holds when the control's pull stays live; fails when the value takes it away (CE62).
3. A resumed run continues as it was asked (serve.zig:5677-5680). Fails for `--scenario all` (CE63).
4. A podman build runs on the process's CPUs as far as the user manager's cpuset reaches (cpus.zig:977-982). Fails past 512 bytes (CE64).
5. A run records each unreached declaration once (report.zig:553-557, main.zig:2264). Fails for trees (CE65).
6. A bundle holds every input its timeline replays on (bundle.zig:2-9, docs/INSPECT.md:3-12). Fails for injectors (CE66).
7. A run of an uninstrumented system that ends is said uncovered (serve.zig:692-694, 784-787). Fails for runs from a snapshot (a note: by design since CE56's fix).

## Search runs (`runs8/`)

- `resume.txt`: c4f246e's worlds complete (up to 156,250 timelines); df8f08b's CE45 paths found; the drained world (CE61) and two scenarios (CE63) found at c4f246e.
- `serve.txt`: the gate's label complete at c4f246e and found at df8f08b and a7fe05d; the uninstrumented label found for runs from a snapshot (the note). The resume worlds in this file are round 3's 3939448 model, unversioned, found as before.
- `tape6.txt`: c4f246e's full-tape worlds complete; df8f08b's cut and strategy worlds found; the earlier-generation strategy world found; the step worlds as round 7's.
- `request.txt`: c4f246e's complete (256); df8f08b's found through `--injector`; each flag alone boots its inputs at c4f246e.
- `explain.txt`: the censuses above.
- `tree-census.txt`: distinct moments 0 of 1,000 in every world (round 7: 18 to 88).

Searches of models whose code c4f246e left as it was (junit, CI, aimed, disks, the composer, persistence, verdicts, durability, the clock, steering) were not rerun: their code is the same and round 7's results stand.

The Zig runs (`scratch/zig8/run-all.sh`, `runs8/*-zig.txt`):
- CE45's three paths: red df / green c4. The complete run resumed again: green on both.
- CE56: red df / green c4 (controls green).
- CE57 (round 7's tests): red df / green c4 (control green on both).
- CE58: red df / green c4.
- CE59: red df (6 of 64; 104 of 2,000 lists) / green c4.
- CE60: red df / green c4.
- Red on c4f246e:
  - CE61 (red on df too; control green);
  - CE62 (two tests, red on df too; control green on c4);
  - CE63 (red on df too);
  - CE64 (control green);
  - CE65 (control green);
  - CE66 (control green).

## Theorems (9, `Replica/Theorems8.lean`)

General:
- `ce60_closed`

The fixes, by computation:
- `ce45_paths_closed`
- `ce56_closed_and_its_note`
- `ce57_closed_ce62_left`
- `ce58_closed_but_earlier_generations`
- `ce59_closed`

New counterexamples, by computation:
- `ce61_drained_catalog_line`
- `ce62_one_history_needed`
- `ce63_scenario_resumed_alone`

Pinned this round (Theorems7, to `.vdf8f08b`): `ce53_closed`, `ce50_closed_ce56_said`, `ce56_snapshot_run_said_uninstrumented`, `ce57_one_history_needed`, `ce58_cut_or_strategy_past_the_marker`, `ce59_offsets_meet`. `ce51_closed` gained `Ver.sinceC4` in its simp set. Theorems6 and Theorems7's injector paths are written by parts.

`lake build` builds all 123 jobs (`Replica` and `replica` to `replica8`).

## Library gaps

- CE59's fix is an invariant: "a list of pairwise distinct moments stays so through `returns_earlier`". I checked it by the census and 2,000 Zig lists, not proved. A proof needs lemmas for `Array.set!` inside a `for` loop with mutable state (`Nodup` of a set at an index). Lean's core has none ready for `Id.run do` loops, as round 7 found for the tape.
- Paths as strings made `ce60_closed` unprovable by `simp` (`String.splitOn` has no lemmas for a prefix ending in "/"). Paths as lists of parts made it one line.
- A census over seeds with per-property counts is still written by hand in each model (Explain7, Resume4, TreeProps).

## What I couldn't do

- Run any test in the platform's tree or on Linux. Every Zig test ran on the Mac against copies of the files.
- Learn what rootless podman or buildah does with `--cpuset-cpus` when the user manager has no cpuset controller. Their sources are outside my copies, so the "no file is no cap" reading stays a risk to check on a host without isolate.sh.
- Trace how long an earlier generation's holders on disk live. That decides whether CE58's earlier-generation remainder can make a node.
- Prove CE59's invariant in general (above).
- Measure a long run's record for CE65; the sizes are arithmetic.
