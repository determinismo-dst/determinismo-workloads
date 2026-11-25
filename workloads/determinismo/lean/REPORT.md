## What this is

A Lean 4 (v4.36.0) replica of the parts of determinismo (platform commit 0dea225) that decide what a run's verdict means. Each part is written function by function from the Zig, with file and line beside it, and searched against what the documentation promises. The SDK at `upstream/sdk/lean` is a path dependency.

Files, in this directory:
- `Replica/Composer.lean` and `Replica/ComposerProps.lean`: the composer and its properties.
- `Replica/ComposerSearch.lean`: the composer's worlds and searches.
- `Replica/Faults.lean`: the fault injector's rules.
- `Replica/Verdicts.lean`: assertions to verdicts.
- `Replica/Tape.lean`: tapes and replay.
- `Replica/Theorems.lean`: the theorems.
- `Replica/Prelude.lean`, `Replica/Searching.lean`, `Main.lean`: shared helpers and the command line.

Commands:

    lake build
    .lake/build/bin/replica composer <exhaust> <seeds> <drawn-seeds> [<property>]
    .lake/build/bin/replica cworld <property> <world> <exhaust> <seeds> <first-seed>
    .lake/build/bin/replica cdrawn <property> <seeds> <first-seed>
    .lake/build/bin/replica faults <exhaust> <seeds>
    .lake/build/bin/replica verdicts <exhaust>
    .lake/build/bin/replica tape <exhaust>

## Counterexamples

### CE1: a finally runs after a command that did not run to completion

**Property.** docs/ANTITHESIS.md, Test templates: "a finally command waits for them and runs only when every command ran to completion". I checked it with the exception that `composer.zig:517` intends: drivers killed by the length are forgiven.

**Minimal case.** Proven as `finally_after_a_signal`. A parallel driver and a finally, a 60 ms length, parallelism 2.
- drive#1 runs 100 ms.
- drive#2 ends by SIGKILL at 20 ms. It is reaped with status 137, so `interrupted` becomes 1.
- drive#3 starts at 20 ms and runs 100 ms.
- At 90 ms (60 ms length plus 30 ms grace) drive#1 and drive#3 are killed, `bounded` is set, `interrupted` is reset to 0, and `check` runs.

The searches also found it in drawn scenarios with the Zig's constants: a start exiting 137 under `--timeline 100000`.

**Zig path.**
- `guest/runtime/composer.zig:324-325`: a signal, or a code of 128 or more, counts as interrupted.
- `composer.zig:504-513`: the length's grace, then `kill_all`.
- `composer.zig:519`: `if (bounded) composer.interrupted = 0;` wipes every earlier interruption, not just the length's.
- `composer.zig:942`: the finally runs when `interrupted == 0`.

**On the platform.**
- Scenario: `s.parallel_driver("work", work)` and `s.finally("check", check)`.
- `work`: one start in four writes `/tmp/interrupted` and calls `std.posix.raise(.KILL)`; the others sleep 120 s. In a Compose template the same happens when a node restart kills a command (exit 137).
- `check`: `sdk.always(!exists("/tmp/interrupted"), "a finally runs only after every command completed", .{})`.
- Run: `determinismo explore ... --timeline 30s --branches 32`. The assertion fails in timelines that have both a signal exit and `length_reached`.

### CE2: with min_drive 0, exits are reported as killed and failures hidden

**Property.** docs/ANTITHESIS.md: default property "commands finish with zero exit code", and "killed commands are no failing exits". Only the composer's own kills are exempt.

**Minimal case.** Proven as `failing_exit_hidden`. A parallel driver and an eventually, `min_drive_ms = 0`, no swarm.
- Four starts happen one at a time.
- The fourth exits 1 at 4 ms, during the last random pause.
- `kill_all` reaps it with `killed = true`, so no false "test commands exit successfully" appears in the timeline.

With the Zig's constants (drawn: `--timeline 100s`, min_drive 0), 16 starts that had exited were reported killed at once.

**Zig path.**
- `composer.zig:375-386` `wait_below`: reaps only while `running_count >= count`, so exited starts below the parallelism stay unreaped.
- `composer.zig:795`: `if (max_ms == 0) return;`, so no reaping happens before the kill.
- `composer.zig:390-396` `kill_all`: reaps every child with `killed = true`, including ones that had exited on their own.
- `composer.zig:1200-1203` `report_exit`: an exit reported as killed is not judged.

**On the platform.**
- Scenario: `s.parallel_driver("work", work)` where `work` returns `error.Failed` at once, and `s.eventually("check", check)`.
- Run: `determinismo explore ... --min-drive 0 --drive-max none --decide composer.parallelism_log2=5,composer.load=0,composer.starts_log2=0`.
- Every start of `work` exits 1, yet "test commands exit successfully" never fails. Every `command_exit` has `killed: true`, and "test command completed: work" is never reached.

### CE3: workload marking keeps no driver (and the composer panics)

**Property.** `.claude/skills/determinismo-workload/SKILL.md`: "keeps one marked driver at least". Also `sdk/zig/schema.zig:704-708`.

**Minimal case.** Proven as `singleton_marked_panics`, with decisions `[0, 7, 0, 7, 7]`.
- `s.singleton_driver("workload")` marked with `s.workload`, plus two parallel nemeses.
- The singleton isn't drawn for this timeline (`composer.singleton` = 7 against an eighths share of 1).
- Both nemeses are left out (`composer.swarm_p` = 0, each nemesis's swarm draw 7).
- Nothing counts as needing rescue, so the composer panics at `run_drivers`.

Other cases:
- In timelines where the singleton isn't drawn but a nemesis is kept, only nemeses run: no marked driver at all.
- Same with `s.first("load")` marked: proven by search, decisions `[0, 7, 7, 0, 0]`.
- Five unmarked anytime commands: proven as `five_anytime_panics`.

**Zig path.**
- `composer.zig:225-228`: `workload_marked` is computed over all commands.
- `composer.zig:249-260`: `needed` counts only parallel, serial and anytime commands (unmarked: only parallel and serial).
- `composer.zig:261`: the rescue runs only if `needed > 0`.
- `composer.zig:718`: `assert(kinds.len > 0)` panics in ReleaseSafe (`build.zig:9`).
- `sdk/zig/system.zig:311` lets `workload` mark any command.

**On the platform.** The scenario above, run with `--decide "composer.singleton=7,composer.swarm_p=0,composer.swarm nemesis1=7,composer.swarm nemesis2=7"`. det-composer dies with "reached unreachable code" after faults start: no driver phase, no ending, no checks.

### CE4: a timeline's length doesn't bound serial drivers or singleton timelines

**Property.** The `Scenario.drive_ms_max` comment in `sdk/zig/schema.zig`: "a timeline's length no longer follows how slow its commands are". Also `composer.zig:504-506`: "the commands still running get a grace, then are killed".

**Minimal case.** Proven as `serial_past_the_length`. A serial driver and a parallel driver, a 60 ms length. The serial driver starts at 40 ms and runs to 240 ms; faults keep running until 240 ms, past 60 + 30. A singleton timeline isn't bounded either. With the Zig's constants: a 60 s start ran to 61 s past its length's end.

**Zig path.**
- `composer.zig:817-821`: a serial start goes through `run_to_completion`.
- `composer.zig:398-403`: `run_to_completion` ends in `wait_all`, with no deadline.
- `composer.zig:488-489`: `run_singleton` waits for the singleton, and `length_end_ns` stays null.
- `composer.zig:504-513`: so the grace and kill never apply.

**On the platform.** `s.serial_driver("slow", slow)` where `slow` sleeps 300 s, beside a parallel driver; run with `--timeline 30s`. `fault` events appear long after 60 s past the driver phase's start.

### CE5 (minor): a driver starts past half the timeline limit

**Property.** The comment at `composer.zig:730`: "No driver starts past half the timeline's limit".

**Minimal case.** Proven as `start_past_half_the_limit`. A 30 ms limit; two quiet stretches carry the first start to 20 ms, past the 15 ms stop.

**Zig path.** `composer.zig:736-741`: the stop is checked before `while (!load.next(...)) {}` sleeps through quiet stretches.

**On the platform.** It applies only with `--drive-max none --timeline-limit <L>`. Look for a `command_start` after `composer_start` + L/2 following a quiet `composer_load`.

### CE6: fault exclusions miss link faults from earlier nodes

**Property.** docs/ANTITHESIS.md, Fault exclusions: "a node whose name matches gets no fault of its own and is in no partition, isolation or outage".

**Minimal case.** Proven as `excluded_node_listed`. Nodes `a` and `b` (defaults), with `b` excluded. The fault list contains `partition a b`, `degrade a b` and `degrade b a` (the last has `node: b`). A drawn `partition a b` happens at 20 ms.

**Zig path.**
- `guest/runtime/faults.zig:1380-1381` skips the excluded node's own loop.
- `faults.zig:1475-1500` (`links_collect` and `links_add`) adds each earlier node's links to every later node without checking exclusion.
- No other exclusion check covers links (`faults.zig:4104 faultable`).

**On the platform.** The e2e check uses `^postg.es$`, the first of shop's nodes, so it passes. Instead:

    determinismo explore --program shop-test --scenario prices --seed 2 --branches 16 --fault-exclusions '^redis$' --events-dir E
    determinismo query E 'event=fault details.node=redis' --count

Expect a nonzero count; `details.peer=redis` also matches.

### CE7: an outage ignores the recovery window that node_start counts

**Property.** docs/ANTITHESIS.md, cap on nodes down: "outages counted", for "a 2n+1 cluster surviving n". `node_start` counts a node back from a fault less than `quorum_recovery_ms` ago as down.

**Minimal case.** Five nodes allowing restart and crash, `nodes_down_max = 2`. n0 is restarted and comes back. Within its recovery window, an outage of n1 and n2 is admitted: n0 recovering plus n1 and n2 down makes three. A restart of n2, then n3, at the same moments would have been refused `NodesDownMax`.

**Zig path.**
- `faults.zig:2087-2111` (`nodes_down`) and `faults.zig:2134-2148` (`node_start`) count recovering nodes.
- `faults.zig:3063-3072` (`outage_start`) counts only active slots.
- `faults.zig:2205-2207` sets the recovery window.

**On the platform.** Five nodes, `s.nodes_down_max = 2`. A driver calls `sdk.fault(.{ .kind = "restart", .node = "n1", .duration_ms = 1000 })`, sleeps 2 s, then `sdk.fault(.{ .kind = "outage", .nodes = &.{ "n2", "n3" } })`. The outage's `fault` event appears; two restarts of n2 and n3 in its place give `fault_skipped NodesDownMax` for the second. The literal cap (nodes under a takes-down fault) holds in every search.

### CE8: injected faults start in quiet periods

**Property.** docs/ANTITHESIS.md, Pausing faults: "none but clock skips start". The workload skill says `sdk.fault` faults are "applied, logged and undone like a drawn one".

**Minimal case.** A quiet period is requested at 0 ms (until 50 ms); an injected `restart a` starts at 0 ms.

**Zig path.**
- `faults.zig:392` checks quiet periods for drawn faults only.
- `faults.zig:4372-4392` (`requests_read`) and `faults.zig:4541-4560` (`inject`) apply injected faults at once: no quiet check, no exclusion check (`faults.zig:4571-4600`).

**On the platform.** A driver calls `sdk.stop_faults(10 * std.time.ns_per_s)` and then `sdk.fault(.{ .kind = "restart", .node = "db" })`; the `fault` event lies inside the `faults_quiet` window. This would break `sdk.progress_while_quiet` checks beside a nemesis driver that uses `sdk.fault`.

### CE9: one message with two kinds, judged by whichever timeline merges first

**Property.** ANTITHESIS.md "Judged as Antithesis does", and the exploration's exit status. The verdict must not depend on the order timelines end (README_AI.md: "--jobs, same timelines as one worker"; `report.zig:506`).

**Minimal case.** Proven as `verdict_depends_on_order`. Timeline T1 has `sometimes(true, "m")`; T2 has `always(false, "m")`. If T1 is merged first the exit is 0 and T2's false `always` is hidden. If T2 is first the exit is 3. Serve lists two properties, the `always` failing.

**Zig path.**
- `src/report.zig:481-489` (`aggregate_find`) matches by name only.
- `report.zig:491-506` (`merge`), and `report.zig:356-366` (`failing`) uses the first branch's kind.
- `src/core/events.zig:1457-1470` refuses the mismatch only within one timeline.

**On the platform.** It needs uncatalogued messages (`assert_computed`): a driver evaluates `sdk.assert_computed(.sometimes, true, msg, .{})` or `.always, false` with the same runtime message, by a draw. Compare the CLI summary ("PASS sometimes ... failing in N") with `GET /runs/<id>/properties` (always failing). Realism is low to medium: catalogued assertions with two kinds fail in the setup instead.

### CE10: a sometimes true in another scenario still fails the run

**Property.** report.zig:122-124, the Catalog: "an assertion must be reached (made true, for a `sometimes`) in some timeline of some scenario, as in an Antithesis run". Also ANTITHESIS.md: "A test program's catalog spans its scenarios".

**Minimal case.** Proven as `sometimes_across_scenarios`. Scenario A evaluates `sometimes(false, "m")`; scenario B evaluates it true. The explorer exits 3; judged as documented, it passes. A `sometimes` never reached in A at all would pass.

**Zig path.** `src/main.zig:1131-1146`: each scenario's `failing_properties` counts on its own, while `catalog_reached` and `judge` span scenarios.

**On the platform.** Two scenarios with literal `sdk.sometimes(cond, "reached the rare state", .{})`, false in a's drivers and true in b's. `determinismo explore ... --scenario all` exits 3.

### CE11: messages sharing their first 192 bytes become one property

**Property.** Messages are identities (the skill: "Messages are literals: they are the property's identity").

**Minimal case.** Proven as `long_messages_merge`. Two `sometimes` whose messages are 193 bytes and differ in the last byte: one true, one never true. The explorer exits 0; as documented (and in serve), the second fails. The same happens with an `always` never evaluated.

**Zig path.** `src/core/events.zig:14` sets `message_size_max = 192`; `events.zig:1457-1462` cuts names to it. Serve keeps the full message (`src/store.zig:765`).

**On the platform.** Parametrized test names or long computed messages sharing a 192-byte prefix: compare the CLI summary with serve's properties.

### CE12: replays of serve replies and fork indices lose a decision event

**Property.** README_AI.md: "every timeline replays bit-identically". ARCHITECTURE.md M3: "Record → replay matches all checkpoints". `vm.zig:3729`, for egress: "a replay's history is the run's".

**Minimal case.** Six guest events, then a `det.serve_status` pull. The recording has event 7, `decision ... serve's reply`; the replay has none. The same for `det.fork_index`.

**Zig path.**
- `src/core/vm.zig:3775-3803`: for serve, the decision event is emitted only when answered live.
- `vm.zig:3680-3692`: for a fork taken from the tape, no event.
- Compare egress at `vm.zig:3729-3731` and ingress at `vm.zig:3764-3769`, which emit it either way.

**On the platform.** Record a timeline whose guest calls `sdk.serve` (or `sdk.fork`) with at least 64 more guest events after it, then `explore --tape branch-N.jsonl`. Expect "replay diverged from its tape". This is unconfirmed: the e2e serve-replay check stops at an earlier moment.

### CE13: a passed-over checkpoint disables all later checks

**Property.** README_AI.md: "tapes with checkpoints (a replay stops where it diverges)". ARCHITECTURE.md §7: checkpoints "for divergence detection".

**Minimal case.** Proven as `check_other_count` and `checks_never_stop`. The tape has checkpoints at 4 and 8. The replay gets one extra kernel line before guest event 4, so count 4 is a kernel line (no check) and every later count misses 4. The cursor waits at 4 forever and the replay runs to its end unstopped.

**Zig path.**
- `src/core/tape.zig:219-228` (`check`): `if (expected.events != now.events) return;` never advances past a skipped count.
- `vm.zig:3384-3397`: checkpoints are taken only after guest events.
- `vm.zig:2665-2679` (kernel console lines) and `vm.zig:3845-3862` (decision events) emit without a checkpoint.

**On the platform.** A Zig unit test against `tape.Overrides`: parse a tape with checkpoint `{events: 64}`, call `check(.{.events = 128, ...wrong hash})`, and no error comes back. On a run, any replay whose event 64·k is a VM-made line (as CE12 can cause) loses all later checks. The run's own replay verification still compares final hashes (`src/replays.zig`).

### CE14 (minor): thinning can overflow the checkpoint table

**Minimal case.** Proven as `thinning_can_overflow`. A table of 2 with checkpoints every 2 events: checkpoints at 4, 8 and 12 (events 2, 6 and 10 were kernel lines). After doubling the interval both kept checkpoints stay, and `assert(checkpoint_count < checkpoint_count_max)` fails (`tape.zig:585-600`).

**Realism.** On the platform this needs 16,384 checkpoints at even multiples only. Not practically reachable.

### Note: anytime beside the singleton

`composer.zig:670-676` starts an anytime command beside the singleton, also exceeding `parallel_max = 1` (proven as `anytime_beside_the_singleton`). This contradicts "runs no other driver" only if anytime commands count as drivers, which `composer.zig:214` says they do. The skill's stricter property (no parallel or serial driver) holds.

### Note: other doc mismatches found while reading
- schema.zig:647 says "4 to 63" starts; with the swarm on it's 2 to 63 (`composer.zig:690-697`).
- Serve's "N failing" count leaves out "unreached" properties (`index.html:1386`), while the explorer fails them.

## What was replicated, and what is not exact

**Composer** (`composer.zig` `main`, 406-523, and every function it calls): kind counts, pick, swarm with weights and the saturating rescue, start, reap, wait_below, wait_all, wait_until, kill_all, run_to_completion, faults start and stop, singleton draw, run_singleton, starts draw, drive draw, Load stretches, run_drivers, min_drive, drive_again, ending pick, run_ending, the ending window, commands_declare and report_exit. Decision names are the Zig's.

Not exact:
- Commands are world decisions (`world.run_ms`, `world.exit`) made when each starts.
- Time is in ms, and constants scale down in small worlds (`Consts.tiny` and `Consts.small`).
- wait4 returns the exited child with the lowest pid.
- The injector never exits on its own.
- Not modeled: `swarm.seed` (2^64 options), scripts, dev mode, the SDK setup wait, checks streaming, invalid-command reports, injector choice.
- `composer.again` is drawn only when the explorer is asked.
- Empty polls are skipped exactly, by jumping to the next poll at or past the earliest exit.

**Fault injector:** `faults_collect` (exclusions, links, groups, outages, restore), `swarm_select`, `fault_weighted`, `fault_choose` (aim), `outage_draw`, the main loop with pacing and quiet checks, `node_admits` (layers and overlap), `nodes_down`, `node_start`, `outage_start`, `node_end` (recovery windows), `quiet_request` and resume, `inject`, heal.

Not exact: durations and waits come from two-value menus; quorum, aftershocks, crash points, the node-state check, pods, disks and regimes (except the overlap share) are left out; requests arrive one per sleep from a menu; network faults are lifetimes only.

**Verdicts:** `events.zig` per timeline (truncation, kind errors, passing), `report.zig` merge, failing, unreached and the catalog, `main.zig`'s exit status, and serve's `properties_sql`. Not modeled: moments, locations, guidance, run-level properties, tree ancestry.

**Tape:** `tape.zig` Overrides (`kind_of`, `parse`, `apply`, `reason`, `kind_at`, `check`, `checkpoint_keep`, `seek_inside`), `vm.zig` `checkpoint` and `decide_random` for each label class (plain, strategy override, `drive_ms`, `explore_here`, fork, egress, ingress, serve), and decisions as a function of seed and index.

Not exact: values are small numbers; the hash is FNV-like; reply-byte pulls, steps and sessions, and extending tapes are not modeled.

## Assumptions
- Where the docs say "drivers", parallel, serial and singleton drivers count; I check anytime both ways.
- A ReleaseSafe `assert` failure is a panic that ends the composer.
- `--min-drive 0`, `--drive-max none` and `s.workload` on any command are valid configurations, as the docs and API allow.
- An error inside one timeline (a message with two kinds) ends the worker (`main.zig:3659`) and is not a silent verdict.
- Serve's "unreached" counts as failing, because the UI gives it an error badge.
- Antithesis semantics, which the docs say the platform follows, cover scenarios explored together and messages as identities.

## Properties, with sources (29)

**Composer (14).** Holding ones are marked (holds).
1. One ending command per timeline (skill). (holds)
2. An `eventually` runs with every other command ended (ANTITHESIS.md). (holds)
3. A `finally` only after every command ran to completion, the length's kills aside (ANTITHESIS.md; `composer.zig:517`). Fails: CE1.
4. The same, strict (ANTITHESIS.md). Fails by design with lengths.
5. Singleton alone among parallel and serial drivers (skill). (holds)
6. Singleton alone with anytime counted. Fails: note.
7. Serial driver alone (ANTITHESIS.md; Antithesis reference). (holds)
8. `parallel_max` respected (schema.zig). Fails only through the singleton-plus-anytime note.
9. Faults only in the driver phase (ANTITHESIS.md; AGENTS.md). (holds)
10. The swarm keeps a marked driver (skill). Fails: CE3.
11. No panic on a valid scenario. Fails: CE3.
12. The length bounds drivers (schema.zig; `composer.zig:504`). Fails: CE4.
13. Own exits are judged (ANTITHESIS.md). Fails: CE2.
14. No start past half the limit (`composer.zig:730`). Fails: CE5.

**Fault injector (7).**
1. Exclusions. Fails: CE6, CE8.
2. Exclusions for drawn faults only. Fails: CE6.
3. Literal nodes-down cap. (holds)
4. Cap counting recovering nodes. Fails: CE7.
5. Quiet periods. Fails: CE8.
6. Quiet periods for drawn faults only. (holds)
7. Nothing lasts past the stop (`faults.zig:2`, 408). (holds)

**Verdicts (5).**
1. Order independence. Fails: CE9.
2. Explorer as documented. Fails: CE9, CE10, CE11.
3. Serve as documented. (holds)
4. Explorer agrees with serve. Fails: CE9, CE11.
5. Events are not properties (skill). (holds; theorem)

**Tape (3).**
1. Replay reproduces the history. Fails: CE12, CE14.
2. The n-th pull gets the n-th answer (ARCHITECTURE.md §7). (holds)
3. A replay stops where it diverges. Fails: CE13.

## Search runs

**Composer**, all in `runs/composer-*.txt` and `runs/second-*.txt`:
- 14 properties over 14 small worlds.
- The no-swarm worlds were searched depth-first to the end, from 4 to 35,121 timelines each.
- The swarm worlds were capped at 5,000 timelines (their decision trees have no end) and also explored with 2,000 or 5,000 seeds.
- Scenarios drawn at random with the Zig's constants: 500 seeds, then 5,000 more (seeds 500 to 5,499) per property, about 7 ms per timeline.

**Fault injector** (`runs/faults.txt`): 7 properties over 6 worlds, depth-first up to 100,000 timelines (one world complete at 92,224) and 5,000 seeds at four times the injections.

**Verdicts** (`runs/verdicts.txt`): 5 properties over 6 worlds; every world completed (9 to 29,282 timelines).

**Tape** (`runs/tape.txt`): 3 properties over 7 worlds; four worlds completed (16,384 to 65,536 timelines), three stopped at 1,000,000.

Every counterexample was shrunk; each one's decisions (as tape JSON) and story are in those files.

## Theorems (20, in `Replica/Theorems.lean`)

General ones:
- `foldlM_drops_events` and `events_are_not_properties`: dropping events leaves a timeline's property table unchanged.
- `check_other_count` and `checks_never_stop`: the checkpoint cursor never advances on another count.
- `rescue_keeps_one`: the swarm's saturating rescue keeps at least one counted command.
- `literal_le_counted`: node_start's count bounds the literal count.

By computation (`native_decide`):
- `rescue_keeps_the_rest`, `singleton_marked_panics`, `excluded_node_listed`.
- `verdict_depends_on_order`, `sometimes_across_scenarios`, `long_messages_merge`.
- `thinning_can_overflow`, `thinning_usual`.
- `finally_after_a_signal`, `serial_past_the_length`, `start_past_half_the_limit`, `anytime_beside_the_singleton`, `five_anytime_panics`, `failing_exit_hidden`.

## Library gaps (all built here)
- No uniform decision without building a weights list (`decide` uses `List.replicate n 1`): I added `Replica.below`, which draws the same values.
- `exhaust` only goes depth-first: no breadth-first or bounded-depth mode, and no per-name caps. Wide early decisions (the swarm's 7- and 8-way draws) and trees with no end (quiet stretches) can't be completed.
- No timing or progress reporting for searches: I added `Searching.lean`.
- No model of processes (spawn, wait4, kill) or of an injector's state: both are built in the replica.
- Concrete counterexamples needed `native_decide`.
