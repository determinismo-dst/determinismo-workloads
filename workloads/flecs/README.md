# Flecs under determinismo

[Flecs](https://www.flecs.dev/flecs/) (v4.2.0, the commit pinned in the Dockerfile), an
in-memory entity component system, under a stress harness (`stress.c`): rounds of random
operations against a world with 0 to 4 worker threads, checked against a model of what it must
hold, through the C SDK. The node is built from Flecs's source (`Dockerfile`: clang, the flags
below, the binary unstripped in /symbols).

```
zig build -Drelease flecs-test
determinismo explore --kernel ~/guest/vmlinuz --initrd ~/guest/base.cpio \
  --program zig-out/bin/flecs-test --scenario stress --seed 1 --branches 64
```

Operations (each drawn through the SDK, named for strategies): entities created alone, as
children, as instances of prefabs; deleted (children with them, relationships to them removed);
components set and removed, tags, an exclusive relationship, reparenting; batches through a
stage in readonly mode (merged at its end); frames of two multi-threaded systems (Move, Decay,
which deletes from worker threads) with observers. After each, the entities it touched are
checked against the model (alive, components and values, tags, parent, relationship, prefab);
every 25 steps all of them, a cached and an uncached query, and a parent's children. Inside the
systems: each entity visited once a frame.

The SDK goes further in: Flecs's OS hooks (mutexes, condition variables, thread creation, atomic
counters) yield the CPU when the platform says so (buggify), so the explorer varies interleavings
exactly where Flecs synchronizes; Flecs's sanitize checks (`FLECS_SANITIZE`, leak checks
included) and the build's undefined-behavior traps report as properties; the whole of Flecs is
instrumented for edge coverage (trace-pc-guard), which strategies and the tree see, as source
lines. The SDK's assertions in Flecs's own source (`assertions.patch`, assertions only),
`sometimes` on its rarer paths: a deleted entity's id recycled; a worker thread's queued
commands merged into the world; a deferred
command on an entity deleted before the merge discarded; a deferred set whose parent died
discarded and its entity deleted.

Faults: what varies a library's behavior is scheduling, not the network or restarts (its state is
its memory): pauses of the process or of one of its threads, CPU throttling, clock skips.

## Status

Built against v4.2.0 since 2026-11-04 (released that day; the Dockerfile's commit). The hazard below is in the release: its
notes list 2c517a7 ("Remove implicit defer mode from core") and PR #2338's locking for
hooks and observers, and its new assert covers adding through the world in an immediate
system, not deleting. `old_idiom.c` (the program below), rebuilt against v4.2.0 with `FLECS_SANITIZE`:
e5 and e6 still at 2 and 3 after the first frame (1 and 2 right), no assert, exit 0. Not in
Flecs's tracker (searched 2026-11-04). The harness on v4.2.0 (trial run 965, seed 1, 2
timelines): every property holds; "a system deletes an entity from a worker thread" not yet
reached in two. Its hunt: `infra/hunts/flecs-stress.json`.

Its first pass (run 969, 15 minutes): 3,204 timelines of 6.9 virtual seconds on average, and 87
GB of events, more than serve took in for many minutes (its page and run-health timed out). The
model checks every entity every frame, each check an assertion, each evaluation an event (up to
140 MB a timeline). The harness now sends each assertion's first pass and first failure, as
Antithesis's SDKs do (`det_first_pass_first_failure`): trial run 972, 8 timelines, 38 MB, 2.5 GB
per virtual hour, nine tenths of it the `flecs.operation` decisions, each repeating its eleven
options (262 bytes).

v4.1.6 passes everything. So does master (3988dee) since the harness uses master's API: 32
timelines, every property, every "sometimes" reached (worker-thread deletes, observers during
merges, frames on several threads); then a 45-minute tree exploration on srv1 (seed 2): 4,528
timelines, none failing.

### Found: master's old-idiom hazard (2c517a7, "Remove implicit defer mode from core")

Under determinismo, master first aborted in 30 of 32 timelines on Flecs's own check
`assert(!(world->flags & EcsWorldReadonly))` in `flecs_table_ensure`. `determinismo stacks` at the
moment (frame pointers on) showed where: `ecs_progress` > worker pipeline > the `Decay` system >
`ecs_delete(it->world, e)` > `flecs_on_delete` > `flecs_table_ensure`. Bisected natively (a
16-line repro, outside determinismo) to 2c517a7 (2026-09-08), which made it the rule: systems and
observers get `it->stage` to queue operations, and `it->world` is the world itself, whose
operations run at once. So the idiom every Flecs program used until then, `ecs_delete(it->world,
e)` in a system, now deletes at once, inside the table the system is iterating, and nothing says
so, `FLECS_SANITIZE` included:

- Single-threaded, other entities' writes are lost: six entities with health 1, 2, 3, 1, 2, 3, a
  system that decrements each and deletes at 0; after the first frame e4 and e5 still have their
  starting values (the delete moved the table's last row while the system wrote on), and e4 is
  alive a frame after it reached 0. v4.1.6: every value right.
- With worker threads, `double free or corruption (fasttop)`, or the readonly assert above when a
  delete needs a new table (an entity that is a parent or a relationship target).

Locking a table while a system iterates it, as Flecs did (the LOCKED_STORAGE errors), would turn
the silent corruption into an error; master's open PR #2338 locks tables for OnAdd/OnRemove
hooks and observers only. Not reported upstream (findings stay here); nothing in Flecs's tracker
mentions it as of 2026-10-27.
