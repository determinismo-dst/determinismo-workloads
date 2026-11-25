# flecs v4.2.0 in Lean 4 — round 3 report

Everything is in this directory:
- `FlecsLean/*.lean`: the model and its searches. New this round: `Workers.lean` (worker-thread synchronization), `Activity.lean` (system activity and `EcsEmpty`) and `TheoremsInh.lean`. Round 1 and 2 files were extended (see "What was replicated").
- `Main.lean`: the `flecs-search` program.
- `tests/flecs_lean/*.c`: 41 C tests, 8 of them new. `README.txt` maps them to predictions.
- `.jobs/r3-*.log`: this round's run logs. `scratch/r3-runs.sh` re-runs the final batch. `scratch/tape.py` prints tapes in `name=v/n` form.

To build, run `lake build FlecsLean flecs-search`. New modes of `.lake/build/bin/flecs-search`:
- `inh-explore SEED N ENTS LEN STAGED PROPS` and `inh-exhaust LIMIT ENTS LEN STAGED PROPS`: prefab inheritance. `STAGED` is 0 or 1; `PROPS` is a comma list of property prefixes, or `all`.
- `inh-small LIMIT LEN`: exhaustive; a base, two instances, world calls only.
- `range-inst LIMIT ENTS LEN`: exhaustive; entity ranges and instantiation.
- `workers explore|exhaust STAGES OPS FRAMES SPURIOUS N SEED FILTER`, with `OPS` like `mt,st,mt`.
- `act explore SEED N LEN`, `act exhaust LIMIT LEN`, `act lib MODE SEED N LEN PROP`.
- `lib inh|inhw|inhs|inhsx|rix SEED N ENTS LEN PROP`: determinismo's explore or exhaust, shrink and tape over the new generators.
- `trace-case NAME`: runs a case op by op and prints the reachable caches, override caches and records.
- Query programs gained `ecs_query_is_true` and `ecs_query_count` probes.

Line numbers refer to files under `src/` at v4.2.0 unless a path says otherwise. Every C test needs a debug build (asserts on). A test returns 0 when flecs behaves as documented. A non-zero return or an abort confirms the prediction. A return of 2 means the test's setup did not hold. In a tape, `name=v/n` means the named decision took value `v` of `n` options.

## Counterexamples

### F24. The table override cache misses changes of the base, so overrides are copied from the wrong place

The consequences are an assert, wrong values, and missing or bad OnSet events.

An assert, with no traits and a plain base:
```c
base = ecs_new(world); ecs_set(world, base, Position, {1, 2});
inst = ecs_new_w_pair(world, EcsIsA, base);  // inst gets a copy of {1, 2}
ecs_add(world, base, Tag);
ecs_remove(world, inst, Position); ecs_add(world, inst, Position);
ecs_remove(world, base, Position);
ecs_remove(world, inst, Position); ecs_add(world, inst, Position);
// table.c 979: ecs_assert(base_ptr != NULL, ECS_INTERNAL_ERROR)
```

A wrong value, also with default traits:
```c
base = ecs_new(world); ecs_set(world, base, Position, {1, 1});
inst = ecs_new_w_pair(world, EcsIsA, base);
ecs_remove(world, base, Position);
ecs_remove(world, inst, Position); ecs_add(world, inst, Position);
ecs_set(world, base, Position, {99, 99});
inst2 = ecs_new_w_pair(world, EcsIsA, base);  // ctor value, not {99, 99}
inst3 = ecs_new_w_pair(world, EcsIsA, base);  // the same for every new instance
```

With Position `(OnInstantiate, Inherit)` and an OnSet observer with the default `self|up(IsA)` source:
```c
base = ecs_new_w_id(world, EcsPrefab); inst = ecs_new_w_pair(world, EcsIsA, base);
ecs_add(world, base, Tag); ecs_add(world, inst, Position);
ecs_set(world, base, Position, {50, 50});
ecs_remove(world, inst, Position);   // re-exposes {50, 50}: no OnSet
```
```c
base = ecs_new_w_id(world, EcsPrefab); inst = ecs_new_w_pair(world, EcsIsA, base);
ecs_set(world, base, Position, {50, 50}); ecs_add(world, inst, Position);
ecs_remove(world, base, Position);
ecs_remove(world, inst, Position);   // OnSet with source base, which has no Position;
                                     // reading the field dereferences a NULL table record
```

- **Properties:**
  - No internal assert on valid use (Manual.md "Error handling").
  - P-I2, override values. ComponentTraits.md "OnInstantiate trait": "By default, when an entity is instantiated, the components from the base entity (the IsA target) are copied to the instance". Inherit components "can be overridden manually by adding the component to the instance ... the component is copied from the base entity". For DontInherit, "its value is not copied". PrefabsManual.md "Component Overriding": the override "is initialized with the value from the prefab component".
  - P-I3. ObserversManual.md "OnSet and Inheritance", "Removing an Override": "the inherited component is reexposed ... An OnSet event will be produced".
  - An OnSet observer's source has the component (ObserversManual.md "OnSet Events").
- **Code path:**
  - A table with an `(IsA, base)` pair keeps an override cache: per column, a ref to the base the column's value is copied from (`flecs_table_init_overrides`, table.c 436-459). An entity that gets the component in that table is constructed from that ref (`flecs_table_invoke_ctor`, 963-993; on grow at 1562 and on move at 1845). `flecs_table_get_override` (2310-2340) gives the same refs to `flecs_emit_on_set_for_override_on_add` and `_on_remove` (observable.c 890-1001), and to `flecs_defer_ensure` (commands.c 590-611).
  - `flecs_table_update_overrides` (table.c 471-508) recomputes the refs only when the generation of the base's `(IsA, base)` reachable cache has changed (483).
  - That generation only goes up when the reachable cache goes from valid to invalid. `flecs_emit_propagate_invalidate_tables` skips a record whose cache is already invalid ("Subtree is already marked invalid", observable.c 504-510).
  - The cache becomes valid again only when an IsA pair to the base is added or removed (`flecs_emit_forward`, 811-812, through `flecs_reachable_cache_ensure`, 776-778).
  - The sequence is therefore:
    1. An IsA add makes the cache valid.
    2. A change of the base makes it invalid (generation + 1).
    3. An override cache refreshed now stores that generation.
    4. Further changes of the base leave the generation alone.
    5. The override cache keeps refs computed for an older state of the base.
  - The stale ref is read through `ecs_ref_get_id` (ref.c 143-162), which re-resolves the base's current table. The result is NULL when the base lost the component (the assert at table.c 979), and the base's value when the base is the wrong source. When the ref was computed while the base lacked the component, nothing is copied.
  - The reachable cache itself stays correct: P-RC (a valid cache equals a fresh walk) held in every run. Only the override cache is wrong, because it reads the generation without validating it.
- **Story:**
  - P1 reports "storage/table.c 979: ecs_assert(base_ptr != NULL): the override ref of table 2 for 60 points at 389, which no longer has it".
  - P-I2 reports "table 2 constructs 60 from none = 0, but the base the entity inherits from is (some 389) = 99", once per new instance.
  - P-I3 reports "removing the override re-exposed the inherited component, but no OnSet observer was invoked for entity 390".
  - The source check reports "OnSet observer for 61 invoked for entity 390 with source 389, which does not have the component (observable.c 978-1000: base_tr is NULL)".
  - `trace-case` shows `cr (287, 389) cur=0 gen=1` throughout, and the table keeps `bases := #[(…, 1)]`.
- **Tapes:**
  - Assert, determinismo `exhaust` over `inh-small` (6 calls), after 406,258 timelines: `inh.c1=0/2 flecs.hooks=0/2 inh.call=3/9 inh.call=0/9 flecs.value=0/2 inh.call=5/9 inh.call=1/9 inh.call=4/9 inh.call=6/9`. Shrunk:
    1. e1 IsA e0
    2. set C1 on e0
    3. add C1 to e1
    4. remove C1 from e0
    5. e2 IsA e0
    6. add C1 to e2
  - Wrong value, after 436,087 timelines: `inh.c1=0/2 flecs.hooks=0/2 inh.call=3/9 inh.call=2/9 inh.call=5/9 inh.call=0/9 flecs.value=0/2 inh.call=7/9 inh.call=5/9`. Shrunk:
    1. e1 IsA e0
    2. add Tag to e0
    3. add C1 to e1
    4. set C1 to 50 on e0
    5. remove C1 from e1
    6. add C1 to e1: constructed, not copied from 50
  - Missing OnSet, after 143,609 timelines: `inh.c1=0/2 flecs.hooks=1/2 inh.call=3/9 inh.call=2/9 inh.call=5/9 inh.call=0/9 flecs.value=0/2 inh.call=7/9`.
  - Through stages (determinismo `explore`, staged generator), after 100,607 timelines: `flecs.stages=1/2 flecs.hooks=0/2 inh.c1=1/2 inh.c0=0/3 flecs.entity=0/4 flecs.target=2/3 flecs.call=3/13 …`. The assert fires inside a merge.
- **Theorems:**
  - `override_cache_misses_changes`: for every reachable-cache state with current ≠ generation, and every number of later changes, the override check never fires.
  - `override_cache_sees_first_change`: from a valid cache, the first change is seen.
  - `reachable_invalid_state`: that state follows from an IsA add and one change.
- **C tests:**
  - `override_cache_stale_ref.c` (abort)
  - `override_cache_stale_value.c`
  - `override_cache_onset_missing.c`
  - `override_cache_onset_source.c`: it checks the source before reading the field, so it fails instead of crashing.

### F25. After `ecs_run_aperiodic(EcsAperiodicEmptyQueries)`, a system stays inactive when its query matches entities again

What happens:
```c
ECS_SYSTEM(world, Sys, EcsOnUpdate, Position);
e = ecs_insert(world, ecs_value(Position, {1, 2}));
ecs_progress(world, 0);                              // Sys runs
ecs_remove(world, e, Position);                      // [Position] is empty, still matched
ecs_run_aperiodic(world, EcsAperiodicEmptyQueries);  // Sys gets EcsEmpty
ecs_add(world, e, Position);                         // e is back in [Position]
ecs_progress(world, 0);                              // Sys does not run
```
A new table matched later doesn't help either, as long as the system's cache still holds another (empty) table.

- **Property:** PA1, an enabled system whose query matches an entity when `ecs_progress` starts runs in that frame.
  - Systems.md "Pipelines": "A pipeline is a list of systems that is executed when the ecs_progress/world::progress function is invoked".
  - Systems.md "Sync points" calls a system inactive when "it doesn't match any entities".
- **Code path:**
  - `flecs_process_empty_queries` (world.c 1338-1354) adds `EcsEmpty` to every query entity whose `ecs_query_is_true` is false. That includes queries whose matched tables are all empty.
  - `EcsEmpty` is removed in one place: `flecs_query_cache_add_table` (group.c 216-245), and only when the cache had no table before (`was_empty`, 223 and 240-243).
  - An entity entering a table the cache already holds adds no table. A new table joining a cache that holds other tables does not count as `was_empty`.
  - The pipeline schedules only systems without `EcsEmpty` (pipeline.c 295-296).
  - flecs's own test `SystemMisc_system_readeactivate` stops right after the deactivation.
- **Story:** PA1 reports "system 0 matches 1 non-empty table(s) but has EcsEmpty, so ecs_progress does not run it".
- **Tapes** [activity generator]:
  - Determinismo `exhaust` (6 calls), after 8,398 timelines: `act.sys1.kinds=0/2 act.call=0/6 act.kind=0/2 act.call=0/6 act.kind=1/2 act.call=1/6 act.kind=0/2 act.call=2/6 act.sys=0/2 act.call=3/6 act.call=0/6 act.kind=0/2`. Shrunk:
    1. add an entity of kind 0
    2. remove it
    3. create system 0
    4. EmptyQueries
    5. add an entity of kind 0
    6. progress
  - The second form, `explore` after 364 timelines: `act.sys1.kinds=1/2 act.call=0/6 act.kind=1/2 act.call=4/6 act.call=3/6 act.call=2/6 act.sys=1/2 act.call=5/6 act.call=1/6 act.kind=1/2 act.call=3/6 act.call=0/6 act.kind=0/2`. Shrunk:
    1. add an entity of kind 1
    2. create system 1 (matches kinds 0 and 1)
    3. remove the entity
    4. EmptyQueries
    5. add an entity of a new kind 0
    6. progress: the new table joins a cache that still holds the empty one, so the system stays inactive
- **Theorem:** `addToCache_keeps_empty`: for every world and system, adding a table to a cache that already holds one leaves `EcsEmpty` as it was.
- **C test:** `pipeline_system_stays_inactive.c`

### F26. The worker threads' synchronization does not re-check its condition after a wait

A spurious wakeup trips internal asserts or runs systems during a merge.

What happens, with two stages and one multi-threaded op:
```
main:   flecs_wait_for_sync: workers_waiting (0) != 1 → ecs_os_cond_wait(sync_cond)
main:   wakes without a signal (pthread_cond_wait may)
main:   worker.c 156-157: ecs_assert(world->workers_waiting == (stage_count - 1), ECS_INTERNAL_ERROR)
```
In a release build the main thread then merges the stages while the worker still runs its systems.

A worker that wakes without a signal in `flecs_sync_worker` runs pipeline ops again. This can happen:
- during the main thread's merge;
- on a single-threaded op, which trips pipeline.c 556 (`ecs_assert(!stage_index || op->multi_threaded, ECS_INTERNAL_ERROR)`);
- when no op is running, so `pq->cur_op` is NULL (pipeline.c 553, a NULL dereference).

A worker parked at start-up that wakes the same way does the same before the first frame.

- **Properties:**
  - No internal assert or crash (Manual.md "Error handling").
  - PW2: no worker runs systems while the main thread merges, or outside a multi-threaded op (Systems.md "Threading": systems run on the workers between sync points).
  - Spurious wakeups are allowed by `pthread_cond_wait` ("Spurious wakeups ... may occur", POSIX) and by `SleepConditionVariableCS`. `ecs_os_cond_wait` is one or the other (addons/os_api_impl/posix_impl.inl 200-208, windows_impl.inl 127-132), and an application may supply its own.
- **Code path:**
  - `flecs_wait_for_sync` (addons/pipeline/worker.c 138-159) waits with `if`, not `while`, then asserts the condition it did not re-check (156-157).
  - `flecs_sync_worker` (13-31) and the start of `flecs_worker` (44-50) wait on `worker_cond` with no predicate at all. They then run `flecs_run_pipeline_ops` (pipeline.c 545-579), which reads `pq->cur_op` (553) and asserts the op is multi-threaded (556).
  - Without spurious wakeups the protocol held in every interleaving searched (see "Search runs").
- **Story:**
  - Main thread: "3: main: frame 0 op 0 (multi-threaded) begins; 7: main: waits on sync_cond (0 workers waiting); 11: thread 0: spurious wakeup from sync_cond". Then PP1: "worker.c 156-157: ecs_assert(...) after flecs_wait_for_sync returned (0 of 1 workers waiting, frame 0)".
  - Worker: "1: thread 1: spurious wakeup from worker_cond". Then PW2: "worker 1 runs the systems of op 0 while the main thread is outside the op".
- **Tapes** [workers model, determinismo `explore`, one spurious wakeup allowed]:
  - Main thread, after 16 timelines: `thread.next=0/2 ×9 cond.spurious=0/2 thread.next=0/2 cond.spurious=0/2 thread.next=1/2 thread.next=0/2 cond.spurious=1/2 thread.next=0/2 thread.next=0/2`
  - Worker during a merge or outside an op, after 2 timelines: `thread.next=0/2 thread.next=1/2 cond.spurious=1/2 thread.next=0/2 thread.next=1/2 thread.next=1/2 thread.next=1/2 thread.next=0/2 thread.next=1/2`
  - Worker on a single-threaded op, after 11 timelines: `thread.next=0/2 thread.next=0/2 thread.next=0/2 thread.next=1/2 cond.spurious=1/2 thread.next=1/2 …`
  - Three stages, two frames: a worker reading a NULL `cur_op`, after 2 timelines.
- **C test:** `workers_spurious_wakeup.c` (needs threads). It installs an OS API `cond_wait` that, once on the main thread, releases and retakes the mutex and returns, which any condition variable may do. The worker's system sleeps so that the main thread reaches the sync point first.

### F27. `ecs_query_is_true` and `ecs_query_count` clear the change state that `ecs_query_changed` reports

What happens:
```c
q = ecs_query(world, { .terms = {{ ecs_id(Position), .inout = EcsIn }},
    .cache_kind = EcsQueryCacheAuto, .flags = EcsQueryDetectChanges });
ecs_query_changed(q); /* iterate q fully */
ecs_set(world, e, Position, {2, 2});
ecs_query_changed(q);    // true
ecs_query_is_true(q);
ecs_query_changed(q);    // false: no iteration happened
```
The same happens for a table unmatched since the last iteration (q = `[in] Position, [in] Velocity(up)`, and the parent loses Velocity), with either `ecs_query_is_true` or `ecs_query_count`. `ecs_query_count` also refreshes the fixed-source monitor.

- **Property:** P-CD1 (round 2), extended.
  - flecs.h 4797-4810, `ecs_query_changed`: "Return whether the query data changed since the last iteration. The operation will return true after: ... new tables have been matched or unmatched ... matched components were changed". Also: "The changed state of a table is reset after it is iterated".
  - Queries.md "Change Detection": a `set` is detected, and "the query state for that table will remain changed until the table is iterated by the query".
  - `ecs_query_is_true` (flecs.h 4955-4961) and `ecs_query_count` (4945-4953) are documented as tests, not iterations.
- **Code path:**
  - Both create an iterator. `flecs_query_cache_iter_init` sets `prev_match_count = match_count` (cache_iter.c 36), which drops the record of tables matched or unmatched since the last iteration.
  - `ecs_query_is_true` (api.c 706-713) calls `ecs_iter_is_true` (iter.c 511-526): one `next`, then `ecs_iter_fini`. The fini runs change detection on the current result (`flecs_query_iter_fini`, eval_iter.c 670-686), which syncs the first table's monitor (`flecs_query_sync_match_monitor`, change_detection.c 581-633).
  - `ecs_query_count` (api.c 667-704) skips every result. But the end of the iterator updates the fixed monitor (eval_iter.c 597-605), and empty tables are synced (cache_iter.c 81-97).
  - `ecs_run_aperiodic(EcsAperiodicEmptyQueries)` calls `ecs_query_is_true` on every query (world.c 1338-1354), so it does this to all of them.
- **Story:** P-CD1 reports "query 0 returned false after a documented change: table 1: (some m1,389/60:1) -> m1,389/60:2" for the set, and "unmatched since the last iteration: tables [3]" for the unmatched table.
- **Tape** [query generator, determinismo `explore`, filter "unmatched", after 114,845 timelines]: `q.count=0/2 q.menu=0/11 q.fixed=0/3 q.kind=0/5 q.mode=0/3 q.ask=0/2 q.kind=1/5 q.kind=2/5 flecs.entity=0/3 flecs.target=1/3 flecs.id=0/7 flecs.call=6/8 … q.kind=4/5 q.probe=0/2`. Shrunk:
  1. query `[in] C0`
  2. ensure C0 on e0
  3. `changed`
  4. add `(Rel, e0)` to e0
  5. iterate
  6. delete e0 (its table is freed, so unmatched)
  7. `isTrue`
  8. `changed` returns false
- **C test:** `query_is_true_consumes_change.c`. It covers both parts, with controls showing the change is reported before the probe.

### F28. With an entity range active, instantiating a prefab with children creates instance children outside the range

What happens:
```c
prefab = ecs_new_w_id(world, EcsPrefab);
pchild = ecs_new_w_pair(world, EcsChildOf, prefab);   // prefab + 1
b = ecs_new(world);
ecs_entity_range_set(world, ecs_entity_range_new(world, 5000, 5010));
ecs_add_pair(world, b, EcsIsA, prefab);   // b's new child has id b + 1, outside [5000, 5010]
```
An instance at the range's last id gets a child at max + 1, and the exhausted range does not assert.

- **Property:** P2k (round 1), extended to every entity a call creates. `ecs_new_from_range` and `ecs_make_alive` are excluded, since they ask for a specific range or id. Source: EntitiesComponents.md "Ranges": "While a range is active, both newly issued and recycled ids fall within the range", and "When the active range runs out of available ids, operations that create new entities will assert" (also addons/entity_ranges.h 54-62).
- **Code path:** `flecs_instantiate_alloc_child_id` (addons/prefab/instantiate.c 45-71) computes `root_instance + prefab_offset` and makes that id alive directly (`flecs_entities_make_alive`, `flecs_entities_ensure`), without going through the active range. `flecs_entity_ranges_on_ensure` (addons/entity_ranges.c 39-53) only moves the `cur` of whichever range contains the id. This is the function behind F21 (round 2); F28 is the other consequence round 2's list named.
- **Story:** P2k reports "entity 392 was created outside the active range [5000, 5010]".
- **Tape** [range generator, determinismo `exhaust`, after 419 timelines]: `ri.call=0/6 ri.call=0/6 ri.call=1/6 flecs.range.min=0/2 flecs.range.max=0/3 ri.call=2/6 flecs.range=0/2 ri.call=3/6 flecs.entity=1/3`. Shrunk:
  1. a prefab with a child
  2. two new entities
  3. a range [5000, unbounded], set active
  4. the second entity IsA the prefab: its child is 393
- **C test:** `instantiate_child_outside_range.c`

### Seen again this round (not new)

- **F12 with prefabs.** Batching runs an entity's later commands before other entities' earlier ones, and with prefabs this changes what instances copy. Batched, `[e0: add Prefab; e1: add (IsA, e0); e0: set C1]` gives e1 a copy of C1; in call order e1 gets none. The same reordering decides whether a child of a prefab gets the Prefab tag. P3 and P5 found it in the IsA and inheritance generators.
- **F11.** OnSet values under batching, now also through up observers and propagation from a prefab. The observer and inheritance generators log OnSet events delivered through up traversal.
- **F21.** P8 finds it in the inheritance and range generators. When the deleted id had been recycled more often than the instance, the handle that comes back is older than the last deleted one.
- **F17.** `ecs_run_aperiodic(EcsAperiodicEmptyQueries)` called from inside a system makes the systems it deactivates leave the schedule at the next merge. The rebuild then resumes as in F17; there is no new code path.

### Not counted as findings

- `ecs_run_aperiodic(world, 0)` does not process empty queries, although flecs.h 2406 says "Specify 0 to run all actions". flecs's own `SystemMisc_system_readeactivate` expects exactly this behavior.
- A cached query with `order_by` in a multi-threaded system asserts ECS_UNSUPPORTED "cannot sort query in multithreaded mode" (order_by.c 87-88). The workers have already swapped rows by then, but the combination is declared unsupported.
- `ecs_iter_changed` on a worker iterator asserts ECS_UNSUPPORTED (change_detection.c 679); this is declared.
- When a change-detecting query syncs a table that has no dirty state, or a match that has no monitor, workers allocate lazily from the world's allocator (table.c 1432-1450; change_detection.c 92). Several workers can do this for the same new table at once. Not modelled at that granularity; left for round 4.

## What was replicated

New files:
- **`Workers.lean`** (addons/pipeline/worker.c, pipeline.c 545-675).
  - Main thread: `flecs_workers_progress`, `flecs_wait_for_workers`, readonly begin and end, `flecs_signal_workers`, `flecs_wait_for_sync`, and the op loop of `flecs_run_pipeline`.
  - Workers: `flecs_worker`, `flecs_run_pipeline_ops`, `flecs_sync_worker`.
  - Shared state: `sync_mutex`, `worker_cond`, `sync_cond`, `workers_waiting`, `workers_running`, `pq->cur_op`.
  - A condition-variable wait releases the mutex and joins the waiters in one step. Signal and broadcast remove waiters; a woken thread reacquires the mutex.
  - Spurious wakeups are a `cond.spurious` decision, with a budget. Which thread steps next is `thread.next` (`Determinismo.interleave`).
- **`Activity.lean`**: `EcsEmpty` at query creation (cache.c 885-903), `ecs_run_aperiodic(EcsAperiodicEmptyQueries)` (world.c 1338-1365), `flecs_query_cache_add_table` (group.c 216-245), `ecs_delete_empty_tables` removing tables from caches, and the pipeline's activity check (pipeline.c 295-296).
- **`TheoremsInh.lean`**: see "Theorems".

Changes to earlier files:
- **Reachable caches** (`Ops.lean`):
  - `flecs_reachable_cache_ensure` (observable.c 708-780): current and generation, the IsA Inherit filter, and recursion through `(trav, x)` and `(IsA, x)`.
  - `flecs_emit_propagate_invalidate_tables` and `flecs_emit_propagate_invalidate` (489-569), at their call sites: component_actions.c 466 and 421, entity.c 198-200 and 1387-1388, commands.c 1282-1290, table.c 2202-2203 and 1097-1101.
  - `flecs_emit_forward` (799-888) now reads the cache, with its asserts (827-829). It forwards IsA too, and emits OnSet for newly inherited ids.
- **Override cache** (`World.lean`, `Ops.lean`):
  - init, update and get, and the ctor from the ref (table.c 436-508, 963-993, 2310-2340), refreshed at grow (1562) and move (1845);
  - `ecs_search_relation` up IsA, with DontInherit (search.c 175-350).
- **Instantiation** (`Ops.lean`):
  - `flecs_add_overrides_for_base` (table_graph.c 718-790);
  - a child of a prefab becomes a prefab (833-844);
  - tables with IsA take the slow move path (table.c 1838-1843).
- **OnSet for inheritance** (`Ops.lean`):
  - observable.c 890-1001 and 1325-1360;
  - propagation along both IsA and ChildOf, observers filtered by their traversal (observer.c 409-412), and the IsA/ChildOf continuation rule (observable.c 424-430).
- **Traits and auto-override** (`World.lean`, `Program.lean`):
  - `(OnInstantiate, Copy|Inherit|DontInherit)` per component: IsA is Inherit; ChildOf and Prefab are DontInherit (prefab.c 150-194);
  - `ECS_AUTO_OVERRIDE | C` ids (world.c 11, entity.c 1444-1453);
  - `ecs_get` through IsA (instantiate.c 485-555);
  - IsA targets are traversable (component_index.c 535-538).
- **`flecs_defer_ensure`'s override path** (commands.c 590-611).
- **Queries**: `ecs_query_is_true` and `ecs_query_count`, as iterators with `EcsIterNoData` (change_detection.c 478-480).
- **Programs and properties**:
  - the inheritance, small-inheritance and range generators;
  - menu 12 (OnSet observers with the default sources);
  - P-I2, P-I3, P-RC, and P2k for every created entity;
  - 8 new cases: 6 world cases and 3 query cases, one per C test program.

## What is not exact, and why

- **Workers:**
  - Systems are atomic steps; data races inside a system are not modelled.
  - Task threads, and `ecs_set_threads` changes between frames, are not modelled.
  - Spurious wakeups are limited by a budget (1 in the runs).
- **Activity:** a system is reduced to the table kinds its query matches, and `ecs_query_is_true` to "some matched table has an entity". Phases and `DependsOn` are not in this model.
- **Inheritance:**
  - Not modelled: component inheritance (`EcsIdHasBases`), sparse and DontFragment components, traits changed after use, and the tree spawner.
  - Edges are not cached. flecs clears a base's edges when the base moves (entity.c 202-204), so the result is the same.
  - The model's `flecs_emit` still invokes self observers after propagation; flecs invokes them before. Only the order of logged events differs.
- **Queries:** wildcard terms, cascade, a real `field_map` and `EcsQueryMatchEmptyTables` are still not modelled.
- **Pipeline:** no phases, `DependsOn` or custom pipelines beyond F25.
- The limits of rounds 1 and 2 remain.

## Assumptions

- **Build:** debug, asserts on. C tests use `ecs_mini()`; the pipeline and worker tests use `ecs_init()`.
- **Traits:** added before a component is used.
- **Programs follow the docs:**
  - IsA and ChildOf targets are lower slots, so there are no cycles.
  - Round 2's assumptions remain.
  - The instantiation cycle check (instantiate.c 253-260) is not compared between batched and one-by-one runs.
- **Threads:** `ecs_os_cond_wait` may return without a signal.
- **Ids:** C0 = 60, C1 = 61, entities from 385. The inheritance generator draws traits per program: C1 is Inherit or Copy; C0 is Copy, DontInherit or Inherit.

## Properties and their sources

Broke means some program violated the property; Held means it held in every run.

1. **P1 under inheritance:** no assert or crash on IsA, override and auto-override calls (Manual.md "Error handling"). **Broke** (F24).
2. **P-I2:** a component an entity gets in a table with IsA is copied from the base it inherits from, or constructed when no base has it (ComponentTraits.md "OnInstantiate trait", PrefabsManual.md "Component Overriding"). **Broke** (F24).
3. **P-I3:** OnSet for adding an IsA pair, removing an override, and setting an inherited component (ObserversManual.md "OnSet and Inheritance"). **Broke** (F24, removing an override). Adding IsA and setting on the base held.
4. **P2a for inheritance:** an OnSet observer's source has the component ("OnSet Events"). **Broke** (F24).
5. **P-RC:** a reachable cache that is valid equals a fresh walk (internal invariant). **Held.**
6. **Forward asserts:** observable.c 827-829 never fire (internal). **Held.**
7. **PA1:** an enabled system that matches an entity when `ecs_progress` starts runs (Systems.md "Pipelines", "Sync points"). **Broke** (F25).
8. **PP1 under threads:** no assert or NULL dereference in the worker protocol. **Broke** with spurious wakeups (F26); **held** without them.
9. **PW1:** each op of a multi-threaded system runs once per stage before its merge. **Held** without spurious wakeups.
10. **PW2:** no worker runs systems during a merge or outside a multi-threaded op (Systems.md "Threading"). **Broke** with spurious wakeups (F26); **held** without them.
11. **Deadlock freedom:** the main thread never waits with every thread blocked. **Held.**
12. **P-CD1 extended:** `ecs_query_is_true` and `ecs_query_count` do not clear reported changes, and unmatched tables are reported (flecs.h 4797-4810, Queries.md "Change Detection"). **Broke** (F27).
13. **P2k extended:** every entity a call creates while a range is active falls in the range (EntitiesComponents.md "Ranges"). **Broke** (F28).

Round 1's 20 and round 2's 11 properties are still checked by their generators. This round P3, P5, P3b and P5b broke again (F11, F12), P8 broke again (F21) and P7 broke again (F20).

## Search runs and results

Inheritance:
- `inh-small`, 5 calls: **complete**, 400,000 programs, 12 failing (OnSet source 8, P-I3 4).
- `inh-small`, 6 calls: **complete**, 4,000,000 programs, 736 failing. All are F24:
  - P1 at table.c 979: 100
  - P-I2: 112
  - P-I3: 180
  - OnSet source: 356
- `inh-explore`, world calls only (seed 1, 100,000 programs, 4 entities, 10 calls): 18 failing: P-I2 3, P-I3 2, P8 13 (F21).
- `inh-explore` with stages (seed 2, 100,000 programs, properties P1, P-I2, P-I3, P-RC, P2): 5 failing: P1 1, P-I2 3, OnSet source 1. No P-RC failures.
- `inh-explore` with stages and every property (seed 1, 20,000 programs): 566 failing. All of them are P3, P5, P3b, P5b (F11, F12) or P8.
- Determinismo:
  - P1 after 406,258 timelines (`exhaust`, 6 calls), and after 100,607 (`explore`, stages);
  - P-I2 after 436,087 timelines;
  - P-I3 after 143,609 timelines (5 calls).
- Round 2's generators at round 2's seeds:
  - IsA (seed 1, 200,000 programs): 2,135 failing; round 2 had 1,503. The extra failures are F12 through copied components and the Prefab tag on prefab children.
  - Observer (seed 1, 200,000 programs): 2,374 failing; round 2 had 2,142. The extra failures are F11 and F12 through logged up-OnSet events and the corrected OnSet condition.
  - No P1, P2 or P-RC failures in either.

Ranges:
- `range-inst`, 3 instance slots, 5 calls: **complete**, 1,419,857 programs, 7,394 failing. P2k at instantiation 7,327 (F28); P8 72 (F21).

Activity:
- `act exhaust`, 6 calls: **complete**, 1,062,882 programs, 796 failing, all PA1.

Workers:
- No spurious wakeups:
  - 2 stages, one multi-threaded op, 1 frame: **complete**, 916,480 interleavings, none failing.
  - `mt,mt` over 2 frames, `mt,st,mt` with 3 stages, and `mt,st`: 2,000,000 to 3,000,000 interleavings each, bound not reached, none failing.
- One spurious wakeup allowed: see F26's tapes.

Queries:
- `query explore` with probes (seed 21, 200,000 programs, 3 entities, 10 calls): 4,322 failing.
  - P1 uninitialized read: 2,931 (F19).
  - P-CD1: F18 and F19 as in round 2, plus F27. Every F27 program's shrunk form ends in `isTrue` or `count` before `changed`.

## Theorems

There is no `sorry`. Every theorem uses only `propext`, `Classical.choice` and `Quot.sound` (printed by `Axioms.lean`).

New in `TheoremsInh.lean`, each for every input:
- `invalidate_invalid` and `invalidate_valid`: the per-record step of observable.c 504-510.
- `changes_invalid`: any number of invalidations of an invalid cache leave it unchanged.
- `override_cache_misses_changes` (F24): once an override cache has stored the generation of an invalid reachable cache, no number of later changes makes it refresh.
- `override_cache_sees_first_change`: from a valid cache, the first change is seen.
- `reachable_invalid_state`: that invalid state follows from the initial record (current -1, generation 0) by one IsA add and one change.
- `addToCache_keeps_empty` (F25): adding a table to a cache that already holds one never removes `EcsEmpty`.

Rounds 1 and 2's theorems are unchanged and still build.

## Library gaps

1. Round 2's gaps remain. Property filters match signatures with digits erased, so a filter like "P2k" never matches and searches filter on words instead.
2. `Determinismo.Threads` has no condition variable. `Workers.lean` builds one on the process memory: waiter lists plus a `cond.spurious` decision.
3. `interleave` treats "every live thread blocked" as a deadlock. The workers model passes a `stuck` callback that accepts workers parked after the main thread finished.
4. `interleave` only schedules ready threads. To allow spurious wakeups, a waiting thread is offered as ready while the budget lasts, which adds decisions.
5. Lean core has no `Nat.iterate`; the theorems define `changes` by recursion.

## Model errors corrected

- Round 2's `flecs_emit_forward` computed the reachable ids fresh each time, and only for ChildOf. It now uses the cache and its generation, and forwards IsA too. Without this, F24 could not show up.
- Round 2's instantiation did not copy the base's Copy-trait components, and did not tag children of prefabs as prefabs. Both are added. Round 2's cases and C tests are unaffected.
- Round 2's `flecs_set_id_move` emitted OnSet only when a self observer existed. `EcsTableHasOnSet` also counts up and self|up observers (entity.c 1966; observer.c 104-127). Corrected.
- Propagation now follows every traversable relationship, using the target's traversable flag.

## C tests (tests/flecs_lean/)

All 41 compile with `cc -c` against `upstream/distr/flecs.h`; none was run.

Round 3:
- F24: `override_cache_stale_ref.c` (abort at table.c 979), `override_cache_stale_value.c`, `override_cache_onset_missing.c`, `override_cache_onset_source.c`
- F25: `pipeline_system_stays_inactive.c`
- F26: `workers_spurious_wakeup.c` (needs threads)
- F27: `query_is_true_consumes_change.c`
- F28: `instantiate_child_outside_range.c`

## For round 4

- **Queries:**
  - wildcard terms and `wildcard_matches` on rematch (match.c 197-286 frees superfluous matches while an iterator may still point into the vector);
  - cascade ordering when a parent's depth changes;
  - partially cached queries with a real `field_map` (api.c 216-232 reads `term[-1]`, the previous query term, not the previous cacheable one);
  - `EcsQueryMatchEmptyTables`.
- **Workers at finer grain:** lazy allocations by several workers at once; `prev_match_count` written by every worker.
- **Pipeline:** phases and `DependsOn` (the builtin pipeline query's cascade and `!Disabled(up)` terms), custom pipelines, and a phase disabled mid-frame.
- **Inheritance:** component inheritance, sparse and DontFragment overrides, OnSet through prefab variants, and the tree spawner.
- **C tests:** run F24 to F28, and round 2's queue.
