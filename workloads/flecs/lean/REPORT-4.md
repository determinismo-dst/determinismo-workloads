# flecs v4.2.0 in Lean 4 — round 4 report

Everything is in this directory:
- `FlecsLean/*.lean`: the model and its searches. New this round:
  - `Validator.lean`: how a query is split into a cached and an uncached part (F29);
  - `InhDF.lean`: overrides of Sparse and DontFragment components through IsA (F32);
  - `PipeQ.lean`: when the pipeline rebuilds its schedule (F31);
  - `WorkersCD.lean`: the worker threads' writes during change detection, load by load (F33);
  - `TheoremsR4.lean`: this round's theorems.
  - Extended: `Query.lean` (wildcard matches, the one-result-at-a-time cache iterator), `QueryProps.lean` (iteration with a call between results, F30), `World.lean`, `Pipeline.lean` (ecs_init's builtin system, the PP4 correction).
- `Main.lean`: the `flecs-search` program.
- `tests/flecs_lean/*.c`: 48 C tests; 7 new, 4 corrected. `README.txt` maps them to predictions.
- `.jobs/r4x/*.log`: this round's run logs. `scratch/r4-runs.sh a|b|c` and `scratch/r4-runs-d.sh` re-run them. `scratch/tape.py` prints tapes in `name=v/n` form.

To build, run `lake build FlecsLean flecs-search`. New modes of `.lake/build/bin/flecs-search`:
- `val explore|exhaust|lib|cases`: query term lists (F29).
- `query iter-exhaust LIMIT`, `query iter-lib MODE SEED N PROP`: iterations with a call after the k-th result (F30). `query cases` and `query trace NAME` include the F30 cases.
- `pq explore|exhaust|lib|cases`: pipeline rebuilds (F31).
- `idf explore|exhaust|lib|cases`: Sparse/DontFragment overrides (F32).
- `wcd explore|exhaust THREADS TABLES RACES N SEED FILTER`: worker interleavings (F33).
- `pipe f17`, `pipe exhaust-frame-builtin LIMIT NSYS FRONT`: round 2's F17 programs with ecs_init's builtin system.

Line numbers refer to files under `src/` at v4.2.0 unless a path says otherwise. Every C test needs a debug build (asserts on). A test returns 0 when flecs behaves as documented. A non-zero return or an abort confirms the prediction. A return of 2 means the test's setup did not hold. In a tape, `name=v/n` means the named decision took value `v` of `n` options.

## Counterexamples

### F29. A cached query whose Or chain ends with a Sparse component crashes when it is created

What happens:
```c
ecs_add_id(world, ecs_id(Position), EcsSparse);
ecs_query(world, {
    .terms = {{ TagA, .oper = EcsOr }, { ecs_id(Position) }},
    .cache_kind = EcsQueryCacheAuto });       // SIGSEGV
```
The same happens for a system with that signature: a system's query has an entity, so its default cache kind is Auto. It also happens for any query that needs a cache (DetectChanges, group_by, order_by). Without a cache the query works.

With a term after the chain the query is created, but its cache holds a different query. For `TagA || Position, TagC` the cache's query is `TagA || TagC`, with one field.

- **Properties:**
  - P1, no crash (Manual.md "Error handling").
  - ComponentTraits.md "Sparse trait": "ECS operations and queries work as expected with sparse components". Queries.md "Or" operator.
  - PV2 (internal): the cache holds the query's cacheable terms, chain by chain (cache.c 11-17: the cache query "does not contain terms that aren't cacheable").
- **Code path:**
  - `flecs_query_finalize_terms` (validator.c 965-1312) decides cacheability per term in `flecs_term_finalize` (837-859). Table-level terms on `$this` are cacheable; DontFragment ones are not.
  - It then makes each Or chain consistent (1075-1087):
    - a term after a non-cacheable Or term loses the flag;
    - a non-cacheable term clears the flag of the chain before it.
  - After that pass it clears the flag of sparse terms (1234-1238). A fragmenting Sparse component passes the first test and fails the second, so `TagA || Position` ends with TagA cacheable and Position not. DontFragment components fail the first test, so their chains stay consistent.
  - `flecs_query_create_cache` (api.c 194-243) copies the cacheable terms, with their operators, into the cache's description: `[TagA ||]`.
  - `flecs_query_cache_init` sets `impl->cache` (cache.c 736), then creates the cache's own query with `ecs_query_init` (750). That runs the validator again, which rejects the terms: "last term of query can't have OR operator" (validator.c 1308-1312). With a term after the chain the second validation sees `TagA || TagC` instead. Depending on that term it may also fail with "terms in an OR chain must have the same source" (1035-1039) or "term after OR expression cannot use operators" (1227-1231).
  - On failure `flecs_query_cache_init` returns NULL (751-753), with `impl->cache` set and `cache->query` NULL.
  - The error path of `flecs_query_init` (api.c 451-457) calls `ecs_query_fini`. Its `flecs_query_fini` (276-334) calls `flecs_query_cache_fini` (cache.c 646-698). That reads `cache->query->world` in `flecs_query_cache_remove_all_tables` (group.c 334) and `cache->query->term_count` (cache.c 689): a NULL dereference.
  - Round 3 noted that api.c 216-232 compares with `term[-1]`. That is harmless while chains are consistent, because a field index is shared only inside an Or chain. PV3 held in every run.
- **Story:**
  - P1 reports "cache.c 750-753: the cache's query is rejected (validator.c 1308-1312: last term of query can't have OR operator); flecs_query_cache_init returns NULL with impl->cache set, and the error path (api.c 451-457 -> 276-334) runs flecs_query_cache_fini on a cache whose query is NULL".
  - PV2 reports "the query's chains [[0, 1], [2]] are cacheable as [true, false, true] (mixed chains [[0, 1]]); the cache's query has 1 field(s) with chains [[0, 2]], expected [[2]]".
- **Tapes** [validator generator, determinismo `exhaust`]:
  - Crash, after 9,793 timelines: `val.storage=0/3 val.storage=1/3 val.comp=0/2 val.src=0/3 val.oper=1/4 val.comp=1/2 val.src=0/3 val.oper=0/4 val.kind=0/4 val.entity=0/2 val.detect=0/2`. Shrunk: components [table, Sparse]; query `[C0 ||, C1]`; cache kind Auto.
  - Wrong cache, after 781,057 timelines: `val.storage=0/3 val.storage=0/3 val.storage=1/3 val.comp=0/3 val.src=0/3 val.oper=1/4 val.comp=2/3 val.src=0/3 val.oper=0/4 val.comp=0/3 val.src=0/3 val.oper=0/4 val.kind=0/4 val.entity=0/2 val.detect=0/2`. Shrunk: components [table, table, Sparse]; query `[C0 ||, C2, C0]`. The cache's query is `C0 || C0`.
- **Theorems:** `or_sparse_cache_crash`, `or_sparse_uncached_ok`, `or_sparse_merges_chain`.
- **C test:** `query_or_sparse_cache_crash.c`. A crash confirms the prediction; the uncached query is the control.

### F30. A call during an iteration that removes a table from the query's cache makes the iterator skip another table, or read freed memory

What happens. The iterated table is locked, as the C++ `each` does, and no entity moves:
```c
q = ecs_query(world, { .terms = {{ ecs_id(Position) }}, .cache_kind = EcsQueryCacheAuto });
e1 = ecs_new_w_pair(world, R, x); ecs_set(world, e1, Position, {1, 1});  // T1 = [Position, (R, x)]
e2 = ecs_insert(world, ecs_value(Position, {2, 2}));                     // T2 = [Position]
e3 = ecs_insert(world, ecs_value(Velocity, {0, 0}));
ecs_set(world, e3, Position, {3, 3});                                    // T3 = [Position, Velocity]
ecs_delete(world, e1);                                                   // T1 empty, still cached
it = ecs_query_iter(world, q);
ecs_query_next(&it);              // T2 (T1 is skipped: empty)
ecs_delete(world, x);             // deletes T1, which is before T2 in the cache
ecs_query_next(&it);              // false: e3 is never returned
```
The same happens when a rematch unmatches the removed table. Example: `[in] C1, [in] C0(up)` over three tables with three parents; after the second result, the first parent loses C0.

With a wildcard term the iterator reads freed memory. Take `(R, *), C0(up)` and an entity with `(R, a)` and `(R, b)` under a parent with C0. After the first result, `ecs_remove(world, parent, C0)` unmatches the table and frees its `wildcard_matches` vector, which `qit->tables` points to.

- **Properties:**
  - P-IT1: an entity that matches the query before and after a call made during the iteration, and that the call does not move, is returned exactly once (once per matched pair). Source, Queries.md "Iteration" (C++): moving entities "can cause unwanted side effects while iterating a table, like iterating an entity twice, or missing an entity. To prevent this from happening, a table is locked by the C++ each and run functions, meaning no entities can be moved from or to it."
  - P1: no read of freed memory.
- **Code path:**
  - The cache iterator keeps a pointer to the group's table vector and an index (`qit->tables`, `qit->cur`; cache_iter.c 41-123, and the trivial version 230-262).
  - Removing a table from a group (`flecs_query_cache_remove_table_from_group`, group.c 176-213) calls `ecs_vec_remove`, which moves the last table into the hole. If the hole is before `qit->cur`, the moved table is now behind the cursor and is never returned.
  - Tables leave the cache during the call in two ways:
    - through `OnTableDelete` (cache.c 590-594); here `flecs_component_release_tables` (component_index.c 753-775) deletes the empty tables of the deleted pair;
    - through rematching. The rematch observers enqueue it (cache.c 258-292), and the end of the call flushes it (commands.c 1518-1525 → match.c 288-365).
  - For a wildcard table, `qit->tables` points to the match's `wildcard_matches` vector while the table's further results are returned (cache_iter.c 106-110).
    - `flecs_query_cache_remove_table` frees that vector (`flecs_query_cache_match_fini`, match.c 48-67).
    - A rematch that finds a single result frees it too (match.c 255-258).
    - The next `ecs_query_next` reads it (cache_iter.c 49, 77-78).
  - `qit->elem` is also a pointer into these vectors. The change detection of the next `ecs_query_next` (eval_iter.c 217-234) syncs whatever match is at that slot.
- **Story:**
  - P-IT1 reports "query 0: entity 391 (pair 0) matched before and after the call made after result 2, and the call did not move it, but the iteration returned it 0 times (returned [(389, 0), (390, 0)], matched before [(389, 0), (390, 0), (391, 0), (392, 0)], after [(390, 0), (391, 0), (392, 0)])".
  - P1 reports "the iterator reads the wildcard_matches vector 1 of the table it is iterating (qit->tables, cache_iter.c 49 and 77-78), which a rematch freed (match.c 247-258) or a table removal freed".
- **Tapes** [iteration generator, determinismo `exhaust`]:
  - Skip, after 52,241 timelines: `it.query=0/4 it.kind=2/8 it.kind=1/8 it.kind=0/8 it.kind=0/8 it.k=1/3 it.target=0/4 it.body=0/4`. Shrunk:
    1. query `C0`
    2. e0 gets `(R, e0)` and C0 (table T1)
    3. e1 gets C1 and C0 (T2)
    4. e3 gets C0 (T3)
    5. iterate; after result 2 (T2), delete e0. T1 is deleted, T3 moves into its slot, and e3 is never returned.
  - Freed vector, after 393,458 timelines: `it.query=2/4 it.kind=0/8 it.kind=0/8 it.kind=0/8 it.kind=5/8 it.k=0/3 it.target=0/4 it.body=1/4`. Shrunk:
    1. query `(R, *), [in] C0(up)`
    2. e0 gets C0
    3. e3 gets `(ChildOf, e0)`, `(R, e1)`, `(R, e2)`
    4. iterate; after result 1, remove C0 from e0. The table is unmatched, its vector is freed, and the next `ecs_query_next` reads it.
- **C test:** `query_iter_skips_table.c`, for the deterministic skip. The freed vector is a block-allocator chunk (`flecs_free_t`), which neither valgrind nor the result shows reliably, so it has no C test.

### F31. The pipeline keeps a stale schedule when its query's match changes outside the cache

What happens:
```c
module = ecs_new(world);
s = ecs_new_w_parent(world, module, "Sys");      // a Parent hierarchy
ecs_add_pair(world, s, EcsDependsOn, EcsOnUpdate);
ecs_system(world, { .entity = s, .callback = Sys });
ecs_progress(world, 0);                           // Sys runs
ecs_enable(world, module, false);
ecs_progress(world, 0);                           // Sys runs again
```
With `ecs_new_w_pair(world, EcsChildOf, module)` instead, Sys is excluded, as documented.

Custom pipelines show the same thing:
- pipeline `System, Running(Game)`: after `ecs_remove(world, game, Running)` the system still runs every frame;
- pipeline `System, Foo` with Foo DontFragment: after the system loses Foo it still runs; a second system that gets Foo is not added.

- **Properties:**
  - PA2: the systems a frame runs are the systems the pipeline query matches when the frame starts (calls happen between frames).
  - Systems.md "Disabling systems": "When the parent of a system is disabled, it will also be excluded from the builtin pipeline. This makes it possible to disable all systems in a module with a single operation." HierarchiesManual.md: ChildOf and Parent hierarchies behave the same for relationship traversal.
  - Systems.md "Custom pipeline": "Applications can create their own pipelines which fully customize which systems are matched". "Pipelines": "A pipeline is a list of systems that is executed when the ecs_progress/world::progress function is invoked".
- **Code path:**
  - `flecs_pipeline_build` (pipeline.c 263-474) rebuilds only when `ecs_query_match_count` (api.c 717-728, the cache's `match_count`) differs from the count it recorded (267-274).
  - It records the count at 465, and only for a non-empty schedule. An empty schedule returns at 390-392, so it rebuilds every frame.
  - The cache's count goes up:
    - when a table joins or leaves the cache (group.c 169, 181);
    - on every revalidation (match.c 356);
    - when a sorted iteration sees a table's entities change (order_by.c 312-315). Every pipeline query is sorted (pipeline.c 800-801).
  - The builtin pipeline's `!Disabled(up(ChildOf))` term is cacheable. Its rematch observer revalidates the module's children, except for tables with the Parent component and a ChildOf term (cache.c 268-273). Those tables are filtered per entity when the query is iterated (compiler.c 683-727). The system's table does not change, so nothing bumps the count.
  - A fixed-source term and a DontFragment term are not cacheable (validator.c 837-859), so they too are evaluated only when the query is iterated. A DontFragment tag does not move the system to another table.
- **Story:** PA2 reports "frame 1: the pipeline (builtin) runs systems [0], its query matches [] (systems [parentComp], module disabled true, …; cache match_count 1, recorded some 1)".
- **Tape** [pipeline-rebuild generator, determinismo `exhaust`, 1 system, 3 calls], after 10,649 timelines: `pq.kind=0/3 pq.parent=2/3 pq.running0=0/2 pq.foo0=0/2 pq.call=0/8 pq.module=0/2 pq.call=0/8 pq.module=0/2 pq.call=0/8 pq.module=0/2`. Shrunk: builtin pipeline; one system in a Parent hierarchy; progress, disable the module, progress.
- **Theorems:** `update_keeps_schedule` (for every state: an unchanged count keeps the schedule), `parent_disable_keeps_count`, `childof_disable_bumps_count`.
- **C tests:**
  - `pipeline_parent_module_disabled.c`. The ChildOf control runs in a world of its own, because its rebuild would re-evaluate the Parent child too.
  - `pipeline_custom_uncached_term.c`, for both custom pipelines.

### F32. Overriding a DontFragment component that is inherited through two IsA levels constructs it instead of copying it

What happens:
```c
ecs_add_id(world, ecs_id(Position), EcsSparse);
ecs_add_pair(world, ecs_id(Position), EcsOnInstantiate, EcsInherit);
ecs_add_id(world, ecs_id(Position), EcsDontFragment);
base = ecs_new(world); ecs_set(world, base, Position, {10, 20});
mid  = ecs_new_w_pair(world, EcsIsA, base);
inst = ecs_new_w_pair(world, EcsIsA, mid);   // ecs_get: {10, 20}, inherited
ecs_add(world, inst, Position);              // inst owns {0, 0}
```
With two direct bases, the override copies from the wrong one: `inst` IsA `mid` (inheriting 5 from `base`) and IsA `other` (owning 7). `ecs_get` returns 5; the override copies 7.

- **Property:** P-I2, extended to Sparse and DontFragment components: an override starts from the value the entity inherited.
  - PrefabsManual.md "Component Overriding": the override "is initialized with the value from the prefab component".
  - ComponentTraits.md "OnInstantiate trait": an Inherit component "can be overridden manually by adding the component to the instance ... the component is copied from the base entity".
- **Code path:**
  - Adding a Sparse or DontFragment component runs `flecs_component_sparse_insert` (storage/sparse_storage.c 445-489). Its `flecs_component_sparse_override` (415-443) copies from the base that `ecs_search_relation(..., EcsIsA, EcsUp, &base)` finds, or constructs the component.
  - For a DontFragment component, `flecs_table_search_relation_for_tgt` (search.c 204-248) checks the target's sparse set and stops (216-221). For every other component it searches the target's table and recurses through the target's own IsA pairs (222-232).
  - `ecs_get_id` and `ecs_has_id` use `flecs_get_base_component` (addons/prefab/instantiate.c 485-555), which checks the base's sparse set and then recurses (531-538). So `ecs_has` and `ecs_get` see the inherited value; the override does not.
  - Fragmenting Sparse components and a single IsA level copy correctly. flecs's own `Sparse_manual_override_component` covers one level.
- **Story:**
  - P-I2 reports "entity 2 inherited C0 = 5 (ecs_get), but ecs_add overrides it with 0: ecs_search_relation finds no base, so the component is constructed (sparse_storage.c 433-434)".
  - For two bases: "entity 3 inherited C0 = 5 (ecs_get), but ecs_add overrides it with 7: ecs_search_relation finds base 2".
- **Tape** [override generator, determinismo `exhaust`, 1 component, 3 entities, 4 calls], after 5,757,588 timelines: `idf.storage=2/3 idf.trait=1/3 idf.call=0/5 idf.e=1/3 idf.b=0/3 idf.call=0/5 idf.e=2/3 idf.b=1/3 idf.call=1/5 idf.e=0/3 idf.v=0/2 idf.call=2/5 idf.e=2/3`. Shrunk:
  1. e1 IsA e0
  2. e2 IsA e1
  3. set C0 = 5 on e0
  4. add C0 to e2
- **Theorems:**
  - `searchUp_dontFragment_one_level`: for every world, the search for a DontFragment component looks only at the direct targets.
  - `two_levels_get_vs_search` and `two_levels_sparse_found`: the test's world, and its Sparse control.
- **C test:** `override_dont_fragment_2_levels.c`, with the Sparse and one-level controls.

### F33. Worker threads allocate a table's dirty state and a match's monitor without synchronization

What happens. Take a `multi_threaded` system whose query has change detection: EcsQueryDetectChanges, and `ecs_query_changed` called on it once, which turns change detection on. A table matched after that has no monitor and no dirty state. In the next frame every worker passes the table and syncs its monitor:
- two workers both see `table->dirty_state == NULL`, both allocate it from the world's allocator, and both store it. One allocation leaks, and counts written to it are lost.
- two workers allocating for two tables at once can get the same chunk from the block allocator's free list, so two tables share one dirty-state array.
- the same holds for the match's monitor (`cache->allocators.monitors`).

All of this is a data race.

- **Properties:**
  - PW3: an allocator never hands one chunk to two allocations.
  - PW4: no allocation is lost.
  - PW5: no data race. C11 5.1.2.4: two conflicting unsynchronized accesses are undefined behavior. See also Systems.md "Threading" (multi-threaded systems run on the worker threads) and Queries.md "Change Detection".
- **Code path:**
  - Every worker runs the whole query. `ecs_worker_next` (iter.c 1036-1095) calls `ecs_iter_next` on the chained query iterator for every table and keeps a slice of its rows.
  - Each `ecs_query_next` first runs change detection on the previous result (eval_iter.c 217-234, 492-500): `flecs_query_sync_match_monitor` (change_detection.c 581-633).
  - That sync:
    - allocates the monitor when there is none (`flecs_query_get_match_monitor`, 79-138: `flecs_balloc`, then `match->_monitor = monitor`);
    - allocates the dirty state when there is none (`flecs_table_get_dirty_state`, storage/table.c 1432-1450);
    - writes `cache->prev_match_count` (change_detection.c 632).
  - `flecs_balloc` (datastructures/block_allocator.c 141-187) pops a free list: `result = ba->head; ba->head = ba->head->next`. Nothing here takes a lock.
  - Every worker writes `prev_match_count` with the same value: a race, but a benign one.
- **Story:**
  - "world allocator gave chunk 2 to thread 0 (table 0) and to thread 1 (table 1): both read the free-list head before either stored the next one (block_allocator.c 172-173)".
  - "thread 1 stores dirty-state chunk 2 into table 0->dirty_state over chunk 1, which another thread stored after both saw NULL (table.c 1438-1442): chunk 1 leaks".
- **Tapes** [worker model, determinismo `exhaust`, 2 threads]:
  - PW5, after 1 timeline (any interleaving): threads 0 and 1 access `match(table 0)->_monitor`, a write then a read.
  - PW4, 1 table, after 26 timelines: `thread.next=0/2` ×7, `thread.next=1/2` ×2, `thread.next=0/2` ×3. Thread 0 allocates; thread 1 reads the still-NULL pointer before thread 0 stores it.
  - PW3 across two tables, after 133,654 timelines: `thread.next=0/2` ×5, `1/2` ×4, `0/2`, `1/2` ×8, `0/2`, `1/2`, …
  - PW3 on the monitors' allocator, after 10,958 timelines.
- **C test:** `workers_dirty_state_double_alloc.c` (needs threads). How it forces the race:
  - its table has 599 four-byte components, so the table's dirty state is 2400 bytes, a size the block allocator gets straight from the OS (block_allocator.c 150-158);
  - the OS API malloc is wrapped: during the frame, a 2400-byte request waits up to 2 seconds for a second one;
  - a correct program makes one request; with the race both threads arrive, and the dirty state is allocated twice.

## The real flecs on rounds 2 and 3: F17, and three tests corrected

The coordinator ran all 41 earlier C tests; two did not behave as predicted. Both are test errors, and one also exposed a gap in the model's world (a missing builtin system). The code path F17 describes is unchanged.

- **`pipeline_disabled_system_skips_next.c` returned 0** (Init ran once, Update ran once).
  - The test used `ecs_init()`. `ecs_init()` imports FlecsScript (world.c 987-989), whose async addon creates `ProgressTasks` (addons/script/eval/async.c 1428-1433). That is an immediate system without terms in `EcsPreUpdate`, so it is always active and runs before every OnUpdate system.
  - So Init was not the first system of the frame. After Init's sync point, the rebuild found ProgressTasks as the last system that had run (pipeline.c 450-458), resumed after it, and ran Update. F17 needs the self-disabling system to be the first system of the frame.
  - The model's frame (Pipeline.lean, round 2) had only the program's systems. `withBuiltin` now adds ProgressTasks, either before the program's systems (phases from OnUpdate on) or after them (OnLoad, PostLoad). For the test's program, `flecs-search pipe f17` gives:
    - only these systems: "ran [0]", PP4 broken (the prediction);
    - ProgressTasks first: "ran [0, 1, 2]" (what flecs did);
    - ProgressTasks last: "ran [0, 2]", PP4 broken.
  - The test now uses `ecs_mini()` with `ECS_IMPORT(world, FlecsPipeline)`. A new test, `pipeline_disabled_system_skips_next_init.c`, keeps `ecs_init()` and puts the systems in `EcsOnLoad`, before ProgressTasks; the skip is predicted there too.
- **`pipeline_disabled_systems_assert.c` aborted, but at the readonly assert of `flecs_table_ensure`** (storage/table_graph.c 527), not at pipeline.c 467-470.
  - Its regular systems A and C called `ecs_enable(it->world, ...)`. In v4.2, `it->world` is the world itself (`flecs_query_iter` sets `it.world = q->world`, query/engine/eval_iter.c 816), and an operation on the world runs at once (`flecs_add_id`, entity.c 437-450, defers only for a stage).
  - Manual.md: "Pass an explicit stage to enqueue ECS operations. Pass the world to execute operations immediately ... Observer and system iterators expose it->stage for queued operations and it->world for access to the actual world. World operations require writable storage."
  - In a readonly system that creates a table in readonly mode: the abort the coordinator saw.
  - The test now uses `it->stage`, and `ecs_mini()` with the pipeline module. The model predicts the 467-470 assert for it. With ecs_init's ProgressTasks before these systems, all three would run once.
- **`pipeline_wildcard_sync_point.c` (F16)** had the same `it->world` error in its regular Writer system. It would abort at the same readonly assert instead of showing the missing sync point. Corrected to `it->stage`.
- **`workers_spurious_wakeup.c` (F26)** read the stage id from `it->world`, which is the world (stage 0) on every thread, so the worker's sleep never ran. The spurious wakeup did not need it and the test reproduced; corrected to `it->stage`.
- **PP4 corrected.** Round 2's check decided "enabled for the whole frame" from a system's state at the start and the end of the frame. It counted a system that one system disabled and a later one enabled again in the same frame. It now also excludes systems disabled by a system that ran. Round 2's F17 programs are unaffected. Before the correction, the "ProgressTasks first" frame search had 1,056 false positives of this kind; now 0.

## Seen again this round (not new)

- **F17 in ecs_init worlds:** systems in OnLoad or PostLoad run before ProgressTasks and show F17 as in round 2. Systems from OnUpdate on do not.
- **F27:** the general query generator still finds its form (`isTrue` or `count` before `changed`).
- **F19:** the uninitialized fixed-source monitor read is still the most frequent failure of the general query generator.

## Not counted as findings

- **Cascade ordering when a parent's depth changes.** ChildOf depths are cached per `(ChildOf, P)` record (`pair->depth`, storage/component_index.c 1102-1232) and updated recursively on reparenting (non_fragmenting_childof.c 293-319). The tables are revalidated through the ancestry observers, and flecs's own tests cover depth-only changes (`Cascade_rematch_after_depth_only_change*`). Read, not modelled; nothing found.
- **The tree spawner** (addons/prefab/tree_spawner.c) caches, per depth, the tables of a Parent-hierarchy prefab. If a prefab's children change after it was instantiated, it aborts with "cannot change children of prefab ... after it has been instantiated" (tree_spawner.c 166-196); that limitation is stated in its own message. `ParentDepth` is Exclusive (bootstrap.c 922), so the depth replacement in `flecs_spawner_transpose_depth` is sound. Read, not modelled.
- **Component inheritance** (`EcsIdHasBases`). Changing a component's bases after it is used asserts (`flecs_assert_relation_unused`, component_index.c 1006-1021). A query enables inheritance only for ids that have bases when it is created, as ComponentTraits.md "Inheritable trait" documents.

## What was replicated

New files:
- **`Validator.lean`**:
  - `flecs_query_finalize_terms`: Or chains, cacheability, the consistency pass, field indices, sparse clearing and the trailing-Or check (validator.c 965-1312, 837-859);
  - `flecs_query_set_caching_policy` (api.c 74-187);
  - `flecs_query_create_cache`, with the field map as written (api.c 194-243);
  - the cache's second validation (cache.c 700-760) and the error path (api.c 451-457, 276-334; cache.c 646-698).
- **`InhDF.lean`**:
  - `ecs_search_relation` through `flecs_table_search_relation`, `_pairs` and `_for_tgt` (search.c 204-434);
  - `flecs_get_base_component` (instantiate.c 485-555);
  - `flecs_component_sparse_override` (sparse_storage.c 415-443);
  - instantiation of Copy components (table_graph.c 718-790; instantiate.c 301-368).
- **`PipeQ.lean`**:
  - the pipeline's rebuild trigger and the recorded count (pipeline.c 263-474);
  - the cache's match count (group.c 169, 181; match.c 356; order_by.c 312-315);
  - the rematch observers and their Parent exception (cache.c 258-292, 334-430);
  - the per-entity filter of uncached terms.
- **`WorkersCD.lean`**: the worker iteration's change-detection writes, load by load (iter.c 1036-1095; eval_iter.c 217-234; change_detection.c 79-138, 581-633; table.c 1432-1450; block_allocator.c 141-187), on `Determinismo.interleave`.

Changes to earlier files:
- **`Query.lean`**:
  - a self term for a wildcard pair yields one result per matching pair; the further ones are the match's `wildcard_matches`, each vector with an identity;
  - table removal and rematch free and reuse vectors as match.c 48-67 and 174-286 do;
  - full iterations return every wildcard result;
  - `QCursor`, `cursorNext` and `cursorSyncElem` transcribe `flecs_query_cache_next` (cache_iter.c 41-123) and the change detection of `qit->elem`, including the marking of written fields.
- **`QueryProps.lean`**: the `iterBody` operation, `refPairs`, P-IT1, the iteration generator, and four cases. The query menu gained three wildcard and grouped queries.
- **`World.lean`**: `QMatch.pair`, `wildPairs`, `wildVec`; `World.vecNext`, `vecFreed`.
- **`Pipeline.lean`**: ProgressTasks (`withBuiltin`), `frameRuns`, and the PP4 correction.

## What is not exact, and why

- **F29:** the uncached part of a query (the compiler and the query VM, compiler.c and engine/) is not modelled. So the results of `TagA || Position(Sparse), TagC` are not predicted; only that its cache holds `TagA || TagC`.
- **F30:**
  - The model tracks the identities of wildcard vectors, not their arrays. A realloc of a vector's array that leaves `qit->elem` dangling is not flagged.
  - Groups are held by id. A group freed and created again with the same id during the call is not told apart from the old one.
  - Cascade (depth groups) is not in the query model. So a table moving to a later group during an iteration, which would be returned twice, is not searched.
  - Wildcards: one wildcard term per query, a self term on a pair.
  - The stepwise iteration covers queries without `order_by` (table slices) and without fixed-source terms.
- **F31:** systems, the module, the phase and `Game` are reduced to the flags the pipeline query reads. Calls happen between frames.
- **F32:** table components use the documented override value. Round 3 models their override cache (F24).
- **F33:**
  - two to three threads, one or two tables, and allocation by popping a free list;
  - the 9 steps per table follow the C code; the rest of each worker's work is not modelled.
- The limits of rounds 1 to 3 remain.

## Assumptions

- **Build:** debug, asserts on. Tests use `ecs_mini()` unless they need ecs_init's addons; pipeline tests import FlecsPipeline.
- **Systems:** they enqueue through `it->stage`, as Manual.md asks (round 4 correction).
- **Traits:** Sparse, DontFragment and OnInstantiate are added before a component is used.
- **Iteration:** the call made during an iteration is a world call on entities outside the iterated table, which is locked as the C++ `each` locks it.
- **Threads:** the OS API's malloc may be wrapped (`ecs_os_api.malloc_`), as F33's test does.
- **Ids in the query model:** C0 = 60, C1 = 61, the Remove relationship 387, the Delete relationship 388, entities from 389.

## Properties and their sources

Broke means some program violated the property; Held means it held in every run.

1. **P1 for query creation:** no crash creating a query from valid terms (Manual.md "Error handling"; ComponentTraits.md "Sparse trait"). **Broke** (F29).
2. **PV2:** the cache holds the query's cacheable terms, chain by chain (cache.c 11-17). **Broke** (F29).
3. **PV3:** the field map maps each cache field to the query field of its terms (cache.c 15-17). **Held.**
4. **P-IT1:** an entity that matches before and after a call made during an iteration, and that the call does not move, is returned exactly once per matched pair (Queries.md "Iteration"). **Broke** (F30).
5. **P1 for iteration:** the iterator reads no freed vector or group. **Broke** (F30, wildcard vector).
6. **PA2:** a frame runs the systems the pipeline query matches when it starts (Systems.md "Disabling systems", "Custom pipeline", "Pipelines"). **Broke** (F31).
7. **P-I2 for Sparse and DontFragment:** an override starts from the inherited value (PrefabsManual.md "Component Overriding"; ComponentTraits.md "OnInstantiate trait"). **Broke** for DontFragment (F32); **held** for Sparse.
8. **PW3:** an allocator gives one chunk to one allocation. **Broke** (F33).
9. **PW4:** no allocation is lost. **Broke** (F33).
10. **PW5:** no data race between worker threads (C11 5.1.2.4). **Broke** (F33).
11. **PP4 in ecs_init worlds:** every system enabled and active for the whole frame runs once (Systems.md "Pipelines"). **Broke** when the systems come before ProgressTasks (F17); **held** when they come after it.

The 44 properties of rounds 1 to 3 (20, 11 and 13) are still checked by their generators, for 55 in all.

## Search runs and results

Validator:
- `val exhaust`, 2 components, 2 terms: **complete**, 82,944 programs, 28 failing, all P1 (trailing Or).
- `val exhaust`, 3 components, 3 terms: **complete**, 20,155,392 programs, 14,616 failing:
  - P1 with the trailing Or: 12,600
  - P1 with "same source": 1,008
  - P1 with "term after OR expression": 672
  - PV2: 336
  - PV3: none

Iteration:
- `query iter-exhaust`: **complete**, 786,432 programs, 1,208 failing: P-IT1 92, freed wildcard vector 1,120.
- The general query generator (round 2's, with the new `iterBody` operation and the wildcard queries) found neither: `query lib explore` 300,000 timelines (seed 7, 3 entities) and 400,000 (seeds 11 and 12, 4 entities). Both structures need about six specific calls.
- `query cases`: round 3's seven cases give round 3's output unchanged; the three F30 cases fail as described.

Pipeline rebuilds:
- `pq exhaust`, 2 systems, 3 calls: **complete**, 364,500 programs, 25,008 failing, all PA2: builtin pipeline 4,440; fixed source 7,232; DontFragment 13,336.
- `pq exhaust`, 1 system, 4 calls: **complete**, 527,076 programs, 42,208 failing, all PA2: builtin 8,732; fixed source 16,738; DontFragment 16,738.

Overrides:
- `idf exhaust`, 1 component, 3 entities, 4 calls: **complete**, 7,290,000 programs, 48 failing, all P-I2 (DontFragment, Inherit, two levels).
- `idf explore`, 2 components, 4 entities, 7 calls, seed 1: 2,000,000 programs, 91 failing, all P-I2 of the same kind. The two-bases variant is a hand-written case (`idf cases`).

Workers:
- `wcd exhaust`: see F33's tapes. Without the race checks, with 2 threads and 1 table: PW4 after 26 timelines, PW3 on one table after 102.

Pipeline frames (the F17 correction, with corrected PP4):
- the program's systems only, 2 systems: **complete**, 65,536 programs, 832 failing (PP4, F17).
- the program's systems only, 3 systems: 3,000,000 programs (bound not reached), 164,164 failing: PP4 160,468; PP1 at pipeline.c 467-470 3,696.
- ProgressTasks last (OnLoad systems), 3 systems: 3,000,000 programs, 472,636 failing, all PP4.
- ProgressTasks first (OnUpdate systems), 3 systems: 3,000,000 programs, none failing.

Regressions (this round's binary):
- `cases` (the world cases of rounds 1-3) and round 3's `query cases`: output identical to round 3's.
- `act exhaust` 6 calls: 1,062,882 programs, 796 failing, as in round 3.
- `inh-small` 5 calls: 400,000 programs, 12 failing, as in round 3.
- `query explore` seed 21: 200,000 programs, 2,038 failing (the generator now has two more operation kinds and three more queries, so the counts differ from round 3's):
  - P1 uninitialized read: 1,828 (F19)
  - the rest are P-CD1, in F18, F19 and F27 forms
  - no P-Q1, no P-IT1, no P1 crash.

## Theorems

There is no `sorry`. Every theorem uses only `propext`, `Classical.choice` and `Quot.sound` (printed by `Axioms.lean`). The concrete ones are checked by the kernel (`decide +kernel`).

New in `TheoremsR4.lean`:
- `or_sparse_cache_crash` (F29): `TagA || Position(Sparse)` crashes with cache kind Auto and as a system's query.
- `or_sparse_uncached_ok`: uncached, or with Position a table component, the query is created.
- `or_sparse_merges_chain`: with a term after the chain, the cache's query is `C0 || C2`, with one field.
- `searchUp_dontFragment_one_level` (F32), for every world, component, entity and depth: the override's search for a DontFragment component that is not DontInherit only looks at the direct IsA targets' own components.
- `two_levels_get_vs_search`: in the test's world, `ecs_get` finds 5 and the search finds no base.
- `two_levels_sparse_found`: with a fragmenting Sparse component, the search finds the base.
- `update_keeps_schedule` (F31), for every state: when the cache's count equals the recorded one, `flecs_pipeline_update` keeps the schedule.
- `parent_disable_keeps_count` and `childof_disable_bumps_count`: disabling the module leaves the count unchanged for a Parent child's pipeline, and bumps it for a ChildOf child's.

The theorems of rounds 1 to 3 are unchanged and still build.

## Library gaps

1. Round 3's gaps remain: property filters erase digits from details, not from property names, and `interleave` has no condition variables.
2. `Determinismo.Threads` has no notion of a data race. `WorkersCD.lean` records every access and checks pairs itself.
3. `decide` does not reduce the models' `Id.run do` loops; `decide +kernel` does.

## Model errors and test errors corrected

- **Pipeline.lean's world lacked ecs_init's builtin systems (F17):** ProgressTasks, an always-active immediate system in PreUpdate. Added as `withBuiltin`.
- **Pipeline.lean's PP4** counted systems disabled and enabled again within a frame. Corrected.
- **The F16, F17 and F26 tests** used `it->world` where v4.2 wants `it->stage`. F17's tests also needed a world without ProgressTasks before their systems. Corrected; see the section above.
- **This round's first iteration runs** let the stepwise iterator run on `order_by` queries (it does not transcribe table slices) and let its call delete a query's fixed source or make a ChildOf cycle. Those programs are excluded now, as round 2 excludes them for other calls. The counts above are from the corrected runs.

## C tests (tests/flecs_lean/)

All 48 compile with `cc -c` against `upstream/distr/flecs.h`; none was run this round.

Round 4:
- F29: `query_or_sparse_cache_crash.c` (a SIGSEGV confirms)
- F30: `query_iter_skips_table.c`
- F31: `pipeline_parent_module_disabled.c`, `pipeline_custom_uncached_term.c`
- F32: `override_dont_fragment_2_levels.c`
- F33: `workers_dirty_state_double_alloc.c` (needs threads)
- F17, new: `pipeline_disabled_system_skips_next_init.c`

Corrected: `pipeline_disabled_system_skips_next.c` and `pipeline_disabled_systems_assert.c` (F17), `pipeline_wildcard_sync_point.c` (F16), `workers_spurious_wakeup.c` (F26).

## For round 5

- **Queries:**
  - model the compiler and VM for Or chains, to predict F29's results with a term after the chain;
  - cascade groups in the query model (a table moving to a later group during an iteration);
  - `EcsQueryMatchEmptyTables`;
  - vector reallocation under `qit->elem`;
  - `order_by` slices in the stepwise iterator.
- **Pipeline:**
  - phase reordering mid-frame: a system's commands change a phase's DependsOn and move systems before the resume point;
  - a phase disabled mid-frame with ProgressTasks in the schedule.
- **Workers:** allocator races between workers for different size classes (`flecs_allocator_get` creating a size class); stage allocators.
- **Inheritance:**
  - OnSet through prefab variants for DontFragment components;
  - the tree spawner;
  - auto-override (`AUTO_OVERRIDE | C`) of DontFragment components through two levels: `flecs_instantiate_override_dont_fragment` reads only the direct base's table.
- **C tests:** run F29 to F33 and the corrected F16, F17 and F26 tests.
