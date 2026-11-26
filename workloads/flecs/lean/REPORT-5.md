# flecs v4.2.0 in Lean 4 — round 5 report

Everything is in this directory:
- `FlecsLean/*.lean`: the model and its searches. New this round:
  - `OrVM.lean`: the query compiler and the query VM for cached queries whose uncached part is Sparse terms (F34);
  - `Spawner.lean`: the tree spawner of `Parent` hierarchies against the `ChildOf` path (F39);
  - `TheoremsR5.lean`: this round's theorems.
  - Extended: `Query.lean` and `World.lean` (cascade groups, group identities, table-array reallocation, order_by slices in the stepwise iterator: F35, F36, F40), `QueryProps.lean` (round 5 iteration generator, P-IT2, cases), `InhDF.lean` (auto overrides: F38), `Pipeline.lean` (phases, phase reordering and disabling: F37), `WorkersCD.lean` (allocator size classes: F33 extended).
- `Main.lean`: the `flecs-search` program.
- `tests/flecs_lean/*.c`: 57 C tests; 9 new (F34-F40), none changed. `README.txt` maps them to predictions.
- `.jobs/r5x/*.log`: this round's run logs. `scratch/r5-runs.sh a|…|k` re-runs them (one job per part); `scratch/r5-cases.sh` prints every case. `scratch/tape.py` prints tapes in `name=v/n` form.

To build, run `lake build FlecsLean flecs-search`. New modes of `.lake/build/bin/flecs-search`:
- `or explore|exhaust|lib|cases`: partially cached queries, compiled and run (F34).
- `query iter5-explore|iter5-exhaust|iter5-lib`: iterations of cascade, grouped, change-detecting and order_by queries with a call after the k-th result (F35, F36, F40). `query cases` and `query trace NAME` include the round 5 cases.
- `pipe phase-exhaust|phase-lib|phase-exhaust-noreorder|phase-cases`: frames with two phases whose systems reorder or disable phases (F37).
- `idf auto-explore|auto-exhaust|auto-lib`: instantiation with auto overrides (F38).
- `sp exhaust|lib|cases`: prefab hierarchies instantiated after their children change (F39).
- `wcd … RACES …` with RACES `2` (size classes, no race reports) or `3` (size classes and races): F33 extended.

Line numbers refer to files under `src/` at v4.2.0 unless a path says otherwise. Every C test needs a debug build (asserts on) and uses `ecs_mini()`; the pipeline test imports FlecsPipeline, which brings no builtin system. A test returns 0 when flecs behaves as documented; a non-zero return, a crash or an abort confirms the prediction; 2 means its setup did not hold. In a tape, `name=v/n` means the named decision took value `v` of `n` options.

## The real flecs on rounds 1–4

The coordinator ran the 48 earlier C tests on the real flecs v4.2.0 (asserts on, macOS and Linux):
- F1–F33 behaved as predicted, with three exceptions: F2's original test (corrected in round 2), F17's first test (corrected in round 4) and F19's uninitialized read, which neither valgrind nor MemorySanitizer showed.
- Round 4's corrected tests confirmed F17 whole (the skip, and the `cur_op` assert) and F16's missing sync point.
- F26 still aborts; F29 segfaults; F33's test saw the dirty state allocated twice.

No test is changed this round: nothing showed a model error behind any of them. `change_detection_fixed_source_added.c` keeps its `flecs_lean: valgrind` comment line.

## Counterexamples

### F34. A cached query whose Or chain starts with a table term and ends with a Sparse term, with a term after the chain, returns the wrong entities, and compiling it writes before the op array

What happens:
```c
ecs_add_id(world, ecs_id(Position), EcsSparse);
q = ecs_query(world, {
    .terms = {{ TagA, .oper = EcsOr }, { ecs_id(Position) }, { TagC }},
    .cache_kind = EcsQueryCacheAuto });       // ops[-1].next is written
e1 = TagA, Position;  e2 = TagA, TagC;  e3 = Position, TagC   (created after q)
iterate q                                     // returns e1 only
```
The documented result is e2 and e3. Without a cache the query returns them. Without the term after the chain the query crashes when it is created (F29).

- **Properties:**
  - PQ-OR1: a query's results are the tables that match its terms, each once. Queries.md "Or" operator and "Iteration"; ComponentTraits.md "Sparse trait": "ECS operations and queries work as expected with sparse components".
  - P1: no access outside the compiler's op array (Manual.md "Error handling").
- **Code path:**
  - The validator leaves TagA and TagC cacheable and Position not (validator.c 1075-1087, 1234-1238; F29). The cache holds `TagA || TagC` (api.c 194-243; cache.c 700-760), a valid query.
  - `flecs_query_compile` (compiler/compiler.c 1047-1340) emits SetIds (1093-1110), then one Cache op that stands for every cacheable term (`flecs_query_insert_cache_search`, 632-747), then compiles Position alone.
  - `flecs_query_compile_term` (compiler_term.c 1147-1563) sees Position as the last term of an Or chain whose first term it never compiled: `is_or` true, `first_or` false (1179), `last_or` true. It sets `ctx->written` to the chain's saved write state, which no first term saved (1222), and calls `flecs_query_end_block_or` with `ctx->cur->lbl_begin == -1`:
    - `first = &ops[-1]` (306): it reads `ops[-1].flags` and, when the garbage has the source bit, `ops[-1].src`; it writes `ops[-1].next` (309). The ops are `stage->operations`, an array from `ecs_os_realloc`; the write lands 42 bytes before it;
    - it sets the Position op's `prev` and the End's `prev` to `lbl_begin`, -1 (310-311).
  - At run time (`flecs_query_run_until`, engine/eval.c 1733-1785): the Cache op yields the first non-empty cached table (cache_iter.c 356-378); the And op tests Position on it (`flecs_query_with`, eval.c 150-252). On failure it jumps to label -1, which ends the iteration (1776). On success the End and Yield follow. The next `ecs_query_next` redoes the End (`qit->op`, eval_iter.c 583), whose `prev` is -1: the iteration ends.
  - So the query returns the first cached table if it has Position, else nothing. TagC is never tested.
  - Other forms:
    - `TagA || Position || TagB, TagC`: TagB loses its cache flag after Position (the consistency pass), so Position and TagB are compiled after the cache. The same `end_block_or` runs with `lbl_begin == -1`; the scan from op 0 also sets SetIds' `prev` to the TagB op (295-297).
    - `Position || TagA, TagC` is consistent: the pass sees Position's cleared flag, so the whole chain is uncached and compiled as a complete Or block (theorem `or_sparse_first_complete_block`).
- **Story:**
  - P1 reports "compiler_term.c 306-309: flecs_query_end_block_or reads ops[-1].flags and ops[-1].src and writes ops[-1].next (lbl_begin is -1: the chain's first term was compiled into the cache, so no Or block was begun)".
  - PQ-OR1 reports "the cached query yields tables [0] but the tables [1, 2] match its terms (ops: 0:SetIds[prev -1, next 1], 1:Cache[prev 0, next 2], 2:And(C1)[prev -1, next 3], 3:End[prev -1, next 4], 4:Yield[prev 3, next 5])".
- **Tape** [Or-chain generator, determinismo `exhaust`, 3 components, 3 terms, 2 tables], after 96,434 timelines: `or.storage=0/2 or.storage=0/2 or.storage=1/2 or.comp=0/3 or.oper=1/4 or.comp=2/3 or.oper=0/4 or.comp=0/3 or.oper=0/4 or.table=0/7 or.table=1/7`. Shrunk: components [table, table, Sparse]; query `C0 || C2, C0`; tables `[C0]`, `[C1]`. Both P1 and PQ-OR1 (the query yields nothing; table `[C0]` matches).
- **Theorems:** `or_after_chain_compile` (the five ops, their labels, one access to `ops[-1]`), `or_sparse_first_complete_block`.
- **C test:** `query_or_sparse_term_after_chain.c`. It wraps the OS API allocator so that every block has a zeroed 64-byte guard before it, and checks the guards when blocks are freed or reallocated. With the guard zeroed, `ops[-1].flags` reads 0 and the compiler takes the same path every run. Confirmed by the wrong entities and by a changed guard. The uncached query is the control.

### F35. While a cascade query is iterated, a call that changes a parent's depth makes the iterator return a table again, or read a freed group and stop

What happens, first form:
```c
q = ecs_query(world, { .terms = {{ ecs_id(Position) },
        { ecs_id(Position), .src.id = EcsCascade, .oper = EcsOptional }},
    .cache_kind = EcsQueryCacheAuto });
p2, p1 roots; c2 child of p2; c1 child of p1     (all with Position)
iterate: roots, c2's table, c1's table; then
    ecs_add_pair(world, p1, EcsChildOf, p2);       // c1's table is locked
the iteration continues and returns c1 again
```
Second form: when the moved table was alone in its group, the group is freed while the iterator is in it:
```c
x root; m child of x (no Position); p1 root; c1 child of p1; g child of m
iterate: p1 (depth 0), c1 (depth 1, alone); then
    ecs_add_pair(world, p1, EcsChildOf, m);
the next ecs_query_next reads the freed group; g (depth 2) is not returned
```

- **Properties:**
  - P-IT1 (round 4): an entity that matches the query before and after a call made during the iteration, and that the call does not move, is returned exactly once. Queries.md "Iteration" (C++): moving entities "can cause unwanted side effects while iterating a table, like iterating an entity twice, or missing an entity. To prevent this from happening, a table is locked by the C++ each and run functions, meaning no entities can be moved from or to it." Queries.md, traversal flags: Cascade iterates "in breadth-first order"; "Grouping": lower group ids are iterated before higher ones.
  - P1: no read of freed memory.
- **Code path:**
  - A cascade query groups its cached tables by ChildOf depth (`flecs_query_cache_group_by_cascade`, query/cache/cache.c 179-191; `flecs_relation_depth`, search.c 517-553), in ascending order (`EcsQueryGroupByOrdered`, cache.c 866-872; `flecs_query_cache_group_insert`, group.c 37-54).
  - The iterator walks a group's table vector, then follows `group->next` (cache_iter.c 41-123, 49-62).
  - Reparenting updates the depth of the children's `(ChildOf, parent)` records (storage/component_index.c 1166-1231). The ancestry observer enqueues a revalidation of the children's tables (cache.c 334-430), which the end of the call runs (`flecs_query_revalidate_table`, match.c 328-365). `flecs_query_cache_move_table_to_group` (group.c 249-274) appends the table to the group of its new depth and removes it from the old one.
  - First form: c1's table moves to group 2, created after group 1. The iterator, done with group 1, follows `next` into group 2 and returns c1's table again.
  - Second form: c1's table was alone in group 1. `flecs_query_cache_remove_table_from_group` (176-213) removes the group: `flecs_query_cache_remove_group` (118-130) unlinks it, sets its `next` to NULL, finalizes its vector, and frees it with `ecs_map_remove_free` (109, an `ecs_os_free`; the group came from `ecs_map_insert_alloc_t`, 66). The next `flecs_query_cache_next` reads `qit->tables` (`&group->tables`) and `group->next` from the freed block. Usually `next` still reads NULL and the iteration ends: g, at depth 2, is never returned.
  - The default group (depth 0) is part of the cache. When it empties, the iterator stops without reading freed memory (round 4).
- **Story:**
  - P-IT1 reports "query 0: entity 392 (pair 0) matched before and after the call made after result 3, and the call did not move it, but the iteration returned it 2 times (returned [(389, 0), (391, 0), (390, 0), (392, 0), (392, 0)], …)".
  - P1 reports "the iterator's group (identity (some 2)) was freed while it was iterated: the next ecs_query_next reads its tables and next (cache_iter.c 49-62) after flecs_query_cache_remove_group freed it (group.c 118-130, 109 ecs_map_remove_free)". P-IT1 reports g returned 0 times.
- **Tapes** [round 5 iteration generator, `query iter5-lib exhaust`; the exhaustive order starts with the cascade query]:
  - P-IT1, after 2,679 timelines: `it5.query=0/5 it5.kind=0/4 it5.kind=0/7 it5.kind=0/7 it5.kind=0/7 it5.kind=4/7 it5.parent=1/4 it5.changed=0/2 it5.k=1/4 it5.target=1/5 it5.body=0/5 it5.newparent=0/5`. Shrunk:
    1. e1 is a root with C0; e4 is a child of e1 with C0.
    2. After the second result (e4's table, group 1), e1 becomes a child of e0.
    3. e4's table moves to the new group 2, and e4 is returned again.
  - Freed group, after 28,705 timelines: `it5.query=0/5 it5.kind=0/4 it5.kind=0/7 it5.kind=0/7 it5.kind=3/7 it5.kind=4/7 it5.parent=3/4 it5.changed=0/2 it5.k=1/4 it5.target=3/5 it5.body=0/5 it5.newparent=0/5`. Shrunk:
    1. e2 is a root with C0; e3 is a root without C0; e4 is a child of e3 with C0.
    2. After the second result (e4's table, alone in group 1), e3 becomes a child of e0.
    3. Group 1 is freed while it is iterated.
  - The generator's random runs (`iter5-explore`, 300,000 programs) found both forms: P-IT1 937 times (with F40's form) and freed groups 36 times.
- **C tests:**
  - `query_cascade_table_twice.c`;
  - `query_cascade_group_freed.c`. The OS API free fills the block with 0xA5 and keeps it, so the stale group's count reads negative and its `next` reads 0xA5A5A5A5A5A5A5A5: the iterator follows it and crashes. Without the wrapper, valgrind reports the read, and the iteration usually just ends without g.

### F36. A call during an iteration that adds a table to the iterated group can reallocate the group's array; with change detection the next `ecs_query_next` reads and writes the freed array

What happens:
```c
q = ecs_query(world, { .terms = {{ ecs_id(Position), .inout = EcsIn }},
    .cache_kind = EcsQueryCacheAuto, .flags = EcsQueryDetectChanges });
32 tables with Position (the group's array is full: capacity 32)
ecs_query_changed(q);                          // turns change detection on
iterate; after the first result:
    ecs_set(world, late, Position, {2, 2});    // late had only Tag_31: a 33rd table
the next ecs_query_next syncs the monitor of qit->elem, in the freed array
```

- **Properties:**
  - P1 (iteration): the iterator reads no freed memory (Manual.md "Error handling").
  - Queries.md "Iteration" (C++ each locks the iterated table; the call moves no entity of it) and "Change Detection".
- **Code path:**
  - `flecs_query_cache_next` stores a pointer to the current match in `qit->elem` (cache_iter.c 104).
  - A new matching table is appended to its group (`flecs_query_cache_add_table_to_group`, group.c 150-171: `ecs_vec_append`, 157-158). A full vector grows to the next power of two (vec.c 366-379, 179-215), and `flecs_brealloc` frees the old array (block_allocator.c 287-326).
  - The next `ecs_query_next` starts with change detection on the previous result (eval_iter.c 217-234, 492-500). When the query has `EcsQueryHasChangeDetection` it calls `flecs_query_sync_match_monitor(impl, qit->elem)` (change_detection.c 581-633). That reads `match->_monitor` and `match->base.table`, and writes the monitor; if the match has no monitor it allocates one and stores it in the freed match (79-138).
  - A cache match is 80 bytes, so 32 tables make a 2560-byte array. That size comes straight from the OS (block_allocator.c 150-158: one chunk per block) and is freed with `ecs_os_free`. Smaller arrays go back to the block allocator's free list: the stale reads still happen, but a free-list pointer overwrites the first match's table field.
  - F30 freed `wildcard_matches` vectors through `qit->tables`. This is a group array, reached through `qit->elem`, and it needs only a new matching table: no table deletion, no rematch.
- **Story:** P1 reports "ecs_query_next syncs the monitor of qit->elem (eval_iter.c 225-230, change_detection.c 581-633), a pointer into table array 1 of group (some 0), which was freed: an ecs_vec_append that grew the array (group.c 157-158, vec.c 373-375, block_allocator.c 314) …".
- **Tape** [round 5 iteration generator, `query iter5-lib explore`, seed 3], after 262 timelines: `it5.query=3/5 it5.kind=0/4 it5.kind=2/7 it5.kind=4/7 it5.parent=0/2 it5.kind=0/7 it5.kind=4/7 it5.parent=2/4 it5.changed=1/2 it5.k=0/4 it5.target=2/5 it5.body=3/5`. Shrunk: `[in] C0` grouped by the Delete relationship, with change detection on; four tables in the default group; after the first result, C1 is added to an entity of another table, which makes a fifth table. The general query generator of rounds 2-4 found it too (11 of 200,000 programs, seed 21).
- **C test:** `query_iter_table_array_realloc.c`, with the same free wrapper as F35's: the stale `base.table` reads 0xA5A5A5A5A5A5A5A5 and the sync crashes.

### F37. A system whose commands reorder the phases makes the pipeline skip, in that frame, the systems that now come before it

What happens:
```c
Pa, Pb: phases, both DependsOn OnUpdate
S1 in Pa: ecs_add_pair(it->stage, Pa, EcsDependsOn, Pb)   (first frame only)
S2 in Pb, immediate
ecs_progress(world, 0);     // S1 runs; S2 does not
ecs_progress(world, 0);     // S2, S1
```
In an `ecs_init()` world, ProgressTasks runs before both and S2 is still skipped.

- **Property:** PP4: every system that is enabled and active for the whole frame runs once. Systems.md "Pipelines": "A pipeline is a list of systems that is executed when the ecs_progress/world::progress function is invoked"; "Builtin Pipeline": "Systems are ordered using a topology sort on the DependsOn relationship"; Queries.md "Grouping": the pipeline query groups systems by their DependsOn depth.
- **Code path:**
  - The builtin pipeline query has `Phase(cascade(DependsOn))` (addons/pipeline/pipeline.c 978-991) and orders by entity id within a group (`flecs_entity_compare`, 801). S1 and S2 are in one group, ordered S1, S2.
  - S2 is immediate, so there is a merge before it. The merge applies `Pa DependsOn Pb`. The cache regroups S1's table one level deeper (the ancestry observer and `flecs_query_cache_move_table_to_group`, as in F35), which bumps `match_count`. `flecs_pipeline_update` (491-519) then rebuilds the schedule (263-474): S2, S1.
  - The rebuild resumes after the last system in the new order whose `last_frame` is this frame (450-458). That is S1, the last system, so `cur_op` becomes NULL and the frame ends.
  - F17 skips through the same resume point when the system that ran leaves the schedule. Here every system stays in it and only the order changes; ProgressTasks does not help, because it is not the last system that ran.
  - A phase disabled mid-frame, with ProgressTasks first: never a skip (see "Search runs"). Without ProgressTasks it is F17.
- **Story:** PP4 reports "system 1 was enabled and active for the whole frame but ran 0 times (ran: [0])".
- **Tape** [phase generator, `pipe phase-lib exhaust`, 2 systems], after 153 timelines: `pipe.frame.terms=0/4 pipe.immediate=0/2 pipe.phase=0/2 pipe.peffect=1/5 pipe.peffect.ph=0/2 pipe.frame.terms=0/4 pipe.immediate=1/2 pipe.phase=1/2 pipe.peffect=0/5`. This is: S0 in phase 0, moves phase 0 after the others; S1 in phase 1, immediate.
- **Theorem:** `reorder_resume_past_end`: after S0's merge, the rebuilt schedule is [S1, S0] and `cur_op` is none.
- **C test:** `pipeline_phase_reorder_skips.c` (`ecs_mini()` with FlecsPipeline).

### F38. An instance of a prefab variant does not own a DontFragment component that the variant's base auto-overrides

What happens:
```c
ecs_add_id(world, ecs_id(Defense), EcsDontFragment);
ecs_add_pair(world, ecs_id(Defense), EcsOnInstantiate, EcsInherit);
ship = prefab; ecs_set(world, ship, Defense, {50}); ecs_auto_override(world, ship, Defense);
freighter = prefab, IsA ship;
inst = ecs_new_w_pair(world, EcsIsA, freighter);
ecs_owns(world, inst, Defense);     // false: inst inherits freighter's Defense
```
Controls: an instance of `ship` owns Defense; with Defense a table component, `inst` owns it. The same holds when the base has the auto-override flag but no value: the variant's instance should get a default-constructed component and gets none.

- **Property:** P-I3: an instance owns every component that its base, or a base of its base, auto-overrides. PrefabsManual.md "Auto Overriding": an auto override "flags a component on the prefab to be always overridden on instantiation" (`ecs_owns(world, inst, Defense); // true`); also "Prefab Variants". ComponentTraits.md "DontFragment trait" (the Sparse storage) and "Sparse trait" ("ECS operations and queries work as expected with sparse components").
- **Code path:**
  - For a table component, `flecs_add_overrides_for_base` (storage/table_graph.c 718-791) adds every `AUTO_OVERRIDE` id of the base's type to the instance's type, and recurses into the base's own IsA targets (780-789).
  - For a DontFragment component it adds nothing. It only flags the table that holds the `AUTO_OVERRIDE` id (`EcsTableOverrideDontFragment`, 739-746).
  - The override itself is done by `flecs_instantiate` (addons/prefab/instantiate.c 393-415). Its `flecs_instantiate_override_dont_fragment` (370-391) reads only the direct base's table. Freighter's table has no `AUTO_OVERRIDE` id.
  - `flecs_instantiate_dont_fragment` (301-368) skips Inherit components of a base the instance has an IsA pair to. So inst inherits Freighter's own Defense, which Freighter got from its own instantiation.
  - F32 is the manual override (`ecs_add`) through two levels: a different function (`flecs_table_search_relation_for_tgt`).
- **Story:** P-I3 reports "entity 2 (IsA 1) does not own C0, which entity 0 auto-overrides (dontFragment, inherit): flecs_instantiate_override_dont_fragment (instantiate.c 370-391) reads only the direct base's table, and the table graph only flags the base that holds AUTO_OVERRIDE (table_graph.c 739-746); ecs_get returns the inherited some 50".
- **Tape** [override generator with auto overrides, `idf auto-lib exhaust`, 1 component, 3 entities, 4 calls], after 1,168,532 timelines: `idf.storage=2/3 idf.trait=0/3 idf.call=0/4 idf.e=0/3 idf.b=0/3 idf.call=0/4 idf.e=1/3 idf.b=0/3 idf.call=2/4 idf.e=0/3 idf.call=0/4 idf.e=2/3 idf.b=1/3`. Shrunk: C0 DontFragment; e1 IsA e0; auto override C0 on e0 (no value); e2 IsA e1.
- **Theorems:**
  - `auto_override_variant_inherits`: the C test's world; the variant owns 50, the instance owns nothing and inherits 50.
  - `auto_override_controls`: the table-component and one-level controls own 50.
  - `autoVisit_direct_first` (for every world): the walk that collects auto-override flags reads the direct base first, then its IsA targets.
- **C test:** `auto_override_dont_fragment_variant.c`, with both controls.

### F39. With a Parent hierarchy, instances made after a prefab child changes copy the prefab child's old type; a Sparse component added to it aborts the next instantiation

What happens:
```c
prefab = ecs_new_w_id(world, EcsPrefab);
child = ecs_new_w_parent(world, prefab, NULL); ecs_set(world, child, Position, {1, 2});
i1 = ecs_new_w_pair(world, EcsIsA, prefab);        // builds the TreeSpawner
ecs_set(world, child, Velocity, {3, 4});
i2 = ecs_new_w_pair(world, EcsIsA, prefab);        // i2's child: Position, no Velocity
```
With `ecs_new_w_pair(world, EcsChildOf, prefab)` instead, i2's child has Velocity {3, 4}.
- If the component set on the prefab child is Sparse, the second instantiation aborts (instantiate.c 124).
- If it has an `on_set` hook, the second instantiation aborts too (component_actions.c 679).
- A component removed from the prefab child is still added, default-constructed, to later instance children.

- **Properties:**
  - P-SP1: an instance's children own the components their prefab child has when the instance is made. ComponentTraits.md "OnInstantiate trait": the default "is Copy, which means that the component is copied to the instance". HierarchiesManual.md "Parent storage details" presents the TreeSpawner, which "caches the structure and tables of the prefab hierarchy", as a performance measure of Parent hierarchies.
  - P1: no internal assert.
- **Code path:**
  - A prefab whose children use `Parent` is instantiated through a TreeSpawner (addons/prefab/instantiate.c 424-440).
  - The first instantiation builds it (`flecs_prefab_spawner_build`, tree_spawner.c 199-224): for each child, the table its instance children go to, computed from the child's table at that moment (`flecs_prefab_spawner_build_type`, 10-60).
  - Later instantiations put each instance child straight into the cached table (`flecs_spawner_instantiate`, 226-350).
  - Then `flecs_instantiate_sparse` (instantiate.c 73-133) walks the prefab child's current table:
    - for a Sparse component it copies into the instance child's sparse storage, after asserting that the instance child has the component (122-124);
    - for every component it notifies OnSet; with an `on_set` hook, `flecs_notify_on_set_w_cr` asserts that the instance child's table has the component (component_actions.c 672-687).
  - Nothing rebuilds the spawner when a prefab child's components change. Only changes to the set of children are refused (`flecs_tree_spawner_assert_not_instantiated`, tree_spawner.c 166-197, called from storage/non_fragmenting_childof.c 49, 75, 255). The ChildOf path reads each child's current table (instantiate.c 135-299).
- **Story:**
  - P-SP1 reports "instance 2: its child for prefab child 0 owns [(0, 1)], the prefab child owns [(0, 1), (1, 3)] (ComponentTraits.md "OnInstantiate trait": Copy); the tree spawner's tables were built at the first instantiation (tree_spawner.c 199-224) and are not rebuilt when a prefab child's components change".
  - P1 reports "prefab child 0 has Sparse C1, which the spawner's cached table for it lacks: flecs_instantiate_sparse asserts (instantiate.c 122-124 …)".
- **Tapes** [spawner generator, `sp lib exhaust`, 2 components, 2 children, 4 calls]:
  - P-SP1, after 10 timelines: `sp.storage=0/2 sp.hook=0/2 sp.storage=0/2 sp.hook=0/2 sp.hier=0/2 sp.child=0/4 sp.child=0/4 sp.call=0/3 sp.call=0/3 sp.call=1/3 sp.k=0/2 sp.c=0/2 sp.call=0/3`. Shrunk: instantiate; set C0 on prefab child 0; instantiate.
  - P1 (hook), after 209,971 timelines: `sp.storage=0/2 sp.hook=0/2 sp.storage=0/2 sp.hook=1/2 sp.hier=0/2 sp.child=0/4 sp.child=0/4 sp.call=0/3 sp.call=0/3 sp.call=1/3 sp.k=0/2 sp.c=1/2 sp.call=0/3`.
- **Theorem:** `spawner_stale_type`: the C test's program gives the second instance's child [Position] with a Parent hierarchy and [Position, Velocity] with ChildOf.
- **C tests:**
  - `tree_spawner_stale_child_type.c`, with the ChildOf control;
  - `tree_spawner_stale_sparse_assert.c`: an abort confirms; the handler prints FAIL and exits 1.

### F40. While an order_by query is iterated, a call that deletes an entity from a table with a later slice makes the iterator return rows past that table's count

What happens:
```c
q = ecs_query(world, { .terms = {{ ecs_id(Position), .inout = EcsIn }},
    .order_by = ecs_id(Position), .order_by_callback = compare_x,
    .cache_kind = EcsQueryCacheAuto });
[Position]: e0 (1), e2 (3), e3 (4);  [Position, Tag]: e1 (2)
slices: [Position] row 0, [Position, Tag] row 0, [Position] rows 1-2
after the second result (e1, its table locked): ecs_delete(world, e2);
the third result is rows 1-2 of [Position], whose count is now 2: e3 and e3 again
```

- **Properties:**
  - P-IT1 (round 4), as in F35: e3 does not move to another table; the table being iterated is locked.
  - P-IT2 (new): a result covers only rows below its table's count. The rows past it hold stale copies: the entity id and the component value of a removed row.
  - Queries.md "Sorting": "A query determines whether a sort operation is needed when an iterator is created for it."
- **Code path:**
  - An order_by query iterates `cache->table_slices` (cache_iter.c 27-34). These are copies of the cache's matches, each with a row range (order_by.c 195-209), built when an iterator is created (`flecs_query_cache_sort_tables`, 228-321, and `flecs_query_cache_build_sorted_table_range`, 81-214).
  - The iterator returns each slice's range (cache_iter.c 356-378 sets `$this`'s offset and count). It skips a slice only when the table is empty (82-98).
  - Deleting a row moves the table's last row into it and decrements the count (`flecs_table_delete`, storage/table.c 1653-1704). The vector slot of the old last row keeps its entity id and its value.
  - Nothing rebuilds the slices until the next iterator.
- **Story:**
  - P-IT2 reports "query 0 returned row 2 of table 1, whose count is 2: an order_by slice (order_by.c 195-209) built before the call covers rows the call removed (the entity id and values there are stale copies)".
  - P-IT1 reports "entity 392 … returned 2 times".
- **Tape** [round 5 iteration generator, `query iter5-lib explore`, seed 4], after 244 timelines: `it5.query=4/5 it5.kind=0/4 it5.kind=0/7 it5.kind=6/7 it5.parent=0/2 it5.kind=6/7 it5.parent=0/3 it5.kind=4/7 it5.parent=0/4 it5.changed=0/2 it5.k=0/4 it5.target=3/5 it5.body=3/5`.
  - Shrunk: order_by on C0. Tables: `[C0]` with e0 (1), and `[C0, (Delete, e0)]` with e2 (2) and e3 (5).
  - After the first result, C1 is added to e3, which leaves its table. The table's second slice row is then past its count.
  - With seed 2 the P-IT1 form came after 1,137 timelines (a delete).
- **C test:** `query_order_by_stale_rows.c`.

## Seen again or extended this round

- **F33 extended (workers, allocator size classes).** `WorkersCD.lean` now models `flecs_allocator_get` creating a size class: `flecs_sparse_ensure_fast_t` and `flecs_ballocator_init` (datastructures/allocator.c 55-87; sparse.c 322-351).
  - Two workers that both find a table's dirty-state size class missing both initialize it. The second `flecs_ballocator_init` drops the first one's state, whose blocks leak.
  - Found after 5,157 timelines: `thread.next=0/2` ×7, `thread.next=1/2` ×4, `thread.next=0/2` ×7.
  - Races between different size classes: none in 3,000,000 timelines (bound not reached). Every worker walks the tables in the same order, so a second worker reaches a table only after the first allocated its dirty state; two workers meet only on one class.
  - The page-creation race of the sparse set is not modelled.
  - Stage allocators: each worker allocates its iterators from its own stage, so there is no race there.
  - No new C test: F33's test already forces the same unsynchronized allocator path.
- **F17 with phases.** A system that disables its own phase skips the next system without ProgressTasks: F17, PP4 and the 467-470 assert. With ProgressTasks first, disabling phases never skipped a system: `pipe phase-exhaust-noreorder`, 3 systems, 2,985,984 programs, 0 failing.
- **F29.** The Or generator's queries whose cache's query is invalid crash when created: 52,920 of 4,741,632 programs.
- **F19, F27.** The general query generator still finds them.

## Not counted as findings

- **OnSet through prefab variants for DontFragment components.** Read, not modelled; a lead for round 6.
  - An IsA add forwards OnSet for inherited components through the reachable-ids cache (observable.c 708-781, 799-870), which lists the base's table type.
  - A DontFragment component is never in a table type, and `flecs_instantiate_dont_fragment` emits OnSet only for the components it copies (instantiate.c 301-368).
  - So an inherited DontFragment Inherit component may produce no OnSet at any depth. ObserversManual.md "OnSet and Inheritance" documents one for Inherit components. flecs's `Sparse_on_set_after_remove_override` covers a different case (removing an override).
- **`EcsQueryMatchEmptyTables` with order_by.** The cache drops the flag (cache.c 744-748); the iterator still gets `EcsIterMatchEmptyTables` (eval_iter.c 855-856). Slices never cover empty tables, so nothing changes. Read, not modelled.
- **Slices of a table deleted during the iteration.** The table struct stays in the store with count 0 (storage/table.c 1205, 1333-1336), so the slice is skipped. The model does not follow a later table reusing the slot.

## What was replicated

New files:
- **`OrVM.lean`**: the compiler for a cached query whose uncached part is `$this` self terms on table and fragmenting Sparse components:
  - SetIds, the cache op (compiler.c 632-747, 1093-1110), and the order the remaining terms are compiled in, with the leading-Optional rule (1126-1190);
  - `flecs_query_compile_term`'s Or-chain state, conditional-evaluation blocks, Not/Optional/Or blocks, `mark_last_or_op` and `end_block_or` (compiler_term.c 98-360, 1016-1021, 1147-1563), including an `lbl_begin` of -1;
  - the VM: `run_until` with the shared `op_index`, and the dispatch for SetIds, Cache, And on a written `$this`, Or with a written source, Not, Optional, IfVar, End and Yield (engine/eval.c 150-252, 532-546, 1193-1214, 1264-1785), driven as `ecs_query_next` drives it (eval_iter.c 573-586).
  - Paths it does not transcribe make a program "unmodelled". None occurred.
- **`Spawner.lean`**: the spawner's build, its cached tables, `flecs_instantiate_sparse`'s walk of the prefab child's current table with its two asserts, and the ChildOf path.

Changes to earlier files:
- **`Query.lean`, `World.lean`**:
  - cascade grouping by ChildOf depth, with ordered group insertion (cache.c 179-191, 866-872; group.c 37-54; search.c 517-553); optional up terms;
  - groups have identities. A new non-default group is a new allocation; the default group is the cache's own (group.c 56-82);
  - each group's table array has an identity and a capacity. `ecs_vec_append` reallocates it when full, and the old one is freed (vec.c 179-215, 366-379); an empty group's array is freed;
  - the cursor (`qit->group`, `qit->elem`) holds identities. It reports a freed group, and a sync of `qit->elem` in a freed array when the query has change detection;
  - the stepwise iterator covers order_by: slices built when the iteration starts, returned by range (cache_iter.c 27-34, 356-378; order_by.c 81-321).
- **`QueryProps.lean`**: the round 5 iteration generator (five query shapes, five entities of seven kinds, an optional `ecs_query_changed`, five kinds of call), P-IT2, and four cases.
- **`InhDF.lean`**: `ecs_auto_override`; `flecs_add_overrides_for_base` with its recursion (table_graph.c 718-791); `flecs_instantiate_override_dont_fragment` (instantiate.c 370-391); P-I3.
- **`Pipeline.lean`**: phases with DependsOn depths. The pipeline query orders by depth, then entity id. Effects reorder a phase or disable one. The rebuild trigger includes the order. ProgressTasks sits in its own phase. The sort is a structural insertion sort, so the kernel can evaluate it.
- **`WorkersCD.lean`**: size classes of the world allocator.

## What is not exact, and why

- **F34:**
  - only `$this` self terms on table and fragmenting Sparse components;
  - the cache's own query (all table terms) is evaluated as documented;
  - tables are given by type, one entity each, created after the query, so the cache holds them in creation order;
  - `ops[-1]`'s content is not modelled: the source bit is taken as clear, as the C test's zeroed guard makes it;
  - select ops on an unwritten `$this`, Or selects and cache tests are not transcribed; no generated program reached them.
- **F35, F36, F40:**
  - depth comes from walking ChildOf targets, not from the `(ChildOf, P)` records; after a call both agree (component_index.c 1166-1231);
  - descending cascade is not modelled;
  - the free-list effect on small arrays (a chunk's first word) is not modelled; any read of a freed array is reported.
- **F37:** a phase reorder is reduced to "this phase now comes after the others".
- **F38:** table components take the documented override value (round 3 models their override cache).
- **F39:**
  - instances at depth 0 only (no transposed caches for deeper instances, tree_spawner.c 114-150);
  - children are not nested;
  - the component's trait is Copy.
- **F33 extended:** sparse-set pages and dense-array reallocation are not modelled.
- The limits of rounds 1 to 4 remain.

## Assumptions

- **Build:** debug, asserts on. All round 5 tests use `ecs_mini()`; the pipeline test imports FlecsPipeline, which brings no builtin system.
- **Systems:** they enqueue through `it->stage`.
- **Iteration:**
  - the call made during an iteration is a world call that moves no entity of the iterated table, which is locked as the C++ `each` locks it;
  - rematches run at the end of the call (round 4);
  - `ecs_query_changed` turns change detection on (`EcsQueryHasChangeDetection`, change_detection.c 135).
- **Allocators:** the OS API's `malloc_`, `calloc_`, `realloc_` and `free_` may be wrapped (F34, F35, F36 tests). Every block flecs frees with `ecs_os_free` came from these.
- **Tables:** two tables never have the same type (the Or generator's programs with duplicate types are skipped).
- **Ids in the query model:** C0 = 60, C1 = 61, the Remove relationship 387, the Delete relationship 388, entities from 389.

## Properties and their sources

Broke means some program violated the property; Held means it held in every run.

New this round:
1. **PQ-OR1:** a query's results are the tables that match its terms, each once (Queries.md "Or", "Iteration"; ComponentTraits.md "Sparse trait"). **Broke** (F34).
2. **P1 for query compilation:** no access outside the op array (Manual.md "Error handling"). **Broke** (F34).
3. **P-IT2:** a result covers only rows below its table's count (Queries.md "Iteration", "Sorting"). **Broke** (F40).
4. **P-I3:** an instance owns every component a base, at any IsA depth, auto-overrides (PrefabsManual.md "Auto Overriding", "Prefab Variants"; ComponentTraits.md "DontFragment trait", "Sparse trait"). **Broke** for DontFragment (F38); **held** for table and Sparse components.
5. **P-SP1:** instance children own the components their prefab child has when the instance is made (ComponentTraits.md "OnInstantiate trait"; HierarchiesManual.md "Parent storage details"). **Broke** for Parent hierarchies (F39); **held** for ChildOf.

Extended to new programs:
6. **P-IT1** to cascade and order_by queries (Queries.md "Iteration"). **Broke** (F35, F40).
7. **P1 for iteration** to freed groups and reallocated group arrays. **Broke** (F35, F36).
8. **PP4** to phases (Systems.md "Pipelines", "Builtin Pipeline"). **Broke** when a phase is reordered (F37), with or without ProgressTasks. When a phase is disabled: **broke** without ProgressTasks (F17), **held** with it first.
9. **PW4** to allocator size classes. **Broke** (F33 extended).
10. **P1 for instantiation** to the spawner's asserts. **Broke** (F39).

The 55 properties of rounds 1 to 4 are still checked by their generators. With the 5 new ones, 60 in all.

## Search runs and results

Or chains (F34):
- `or exhaust`, 3 components, 2 terms, 3 tables: **complete**, 395,136 programs, none failing. A mixed chain needs a term after it; without one it is F29.
- `or exhaust`, 3 components, 3 terms, 3 tables: **complete**, 4,741,632 programs, 3,780 failing:
  - P1: 3,780; PQ-OR1: 3,000.
  - Outcomes:
    - 309,960 ran right;
    - 3,000 out of bounds with wrong results;
    - 780 out of bounds with right results (the first cached table was the only match);
    - none with wrong results alone;
    - no unmodelled path;
    - skipped: 1,838,592 with duplicate types, 2,536,380 not partially cached or rejected, 52,920 F29 crashes.
- `or lib exhaust` (P1, PQ-OR1), 2 tables: after 96,434 timelines (tape above). With 3 tables, PQ-OR1 after 675,034.

Iterations (F35, F36, F40):
- `query iter5-explore`, seed 1: 300,000 programs, 6,398 failing:
  - P1 `qit->elem` in a freed array: 3,373;
  - P1 freed group: 36;
  - P-IT2: 2,836;
  - P-IT1: 937.
- `query iter5-lib explore`:
  - P-IT1: after 1,137 timelines (seed 2, order_by);
  - P1: after 262 (seed 3, F36);
  - P-IT2: after 244 (seed 4).
- `query iter5-lib exhaust`: P-IT1 on cascade after 2,679 timelines; freed group after 28,705.
- `query cases`: the five round 5 cases fail as described. The ten earlier cases print round 4's output.

Pipeline phases (F37):
- `pipe phase-exhaust`, 3 systems, no ProgressTasks: **complete**, 2,985,984 programs, 864,360 failing: PP4 690,156; PP1 at pipeline.c 467-470 174,204.
- The same with ProgressTasks first: **complete**, 2,985,984 programs, 234,144 failing, all PP4 (reorders).
- `pipe phase-exhaust-noreorder` (phase disabling only), 3 systems:
  - without ProgressTasks: **complete**, 379,960 failing (PP4 265,328; PP1 114,632; F17's forms);
  - with it first: **complete**, 0 failing.
- `pipe phase-lib exhaust`, 2 systems: PP4 after 153 timelines.

Auto overrides (F38):
- `idf auto-exhaust`, 1 component, 3 entities, 4 calls: **complete**, 1,750,329 programs, 194 failing: P-I3 182 (DontFragment Copy 53, DontFragment Inherit 129), P-I2 12 (F32).
- `idf auto-lib exhaust`: P-I3 after 1,168,532 timelines.

Tree spawner (F39):
- `sp exhaust`, 2 components, 2 children, 4 calls: **complete**, 3,359,232 programs, 29,696 failing: P-SP1 17,888; P1 (Sparse assert) 7,872; P1 (hook assert) 3,936.
- `sp lib exhaust`: P-SP1 after 10 timelines; P1 after 209,971.

Workers (F33 extended):
- `wcd exhaust 2 1 2`: double initialization after 5,157 timelines.
- `wcd exhaust 2 2 2` filtered on the dense array: none in 3,000,000 timelines (bound not reached).

Regressions (this round's binary):
- `cases` and `val cases`: identical to round 4's output.
- `act exhaust` 6 calls: 1,062,882 programs, 796 failing (round 4: the same).
- `query iter-exhaust`: 786,432 programs, 1,208 failing (P-IT1 92, freed wildcard vector 1,120), as in round 4.
- `pipe f17` and `pipe exhaust-frame` 2 systems (65,536 programs, 832 failing), as in round 4. The ProgressTasks-first frame search: 3,000,000 programs, none failing, as in round 4.
- `query explore` seed 21: 200,000 programs, 2,047 failing (round 4: 2,038):
  - P1 uninitialized read 1,826 (round 4: 1,828);
  - P1 `qit->elem` in a freed array 11 (F36);
  - P-IT2 1 and P-IT1 1: order_by queries of the menu now run the stepwise iteration, which round 4 excluded;
  - the rest P-CD1 as before.

## Theorems

There is no `sorry`. Every theorem uses only `propext`, `Classical.choice` and `Quot.sound` or fewer (printed by `Axioms.lean`). The concrete ones are checked by the kernel (`decide +kernel`).

New in `TheoremsR5.lean`:
- `or_after_chain_compile` (F34): the compiled ops of `TagA || Position(Sparse), TagC`, their labels (-1 on the And and the End), and one access to `ops[-1]`.
- `or_sparse_first_complete_block` (F34's control): with the Sparse term first, the validator uncaches the whole chain and the compiler builds a complete Or block without out-of-bounds access.
- `auto_override_variant_inherits`, `auto_override_controls` (F38).
- `autoVisit_direct_first` (F38, for every world): the auto-override walk reads the direct base, then its IsA targets.
- `spawner_stale_type` (F39).
- `reorder_resume_past_end` (F37).
- `pushMatch_full_reallocates` (F36, for every group and world): appending to a full group array gives the group a new array identity and frees the old one.

The theorems of rounds 1 to 4 are unchanged and still build.

## Library gaps

1. Round 4's gaps remain:
   - property filters erase digits from details, not from property names;
   - `interleave` has no condition variables;
   - `Determinismo.Threads` has no notion of a data race.
2. Property filters match substrings. The filter `P1` also matched `P-SP1`; the spawner's asserts were searched with `no-crash` instead.
3. `while` loops are `partial`, so the kernel cannot evaluate them: OrVM's compiler uses bounded `for` loops instead. The VM's mutual recursion is `partial` as well, so its results come from the searches, not from theorems. A fuel-indexed single function would make them kernel-checkable.

## Model errors and test errors corrected

No C test was changed.
- **Round 4's cursor reported a freed group's `qit->elem` without change detection.** flecs reads `qit->elem` only when the query has `EcsQueryHasChangeDetection` (eval_iter.c 225-230). Corrected. F30's reported use after free comes from `qit->tables`, so it is unaffected.
- **Round 4 held groups by id**, so a group freed and created again with the same id looked unchanged. Groups now have identities.
- **This round's first cursor change** stopped the change oracle from recording results of queries without change detection. The general generator's P-CD1 count rose (2,126 failing instead of 2,038). Corrected; the count is now round 4's plus this round's new failures.
- **The first Or runs** allowed two tables with one type, which flecs never has; those programs are skipped now. The first slice cursor reported a slice of a deleted table as a use after free; it now skips it, as flecs does. All numbers above are from the corrected runs.
- **One of this round's own cases was misdescribed:** "Position || TagA, TagC has an Or block without End". The model computed it right: the validator uncaches the whole chain.

## C tests (tests/flecs_lean/)

All 57 compile with `cc -c` against `upstream/distr/flecs.h`; none was run this round.

Round 5:
- F34: `query_or_sparse_term_after_chain.c` (allocator guard)
- F35: `query_cascade_table_twice.c`, `query_cascade_group_freed.c` (poisoning free; a crash confirms)
- F36: `query_iter_table_array_realloc.c` (poisoning free; a crash confirms)
- F37: `pipeline_phase_reorder_skips.c`
- F38: `auto_override_dont_fragment_variant.c`
- F39: `tree_spawner_stale_child_type.c`, `tree_spawner_stale_sparse_assert.c` (an abort confirms)
- F40: `query_order_by_stale_rows.c`

## For round 6

- **C tests:** run F34-F40.
- **OnSet for inherited DontFragment components on an IsA add:** model `flecs_emit_forward`'s reachable cache (observable.c 708-870) and write the C test (an OnSet observer on a DontFragment Inherit component; one and two IsA levels).
- **Workers:**
  - different size classes need workers at different tables at once, which ordered iteration rules out; look for allocations outside the table walk (iterators, commands);
  - the sparse set's page creation.
- **Query VM:**
  - select ops on an unwritten `$this` and Or selects, to check the VM against uncached queries;
  - DontFragment terms in the uncached part;
  - a fuel-indexed VM for kernel proofs.
- **Spawner:** instances below the root (transposed caches), nested children, auto overrides in spawner types.
- **Cascade:** descending order.
- **Slices:** reuse of a deleted table's slot.
