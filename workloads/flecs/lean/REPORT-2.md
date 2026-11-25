# flecs v4.2.0 in Lean 4 — round 2 report

Everything is in this directory:
- `FlecsLean/*.lean`: the model and its searches. New this round: `Pipeline.lean`, `Query.lean`, `QueryProps.lean`, `Search2.lean` and `TheoremsPipe.lean`. Round 1's files were extended (listed under "What was replicated").
- `Main.lean`: the `flecs-search` program.
- `tests/flecs_lean/*.c`: 33 C tests, 13 of them new. `README.txt` maps them to predictions.
- `.jobs/`: run logs (gitignored). `scratch/*.sh` re-runs every search below; `scratch/tape.py` prints tapes in `name=v/n` form.

To build, run `lake build FlecsLean flecs-search`. New modes of `.lake/build/bin/flecs-search`:
- `pipe explore SEED N NSYS MAXTERMS`
- `pipe exhaust-small LIMIT NSYS MAXTERMS`
- `pipe exhaust-frame LIMIT NSYS`
- `pipe lib MODE KIND SEED N NSYS MAXTERMS PROP`
- `query explore SEED N ENTS LEN`
- `query exhaust LIMIT ENTS LEN`
- `query cases`
- `query trace CASE`
- `query lib MODE SEED N ENTS LEN PROP`
- `obs-explore SEED N ENTS LEN` and `obs-exhaust LIMIT ENTS LEN` (monitors and up observers)
- `isa-explore SEED N ENTS LEN` and `isa-exhaust LIMIT ENTS LEN` (prefabs and instances)
- `lib obs|isa SEED N ENTS LEN PROP` (determinismo's explore, shrink and tape)
- `cases` runs every C test's program in the model.

Line numbers refer to files under `src/` at v4.2.0. Every C test needs a debug build (asserts on). A test returns 0 when flecs behaves as documented; a non-zero return or an abort confirms the prediction. A few return 2 when their setup does not hold. In a tape, `name=v/n` means the named decision took value `v` of `n` options. The generator is named in brackets.

## F2: the model correction

Round 1 predicted a panic: a batched remove of `(Rel, tgt)` after `tgt` was deleted earlier in the same merge, where `Rel` has `(OnDeleteTarget, Panic)`. The real flecs did not panic.

Where the model differed from the code:
- `flecs_remove_invalid` (commands.c 893-942) reads the policy from the `(Rel, *)` component record (909-910). When that record does not exist, it drops the command (925-927), and nothing panics.
- Adding the trait `(OnDeleteTarget, Panic)` to `Rel` does not create `(Rel, *)`. `flecs_register_flag_for_trait` (bootstrap.c 207-218) only sets flags on records that already exist.
- `(Rel, *)` is created with the first `(Rel, x)` record (`flecs_component_new`, component_index.c 440-447). It then lives until `Rel` is deleted.
- Round 1's `initWorld` (Program.lean) created `(R, *)` for every relationship when it set the trait, so the model always found the record.

What changed:
- `initWorld` no longer creates the record. A scenario field, `relRecords`, creates it for programs where the relationship was used in a pair before.
- Round 1's case `batch_remove_dead_target_panic` now completes, as the real flecs did.
- With the record present, the model still panics. That corrected prediction is `batch_remove_dead_target_panic_record.c`: the same program after `ecs_add_pair(world, holder, Rel, other)`.
- Round 1's exploration, with the same seed and 300,000 programs, now reports 53,804 failing programs instead of 52,846.

F3 note: the assert the real flecs reported is the one round 1 named. Its condition, `!ecs_exists(world, t)` (ECS_INVALID_PARAMETER), is at entity.c 2828, and its message ("second element of pair is not alive") is at 2829. No model change was needed.

## Counterexamples

### F15. A system that annotates a write of a component and then reads it aborts the pipeline build

What happens:
```c
ecs_system(world, { .entity = <OnUpdate system>,
    .query.terms = {
        { .id = ecs_id(Position), .src.id = EcsIsEntity, .inout = EcsOut },  // [out] Position()
        { .id = ecs_id(Position), .src.id = EcsIsEntity, .inout = EcsIn  } },// [in]  Position()
    .callback = Sys });
ecs_progress(world, 0);   // pipeline.c 354: ecs_assert(needs_merge == false, ECS_INTERNAL_ERROR)
```
The same happens with `[out] !Position` then `Position(up)`, and with `[out] (*, *)(Game)` then `(R, T)(Game)`. In general: any term that marks an id as written, followed in check order by a term that reads a matching id.

- **Property:** no internal assert on API use the docs allow (Manual.md "Error handling"). Systems.md "Sync points" documents `[out] X()` ("can enqueue commands for X") and `[in] X()` (reads X with `get`).
- **Code path:**
  - `flecs_pipeline_check_terms` (pipeline.c 222-250) checks `$this` terms first, then the rest.
  - In `flecs_pipeline_check_term` (135-220), the first term records the id as written to the stage. The second sees that write and asks for a merge.
  - `flecs_pipeline_build` (263-473) then merges: it resets the write state (332) and checks the same terms again (346-351). They ask for a merge again, and the assert at 354 fires.
- **Story:** PP1 fails while the schedule is built. Theorem `write_then_read_asks_merge` shows the two terms ask for a merge from an empty write state. Theorem `single_term_no_assert` shows that no one-term system can trip the assert.
- **Tapes** [pipe]:
  - Exhaustive, 1 system with 2 terms: complete, 37,056 programs, 3,026 trip the assert. Shrunk: `S0: [[out] !C0, C0]`.
  - Determinismo `explore` (filter "needs_merge"): counterexample after 1 timeline. `pipe.terms=0/3 pipe.id=0/8 pipe.src=0/5 pipe.oper=0/3 pipe.inout=0/6 pipe.active=0/4 pipe.enabled=0/4 pipe.mt=0/3 pipe.immediate=0/3 pipe.effect=4/5 pipe.effect.sys=0/3 pipe.terms=2/3 … pipe.terms=2/3 pipe.id=0/8 pipe.src=0/5 pipe.oper=1/3 pipe.inout=2/6 …`. Shrunk: `S0: [[out] !C0, C0]`.
- **C test:** `pipeline_write_read_same_system.c`

### F16. No sync point between a wildcard or Any write annotation and an overlapping read

What happens:
```c
Writer: [out] (Likes, *)()   // adds (Likes, Bob) to e through it->world (queued)
Reader: (*, Bob)             // $this term; e0 already has (Hates, Bob)
ecs_progress(world, 0);      // Reader sees only e0 in this frame
// likewise: Writer [out] (Likes, Bob)(), Reader (Likes, _)
```

- **Property:** Systems.md "Sync points": "When a pipeline sees a read for a component for which commands could have been inserted, a sync point is inserted before the system that reads". Queries.md "Wildcards": `_` matches any target.
- **Code path:** `flecs_pipeline_get_write_state` (pipeline.c 61-105) compares a read with `ecs_id_match(written, read)` and `ecs_id_match(read, written_wildcard)`. `ecs_id_match` (id.c 12-84) treats only `Wildcard`, and only on the pattern side, as a wildcard:
  - `(*, Bob)` does not match `(Likes, *)`.
  - `(Likes, *)` does not match `(*, Bob)`.
  - `(Likes, Bob)` does not match `(Likes, _)`.

  Overlapping patterns where neither contains the other are missed. So is every read or write written with Any.
- **Story:** PP2 reports "system 0 may enqueue commands for (R, *), system 1 reads (*, T1); they run in the same op without a merge". The exhaustive run over pairs of one-term systems found 10 such shapes. Theorems `wildcard_write_missed` and `any_read_missed` show the comparison and the overlap.
- **Tape** [pipe, full generator, determinismo explore, 227 timelines]: `pipe.terms=0/3 pipe.id=0/8 pipe.src=0/5 pipe.oper=0/3 pipe.inout=0/6 pipe.active=0/4 pipe.enabled=0/4 pipe.mt=0/3 pipe.immediate=0/3 pipe.effect=0/5 pipe.terms=2/3 pipe.id=5/8 pipe.src=1/5 pipe.oper=0/3 pipe.inout=2/6 … pipe.terms=0/3 pipe.id=3/8 pipe.src=0/5 …`. Shrunk: `S0: [[out] (R, _)()]; S1: [(R, *)]`.
- **C test:** `pipeline_wildcard_sync_point.c` (both variants)

### F17. A system that disables itself makes the pipeline skip the next systems in that frame

What happens:
```c
Init:   immediate system; callback: ecs_enable(it->world, it->system, false)
Update: regular system after it
ecs_progress(world, 0);   // Init runs; Update does not run in this frame
```
A second program: A disables itself, B is immediate, C disables itself. The frame runs A and C, skips B, then aborts at pipeline.c 467-470 (`ecs_assert(pq->cur_op <= ecs_vec_last_t(&pq->ops, …), ECS_INTERNAL_ERROR)`). A release build reads past the op array.

- **Property:** Systems.md "Pipelines": "A pipeline is a list of systems that is executed when the ecs_progress/world::progress function is invoked". Update is enabled and active for the whole frame. Systems.md "Disabling systems" uses `ecs_enable` on a system. Also: no internal assert.
- **Code path:**
  - After each op, `flecs_run_pipeline` (pipeline.c 581-675) sets `cur_i` to the last system that ran and calls `flecs_pipeline_update` (609).
  - The disabled system leaves its table. The sorted pipeline query then bumps its match count (order_by.c 315-318), and `flecs_pipeline_build` rebuilds.
  - The rebuild repositions `pq->cur_op`/`cur_i` at the last system in the new schedule whose `last_frame` is the current frame (450-458). Init is gone and Update hasn't run, so they keep their old values: op 0, system 0.
  - `flecs_pipeline_next_system` (475-489) then steps past the new op 0, which now holds Update.
- **Story:** PP4 reports "system 1 was enabled and active for the whole frame but ran 0 times". The second program fails PP1 at pipeline.c 467-470.
- **Tapes** [pipe, frame generator]:
  - Exhaustive, 2 systems (265 timelines): `pipe.frame.terms=0/4 pipe.active=0/2 pipe.enabled=0/2 pipe.immediate=0/2 pipe.effect=1/5 pipe.frame.terms=0/4 pipe.active=0/2 pipe.enabled=0/2 pipe.immediate=1/2 pipe.effect=0/5`. This is `S0: [] disables itself; S1: [] immediate`.
  - Sync point instead of immediate (75 timelines): `pipe.frame.terms=1/4 pipe.active=0/2 pipe.enabled=0/2 pipe.immediate=0/2 pipe.effect=1/5 pipe.frame.terms=3/4 … pipe.frame.terms=0/4 …`. Shrunk: `S0: [[out] C0()] disables itself; S1: [C0]; S2: []`. S1 is skipped.
  - Assert (517 timelines): `pipe.frame.terms=0/4 pipe.active=0/2 pipe.enabled=0/2 pipe.immediate=1/2 pipe.effect=1/5 pipe.frame.terms=0/4 pipe.active=0/2 pipe.enabled=0/2 pipe.immediate=0/2 pipe.effect=4/5 pipe.effect.sys=0/3 pipe.frame.terms=0/4 pipe.active=0/2 pipe.enabled=0/2 pipe.immediate=1/2 pipe.effect=2/5 pipe.effect.sys=2/3`. Shrunk: `S0: [] immediate, disables itself; S1: []; S2: [] immediate, disables itself`.
- **C tests:** `pipeline_disabled_system_skips_next.c`, `pipeline_disabled_systems_assert.c`

### F18. Change detection misses a write to a source entity that moved to another table

What happens:
```c
q = [in] Position, [in] Velocity(game)    // or Velocity(up) with game = parent
    .cache_kind = EcsQueryCacheAuto, .flags = EcsQueryDetectChanges
ecs_query_changed(q); iterate q fully;    // in sync: ecs_query_changed(q) == false
ecs_add(world, game, Tag);                // game moves to [Velocity, Tag]
ecs_set(world, game, Velocity, {2, 2});
ecs_query_changed(q);                     // false; with Velocity(up), ecs_iter_changed is false too
```
The same happens when the write is a `modified`, a queued set merged together with the move, or an iteration of another query with an `inout` Velocity term.

- **Property:** Queries.md "Change Detection": "Setting a component value with set" is detected, and changes are reported "for the components it matched with". flecs's own test `ChangeDetection_query_changed_w_only_parent_after_set` expects a set on the parent to be detected.
- **Code path:**
  - Monitors store dirty counters of the table the source was in: the fixed monitor (change_detection.c 142-201) and match monitors (79-138, synced in 581-633).
  - A table gets a dirty state only when a monitor reads it (table.c 1432-1450). New tables start without one (table_graph.c 424). `flecs_table_mark_dirty` (table.c 1397-1429) does nothing for such a table, so the set on the source's new table is not counted.
  - The check resolves the source's current table (`flecs_query_get_column_for_field`, 30-75) and allocates its dirty state with every counter at 1. The old counter was also 1, so the two compare equal: 194 for fixed sources, 403-415 for up sources.
- **Story:** P-CD1 reports "query 0 returned false after a documented change". For a fixed source: "fixed: 389/60:1 -> 389/60:2". For an up source: "table 3: up 389/60:1 -> up 389/60:2". Both `ecs_query_changed` and `ecs_iter_changed` report it. Query results stay correct (P-Q1 held).
- **Tape** [query generator, determinismo explore, 2,566 timelines]: `q.count=1/2 q.menu=8/11 q.fixed=0/3 q.menu=0/11 q.fixed=0/3 q.kind=3/4 flecs.entity=1/3 flecs.target=2/3 flecs.id=3/7 flecs.call=1/8 q.kind=3/4 flecs.entity=0/3 flecs.target=1/3 flecs.id=0/7 flecs.call=6/8 flecs.set.id=0/2 flecs.value=0/3 q.kind=1/4 q.query=0/2 q.kind=2/4 flecs.entity=0/3 flecs.target=0/3 flecs.id=0/7 flecs.call=5/8 flecs.set.id=0/2 … flecs.call=6/8 flecs.set.id=1/2 flecs.value=0/3`. Shrunk to calls:
  1. query `[in] C0(up)`
  2. add `(ChildOf, e0)` to e1
  3. ensure C0 on e0
  4. queue `modified` C0 on e0
  5. iterate
  6. queue ensure C1 on e0
  7. merge
  8. `ecs_query_changed` → false
- **C tests:** `change_detection_fixed_source_moved.c`, `change_detection_parent_moved.c`

### F19. Change detection on a fixed source that lacks the component: removal is missed, addition reads uninitialized memory

What happens:
```c
q = [in] Position, [in] Velocity(game), DetectChanges
// (a) game has Velocity: ecs_query_changed(q); iterate; ecs_remove(world, game, Velocity);
//     ecs_query_changed(q) == false, though q's results went from one entity to none
// (b) game lacks Velocity: ecs_query_changed(q); iterate; ecs_set(world, game, Velocity, …);
//     ecs_query_changed(q) compares a monitor slot that was never written
```

- **Property:** Queries.md "Change Detection": "Anything that causes adding or removing a component, tag or pair" is detected. Universal rule: no read of uninitialized memory.
- **Code path:**
  - `flecs_query_get_fixed_monitor` (change_detection.c 142-201) allocates the monitor with `flecs_alloc_n` (152-153), which does not zero it.
  - It skips a field whose source has no table record for the component (184), both when it fills the monitor (192) and when it compares it (194).
  - (a): after the removal, the field is skipped.
  - (b): a field skipped when the monitor was filled is later compared against garbage.
  - A combination also shows up: a slot written while the source had the component, compared after the source lost it and regained it in another table.
- **Story:** P-CD1 reports "fixed: 390/60:1 -> (nothing)" for (a). The model flags (b) as "P1 uninitialized read: query 0 compares the fixed-source monitor of field 1, which was never written".
- **Tapes** [query generator]:
  - (b), 16 timelines: `q.count=0/2 q.menu=1/11 q.fixed=1/3 q.kind=1/4 q.kind=3/4 flecs.entity=1/3 flecs.target=0/3 flecs.id=0/7 flecs.call=6/8 flecs.set.id=0/2 flecs.value=0/3 q.kind=1/4 …`. Shrunk: query `[in] C1, [in] C0(e1)`; queue ensure C0 on e1; `ecs_query_changed`; merge; `ecs_query_changed`.
  - (a), 11,060 timelines: `q.count=1/2 q.menu=1/11 q.fixed=1/3 q.menu=0/11 q.fixed=0/3 q.kind=1/4 q.query=0/2 q.kind=2/4 flecs.entity=0/3 flecs.target=0/3 flecs.id=0/7 flecs.call=0/8 q.kind=2/4 flecs.entity=1/3 flecs.target=1/3 flecs.id=0/7 flecs.call=4/8 …`. Shrunk: set C0 on e1; iterate; queue remove C0 on e1; `ecs_query_changed`; merge; `ecs_query_changed` → false.
- **C tests:** `change_detection_fixed_source_removed.c` and `change_detection_fixed_source_added.c`. The second usually returns 0; run it under valgrind (`--error-exitcode=1`) or MemorySanitizer.

### F20. Monitors with up traversal report OnAdd for an entity that already matched, and OnRemove for one that still matches

What happens:
```c
monitor (EcsMonitor) on Position(up)       // trav ChildOf
gp; p = child of gp; c = child of p
ecs_add(world, gp, Position);    // OnAdd p, OnAdd c (both start matching)
ecs_add(world, p, Position);     // OnAdd c again, though c already matched
ecs_remove(world, p, Position);  // OnRemove c, though c still matches through gp
```
`Position(self|up)` monitors behave the same.

- **Property:** ObserversManual.md "Monitors": "A monitor is an observer that fires when an entity starts and stops matching a query". flecs's own `Monitor_monitor_w_superset` expects no event for a second match.
- **Code path:**
  - The event reaches c through propagation. `flecs_emit_propagate_id_for_range` (observable.c 310-376) sets `it->other_table = NULL` (328).
  - `flecs_multi_observer_invoke` (observer.c 654-773) decides "first match" by evaluating the query on the previous table. With no other table it uses the root table (694), which never matches an up term (741-757).
  - So every propagated OnAdd or OnRemove counts as a transition. Forwarded events (adding or removing the ChildOf pair) pass the real other table and are correct.
  - In batched merges, round 1's F10 (events for ChildOf pairs the entity never had) also reaches monitors.
- **Story:** P7 reports "OnAdd for entity 391, which already matched monitor 0 (source 390)". After the call it reports "entity 391 matches monitor 0's term but the monitor reported OnRemove or nothing last".
- **Tape** [observer generator, determinismo explore, 1,003 timelines]: `flecs.stages=0/2 flecs.hooks=0/3 flecs.entity=0/3 flecs.target=0/2 flecs.call=3/7 flecs.obs.what=0/2 flecs.entity=2/3 flecs.target=0/2 flecs.call=2/7 flecs.obs.what=1/2 flecs.pair.target=1/2 flecs.entity=1/3 flecs.target=0/2 flecs.call=1/7 flecs.obs.what=1/2 flecs.entity=0/3 flecs.target=0/2 flecs.call=4/7 flecs.value=0/3 flecs.entity=1/3 flecs.target=0/2 flecs.call=4/7 flecs.value=0/3 …`. Shrunk: add `(ChildOf, e1)` to e2; add `(ChildOf, e0)` to e1; set C0 on e0; set C0 on e1.
- **C test:** `monitor_up_grandparent.c`

### F21. Instantiating a prefab with children makes a deleted entity handle alive again

What happens:
```c
prefab = ecs_new_w_id(world, EcsPrefab);
pchild = ecs_new_w_pair(world, EcsChildOf, prefab);   // prefab + 1
inst = ecs_new(world); b = ecs_new(world);            // b = inst + 1
ecs_delete(world, b);
ecs_add_pair(world, inst, EcsIsA, prefab);            // instance child gets id inst + 1
ecs_is_alive(world, b);                               // true: b is now inst's child
```

- **Property:** EntitiesComponents.md "Liveliness Checking": a deleted entity is not alive. EntitiesComponents.md "Deleting Entities": a recycled id gets a new version, so old handles stay dead.
- **Code path:**
  - `flecs_instantiate_children` (instantiate.c 135-300) reserves child ids at the prefab child's offset (267-279).
  - `flecs_instantiate_alloc_child_id` (45-71) takes `root_instance + prefab_offset`. That sum is 64-bit, so it carries the instance's generation.
  - It only checks that no entity with the 32-bit id is alive. Then it calls `flecs_entities_make_alive` and `flecs_entities_ensure`.
  - `flecs_entity_index_ensure` (entity_index.c 139-186) moves the dead id into the alive part with the given generation. When the deleted id had been recycled more often than the instance, its generation goes backwards.
- **Story:** P8 reports "entity 392 was deleted earlier and is alive again". Its type is `[(ChildOf, inst)]`.
- **Tape** [IsA generator, determinismo explore, 244 timelines]: `flecs.stages=0/2 flecs.entity=1/4 flecs.target=0/2 flecs.call=2/8 flecs.entity=0/4 flecs.target=0/2 flecs.call=3/8 flecs.entity=3/4 flecs.target=0/2 flecs.call=0/8 flecs.entity=0/4 flecs.target=0/2 flecs.call=1/8 flecs.entity=2/4 flecs.target=1/2 flecs.call=3/8 flecs.pair.target=0/2 …`. Shrunk:
  1. create four entities
  2. add `(ChildOf, e0)` to e1
  3. delete e3
  4. add Prefab to e0
  5. queue `(IsA, e0)` on e2
  6. merge
- **C test:** `instantiate_resurrects_deleted_handle.c`

### F22. A batched set, remove and add of the same component keeps the set's value

What happens:
```c
ecs_set(stage, e, Position, {1, 1}); ecs_remove(stage, e, Position); ecs_add(stage, e, Position);
ecs_merge(stage);   // e has {1, 1}; in order, the add after the remove constructs a new value
```

- **Property:** commands are applied in order at the merge (Manual.md "Deferred operations"). Remove destroys the value; add constructs it (EntitiesComponents.md "Operations"). The C test gives Position a ctor, so the documented value is the ctor's.
- **Code path:** `flecs_cmd_batch_for_entity` (commands.c 968-1298) computes the final table, where the remove and the add cancel out. It then copies every Set/Ensure value (1179-1245). The check for a later remove (1193-1197) only asks whether the final table has the component.
- **Story:** P3 reports "batched [(60, 1)] vs one-by-one [(60, 0)]", and P5 reports the same difference against the replay. Round 2's observer generator found this in round 1's batching code.
- **Tape** [observer generator, exhaustive]: `flecs.stages=0/2 flecs.hooks=0/3 flecs.entity=0/3 flecs.target=1/2 flecs.call=4/7 flecs.value=0/3 flecs.entity=0/3 flecs.target=1/2 flecs.call=3/7 flecs.obs.what=0/2 flecs.entity=0/3 flecs.target=1/2 flecs.call=1/7 flecs.obs.what=0/2`
- **C test:** `batch_set_remove_add_value.c`

### F23. A queued ChildOf to a parent that was deleted, and whose id was recycled, attaches the child to the new entity

What happens:
```c
stage = ecs_get_stage(world, 0);
ecs_add_pair(stage, c, EcsChildOf, p);
ecs_delete(world, p);
q = ecs_new(world);     // recycles p's id
ecs_merge(stage);       // c is alive and is a child of q
```

- **Property:** Manual.md "Deferred operations": "Commands that parent an entity to a deleted parent delete the child during the merge". EntitiesComponents.md "Deleting Entities": the version tells a recycled id from the deleted entity.
- **Code path:** the command holds the pair id, which keeps only the 32-bit target (`ecs_pair`, api_defines.h 357-361). At the merge, `flecs_remove_invalid` (commands.c 893-942) tests the target with `flecs_entities_is_valid`. That is true for the recycled id, so the pair is added.
- **Story:** P5 reports "merge: c alive with [(ChildOf, p's id)] vs replay: c deleted". Round 1's generators created every entity before the calls, so no id was recycled before a merge. Round 2's IsA generator creates entities between calls.
- **Tapes** [IsA generator]:
  - Exhaustive, 3 entities × 3 calls, complete: `flecs.stages=0/2 flecs.entity=1/3 flecs.target=1/2 flecs.call=2/8 flecs.pair.target=0/1 flecs.entity=0/3 flecs.target=0/2 flecs.call=0/8 flecs.entity=0/3 flecs.target=0/2 flecs.call=5/8`
  - Determinismo explore, 19 timelines: `flecs.stages=0/2 flecs.entity=0/3 flecs.target=0/2 flecs.call=5/8 flecs.entity=1/3 flecs.target=1/2 flecs.call=2/8 flecs.entity=0/3 flecs.target=0/2 flecs.call=0/8 …`
- **C test:** `staged_childof_recycled_parent.c`

### Not counted as findings

- **An immediate system with `multi_threaded` runs on the worker threads.** All workers run it on stage 0, outside readonly mode. Systems.md says "immediate systems are always single threaded", but system.h says `immediate` "Cannot be true at the same time as multi_threaded". Neither `ecs_system_init` nor `ecs_system_update` checks this, and an update that sets one flag keeps the other.
- **A fixed-source term with default access is marked dirty on every iteration.** change_detection.c 530-578 ignores `shared_readonly_fields`. Queries.md says the default for terms matched on other entities is `In`, but flecs's own test `ChangeDetection_mark_dirty_w_cached_w_fixed_search` expects the marking.
- **`group_by` groups are not ordered by id unless the query uses cascade** (group.c 37-54). Queries.md "Grouping" says groups are sorted by id, and contradicts itself on the direction. flecs's own `GroupBy_group_by` expects reverse creation order.
- **An inactive system that reads a staged id still inserts a merge** (pipeline.c 333-351). Systems.md says inactive systems are ignored for sync points; a code comment explains why.
- **Staged IsA and ChildOf to the same prefab:** whether instantiation sees the instance as the prefab's own child ("cycle detected in IsA relationship", instantiate.c 253-260) depends on batching. The structure is cyclic either way.
- **Change-detecting queries start syncing only after the first `ecs_query_changed` or `ecs_iter_changed`.** This is conservative.
- Systems.md shows `.add = ecs_ids(...)` in `ecs_entity_desc_t`, which v4.2.0 lacks. The C tests add the DependsOn pair instead.

## What was replicated

New files, and the flecs code each follows:
- **`Pipeline.lean`** (addons/pipeline/pipeline.c), function by function:
  - `get_write_state`, `set_write_state`, `check_term` and `check_terms`, with validator.c's inout defaults.
  - `flecs_pipeline_build`: ops, merges, mode switches, both asserts, and the `last_frame` resume logic.
  - `next_system`, `update`, `run_pipeline_ops` and `run_pipeline`: a frame with merges and rebuilds.
  - Systems carry their terms, active and enabled state, `multi_threaded`, `immediate`, and what their merged commands do to the pipeline.
- **`Query.lean`** (query/cache/*.c, eval_iter.c 217-680):
  - Matching: self terms (And, Not, Optional), up(ChildOf) terms and fixed-source terms.
  - Table events, and rematch through propagated OnAdd/OnRemove, `revalidate_table` and `rematch_table`.
  - Groups (ensure, insert at head, swap-remove, move) and `group_by` with the default action.
  - `order_by`: the Hoare quicksort of flecs_c.h 795-852 with `flecs_table_swap`, the slice merge, and `sort_tables`.
  - Change detection: match and fixed monitors, `check_match_monitor(_term)`, `check_cache_monitor`, `sync_match_monitor`, `mark_fields_dirty`, `mark_fixed_fields_dirty`, `ecs_query_changed`, `ecs_iter_changed` and skip.
  - Iteration: `cache_iter_init`, `cache_next` (empty tables are synced), fixed terms evaluated first, and full, skip-all and first-result modes.
- **`QueryProps.lean`:** query programs, the reference evaluation and the change oracle, generators, cases, and a trace mode.
- **`TheoremsPipe.lean`, `Search2.lean`:** see "Theorems" and "Library gaps".

Changes to round 1's files:
- **Dirty state** (`World.lean`, `Ops.lean`): lazily allocated with counters at 1, and marked where flecs marks it:
  - grow (table.c 1558/1586) and delete (1689)
  - merge (2167/2183; the source table is not marked)
  - set (entity.c 833, 1963) and modified (1884, 1925)
  - table swap
- **`flecs_emit`** (`Ops.lean`):
  - propagation (observable.c 310-475)
  - forwarding through a reachable set, computed fresh, for ChildOf (708-888)
  - up and self|up observers, monitors (observer.c 654-773), and the query rematch events
  - `other_table` passed by moves, batches and cleanup
- **Prefabs** (`Ops.lean`): adding `(IsA, base)` instantiates the base's children (observable.c 1200-1228). This uses `flecs_instantiate`, `instantiate_children`, `alloc_child_id` and the cycle check (instantiate.c 45-71, 135-300, 393-480).
- **`Program.lean`, `Gen.lean`, `Cases.lean`:**
  - the F2 correction (`relRecords`)
  - menu configurations 9-11: monitors on C0(up) and C0(self|up), and up observers
  - IsA and Prefab ids
  - P7 and P8
  - the observer and IsA generators
  - 6 new cases
- **`Theorems.lean`:** the generation lemmas re-proved.

## What is not exact, and why

- **Pipeline:**
  - System bodies are not run; the sync property is checked on the schedule.
  - One phase only, ordered by entity id. No `DependsOn` cascade and no custom pipelines.
  - The model rebuilds exactly when the set of enabled, active systems changed. In flecs, a rebuild follows any table change of a matched system.
  - Worker threads are not run.
- **Queries:**
  - Not modelled: wildcard terms, variables, Or terms, cascade, `ecs_iter_set_group`, MatchEmptyTables, non-identity field maps, prefab and disabled tables, sparse components, and IsA in up terms.
  - Table and revalidation events reach the caches at the end of each API call, not when flecs emits them. Nothing reads a cache in between.
  - The reachable set used for forwarding is recomputed each time instead of cached.
  - `order_by` compares values only.
- **Observers:** only ChildOf traversal for up terms. No IsA traversal, no forwarded OnSet for IsA, no override events (observable.c 890-1002). Single-term only; up observers only record their events.
- **Prefabs:** only instantiation of fragmenting ChildOf children and their ids. Inheritance, overrides, auto-override, `ecs_get`/`ecs_get_mut` through IsA, the table override cache, ordered children and the tree spawner are not modelled.
- **Oracles:**
  - The change oracle counts documented writes per entity and component, plus entities entering or leaving tables.
  - It only checks one direction: a documented change happened and flecs says nothing changed. The opposite direction is not checked, because tables that become matched or unmatched also report a change.
  - Monitors are checked after every call outside deferred mode.
- Round 1's limits remain: values are naturals, hook menus are small, thread steps are atomic, and ChildOf depth is not modelled.

## Assumptions

- **Build:** debug (asserts on), `ecs_mini()`; the pipeline tests use `ecs_init()`.
- **Allowed failures:** round 1's list, plus "cycle detected in IsA relationship" (instantiate.c 253-260).
- **Programs follow the docs:**
  - ChildOf and IsA targets are lower slots, so hierarchies are trees.
  - A query's fixed source is not deleted.
  - `ecs_query_changed` and `ecs_iter_changed` are called only on queries created with `EcsQueryDetectChanges`.
- **Pipeline:** systems are created in order. PP3 assumes worker threads exist.
- **Ids:** C0 = 60, C1 = 61, entities from 385, as in round 1.

## Properties and their sources

Broke means some program violated the property; Held means it held in every run.

Pipeline (Systems.md):
1. **PP1** — no internal assert while building or running a schedule (Manual.md "Error handling"). **Broke** (F15, F17).
2. **PP2** — a read of an id that an earlier active system may have written comes after a merge ("Sync points"). **Broke** (F16).
3. **PP3** — immediate systems run single-threaded ("Immediate systems"). Broke only with both flags set, which system.h forbids; not counted.
4. **PP4** — a system enabled and active for the whole frame runs exactly once ("Pipelines"). **Broke** (F17).

Queries (Queries.md):

5. **P-Q1** — a full iteration yields exactly the matching entities, with the current values ("Iteration", "Source", "Relationship Traversal"). **Held.**
6. **P-Q2** — `order_by` yields values in order when no undetected write happened ("Sorting"). **Held.**
7. **P-Q3** — tables of a group are iterated together ("Grouping"). **Held.**
8. **P-CD1** — `ecs_query_changed` and `ecs_iter_changed` report every documented change since the query last iterated ("Change Detection"). **Broke** (F18, F19).
9. **P1u** — no read of uninitialized memory. **Broke** (F19).

Observers and entities:

10. **P7** — monitors fire on start and stop of matching, and their reports agree with the matches after each call (ObserversManual.md "Monitors"). **Broke** (F20).
11. **P8** — a deleted handle is not alive again without `make_alive` (EntitiesComponents.md "Liveliness Checking", "Deleting Entities"). **Broke** (F21).

Round 1's 20 properties are still checked by every generator. Under round 2's generators:
- P3 and P5 broke again (F22, F23, and round 1's F1, F3, F9, F12).
- The storage and entity-index invariants (P2f-P2k) held.

## Search runs and results

Speed per program:
- pipeline: about 14 µs
- query: about 35 µs
- observer: about 180 µs (three runs per program)
- IsA: about 165 µs

Pipeline:
- `pipe explore` with 3 systems and up to 3 terms:
  - 20,000 programs (seed 1): 6,150 failing.
  - 200,000 programs (seed 100000): 60,579 failing. By signature: PP3 35,418; PP4 16,719 + 5,328; PP1 at 354, 9,573; PP1 at 467, 1,492; PP2 96-180 per shape across 10 shapes.
- `pipe explore` with 4 systems: 1,000,000 programs, 380,659 failing, same signatures.
- `pipe exhaust-small`, 1 system × 2 terms: **complete**, 37,056 programs, 3,026 failing (all F15).
- `pipe exhaust-small`, 2 one-term systems: **complete**, 36,864 programs, 1,503 failing (all F16).
- `pipe exhaust-frame`:
  - 2 systems: **complete**, 65,536 programs, 832 failing.
  - 3 systems: 3,000,000 programs (bound not reached), 165,220 failing, including the assert 3,696 times.
- Determinismo: PP2 after 227 timelines, PP3 after 5, PP4 after 13 (75 with the frame generator), the assert after 517; `exhaust` of PP4 after 265.

Queries:
- `query explore`:
  - 20,000 programs: 245 failing.
  - 200,000 programs (3 entities, 10 calls): 3,032 failing.
  - 150,000 programs (4 entities, 14 calls): 2,602 failing.
  - 1,000,000 programs (3 entities, 12 calls): 18,395 failing. P1u appears 33,473 times; P-CD1 fixed 168, up 5, `ecs_iter_changed` 24; one F19 + F18 combination.
- `query exhaust`, 2 entities: 2,000,000 programs (3 calls) and 3,000,000 programs (4 calls), bounds not reached, none failing.
- Determinismo: P1u after 16 timelines, P-CD1 after 2,566 (the fixed variant after 11,060). P-Q1, P-Q2 and P-Q3: 300,000 timelines each, no counterexample.

Observers:
- `obs-explore`:
  - 200,000 programs: 2,142 failing, P7 in 430.
  - 150,000 programs: 2,812 failing, P7 in 621.
  - 1,000,000 programs (4 entities, 10 calls): 13,001 failing, P7 2,863 (F20, plus round 1's F10 reaching monitors).
- `obs-exhaust`, 3 entities × 3 calls: 2,000,000 programs (bound not reached), 1,669 failing, P7 in 148.
- The other failures are round 1's F1, F9 and F12, and F22.
- Determinismo P7: after 1,003 timelines.

IsA:
- `isa-explore`:
  - 200,000 programs: 1,503 failing, P8 in 46.
  - 1,000,000 programs (5 entities, 10 calls): 10,963 failing, P8 383.
- `isa-exhaust`, 3 entities × 3 calls: **complete**, 1,419,769 programs, 360 failing (F23 96, round 1's F9, the IsA-ChildOf cycle).
- Determinismo: P8 after 244 timelines, F23 (P5) after 19.

Round 1's generator, same seed and 300,000 programs: 53,804 failing (round 1: 52,846). The difference comes from the F2 correction.

## Theorems

There is no `sorry`. `FlecsLean/Axioms.lean` prints the axioms: every theorem uses only `propext`, `Classical.choice` and `Quot.sound`. **No `bv_decide` remains.**

- **Generations, re-proved by bit extensionality.** Each `UInt64` is compared bit by bit through `BitVec.getLsbD`. The index is split at 16, 32 and 48, and `simp` closes each case with `omega` discharging the comparisons.
  - Lemmas: `genInc_lo32`, `genInc_generation`, `genInc_high`, `gen_of_pack(')`, `pack_mask`, `unpack`.
  - 16-bit arithmetic through `toNat` and `omega`: `arith16`, `arith16_period`.
  - From these: `genInc_genIter`, `genIter_zero`, `iterate_genInc` and `genInc_period` (F13: 65,536 recycles give back the original handle).
- **Pipeline:**
  - `getWS_empty`: for every id.
  - `checkTerm_empty`: for every term and activity flag.
  - `single_term_no_assert`: for every term.
  - `write_then_read_asks_merge` (F15).
  - `wildcard_write_missed` and `any_read_missed` (F16).
- Round 1's `deleteAction_*` and entity-index lemmas are unchanged.

## Library gaps

1. Round 1's gaps 1-4 remain: no per-cause counts, no call-level shrinking, no allowed-failure notion, and depth-first `exhaust`. Round 1's drivers are now generic: `gexplore`, `gexhaust` and `gshrink` over any program type, and `gtimeline`/`gprogOf` adapt any generator to determinismo.
2. Property filters match signatures with digits erased, so a filter on a line number never matches. The runs filter on words instead ("needs_merge", "cur_op", "fixed:").
3. There is no notion of uninitialized values. The query model keeps unwritten slots as `none` and reports reads of them.
4. Tapes print as JSON lines; `scratch/tape.py` converts them.
5. Lean core has no `fin_cases`. The bit proofs split ranges with `rcases` and use `simp` with `omega` as the discharger, which avoids `bv_decide` and its axioms.

## C tests (tests/flecs_lean/)

All 33 compile with `cc -c` against `upstream/distr/flecs.h`; none was run.

Round 2:
- F2 corrected: `batch_remove_dead_target_panic_record.c` (the round 1 file is kept, with a note at the top)
- F15: `pipeline_write_read_same_system.c`
- F16: `pipeline_wildcard_sync_point.c`
- F17: `pipeline_disabled_system_skips_next.c`, `pipeline_disabled_systems_assert.c`
- F18: `change_detection_fixed_source_moved.c`, `change_detection_parent_moved.c`
- F19: `change_detection_fixed_source_removed.c`, `change_detection_fixed_source_added.c` (valgrind or MemorySanitizer)
- F20: `monitor_up_grandparent.c`
- F21: `instantiate_resurrects_deleted_handle.c`
- F22: `batch_set_remove_add_value.c`
- F23: `staged_childof_recycled_parent.c`

## For round 3

- **Prefab inheritance:**
  - inherited components; `ecs_get` vs `ecs_get_mut`/`ecs_ensure` override copies
  - auto-override
  - the table override cache and its generations (table.c 435-508)
  - changing or deleting prefabs after instantiation
  - IsA traversal in queries and observers; forwarded OnSet for IsA (observable.c 890-1002)
  - `flecs_defer_ensure`'s override path (commands.c 547-627)
- **Worker threads:** query iteration and change detection on worker stages, and the pipeline under real interleavings with `Determinismo.Threads`.
- **Queries:**
  - wildcard terms and `wildcard_matches` shrinking on rematch
  - cascade
  - partially cached queries with a real `field_map`
  - MatchEmptyTables
  - the `prev_match_count` reset at iterator creation (cache_iter.c 36)
- **Reachable-cache invalidation** (observable.c 489-569, entity.c 199).
- **F21's other consequences:** instance child ids inside entity ranges (F8's area), and generations going backwards.
- **Pipeline:** phases and DependsOn, custom pipelines, and `ecs_run_aperiodic(EcsAperiodicEmptyQueries)`, which can make systems inactive mid-frame.
