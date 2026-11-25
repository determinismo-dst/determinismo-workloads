# flecs v4.2.0 in Lean 4 — round 1 report

Everything is in this directory:
- `FlecsLean/*.lean`: the model and its search.
- `Main.lean`: the `flecs-search` program.
- `tests/flecs_lean/*.c`: 20 C tests.
- `.jobs/`: run logs (gitignored).

To build, run `lake build flecs-search FlecsLean`. Then `.lake/build/bin/flecs-search` takes one of these modes:
- `cases` — runs each C test's program in the model.
- `explore SEED N ENTS LEN`
- `exhaust-small LIMIT CFG STAGES ENTS LEN PANICFIRST`
- `ei-explore` and `ei-exhaust` — entity-index programs.
- `lib explore|xsmall|exhaust|ei ...` — determinismo's explore, exhaust, shrink and tape.
- `threads explore|exhaust ...`

## Counterexamples

Every program below is valid flecs API use at the moment each call is made. Line numbers refer to files under `src/` at v4.2.0. Every C test needs a debug build (asserts on). A test returns 0 when flecs behaves as documented. A non-zero return or an abort confirms the prediction.

In a tape, `name=v/n` means the named decision took value `v` of `n` options. The tapes replay through the generator named in brackets after each one.

### F1. A batched remove of a pair whose target died earlier in the merge deletes the entity

What happens:
```c
p = ecs_new(world); e = ecs_new(world); lone = ecs_new(world);
stage = ecs_get_stage(world, 0);
ecs_delete(stage, p);
ecs_add_id(stage, e, Tag);
ecs_remove_pair(stage, e, EcsChildOf, p);    // e never was p's child
ecs_remove_pair(stage, lone, EcsChildOf, p); // alone: a no-op
ecs_merge(stage);
// e is deleted; lone is alive
```

- **Property:** removing a component the entity doesn't have does nothing (EntitiesComponents.md "Operations"). Batching may reorder events, not change outcomes (ObserversManual.md "Event order is undefined between entities"). Only commands that *parent* to a deleted parent delete the child (Manual.md "Deferred operations").
- **Code path:** `flecs_cmd_batch_for_entity` (commands.c 1001-1044) calls `flecs_remove_invalid` (893-942) for every batched command, removes included. For a dead target under a Delete policy it returns false, and the batch calls `ecs_delete(entity)` (1038-1043). A lone remove takes `flecs_remove_id_now` (1416-1419), which has no such check.
- **Story:** the model's one-command-at-a-time merge (P3) and the documented replay (P5) both keep `e`; the batched merge deletes it.
- **Tape** [small menu, random, cfg 0]: `flecs.entity=1/2 flecs.target=1/2 flecs.id=0/11 flecs.call=0/6 flecs.entity=0/2 flecs.target=1/2 flecs.id=4/11 flecs.call=2/6 flecs.entity=0/2 flecs.target=1/2 flecs.id=0/11 flecs.call=3/6 flecs.value=0/2`. This is: delete e1 on stage 0; remove `(ChildOf, e1)` from e0; set C0 on e0; merge. e0 is deleted instead of keeping C0.
- **C test:** `batch_remove_dead_target.c`

### F2. The same with a Panic relationship: the merge panics

What happens:
```c
ecs_add_pair(world, Rel, EcsOnDeleteTarget, EcsPanic);
stage: ecs_delete(stage, tgt);              // legal: nobody has (Rel, tgt)
       ecs_add_id(stage, e, Tag);
       ecs_remove_pair(stage, e, Rel, tgt);
ecs_merge(stage);   // flecs_throw_invalid_delete -> abort
```

- **Property:** no assert on valid calls (Manual.md "Error handling"). Remove of an absent component does nothing.
- **Code path:** commands.c 917-920 → on_delete.c 770-784.
- **Story:** batched, the merge stops with CONSTRAINT_VIOLATED; one command at a time, it completes.
- **Tape** [small menu, cfg 0]: `flecs.entity=0/2 flecs.target=1/2 flecs.id=8/11 flecs.call=2/6 flecs.entity=1/2 flecs.target=0/2 flecs.id=0/11 flecs.call=0/6 flecs.entity=0/2 flecs.target=1/2 flecs.id=0/11 flecs.call=0/6`. This is: remove `(RPanic, e1)` from e0 on the stage; delete e1 on the world; delete e0 on the stage; merge.
- **C test:** `batch_remove_dead_target_panic.c`
- A queued *add* of a Panic pair whose target died before the merge also panics, by the same path; that case is more arguable.

### F3. A queued set of a pair whose target is deleted before the merge aborts the merge

What happens:
```c
stage = ecs_get_stage(world, 0);
ecs_set_pair(stage, e, Position, tgt, {1, 2});
ecs_delete(world, tgt);
ecs_merge(stage);   // assert "second element of pair is not alive" (entity.c 2828)
```
The same happens when `e` already has `(Position, tgt)` and the delete is queued first. The command is then AddModified (commands.c 694-707), and the merge re-adds the pair through `flecs_add_id`.

- **Property:** no assert on valid calls. Commands with dead targets are discarded (Manual.md "Deferred operations"). Deleting a target removes its pairs (Relationships.md "Cleanup properties").
- **Code path:** commands.c 1428-1434 → `flecs_set_id_move` (entity.c 1931) → `flecs_ensure` (507-578) → `flecs_add_id_w_record` → `flecs_table_traverse_add` → `flecs_table_traverse_dont_fragment` (table_graph.c 937) → `ecs_make_alive_id` (entity.c 2828-2829). When batched, `flecs_remove_invalid` drops the command instead (commands.c 1031-1036).
- **Story:** merge fails with INVALID_PARAMETER; the replay succeeds (P5).
- **Tape** [full generator]: `flecs.stages=0/2 flecs.hooks=0/9 flecs.rel.order=0/2 flecs.entity=0/3 flecs.call=0/12 flecs.target=1/2 … flecs.entity=1/3 flecs.call=5/12 flecs.target=1/2 flecs.set.id=2/4 flecs.value=0/3 flecs.entity=0/3 flecs.call=0/12 flecs.target=0/2`. Shrunk to calls: new, new, set `(C0, e0)` on e1 via the stage, delete e0 on the world, merge.
- **C tests:** `staged_set_pair_dead_target.c`, `staged_set_pair_existing_dead_target.c`

### F4. Batched commands plus an observer that deletes its entity through it->stage: internal assert

What happens:
```c
observer OnRemove(Position) { ecs_delete(it->stage, it->entities[i]); }
e = ecs_insert(world, ecs_value(Position, {1, 2}));
ecs_remove(stage, e, Position);
ecs_add_id(stage, e, Tag);
ecs_merge(stage);   // commands.c 1277: ecs_assert(r->table != NULL, ECS_INTERNAL_ERROR)
```

- **Property:** no assert. Observers must use `it->stage` for structural changes, and observer commands finish before the next command (Manual.md "Deferred operations").
- **Code path:** the batch commits inside `flecs_commands_begin`/`end` (commands.c 1156-1158). The end flushes the observer's delete. Then the batch reads `r->table`: in the has-set loop (1191, `flecs_get_mut` asserts at entity.c 601) or at 1277. A release build dereferences NULL at 1285.
- **Story:** batched, an INTERNAL assert; one command at a time, the entity is deleted cleanly (P3).
- **Tape** [full generator]: `flecs.stages=1/2 flecs.hooks=2/9 … flecs.entity=1/3 flecs.call=2/12 flecs.target=2/3 flecs.id=0/7 flecs.entity=1/3 flecs.call=8/12 flecs.target=2/3 …`. Shrunk: add C0 on stage 1; clear on stage 1; add C1 on the world; merge stage 1.
- **C test:** `batch_observer_deletes_entity.c`

### F5. ecs_set/ecs_ensure abort when an OnAdd observer deletes the entity through it->stage

What happens:
```c
observer OnAdd(Position) { ecs_delete(it->stage, it->entities[i]); }
ecs_add(world, a, Position);              // works, a is deleted
ecs_set(world, e, Position, {1, 2});      // entity.c 575: r->table != NULL (INTERNAL)
// the same for a lone queued ecs_set / ecs_ensure at ecs_merge
```

- **Property:** no assert; observers may delete through the stage.
- **Code path:** `flecs_ensure` flushes the observer's commands (entity.c 565-566) and then asserts `r->table` (575). For ensure, the error message at entity.c 1748-1752 covers a *removed* component; this assert fires before it, as INTERNAL. Batched, the same queued set survives, because OnAdd runs after the copy (commands.c 1279-1288).
- **Story:** P1 fails; P3 differs (batched fine, one command at a time aborts).
- **Tape** [full generator]: `flecs.stages=0/2 flecs.hooks=3/9 flecs.rel.order=0/2 … flecs.entity=1/3 flecs.call=5/12 flecs.target=0/2 flecs.set.id=1/4 flecs.value=0/3 …`. Shrunk: new, new, set C1 on e1 via the world.
- **C tests:** `set_observer_deletes_entity.c`, `staged_set_observer_deletes_entity.c`

### F6. An on_set hook that moves its entity makes OnSet observers run for another entity

What happens:
```c
hook on_set(Position) { if (p->x == 99) ecs_add_id(it->world, e, Tag); }
observer OnSet(Position) records it->entities[0] and p->x
ecs_set(world, e, Position, {1,1}); ecs_set(world, f, Position, {2,2});
ecs_set(world, e, Position, {99,99});   // observer sees f with {2,2}
// if e is alone in its table, the observer reads past the table's count
```

- **Property:** OnSet is emitted for the entity that was set (ObserversManual.md "OnSet Events"). Tables aren't locked for on_set hooks; flecs' own test `ComponentLifecycle_locked_storage_on_set` does this add.
- **Code path:** `flecs_notify_on_set_w_cr` (component_actions.c 641-702) captures `table`/`row` before the hook (685) and emits with them afterwards (690-700). The move swapped `f` into that row.
- **Story:** oracle P2 reports "OnSet observer for id 60 invoked for entity 390, but the set was on entity 389". The single-entity variant is P1 no-stale-read.
- **Tapes** [full generator, cfg 1]:
  - Wrong entity: `flecs.stages=0/2 flecs.hooks=1/9 … flecs.entity=0/3 flecs.call=6/12 flecs.target=0/2 flecs.id.component=0/2 flecs.value=2/3 …`. Shrunk: ensure C0=99 on e0, ensure C0 on e2, modified C0 on e0.
  - Stale read: `flecs.stages=0/2 flecs.hooks=1/9 … flecs.entity=1/3 flecs.call=4/12 flecs.target=0/2 flecs.set.id=0/4 flecs.value=2/3 …`. Shrunk: set C0=99 on e1 on the world.
- **C test:** `on_set_hook_moves_entity.c`

### F7. Panic isn't enforced when another pair to the same target follows it in the type, or any pair has Delete

What happens:
```c
RPanic = ecs_new(world); ecs_add_pair(world, RPanic, EcsOnDeleteTarget, EcsPanic);
RPlain = ecs_new(world);                 // created after: larger id
ecs_add_pair(world, e, RPanic, t); ecs_add_pair(world, e, RPlain, t);
ecs_delete(world, t);                    // no panic; e silently loses both pairs
// also: e has (RPanic, t) and (ChildOf, t) -> e deleted, no panic
```

- **Property:** ComponentTraits.md "OnDeleteTarget": Panic throws when the target is deleted.
- **Code path:** `flecs_get_delete_action` (on_delete.c 111-152) keeps the policy of the *last* matching pair; a Delete returns at once (131). Theorem `deleteAction_panic_iff`: Panic is enforced only if no pair has Delete and the Panic pair is last in type order.
- **Story:** oracle P2 reports "deleting t did not panic although e holds a pair with a Panic relationship to it". The control (the other creation order) panics.
- **Tape** [full generator]: `flecs.stages=0/2 flecs.hooks=0/9 … flecs.entity=2/3 flecs.call=2/12 flecs.target=0/2 flecs.id=3/7 flecs.pair.target=1/3 flecs.entity=1/3 flecs.call=0/12 flecs.target=1/2 flecs.entity=2/3 flecs.call=11/12 flecs.target=0/2 flecs.pair.target=1/3 …`. Shrunk: add `(ChildOf, e1)` to e2; delete e1 on the stage; add `(RPanic, e1)` to e2; merge.
- **C tests:** `panic_target_order.c`, `panic_target_with_childof.c`

### F8. Entity ranges: make_alive of an id recycled while its range was inactive

What happens:
```c
a = ecs_entity_range_new(world, 5000, 6000); b = ecs_entity_range_new(world, 7000, 8000);
ecs_entity_range_set(world, b); e = ecs_new(world);      // 7000
ecs_entity_range_set(world, a); ecs_delete(world, e);   // 7000v1 into b's recycled list
ecs_make_alive(world, e);                               // allowed: id not in use
ecs_entity_range_set(world, b);   // entity_ranges.c 129: r->table == NULL (INTERNAL)
// or: ecs_new_from_range(world, b) returns the alive entity (entity.c 660 assert)
```

- **Property:** `make_alive` keeps the id alive and may be used on an id not in use (EntitiesComponents.md "Manual Ids"). Each range keeps its own recycled ids, and `ecs_new_from_range` creates a *new* entity (entity_ranges.h). No internal asserts.
- **Code path:** `flecs_entity_ranges_on_delete` (entity_ranges.c 55-83) moves the id to the range's list. `ecs_make_alive`/`flecs_entity_index_ensure` (entity_index.c 139-186) never takes it back out. `flecs_entity_index_set_range` (125-131) and `ecs_new_from_range` (249-252) reuse it. In a release build, `set_range` turns the alive entity not-alive while it sits in a table.
- **Story:** the entity-index search (200,000 programs) found three symptoms of this one cause: entity_ranges.c 129, entity.c 660, and entity_index.c 152-154.
- **Tapes** [entity-index generator]:
  - `flecs.ei.call=4/7 flecs.range.min=0/3 flecs.range.max=0/4 flecs.ei.call=6/7 flecs.range=0/3 flecs.ei.call=3/7 … flecs.ei.call=2/7 flecs.entity=1/4 flecs.ei.call=0/7 flecs.ei.call=3/7 flecs.entity=1/4 flecs.generation=0/3 flecs.ei.call=5/7 flecs.range=0/3`
  - The new_from_range variant: `… flecs.ei.call=3/7 flecs.entity=0/4 flecs.generation=1/3 … flecs.ei.call=6/7 flecs.range=0/3`
- **C tests:** `range_make_alive_recycled.c`, `range_new_from_range_duplicate.c`

### F9. A queued set is written in place, and is lost if the component goes away before the merge

What happens:
```c
e = ecs_insert(world, ecs_value(Position, {0, 0}));    // no OnSet hooks/observers
ecs_set(stage, e, Position, {1, 1});   // written into e's storage now, queues only an add
ecs_remove(world, e, Position);        // or: ecs_remove_all(stage, ecs_id(Position)) queued first
ecs_merge(stage);                      // Position re-added default-constructed, not {1,1}
```

- **Property:** "The queued changes become visible when the stage is merged" (Manual.md "Deferred operations"), applied in order. With two or more stages the same call queues the value (commands.c 651-654), so the result depends on the stage count.
- **Code path:** `flecs_defer_set_impl` trivial path (commands.c 663-679). `flecs_defer_skip_removed` (379-406) sees only queued remove/clear, not removals on the world or queued `remove_all`/`delete_with`.
- **Story:** P5: merge gives C0 = 0; the replay gives C0 = 1.
- **Tape** [small menu, exhaustive, cfg 0]: `flecs.entity=0/2 flecs.target=0/2 flecs.id=0/11 flecs.call=1/6 flecs.entity=0/2 flecs.target=1/2 flecs.id=0/11 flecs.call=3/6 flecs.value=0/2 flecs.entity=0/2 flecs.target=0/2 flecs.id=0/11 flecs.call=2/6`
- **C tests:** `staged_set_value_lost.c`, `staged_set_after_remove_all.c`

### F10. Batched ChildOf changes emit OnAdd/OnRemove for a pair the entity doesn't have

What happens:
```c
observers OnAdd/OnRemove on (ChildOf, *)
ecs_add_pair(stage, e, EcsChildOf, p1); ecs_add_pair(stage, e, EcsChildOf, p2); ecs_merge(stage);
// OnRemove (ChildOf,p1) while e is in the root table, then OnAdd (ChildOf,p1) while e has (ChildOf,p2)
ecs_add_pair(stage, c, EcsChildOf, p1); ecs_clear(stage, c); ecs_merge(stage);
// OnAdd (ChildOf,p1) for c with no components, and never an OnRemove
```

- **Property:** "An event only fires when the component is actually added/removed" (ObserversManual.md "OnAdd Events", "OnRemove Events").
- **Code path:** flecs_emit skips ids the event's table doesn't have, with a comment naming this exact batching case, but exempts ChildOf pairs (observable.c 1265-1274). Other exclusive relationships aren't affected.
- **Story:** oracle P2 reports "onAdd observer for id (ChildOf,p) invoked for entity 390, which does not have the id".
- **Tape** [small menu, cfg 5]: `flecs.entity=1/2 flecs.target=1/2 flecs.id=3/11 flecs.call=1/6 flecs.entity=1/2 flecs.target=1/2 flecs.id=0/11 flecs.call=4/6`
- **C test:** `batch_childof_replaced_onadd.c`

### F11. Under batching, OnSet observers and on_set hooks see later values

What happens:
```c
observer OnSet(Position)
ecs_set(stage, e, Position, {1,1}); ecs_set(stage, other, Position, {2,2});
ecs_set(stage, e, Position, {3,3}); ecs_merge(stage);    // e's OnSet calls see 3, 3 (immediately: 1, 3)
ecs_set(stage, e, Position, {99,99}); p = ecs_ensure(stage, e, Position); p->x = 1;
ecs_merge(stage);                                         // the set's OnSet sees 1
```

- **Property:** ObserversManual.md "OnSet order is maintained … agnostic to whether operations are deferred or executed immediately".
- **Code path:**
  - The batch copies every set value before any OnSet runs (commands.c 1179-1241).
  - `flecs_defer_ensure` returns a queued set's own storage (`flecs_defer_find_cmd_value`, 489-545 via 567-574).
  - An `on_set` hook sees the same later value; the exhaustive runs (cfg 1) show its side effect (adding a tag at value 99) changing the final state.
  - A later queued clear in the same batch drops an earlier set's OnSet.
- **Story:** P3b/P5b report "batched OnSet [(60, 3), (60, 3)] vs one-by-one [(60, 1), (60, 3)]".
- **Tape** [full generator]: `flecs.stages=1/2 flecs.hooks=7/9 … flecs.entity=0/3 flecs.call=4/12 flecs.target=2/3 flecs.set.id=0/4 flecs.value=1/3 flecs.entity=0/3 flecs.call=5/12 flecs.target=2/3 flecs.set.id=0/4 flecs.value=0/3 …`. Shrunk: set C0=2 then C0=1 on stage 1; merge.
- **C tests:** `batch_onset_values.c`, `staged_ensure_rewrites_set.c`

### F12. Batching runs an entity's later commands before other entities' earlier ones; a child survives its parent's deletion

What happens:
```c
ecs_add_pair(stage, c, EcsChildOf, p);
ecs_delete(stage, p);
ecs_remove_pair(stage, c, EcsChildOf, p);   // or ecs_clear(stage, c)
ecs_merge(stage);   // c alive; in queue order c is p's child when p dies and is deleted
// also: a queued ecs_modified sees a component added by a later queued ecs_add (extra OnSet)
```

- **Property:** commands run at merge in queue order. Commands on entities deleted before they run are discarded. Deleting a parent deletes its children (Relationships.md "Cleanup properties"). Batching is allowed to reorder events, not to change which entities survive (ObserversManual.md "Event order is undefined between entities").
- **Code path:** `flecs_commands_flush` batches all of an entity's commands at its first one (commands.c 1351-1369, 968-1134).
- **Story:** P3 and P5 both differ. Also found by the two-worker-thread search: P5 for threads, after 1,420 timelines.
- **Tapes:**
  - [small menu, cfg 0]: `flecs.entity=1/2 flecs.target=1/2 flecs.id=3/11 flecs.call=1/6 flecs.entity=0/2 flecs.target=1/2 flecs.id=0/11 flecs.call=0/6 flecs.entity=1/2 flecs.target=1/2 flecs.id=0/11 flecs.call=4/6`
  - Threads: `flecs.entity=0/2 flecs.call=5/6 flecs.entity=0/2 flecs.call=3/6 flecs.id=0/2 flecs.value=0/2 flecs.entity=1/2 flecs.call=1/6 flecs.id=3/5 flecs.entity=1/2 flecs.call=2/6 flecs.id=0/3 flecs.entity=0/2 flecs.call=0/6 flecs.entity=1/2 flecs.call=5/6 thread.next=0/2 ×4`
- **C test:** `batch_child_survives_parent_delete.c`

### F13. The generation wraps after 2^16 recycles

What happens: delete `e`, then 65,536 times create (recycling the same id) and delete. `ecs_is_alive(world, e)` is true again for the deleted handle.

- **Property:** EntitiesComponents.md "Deletion" and "Liveliness Checking": a deleted handle is not alive.
- **Code path:** `ECS_GENERATION_INC` uses a 16-bit field (api_defines.h 333-335). Theorem `genInc_period`: 65,536 increments give back the original handle (checked by `bv_decide`, so it carries new axioms).
- **Tape:** none; this needs 65,536 recycles, beyond the search bounds.
- **C test:** `generation_wraps.c`

### F14. Inside an on_add hook the entity doesn't have the component yet (lower confidence)

What happens: in Position's `on_add` hook, `ecs_has(it->world, e, Position)` is false and `ecs_get` returns NULL.

- **Property:** the component lifecycle diagram (EntitiesComponents.md, `img/component-lifecycle.svg`) shows "table move → ctor → on_add hook". The docs don't say this in words.
- **Code path:** `flecs_table_move` runs the add hooks (table.c 1886-1906) before `flecs_move_entity` repoints the record (entity.c 188-191).
- **Tape** [full generator, cfg 4]: `flecs.stages=0/2 flecs.hooks=4/9 … flecs.entity=2/3 flecs.call=2/12 flecs.target=0/2 flecs.id=0/7 …`. Shrunk: add C0 to e2 on the world.
- **C test:** `on_add_hook_view.c`

### Not counted as findings

- **Batching elides an add/remove pair, along with its hooks' and observers' side effects.** For example, an OnRemove observer that deletes its entity, or an `on_remove` hook that enqueues a set. The docs warn about this: "features like command batching impact how and when events are emitted" (ObserversManual.md "Bad Use Cases").
- **A `ecs_ensure` write on one stage overwritten by an earlier-merged stage's queued ensure.** `ensure` on a stage is documented to return existing storage.
- **227 P1 failures in explore-c** come from menu 6's observer body calling `ecs_set` on an entity that was already dead. That is the hook author's misuse.

## What was replicated

Files and the flecs code each follows (line numbers are cited in the comments throughout):
- `Ids.lean`: ids, generations and pairs (api_defines.h; builtin ids from world.c 24-102).
- `EntityIndex.lean`: all of `storage/entity_index.c` and `addons/entity_ranges.c` — dense/sparse index, recycling, `make_alive`, `get_alive`, `is_valid`, ranges.
- `World.lean`: tables (type, entities, columns, debug lock counters); component records (refcounts, wildcard records, table caches, `flecs_component_new`'s target-alive assert and IsTarget/IsId row flags); hook and observer configuration; command-queue types (commands.h).
- `Ops.lean`:
  - Graph and table moves: `flecs_table_traverse_add`/`_remove`; `flecs_find_table_with`/`without` (exclusive replace); `flecs_table_ensure`/`fini`; `flecs_table_append`/`delete`/`move`/`merge` (swap-remove, hooks in column order, complex vs fast paths).
  - Entity paths: `flecs_move_entity`, `flecs_commit`, `flecs_ensure`, `flecs_get_mut`, `flecs_set_id_move`, `flecs_modified_id_if`, `flecs_notify_on_set_w_cr`, `flecs_invoke_hook` (locks), `flecs_emit` (single-term observers, the table-record skip and its ChildOf exemption).
  - Commands: the whole of commands.c's queue — `flecs_cmd_new_batched` (entry caches, sparse entries by 32-bit index, different-generation handling), `remove`/`clear` bookkeeping, `skip_removed`, `find_cmd_value`, `defer_set_impl` (trivial in-place path, stage-count rule), `defer_ensure`, `flecs_remove_invalid`, `flecs_cmd_batch_for_entity` (split, set copy, deferred OnAdd), `flecs_commands_flush` (nested levels, cursor/resume, destination stage flushes), `commands_begin`/`end`.
  - Cleanup: on_delete.c — mark, `get_delete_action`, `target_mark`, `remove_from_table`, `clear_entities`, `clear_ids`, `flecs_on_delete`.
  - Public API: `ecs_new`, `delete`, `add`, `remove`, `set`, `ensure`, `modified`, `clear`, `delete_with`, `remove_all`, `merge`, `readonly_begin`/`end`, `make_alive`, `new_from_range`.
- `Program.lean`, `Gen.lean`, `Search.lean`, `Threads.lean`: programs, oracles, generators, search drivers, the determinismo adapter, and worker threads through `Determinismo.Threads.interleave`.

## What is not exact, and why

- **Graph edges aren't cached.** The only behaviour that depends on an edge existing is the `ecs_make_alive_id` call on a new edge. For a dead target the edge never exists: it is removed when its table is freed (table.c 1306, table_graph.c 1161-1213).
- **Wildcard record lists are scans in creation order.** The `(*)`, `(*,*)`, `(ChildOf, 0)` and Flag records aren't modelled.
- **Table event flags are computed from the configured hooks and observers.** This is the same as flecs when observers exist before tables, as they do in every scenario.
- **Observers are single-term with self source, run in creation order** (the docs leave the order undefined). There is no up traversal, propagation or forwarding.
- **Values are naturals and the constructor gives 0.** In C, components without a ctor are uninitialized; the C tests use a ctor sentinel.
- **Hooks and observers have bodies from a small menu** (add, remove, set, delete through world or stage). ctor, dtor, move, copy, on_replace and on_validate aren't modelled.
- **Not modelled:** IsA/prefabs/overrides, Union, sparse/DontFragment, non-fragmenting ChildOf (`Parent`), ordered children, names, toggles, With, emplace, clone, bulk operations, custom events, queries and query caches (part 5), systems/pipeline (part 6), and ChildOf depth tracking. Because depth isn't modelled, programs never make an entity its own parent.
- **Thread steps are whole API calls, atomic.** Data races inside a call aren't modelled.

## Assumptions

- **Build and world:** debug build (asserts on). The C tests use `ecs_mini()`.
- **Id ordering:** user components get low ids (< 256), below the builtins; user tags and relationships get ids above all builtins. The model uses C0=60, C1=61 and user entities from 385, as `EcsFirstUserEntityId` does.
- **Allowed failures** (not bugs):
  - an argument check of the call itself;
  - a locked-storage assert caused by a hook or observer body using `it->world` on a locked table (Manual.md);
  - the Panic of deleting a target that is in use;
  - for ranges: overlap, creation after deletes, an exhausted range, and `make_alive` of an id alive with another generation.
- **Docs-allowed calls only:** programs issue only calls the docs allow at the moment they are made. That means alive entities, no world calls during readonly, `modified()` on the world only for a component the entity has, and no ChildOf to itself.
- **Merge order:** stages merge in order 0 … n-1.

## Properties and their sources

Broke means the property was violated by some program; Held means it held in every run.

1. **P1a** — no assert, crash or use-after-free (Manual.md "Error handling"). **Broke** (F2–F5, F8).
2. **P1b** — no read of table storage past its row count. **Broke** (F6).
3. **P2a** — OnSet goes to the entity that was set (ObserversManual.md "OnSet Events"). **Broke** (F6).
4. **P2b** — OnAdd runs only for ids the entity has ("OnAdd Events"). **Broke** (F10).
5. **P2c** — OnRemove runs only for ids the entity has ("OnRemove Events"). **Broke** (F10).
6. **P2d** — deleting a target held by a Panic pair panics (ComponentTraits.md "OnDeleteTarget"). **Broke** (F7).
7. **P2e** — `make_alive` leaves the id alive (EntitiesComponents.md "Manual Ids"). **Held.**
8. **P2f** — each alive entity sits in exactly one live table, at its recorded row. **Held.**
9. **P2g** — table rows hold only alive entities. **Held.**
10. **P2h** — every live table is in the records of each of its ids. **Held.**
11. **P2i** — after an operation, no table holds a pair with a dead target (Relationships.md "Cleanup properties"). **Held** (the F3 crashes abort first).
12. **P2j** — `ecs_new` never returns an alive id. **Held.**
13. **P2k** — `ecs_new` returns ids inside the active range (EntitiesComponents.md "Ranges"). **Held.**
14. **P3** — the batched merge gives the same state and failure as running each command alone (ObserversManual.md "Event order is undefined between entities"). **Broke** (F1, F4, F5, F12).
15. **P3b** — per-entity OnSet values are the same batched and one by one ("OnSet order is maintained"). **Broke** (F11).
16. **P4** — inside an on_add hook the entity has the component (lifecycle diagram). **Broke** (F14).
17. **P5** — the merge equals replaying the queued calls on the world in order, with the documented discard rules (Manual.md "Deferred operations"). **Broke** (F1, F3, F9, F12).
18. **P5b** — per-entity OnSet values are the same merged and replayed. **Broke** (F11).
19. **P6** — with worker threads (one stage each, multithreaded readonly), the merged state doesn't depend on how the threads interleaved. **Held.**
20. **P5t** — the threads' merged state equals replaying stage 0's calls, then stage 1's. **Broke** (F12).

## Search runs and results

Speed: about 60 µs per program, including the three runs P3 and P5 need. Every hook and observer configuration (`cfg` 0–8) was covered.

Own drivers:
- **Random exploration** (`explore`, 300,000 programs, 3 entities, 8 calls, seed 900000): 52,846 failing. By property:
  - P1a: 18,090 — pair dead target 2,704; `entity.c 575` 10,431; batched Panic 4,222; `commands.c 1277` 326; `entity.c 601` 180; hook misuse 227
  - P1b: 2,967
  - P2: 417
  - P3: 6,623
  - P3b: 765
  - P4: 24,707
  - P5: 7,400
  - P5b: 1,030
- **Earlier random runs:** 200,000 programs at 3 entities × 6 calls, and 200,000 at 4 × 10. Same causes, before the misuse filter.
- **Exhaustive, small call menu**, 2 entities, 2 calls, all 9 configurations: **complete**, 94,864 programs each (853,776 total). Failing per cfg: 132, 17,744, 204, 4,810, 45,500, 156, 424, 460, 392.
- **Exhaustive, 3 calls**, cfgs 0, 2, 3, 5, 8: 1,500,000 programs each, bound not reached.
- **Entity index:** random 200,000 programs of 12 calls found 22 failing, all one cause (F8). Exhaustive at 5 calls: 2,000,000 programs, bound not reached, none failing (F8 needs a specific 5–6 call shape).

determinismo `explore`, `exhaust` and `shrink`:
- One run per finding, with a signature filter: F1 after 1,970 timelines; F2 188; F3 9; F4 550; F5 44; F6 36,718 (stale-read variant 8); F7 54; F8 48,034 and 6,094; F10 665; F11 482; F12 318; F14 30.
- `exhaust` of P3 on the small menu (2 calls, cfg 0): complete, 94,864 timelines, no counterexample.

Threads:
- `exhaust`, 300,000 timelines each for cfg 0 and cfg 8: no P6 or P5t violation, bound not reached.
- `explore` (3 calls per thread): P5t after 1,420 timelines (F12).

## Theorems

No `sorry`. Each theorem's axioms are printed by `FlecsLean/Axioms.lean`.

Standard axioms only (propext, Classical.choice, Quot.sound):
- `deleteAction_delete`: any Delete pair gives Delete.
- `deleteAction_no_delete`: with no Delete, the last pair's policy wins.
- `deleteAction_panic_iff`: Panic is enforced exactly when no pair has Delete and the Panic pair is last. The model's `deleteActionFor` uses this same function.
- `EIndex.tryGetAny_some`.
- `EIndex.not_alive_of_dead_slot`: under the dense/sparse invariant, ids in the not-alive part of the dense array are not alive.
- `EIndex.newId_recycled_not_alive`: `new_id`'s recycle branch never returns an alive id.
- `toUInt64_succ`.

Checked by `bv_decide`, which adds native-evaluation axioms (`*._native.bv_decide.ax_1_5`). These do not meet "no new axiom":
- `genInc_lo32`, `genInc_generation`, `genInc_high`, `genInc_genIter`, `genIter_zero`, `iterate_genInc`, `genInc_period` (the 2^16 wrap behind F13).

## Library gaps

1. `explore` and `exhaust` stop at the first counterexample and give no per-property or per-cause counts. I added counting drivers that key failures by a signature (property plus detail with numbers erased).
2. `shrink` only cuts the decision path or sets values to 0; it can't drop a call from the middle of a program. I added call-level shrinking that keeps the same signature (`shrinkSig`).
3. There is no notion of allowed failures versus bugs, and no support for comparing runs. Both are done in the properties: each program runs three ways (merge, one command at a time, documented replay).
4. `exhaust`'s depth-first order reaches deep but narrow bugs late. The range bug needs 5–6 calls in a specific shape: 2,000,000 exhaustive timelines missed it, and random exploration found it.
5. `Threads` steps are atomic and stage-agnostic. I built worker stages on `Process` memory, with whole API calls as steps.

## C tests (tests/flecs_lean/)

All 20 compile with `cc -c` against `upstream/distr/flecs.h`; none was run.

- F1: `batch_remove_dead_target.c`
- F2: `batch_remove_dead_target_panic.c`
- F3: `staged_set_pair_dead_target.c`, `staged_set_pair_existing_dead_target.c`
- F4: `batch_observer_deletes_entity.c`
- F5: `set_observer_deletes_entity.c`, `staged_set_observer_deletes_entity.c`
- F6: `on_set_hook_moves_entity.c`
- F7: `panic_target_order.c`, `panic_target_with_childof.c`
- F8: `range_make_alive_recycled.c`, `range_new_from_range_duplicate.c`
- F9: `staged_set_value_lost.c`, `staged_set_after_remove_all.c`
- F10: `batch_childof_replaced_onadd.c`
- F11: `batch_onset_values.c`, `staged_ensure_rewrites_set.c`
- F12: `batch_child_survives_parent_delete.c`
- F13: `generation_wraps.c`
- F14: `on_add_hook_view.c`

## For the next rounds

- **To model next:** queries and query caches (cache.c, match.c, change detection), the pipeline's sync points, IsA/prefab overrides, and observer up-traversal.
- **Theorems:** re-prove the generation lemmas without `bv_decide` (bit extensionality), so they meet "no new axiom".
