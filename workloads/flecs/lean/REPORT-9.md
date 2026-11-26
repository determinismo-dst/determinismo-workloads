# flecs v4.2.0 in Lean 4 — round 9 report

Everything is in this directory.

New files under `FlecsLean/`:
- `OrUp.lean`: `select_or` over an unwritten `$this` with up and self|up terms. It follows the iterator's field state: `ids`, `trs`, `columns`, `sources` and the up flag (F59).
- `SparseIter.lean`: iterating a DontFragment component while its sparse set changes, for both the trivial sparse search and the VM's sparse select (F60).
- `SortGroup.lean`: order_by with group_by, and `ecs_iter_set_group` (F61).
- `TheoremsR9.lean`: this round's theorems.

Extended files:
- `EvHier.lean`: setting the Parent component to the parent the entity already has (F62), and property P-EV7.
- `SpawnDepth.lean`: repeated instantiations at one depth.
- `TheoremsR8.lean`: `parent_reparent_no_remove`, re-proved over the extended `step`.
- `Axioms.lean`: the new theorems.

Other files:
- `Main.lean`: the `flecs-search` program, with the new modes `ou`, `si9` and `sg`.
- `tests/flecs_lean/`: 87 C tests, 6 of them new; none of the earlier ones changed. `README.txt` maps them to predictions, with build flags.
- `.jobs/r9/*.log`: this round's logs. `scratch/r9-runs.sh a|b|c|d|e|f` re-runs the searches.

New modes of `flecs-search`:
- `ou explore|exhaust|lib|cases` (F59)
- `si9 exhaust|lib|cases` (F60)
- `sg exhaust|cases` (F61)
- `eh` (extended: F62), and `sd cases` (two new cases)

Line numbers refer to files under `src/` unless a path says otherwise. In a tape, `name=v/n` means the named decision took value `v` of `n` options.

## The real flecs on round 8

As the coordinator reported, every round-8 prediction is confirmed:
- F55 corrected: the leak, with `FLECS_USE_OS_ALLOC` and with `FLECS_SANITIZE`; the allocator crash, in debug and `-DNDEBUG`.
- F56: its debug abort is the columns check REPORT-8 said may come first.
- F57.
- F58: the debug abort and the release leftover.
- The Parent forms of F48 and F50.

No model correction this round.

## Counterexamples

### F59. In an uncached Or chain with an up or self|up term, results carry another term's source, id or up flag

The outcome is a wrong source, a wrong id, a value read from another entity, a crash, or a debug abort. All four forms come from one place: `flecs_query_select_or` restores only three of the field's five pieces of state.

```c
// (b) Position(up) || Velocity, uncached
p [Position, Velocity {100,200}];  c ChildOf p [Velocity];  e [Velocity {3,4}]
// e's result: ecs_field_src(it, 0) == p; ecs_field(it, Velocity, 0) reads p's {100,200}
// (a) p [Position]; c ChildOf p; e [Velocity]
// e's result: source 0, columns[0] = -1, up flag set; ecs_field reads entity 0's record:
//   debug assert "entity 0 does not exist", release NULL table
// (c) Position(self|up) || Velocity, the world of (a)
// ecs_query_next aborts (debug): "it->columns[0]=-1 does not match expected 0"
// (d) Position || Velocity(up); x [Velocity]; D ChildOf x [Position]; D2 ChildOf x [Tag]
// D2's result: ecs_field_id(it, 0) == Position; ecs_field crashes (NULL table record)
```

**Properties:**
- P-OR1 (new): a result of an Or chain describes the term that matched it.
  - Queries.md "Source": `ecs_field_src` "Returns 0, meaning entity is stored in it.entities" for a `$this` match.
  - flecs.h `ecs_field_src`: "the entity on which the field was matched".
  - Queries.md "Or Operator": "a single term can return results of multiple types … an application has to make sure that it is working with the expected type".
  - The same section: "We can only use ecs_field if the field type is the same for all results". Position and Velocity are both `{float x, y}` in the tests.
- P1: no crash or abort. Manual.md "Error handling".

**Code path:**
- `flecs_query_select_or` (query/engine/eval.c 1390-1508):
  - a result of the first term is yielded as is;
  - a result of a later term is checked against the earlier terms with `$this` marked written (1458-1481). A failing term falls through to the next one (`flecs_query_end_block_or`, compiler_term.c 282-305);
  - a duplicate is skipped without restoring anything (1473-1477, 1488-1490);
  - otherwise only the field's `it->ids`, `it->trs` and `it->columns` are restored (1492-1495), from the values saved before the check (1454-1456). `it->sources` and the field's bit in `it->up_fields` are not.
- What each op writes:
  - A self select (`flecs_query_select_w_id`, eval.c 52-133) and a self with (`flecs_query_with`, 150-249) write ids, trs and the column through `flecs_query_set_match` (eval_utils.c 383-399).
    - The column is -1 whenever the source or the up flag is set (`flecs_query_it_set_tr`, 359-369).
    - Neither op touches the source or the flag.
  - The up select (`flecs_query_up_select`, eval_up.c 124-283):
    - it writes ids once per selected table;
    - it resets the source before each table (207) and sets it to each traversable entity (98);
    - it sets the up flag at each yield (280);
    - when exhausted, the source is 0 again but the flag stays set.
  - The self|up select yields each table that has the component first, with the flag reset (220-231).
  - The up with (`flecs_query_up_with`, 452-546) writes source, tr, id and flag on success (`flecs_query_up_set_fields`, 285-301), and nothing on failure.
  - The self|up with (`flecs_query_self_up_with`, 548-590) resets the flag first (557), even when it then fails.
- The forms:
  - (a) The up term's flag outlives it. The self term's columns become -1 while the source is 0.
  - (b) The duplicate check of c's table runs the up term, which succeeds and writes the source p. The self term's next results keep it.
  - (c) The duplicate check's self|up with resets the flag after `select_or` saved the column -1. The restore leaves tr set, source 0, flag clear and column -1, so a debug build's `flecs_iter_assert_columns` (eval_iter.c 253-273) aborts.
  - (d) The up select writes ids once per parent table. The duplicate check of D's table (a self term, `flecs_query_with`) writes Position's id and D's record. D2's result then saves and restores those.
- How `ecs_field` (iter.c 112-160) reads the field:
  - a column ≥ 0 reads `it->table`'s column;
  - otherwise `flecs_field_shared` (206-246) reads the source's table;
  - a source 0 means `flecs_entities_get(world, 0)`: "entity 0 does not exist" (storage/entity_index.c 74-75) in a debug build, a NULL table in a release build;
  - a source whose table lacks the id gets a NULL record from `flecs_component_get_table` (242-244).
- flecs's own `Traversal_this_or_w_up*` tests use tags (no columns) and only up terms (`Foo(up) || Bar(up)`). The model finds no failure in that shape (a case).
- A cached query evaluates the chain once per table when its cache is built. `flecs_query_cache_match_set` stores `it->up_fields` and the sources (query/cache/match.c 122-160), so forms (a) and (b) would be kept in the cache. Read, not tested: the tests use uncached queries.

**Story** (form b):
- "wrong source: result [e1] from term 2 (Velocity) of Position(up) || Velocity: ecs_field_src is e2, expected 0 (columns -1, source e2, up flag true): select_or restores only ids, trs and columns (eval.c 1492-1495); the source was written by an earlier term's duplicate check (flecs_query_up_set_fields, eval_up.c 285-301)";
- "wrong value: … ecs_field reads Velocity of e2, expected Velocity of e1".

**Tapes** (`ou lib exhaust`, 3 entities, 2 terms):
- Wrong source (form b), after 4,189 timelines: `ou.own=0/4 ou.par=0/4 ou.own=1/4 ou.par=3/4 ou.own=1/4 ou.par=0/4 ou.kind=1/3 ou.comp=0/2 ou.kind=0/3 ou.comp=0/2`.
  - Shrunk: e1 [Position] ChildOf e2, e2 [Position]; `Position(up) || Position`. e2's own result names the source e2.
- Wrong value (form d with self|up), after 2,166: `ou.own=0/4 ou.par=0/4 ou.own=0/4 ou.par=3/4 ou.own=3/4 ou.par=0/4 ou.kind=0/3 ou.comp=0/2 ou.kind=2/3 ou.comp=1/2`.
  - Shrunk: e1 ChildOf e2, e2 [Position, Velocity]; `Position || Velocity(self|up)`. e1's result reads e2's Position.
- Crash (form a), after 1,885: `ou.own=0/4 ou.par=0/4 ou.own=0/4 ou.par=3/4 ou.own=1/4 ou.par=0/4 ou.kind=1/3 ou.comp=0/2 ou.kind=0/3 ou.comp=0/2`.
  - Shrunk: e1 ChildOf e2, e2 [Position]; `Position(up) || Position`.
- Debug abort (form c), after 21,050: `ou.own=0/4 ou.par=2/4 ou.own=1/4 ou.par=0/4 ou.own=2/4 ou.par=0/4 ou.kind=2/3 ou.comp=0/2 ou.kind=0/3 ou.comp=1/2`.
  - Shrunk: e0 ChildOf e1, e1 [Position], e2 [Velocity]; `Position(self|up) || Velocity`.

**C tests:**
- `query_or_up_then_self_fields.c`: form (b), then form (a).
  - Two controls run first: the self term first (`Velocity || Position(up)`), and form (a)'s world without the child.
  - Each result's source, `columns[0]` and up flag are printed before the field is read.
  - Form (b) confirms by a wrong source or value; form (a) by the abort or the crash.
- `query_or_self_up_then_self_columns.c`: form (c).
  - Debug: the abort in `ecs_query_next`.
  - `-DNDEBUG`: columns -1, then a crash in `ecs_field`.
- `query_or_self_then_up_fields.c`: form (d).
  - The control is `Velocity(up)` alone.
  - The wrong id or the crash confirms.

### F60. Removing a DontFragment component while iterating a query on it skips entities (the trivial sparse search) or returns one twice (the VM's sparse select)

```c
Df: DontFragment tag on 2100 entities;  query "Df" (uncached: the trivial sparse search)
while (ecs_query_next(&it)) for each entity: ecs_remove_id(world, e, Df);
// 1076 returned; the last 1024 created keep Df and are never returned
// "Df, !Unused" (the VM's select) with the same loop: all 2100
a0, a1 in [Position]; b0, b1 in [Position, Tag]; Df added to a0, b0, a1, b1
query "Df, Position" (uncached); after the first result (b1): ecs_remove_id(world, a0, Df)
// b1 is returned twice: the last result is the range b0, b1
```

**Property P-IT4** (new): removing a DontFragment component during an iteration over it neither skips nor repeats another entity.
- flecs's own `DontFragment_add_to_self_while_iterate` (test/query/src/DontFragment.c 6427-6471) changes the DontFragment ids of the current result while iterating, without deferring. A DontFragment change moves no entity.
- Systems.md "Immediate systems": operations through the iterator's world "execute immediately"; only "operations on the iterated over entity must still be deferred".
- Queries.md "Iteration": table locking exists so that changes do not cause "iterating an entity twice, or missing an entity".

**Code path:**
- A DontFragment id keeps its entities in a sparse set.
  - A removal swaps the removed id with the last one and shrinks the count (`flecs_sparse_remove`, datastructures/sparse.c 398-…; `flecs_sparse_swap_dense`, 177-191).
  - No entity changes table, so no table lock applies.
- The trivial sparse search (`flecs_query_trivial_sparse_search`, query/engine/eval_sparse.c 506-618):
  - it is chosen for a query whose terms are all self `$this` And terms on DontFragment ids (validator.c 1902-1942);
  - the query is uncached, as a query with no cacheable term always is (api.c 149-161);
  - it walks the dense array forward from `op_ctx->cur`, in batches of FLECS_QUERY_SPARSE_BATCH_SIZE (1024, query/types.h 373), re-reading the count (561-575);
  - an id swapped into a slot it has already passed is never returned.
- The VM's sparse select (`flecs_query_sparse_select_id`, 121-182):
  - it walks backward from the count at its first call, grouping ids of one table at adjacent rows (159-175);
  - removing the current result's ids is safe there, because the ids swapped in were already returned;
  - removing an id not yet returned swaps an already returned id into its slot.
- The select asserts `cur < count` ("sparse iterator invalidated while iterating", 145-146). That catches a set that shrank below the cursor. The model counts those programs separately, as a debug abort flecs intends; the C test's program does not reach it.

**Story:**
- "skipped: the trivial sparse search (batch 2 standing for 1024) never returns e3, which had Df until its turn: removing a returned entity's Df swapped a later id into a slot the forward walk had passed (eval_sparse.c 561-575, sparse.c 177-191)";
- "twice: the VM's sparse select (Df, Position, uncached) returns e3 2 times: removing an unvisited entity's Df swapped the last dense id (already returned: the select walks backward, eval_sparse.c 140-149) into its slot (sparse.c 177-191)".

**Tapes** (`si9 lib exhaust`, 4 entities, 3 callbacks):
- Skipped, after 2 timelines: `si9.tab=0/2 si9.tab=0/2 si9.tab=0/2 si9.tab=0/2 si9.mode=0/2 si9.batch=0/2 si9.self=0/2 si9.rm=0/5 si9.rm=0/5 si9.rm=1/5`.
  - Shrunk: one table, batch 1; the third callback removes e0, so e3 is never returned.
- Twice, after 1,276: `si9.tab=0/2 si9.tab=0/2 si9.tab=0/2 si9.tab=1/2 si9.mode=1/2 si9.self=0/2 si9.rm=1/5 si9.rm=0/5 si9.rm=0/5`.
  - Shrunk: e3 in the second table; the first callback removes e0.

**C test:** `sparse_remove_while_iterating.c`.
- Part A: the trivial search, with the VM's select as the control.
- Part B: the VM's select.

Round 7 read the forward walk and did not file it ("Queries.md asks for deferred or staged changes during iteration"). Two things changed that:
- flecs's own test changes the DontFragment ids of the current result without deferring;
- the VM's backward walk shows that removing the current result's ids is meant to be safe. The trivial search is an optimisation of the same query, and it walks the other way.

### F61. `ecs_iter_set_group` on a query with group_by and order_by returns the group table by table, not in order

```c
group_by (Rel, *) target; order_by Position.x
group TgtA: [Position, (Rel, TgtA)] x = 1, 3; [Position, (Rel, TgtA), Tag] x = 2, 4
ecs_iter_set_group(&it, TgtA);   // 1, 3, 2, 4; a full iteration gives the group as 1, 2, 3, 4
```

**Property P-SO1** (new): the results of an order_by query come in order of the sorted component, group by group. `ecs_iter_set_group` limits them to one group and keeps that order.
- Queries.md "Sorting": "Sorted queries use a two-step process to return entities in a sorted order … This second step is necessary to support datasets where ordered results have entities interleaved from multiple tables".
- flecs.h `ecs_iter_set_group`: "This operation limits the results returned by the query to only the selected group ID".
- flecs's own `GroupBy_group_by_w_sort_reverse_group_creation` expects the sorted results group by group.

**Code path:**
- `flecs_query_cache_iter_init` (query/cache/cache_iter.c 11-37) sorts the changed tables in place and points the iterator at `cache->table_slices` (30-33).
- `flecs_query_cache_build_sorted_tables` (order_by.c 212-222) builds the slices group by group, merging each group's tables (`flecs_query_cache_build_sorted_table_range`, 91-208).
- `ecs_iter_set_group` (query/api.c 758-795) replaces the slices with `&group->tables` (787-791): the group's matches in insertion order, each a whole table.

**Story:** "after ecs_iter_set_group(group 0), the order_by query returns [1, 3, 2, 4], expected [1, 2, 3, 4]: ecs_iter_set_group iterates the group's tables (query/api.c 787-791), not the sorted slices (cache_iter.c 30-33, order_by.c 212-222), so the group's tables are not merged".

**Search:** `sg exhaust 3 2` (3 tables of 2 values each, 2 groups) is complete: 98,304 programs, 25,668 failing.
- Every failing program goes through `ecs_iter_set_group`, with two or more tables in the group whose values interleave.
- A full iteration is in order in every program.

**C test:** `query_order_by_set_group_unsorted.c`; the full iteration is the control.

### F62. Setting the Parent component to the parent the entity already has, or `ecs_modified` on it, delivers OnAdd (ChildOf, parent) again, and forwards the parent's components as OnAdd again

```c
Tag; p has Tag; e = ecs_new_w_parent(p); g = ecs_new_w_parent(e)
observers: (ChildOf, *) OnAdd; Tag(up) OnAdd
ecs_set(world, e, EcsParent, {p});      // OnAdd (ChildOf, p) for e; OnAdd Tag for e and g
ecs_modified(world, e, EcsParent);      // the same
// ChildOf storage: ecs_add_pair(c, EcsChildOf, p) again: nothing
```

**Property P-EV7** (new): an OnAdd only when the entity gains the id. ObserversManual.md "OnAdd Events": "An event only fires when the component is actually added to the entity, so not on each add operation".

**Code path:**
- `ecs_set_id` (entity.c 1981-2031) calls `flecs_copy_id` (810-841).
- The `on_replace` hook `flecs_on_replace_parent` (storage/non_fragmenting_childof.c 113-197) returns for an unchanged parent (138-144: "Setting the parent a child already has is a no-op").
- `flecs_copy_id` still emits OnSet (838-839). The table has OnSet observers for EcsParent because a `(ChildOf, *)` OnAdd observer counts as one (observer.c 151-157).
- `flecs_emit` re-emits the Parent component's OnSet as the OnAdd of `(ChildOf, parent)` (observable.c 1160-1183). Its forward delivers the parent's components (799-888) and propagates them below the entity.
- `ecs_modified` reaches the same OnSet (`ecs_modified_id`, entity.c 1889-1925).
- This is the other side of F57: the re-emission turns every OnSet into a pair OnAdd, whether the parent changed or not, and never emits the old pair's OnRemove.

**Story:**
- "pair: after ecs_set(e2, EcsParent, {e0}), the (ChildOf, *) OnAdd observer was invoked for e2 and e0, but e2's parent was already e0 (Parent storage): …";
- "component: … the OnAdd observer was invoked for e3 with source e0, but e3 already had C from e0 (table): the re-emitted OnAdd of an unchanged (ChildOf, parent) forwards the parent's components again".

**Tape** (`eh lib exhaust`, 3 entities, 5 calls), after 1,889,797 timelines: `eh.storage=0/2 eh.hs=0/2 eh.hs=0/2 eh.hs=1/2 eh.call=0/4 eh.e=0/3 eh.call=0/4 eh.e=0/3 eh.call=0/4 eh.e=0/3 eh.call=2/4 eh.e=2/3 eh.p=0/3 eh.call=2/4 eh.e=2/3 eh.p=0/3`.
- Shrunk: `ecs_set(e2, EcsParent, {e0})`, twice.

**C test:** `parent_set_same_parent_on_add.c`; the ChildOf re-add is the control.

## Fixes for F48–F58

For each finding: the function, the change a fix would make, and why it is safe.

### F48: a base's OnAdd and OnRemove of a DontFragment component reach an instance that owns it

- **Where:**
  - `flecs_emit_propagate_id_for_range` (observable.c 310-376), whose ownership test at 324 is `owned = flecs_component_get_table(cr, table) != NULL`;
  - the Parent path's per-row walk (389-418), which reaches the same function.
- **Change:**
  - When `cr->flags & EcsIdDontFragment`, decide ownership per entity with `flecs_sparse_has(cr->sparse, entities[row])`.
  - Split the range into runs of owning and non-owning entities.
  - Skip the observers of the owning runs and do not propagate below them, as is done for an owning table today.
- **Why safe:**
  - For table and Sparse components the table test stays as it is.
  - The per-entity test is the one up traversal already uses for DontFragment ids (`flecs_query_sparse_self_up`, eval_sparse.c 387-490), so events and queries agree.

### F49: OnAdd and OnRemove name a base that is not the entity's source

- **Where:** for IsA, the propagation (`flecs_emit_propagate_id_for_range`, observable.c 310-376) and the forward (`flecs_emit_forward_id`, 613-706).
- **Change:**
  - Before invoking an observer for a table reached through `(IsA, b)`, find the table's primary source of the id.
  - The primary source is the first base in type order that provides the id, as `flecs_get_base_component` computes it (addons/prefab/instantiate.c 485-555), or `ecs_search_relation(world, table, 0, id, EcsIsA, EcsUp, &src, …)`.
  - Invoke and propagate further only when that source is the emitting base, or is reached through it.
  - In a diamond the second path then stops, and the inheritor gets one event.
- **Why safe:** it only removes events whose (entity, source) pair differs from what `ecs_get` and up queries report. The event the primary base sends is unchanged.

### F50: no forwarded OnAdd or OnRemove for an inherited DontFragment component

- **Where:** `flecs_reachable_cache_ensure` (observable.c 708-780), which lists the target's table type.
- **Change:**
  - When the target's record has `EcsEntityHasDontFragment`, add the DontFragment ids the target has.
  - To find them, walk `world->cr_non_fragmenting_head` and keep each record with `flecs_sparse_has(cr->sparse, tgt)`, filtered as the table ids are (for IsA, Inherit ids only, 736-738).
  - Invalidate the reachable cache when a DontFragment id is added to or removed from an entity that is the target of a traversable pair. These changes do not move the entity between tables, so nothing invalidates the cache today.
- **Why safe:**
  - Forwarding already handles ids without a column; it gates only OnSet on a column (685).
  - The added ids are exactly those that up traversal finds.

### F51: no OnSet for the inheritors of a variant that gains a base or loses an override

- **Where:**
  - (a) `flecs_emit_forward` (observable.c 799-888): the propagation down from the variant passes only the observers of the emitted event (`er`, 835-888), not `er_onset`.
  - (b) `flecs_emit_on_set_for_override_on_remove` (951-1002) emits OnSet for the variant's table only.
- **Change:**
  - (a) Pass `er_onset` to the propagation as well, gated on a column as the variant's own OnSet is (685).
  - (b) After the variant's OnSet, propagate it with `flecs_emit_propagate` to the variant's inheritors that do not own the component.
- **Why safe:**
  - The inheritors get exactly the event the variant gets, for the value both now read.
  - Owned components stop the propagation, as they already do for OnAdd and OnRemove.

### F52: a Parent-storage prefab child with an Inherit component that is Sparse or has an on_set hook aborts the instantiation

- **Where:** `flecs_instantiate_sparse` (addons/prefab/instantiate.c 73-133), called from `flecs_spawner_instantiate` with `emit_non_sparse = true` (tree_spawner.c 337-338).
- **Change:**
  - Skip ids whose record has `EcsIdOnInstantiateInherit`. This is the filter `flecs_prefab_spawner_build_type` already applies to the instance child's table (tree_spawner.c 27-31).
  - If an OnSet is wanted for these ids (round 6's F41 asks for one), emit it through `flecs_emit` with the prefab child as the source, not through a local column.
- **Why safe:**
  - The instance child does not own these ids; it reads them through `(IsA, c)`.
  - What aborts today is the copy into its sparse storage, or the hook call on its absent column. Nothing else reads those writes.

### F53: `ecs_iter_changed` and `ecs_iter_skip` abort in a multi-threaded system

- **Where:** `ecs_iter_changed` (query/cache/change_detection.c 680-705) and `ecs_iter_skip` (718-…). Both require `it->next == ecs_query_next`.
- **Change:**
  - Also accept `it->next == ecs_worker_next`, and work on `it->chain_it`: the stage's query iterator, which `ecs_worker_iter` stores (src/iter.c 1008-1034).
  - Read `chain_it->priv_.iter.query.elem` for the match.
  - Set EcsIterSkip on `chain_it`. `ecs_worker_next` copies its flags back (1053-1054).
- **Why safe:**
  - A worker's result is a row slice of the query iterator's current result, so the match and its monitor are the same.
  - Two workers skipping or reading the same match at once is the existing threading question of F33, not a new one; reading is race-free.

### F54: the run callback of a single-threaded system over a trivially cached query does not get a query iterator

- **Where:** `flecs_run_system` (addons/system/system.c 119-121), which sets `it->next = flecs_query_trivial_cached_next`.
- **Change:** keep `it->next = ecs_query_next`. `ecs_query_next` already dispatches to the trivial cache path for EcsIterTrivialCached (eval_iter.c 530-540).
- **Why safe:**
  - The results are the same; the cost is one flag test per `next`.
  - It restores the promise of system.h 55-66 that such a callback gets `ecs_query_next`, which `ecs_iter_skip` and `ecs_iter_changed` check.

### F55, F56 (and round 6's F46): stale order_by slices

- **Where:**
  - The slices are struct copies (`flecs_query_cache_build_sorted_table_range`, order_by.c 195-205), which the iterator reads (cache_iter.c 41-120).
  - The sort rebuilds them when `match_count != prev_match_count` (order_by.c 315).
  - But every monitor sync resets `prev_match_count` (change_detection.c 632).
- **Change, in two parts:**
  - Give the slices their own counter, `cache->slices_match_count`. It is set when the slices are built and compared with `match_count` in `flecs_query_cache_sort_tables`. `prev_match_count` stays for `ecs_query_changed`. This removes F56: the first iterator after a deletion rebuilds.
  - Make each slice record its table's id as well. In `flecs_query_cache_next`, check `ecs_map_get(&cache->tables, slice_table_id)` before touching `qm->base.table`. A slice whose table has left the cache is then skipped without reading the table, syncing a monitor or yielding. No dirty state is planted and nothing is written into a freed monitor. This removes F46's yield into reused memory, and both forms of F55 within the iteration.
- **Why safe:**
  - The table id is never reused for another table while the slices exist: ids come from the table store's sparse set, with generations. So the map lookup tells a removed table from a new table in the same memory.
  - The extra rebuild happens only after matches changed.

### F57: re-parenting a Parent-storage child delivers no OnRemove

- **Where:** `flecs_on_replace_parent` (storage/non_fragmenting_childof.c 113-197), and the OnSet re-emission in `flecs_emit` (observable.c 1160-1183).
- **Change:**
  - In the hook, when `old_parent != new_parent` and `old_parent` is alive:
    - emit the OnRemove of `(ChildOf, old_parent)` for the entity with `flecs_emit`, before the hierarchy is updated. Its forward then delivers the old parent's components as removed;
    - emit the OnAdd of `(ChildOf, new_parent)` after the update.
  - In observable.c, keep re-emitting the Parent component's OnAdd and OnRemove (a first set and a removal), and drop the translation of OnSet. This also fixes F62.
- **Why safe:**
  - It is the order the ChildOf storage uses: `flecs_actions_move_remove` emits the OnRemove of the replaced exclusive pair, then the OnAdd.
  - The observers run inside the hook's table lock. That is the same situation as any OnSet observer: changes to locked tables go through `it->stage` (Manual.md 334).

### F58: an instance at depth 6 or more keeps its children's spawn tables for good

- **Where:** `flecs_spawner_instantiate` (addons/prefab/tree_spawner.c 226-349).
  - `flecs_spawner_transpose_depth` (120-149) fills the temporary vector and keeps each table (148).
  - The vector is freed without a release (346-348).
- **Change:** release the temporary vector's tables before `ecs_vec_fini_t`, with the loop of `flecs_tree_spawner_release_tables` (prefab.c 9-18, made visible to tree_spawner.c). Equivalently, keep no tables for the temporary vector at all.
- **Why safe:**
  - The keep exists so that `ecs_delete_empty_tables` does not free a table a cached vector still points to.
  - The temporary vector is gone when the call returns, and the children just created keep the tables non-empty for as long as they exist.
  - Repeated deep instantiations (this round's `sd` cases) then leave the keep count unchanged.

### The new findings, briefly

- **F59:** in `flecs_query_select_or`, save the source and the field's up bit along with ids, trs and columns (eval.c 1454-1456).
  - Restore all five after the duplicate check, whether it finds a duplicate (before the `continue`, 1488-1490) or not (1492-1495).
  - Also reset the field's source and up bit when the chain moves to its next term (1499-1503), so a self term starts from a self state.
  - Safe: these are the values the term itself produced.
- **F60:**
  - Walk the trivial sparse search backward, like the VM's select, so that removing the current batch's ids is safe.
  - For removals elsewhere, a debug-build lock on the sparse set during iteration (like the table lock) could assert ECS_LOCKED_STORAGE, and the docs could say which removals are allowed.
- **F61:** while building the slices, record each group's first and last index in `table_slices`. `ecs_iter_set_group` on a query with order_by then iterates `table_slices` between those bounds instead of `group->tables`.
- **F62:** see F57.

## Round 8's list

### eval_sparse.c in a model

`SparseIter` models:
- the sparse set with swap-remove;
- the trivial sparse search's forward batches;
- the VM's backward select, with its range grouping and its `cur < count` assert;
- removals made by the loop, interleaved with the iteration.

Results:
- DontFragment select and with ops on entity ranges: the grouping produces ranges of adjacent rows in one table, and the next op sees exactly the grouped entities. No counterexample without removals.
- SparseNot after select_all: the C test's control (`Df, !Unused`) uses that plan. `flecs_query_sparse_with_id` with `not` walks the range and groups as the positive form does. No counterexample.
- The trivial sparse search under removals: F60.

### select_or with multi-op terms, and the fields restored after the duplicate check

`OrUp` models it: F59. Multi-op terms, read:
- The duplicate check saves, zeroes and restores the op context of the chain's first op only (eval.c 1461-1471).
  - The ops of later alternatives keep their contexts.
  - An up op reuses its `impl` (eval_up.c 132-138), which the iterator frees at fini, so nothing leaks.
- A DontFragment term inside an Or chain compiles to a sparse select that writes neither trs nor columns (eval_sparse.c 177-179), so it would carry the previous term's values. ComponentTraits.md lists `Or` among the operators DontFragment does "not yet" support, so this is not filed.

### Other users of prev_match_count and of stale slices

- `ecs_query_changed` reads `prev_match_count` through `flecs_query_check_cache_monitor` (change_detection.c 263-298).
  - A table matched during an iteration that the iterator did not reach still reports a change: its new match has no monitor, and creating one returns true (79-138).
  - A table unmatched during an iteration does not report one (REPORT-8, not filed).
- group_by with order_by:
  - the slices are built per group, and deleting a group leaves the same struct copies as F56 (read);
  - `ecs_iter_set_group` bypasses the slices: F61.

### The Parent storage's other re-emitted events

- OnSet for `(ChildOf, parent)` observers: a pair is a tag, so neither storage has OnSet observers of `(ChildOf, *)`. The Parent component's OnSet becomes an OnAdd of the pair, even when nothing changed: F62.
- A re-parent that changes depth: `flecs_on_replace_parent` adds the new `(ParentDepth, n)` through `it->stage` (non_fragmenting_childof.c 187).
  - Inside `ecs_set`, that stage's command queue is flushed at `flecs_commands_end` (entity.c 2028; commands.c 1577-1588), after `flecs_copy_id` has written the value and emitted OnSet.
  - The children's depths are queued the same way (component_index.c 1123-1128).
  - No stale pointer and no counterexample; read, not modelled.

### The spawner's temporary vector at depth

- Repeated instantiations at one depth ≥ 6 keep the table once per call. Theorem `spawn_depth_repeat`: three at depth 8 give a keep count of 3; three at depth 3 give 1. This is F58, seen again.
- A prefab child added after a deep instantiation:
  - the first instantiation at any depth builds `data[0]` (`flecs_prefab_spawner_build`, tree_spawner.c 199-223);
  - so a debug build asserts "cannot change children of prefab … after it has been instantiated" (`flecs_tree_spawner_assert_not_instantiated`, 166-197), as it does at depth 0;
  - a release build uses the stale `data[0]`, which is round 5's F39. Nothing new.

## Not counted as findings

- **F60's assert form.** The VM's select asserts "sparse iterator invalidated while iterating" (eval_sparse.c 145-146) when the set shrinks below its cursor. That is flecs's own guard; the search counts it apart.
- **DontFragment terms in Or chains** (above): documented as not supported yet.
- **The source change on re-parenting with Parent storage** (REPORT-8): unchanged. P-EV7 only checks unchanged parents.
- **A cached query with an up Or chain** keeps F59's state in its cache (match.c 122-160): read, not tested.

## What was replicated

- **OrUp:**
  - tables in creation order, ChildOf parents, the traversable flag;
  - the down cache: breadth first, with leaves, and with self skipping owners;
  - the field state of one Or field: ids, trs, columns, sources, the up flag;
  - self select and with, up select and with, self|up select and with, as listed in the code path;
  - `flecs_query_select_or`'s duplicate check (fall-through over the earlier terms) and its restore;
  - the debug columns check, and what `ecs_field` and `ecs_field_src` return.
- **SparseIter:**
  - the sparse set's dense order and swap-remove;
  - the trivial search's forward batches, with the count re-read;
  - the VM select's backward walk, range grouping and assert;
  - the loop's removals, from the current result and from other entities.
- **SortGroup:** the in-table sort, the per-group merge into slices, and `ecs_iter_set_group`.
- **EvHier:** the same-parent set, with both storages.
- **SpawnDepth:** repeated instantiations.

## What is not exact

- **OrUp:**
  - one field, and two components with columns;
  - ChildOf only (no IsA); no prefab or disabled tables; no ordered children;
  - a table's down cache is computed whole rather than cached across calls (`last_down_table` is not modelled);
  - table order is entity order, so the C tests create tables in the order the model assumes;
  - a debug abort ends the check of the rest of the iteration.
- **SparseIter:** batch sizes 1 and 2 stand for 1024; one DontFragment tag; no additions during iteration.
- **SortGroup:** values only; ties keep the earlier table, as the merge does; groups come in the order they first appear.
- **EvHier:** as in round 8.

## Assumptions

- **Builds:** debug with asserts on for every new test; the F59 tests also in `-DNDEBUG`.
- All new tests use `ecs_mini()`.
- `query_or_up_then_self_fields.c` and `query_or_self_then_up_fields.c` assume the table creation order their comments state: the Velocity tables, and the `(ChildOf, x)` tables, come in the order they were created.

## Properties

New:
1. **P-OR1** (Queries.md "Source", "Or Operator"; flecs.h `ecs_field_src`): broke (F59).
2. **P-OR2** (each entity once in an Or chain: the duplicate check's purpose, eval.c 1424-1426): holds in every program run.
3. **P-IT4** (flecs's own `DontFragment_add_to_self_while_iterate`; Systems.md "Immediate systems"; Queries.md "Iteration"): broke (F60).
4. **P-SO1** (Queries.md "Sorting"; flecs.h `ecs_iter_set_group`): broke (F61).
5. **P-EV7** (ObserversManual.md "OnAdd Events"): broke (F62).

Extended: P1, to Or chains (F59).

That makes 82 properties in all.

## Search runs

Counts per property: one program can count under several.

- **`ou exhaust 3 2`** (3 entities, 2 terms): complete, 147,456 programs, 2,290 failing.
  - crash: 1,542;
  - wrong source: 668;
  - wrong value: 366;
  - debug abort: 86.
- **`ou exhaust 3 3`**: complete, 884,736 programs, 21,056 failing.
  - crash: 13,808;
  - wrong source: 6,562;
  - wrong value: 3,202;
  - debug abort: 1,316;
  - P-OR2 holds in every program.
- **`ou lib`:** wrong source after 4,189 timelines; wrong value after 2,166; crash after 1,885; debug abort after 21,050.
- **`si9 exhaust 4 3`:** complete, 12,000 programs, 7,408 failing.
  - skipped: 7,184;
  - twice: 1,082;
  - flecs's "invalidated" assert: 992.
- **`si9 exhaust 5 4`:** complete, 248,832 programs, 173,344 failing.
  - skipped: 188,896;
  - twice: 30,986;
  - the assert: 25,632.
- **`si9 lib`:** skipped after 2 timelines; twice after 1,276.
- **`sg exhaust 3 2`:** complete, 98,304 programs, 25,668 failing.
- **`eh exhaust 3 4`:** complete, 1,679,616 programs, 104,132 failing (round 8: 66,608).
  - P-EV7 pair: 40,624; P-EV7 component: 1,512;
  - every earlier count unchanged.
- **`eh exhaust 3 5`:** complete, 30,233,088 programs, 2,854,252 failing (round 8: 1,848,016).
  - P-EV7 pair: 1,140,856; P-EV7 component: 59,456;
  - every earlier count unchanged.
- **`eh lib P-EV7`:** after 1,889,797 timelines.
- **`sd`:**
  - `exhaust 3`: complete, 729 programs, 513 failing, as in round 8;
  - the new cases: three instances at depth 8 fail; three at depth 3 hold.
- **Regressions:**
  - `cases`, `val`, `or`, `query`, `sp`, `sp six`, `idf`, `osi`, `sl`, `ev`, `si`, `or uncached`, `pipe phase-cases`, `s8 cases`, `ik cases` and `sl7 cases`: identical to round 8;
  - `or exhaust 3 3 3`: 3,780; `ev exhaust 3 4`: 44,566. Both as in round 8.

## Theorems

No `sorry`.
- `self_select_keeps_source_and_flag` (all programs): a self term's select never changes the field's source or up flag [propext, Quot.sound]
- `restore_keeps_source_and_flag` (all states): `select_or`'s restore keeps the source and flag the duplicate check left [no axioms]
- `orup_cases` (kernel): the four F59 forms and the controls [propext, Classical.choice, Quot.sound]
- `sparse_iter_cases` (kernel): F60's programs and controls [propext, Quot.sound]
- `sparse_remove_moves_last` (all arrays): a swap-remove puts the last id into the removed slot [propext, Classical.choice, Quot.sound]
- `sortgroup_cases` (kernel): F61's program and controls [propext]
- `same_parent_on_add` (all worlds): setting a Parent-storage child's parent to the one it has delivers OnAdd (ChildOf, parent) [propext, Classical.choice, Quot.sound]
- `evhier9_cases` (kernel): F62's program and its ChildOf control [propext, Classical.choice, Quot.sound]
- `spawn_depth_repeat` (kernel): keep counts after repeated instantiations [no axioms]
- Round 8's `parent_reparent_no_remove`, re-proved over the extended `step` [propext, Quot.sound]

## Library gaps

- Round 8's gaps remain.
- `while` loops in `Id.run do` blocks are not kernel-reducible, so `decide +kernel` gets stuck on them. The models use bounded `for` loops and structural recursion instead.
- `gshrink` loops when a candidate equals the program: an unchanged candidate still fails with the same signature. This round's first shrink candidates did that; they are now filtered to strictly smaller programs.

## For round 10

- Run the new C tests:
  - `query_or_up_then_self_fields.c`, `query_or_self_up_then_self_columns.c` and `query_or_self_then_up_fields.c`, in debug and `-DNDEBUG`;
  - `sparse_remove_while_iterating.c`;
  - `query_order_by_set_group_unsorted.c`;
  - `parent_set_same_parent_on_add.c`.
- F59 in cached queries: the cache's stored `_up_fields` and sources (match.c 122-160), with a custom traversable relationship (ChildOf chains use the tree ops).
- Or chains with IsA up terms, and with wildcard terms (variables written by the duplicate check).
- The trivial sparse search with two or more terms under removals from the non-lead sets: the lead set is chosen once (eval_sparse.c 528-546).
- `ecs_iter_set_group` with change detection, and group deletion with order_by.
