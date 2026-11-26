# Fixes for the flecs v4.2.0 findings

Proposed changes to flecs v4.2.0 for the findings in `REPROS.md` (F1–F47, from the Lean replica's reports `REPORT.md` to `REPORT-6.md`). Each patch is a `git diff` against the release's `src/` (and `include/` where a public header changes) and applies to a clean v4.2.0 with `git apply`.

Not patched here, as asked: F10 (open issue #2363), F15 (fixed by PR #2417, after v4.2.0) and F24 (open PR #2397).

## Summary

- **Fixed, one patch each:** F1 (also F2), F3, F4, F5, F6, F7, F8, F11, F12, F16, F17, F18 (also F19), F20, F21, F22, F23, F25 (also F27), F26, F27, F29 (also F34), F31, F32, F33, F36, F38, F39, F40, F41, F42, F43, F44, F45, F46, F47.
- **Patches shared by two findings:**
  - `F1.diff` fixes F1 and F2;
  - `F18.diff` fixes F18 and F19;
  - `F29.diff` fixes F29 and F34;
  - `F25.diff` contains `F27.diff`'s change. Apply one of them: `F25.diff` fixes both.
- **F47** is fixed in the code (the pipeline sorts before the workers start), not only in the documentation; its section says why.
- **No fix:** F9, F13, F14, F28, F30, F35 and F37 (see "Findings without a fix" at the end).

## Layout

- `fixes/F<n>.diff`: one patch per finding (or per shared change).
- `fixes/checks/*.c`: extra programs used to check a fix beyond the finding's own test (each section names its own).
- `fixes/attempts/*.diff`: changes that were tried and dropped, for F9 and F37.
- `tests/`: unchanged copies of `tests/flecs_lean` and its `README.txt`.
- `orig/flecs-4.2.0/`: the untouched release (read-only), from `https://github.com/SanderMertens/flecs/archive/refs/tags/v4.2.0.tar.gz` (sha256 `4107b0a36aa25f80ddcd6f939451ccfe1bacafcccdd2695840a4a8c413d05b40`).
- `work/F<n>/`: the edited `src/` and `include/` copies the patches were made from; `work/ALL/` is the combined tree of `fixes/all-fixes.diff`.
- `bin/`: the scripts named below. `bin/chk.sh` runs a program of `fixes/checks` against a build.
- `build/asan/` and `build/tsan/`: the AddressSanitizer build used for F46 and the ThreadSanitizer release builds used for F47 (`bin/asan-build.sh`, `bin/asan-run.sh`, `bin/tsan-build.sh`, `bin/tsan-run.sh`, `bin/tsan-pairs.py`).
- `build/verify/F<n>/summary.txt` and `build/verify/together/summary.txt`: the output of the final checks. `build/orig/suites/*.log` holds the baseline runs.

## How each patch was checked

Every patch was checked from its final `fixes/F<n>.diff` alone (`bin/verify-one.sh`):

1. `git apply --check` against a fresh copy of v4.2.0's `src/` and `include/`.
2. The same hunks applied to the amalgamation: `bin/apply2distr.py` finds each hunk's old text in `distr/flecs.c` (or `distr/flecs.h`), widening it with the source file's surrounding lines until it occurs once, and replaces it.
3. The finding's C tests, built against the patched amalgamation in two ways: linked with a patched `flecs.o`, and with the one-step command `cc -std=gnu99 -O1 -g -I distr <test>.c distr/flecs.c -lm -lpthread`. Both builds of every test exit 0.
4. The same tests built against the unpatched release still fail. The section of each finding gives the output.
5. flecs's own test suites, built against the patched amalgamation (see "flecs's suites").
6. For memory and thread findings, sanitizer builds of the same amalgamation: AddressSanitizer with `FLECS_USE_OS_ALLOC` (F46), ThreadSanitizer in a release build (F47).

The test programs are the ones in `tests/` (debug builds, asserts on, macOS arm64, Apple clang).

## flecs's suites

- **Suites run:** core, query, addons, collections and cpp (the C++ API). They are built from the release's `test/` sources and their generated `main.c` files, against the amalgamation compiled with `-O1 -g` (asserts on), and run with `-j 2`.
- **Test harness:** bake 3's standalone harness (`templates/test_harness/bake_test.c` from a local bake 3 checkout). The bake 2 runtime installed on this Mac lacks `test_param`, which v4.2.0's suites use.
- **Not run:** meta, script and cpp_addons. No patch touches the meta, script or C++ addon sources.
- **Baseline on unpatched v4.2.0:**
  - core 3870 pass / 0 fail;
  - query 4798 pass / 6 fail;
  - addons 643 / 0;
  - collections 97 / 0;
  - cpp 1919 / 0.
- **The 6 query failures:** `Sparse.ecs_field_on_sparse_self`, `Sparse.ecs_field_on_sparse_up` and `DontFragment.ecs_field_on_dont_fragment_up`, each with `cache_kind` default and auto. Each test calls `test_expect_abort()` and then reaches flecs's documented INVALID_OPERATION assert. This harness counts the abort as a failure. They fail identically on every build here.
- **"Unchanged" in a section** means the same pass and fail counts and the same failing tests as this baseline. The per-patch results are in `build/verify/F<n>/summary.txt`.

## Patches that touch the same code

Each patch applies alone to v4.2.0. Applied together:

- **F1 and F23** overlap in `flecs_cmd_batch_for_entity`: F1 inserts a check just before the batched `flecs_remove_invalid` call, and F23 changes that call. After F1, `git apply` refuses F23 because the hunk's context changed; `patch -p1` applies it correctly.
- **F3 and F23:** F23 adds a `cmd` parameter to `flecs_remove_invalid`, and F3 adds a new call to it. With both applied, F3's call becomes `flecs_remove_invalid(world, cmd, id, &valid_id)`.
- **F25 contains F27.** Apply one or the other, not both.
- **F16 and F15:** apply F16 with F15's upstream fix (PR #2417). A system whose own `[out]` annotation overlaps its own later read only through wildcards now reaches F15's assert, as the exact-id form already does on v4.2.0.
- **New iterator flag bits:** F20 adds bit 23 (`EcsIterPropagated`), and F25/F27 add bit 24 (`EcsIterNoChangeDetection`). They do not collide.
- **F41, F42 and F43** all edit `src/observable.c`. F41 and F42 both add `flecs_emit_invoke_not_owned`, and F41 and F43 both add `flecs_emit_isa_source` (the same text in each patch). Applied together, the file keeps one copy of each; the other hunks don't overlap. Together, an OnSet through IsA follows the entity's source (F43) for every storage, and per-entity ownership of DontFragment components (F42) applies to the propagation that F43 leaves in place.
- **F45 and F38:** F45 makes `flecs_instantiate_override_dont_fragment` non-static with its v4.2.0 signature and calls it from `flecs_spawner_instantiate`. F38 adds a `depth` parameter to it and makes it walk the base's IsA targets. Together, the declaration in `prefab.h` has the `depth` parameter, and the spawner calls it with 0 when the prefab child's table has `EcsTableOverrideDontFragment` or `EcsTableHasIsA` (F38's condition in `flecs_instantiate`).
- **F44, F45 and F39** edit `flecs_spawner_instantiate`: F44 adds a parameter next to F39's first hunk and a pass after the spawn loop, F45 a call inside it. `patch -p1` applies them in numeric order.
- **F46 and F36** both change `ecs_iter_changed`. Together, F36's `flecs_query_cache_iter_elem` returns NULL for a slice that F46 cleared, and F46's own change to `ecs_iter_changed` is left out; F46's guard in `flecs_query_change_detection` stays. F46 and F40 change different parts of `flecs_query_cache_next`.
- **F47** edits `flecs_query_cache_iter_init`, `order_by.c` and `cache.h` next to F46's and F40's hunks, without overlap. F47 removes the sorting races of a multithreaded order_by system and F33 its monitor races; the ThreadSanitizer reports left with every patch are under "Everything together".
- **All others** apply together in numeric order. F11, F12 and F22 edit different parts of the batch code in `commands.c`.

`fixes/all-fixes.diff` is every patch applied together (F27 through F25, F23 adjusted, and F41–F43, F45 with F38 and F46 with F36 merged, as above). The build from it was checked like the single patches; the results are under "Everything together".

## Everything together

`fixes/all-fixes.diff` was built and checked as one patch (`bin/verify-combo.sh`), with every test in `tests/`:

- **The finding tests of the fixed findings:** all 50 exit 0 (the 42 of rounds 1–5 and the 8 of round 6). Two of them also pass on v4.2.0: `batch_remove_dead_target_panic.c` (F2's first form) and `change_detection_fixed_source_added.c` (F19).
- **The tests that are still red:**
  - the no-fix findings: `staged_set_value_lost.c` and `staged_set_after_remove_all.c` (F9), `generation_wraps.c` (F13), `on_add_hook_view.c` (F14), `instantiate_child_outside_range.c` (F28), `query_iter_skips_table.c` (F30), `query_cascade_table_twice.c` and `query_cascade_group_freed.c` (F35), `pipeline_phase_reorder_skips.c` (F37);
  - the findings left to upstream: `batch_childof_replaced_onadd.c` (F10), `pipeline_write_read_same_system.c` (F15), and the four `override_cache_*.c` tests (F24).
- **F10's test:** the F12 patch fixes its add-then-clear half. The other half, a ChildOf pair replaced within one batch, still fails.
- **Suites:** core 3870 / 0, query 4798 / 6 (the baseline's 6), addons 643 / 0, collections 97 / 0, cpp 1919 / 0: unchanged.
- **Warnings:** the amalgamation compiles without warnings with all patches.
- **Round 6's extra checks** (`fixes/checks/F41_*.c` to `F47_*.c`) all pass on the combined build. The earlier checks give the results their sections describe (F5's check stops at the documented INVALID_OPERATION; F20's Parent `self|up` variant still fails).
- **ThreadSanitizer, all patches** (release build, `workers_order_by_sort_race.c`, 3 runs): "two threads sorting at once: 0; table intact: 1" and 4 race reports in each run, none in sorting, slices or monitors (F47 removes those, F33 the monitor syncs). The 4 left are statistics counters that every worker increments without atomics (`q->eval_count` in `flecs_query_iter`, `world->info.queries_ran_total` and `systems_ran_total`) and the worker loop's read of `world->flags` against `ecs_frame_begin`. No patch here changes them.

## Findings

One section per finding, in order. The line numbers are those of v4.2.0's `src/` unless a path says otherwise. F10, F15 and F24 are left to their upstream issue and PRs.

### F1. A batched remove of a pair whose target died earlier in the merge deletes the entity

- **Change:** in `flecs_cmd_batch_for_entity`, a batched `EcsCmdRemove` of a pair whose target is no longer valid is skipped before `flecs_remove_invalid` applies the relationship's `OnDeleteTarget` policy (Delete or Panic). Patch: `fixes/F1.diff`, shared with F2.
- **Root cause:** `flecs_cmd_batch_for_entity` (src/commands.c 1001-1044) calls `flecs_remove_invalid` (893-942) for every batched command with an id, removes included. For a dead target under a Delete policy it returns false (913-916) and the batch deletes the entity (1038-1043); under Panic it panics (917-920). The policy is meant for commands that would *add* a pair to a deleted target. A remove of a pair the entity cannot have (its target's cleanup already ran) is a no-op, which is what a lone remove does (`flecs_remove_id_now`, 1416-1419).
- **Test:** `batch_remove_dead_target.c`: red on v4.2.0 (rc=1, `FAIL: entity deleted by remove of (ChildOf, deleted parent) it never had`), green with the patch (rc=0).
- **Suites:** core, query, addons, collections and cpp with this patch: unchanged from v4.2.0 (core 3870 / 0, query 4798 / 6, addons 643 / 0, collections 97 / 0, cpp 1919 / 0; see "flecs's suites").
- **Risk:** low. Only removes are affected, and only when the pair's relationship is alive and its target is not. Adds, sets and ensures of such a pair keep the documented Delete/Panic/Remove behavior. `flecs_remove_invalid` itself is unchanged.

### F2. The same with a Panic relationship: the merge panics

- **Change:** the F1 change: a batched remove of a pair whose target is gone is skipped before the `(OnDeleteTarget, Panic)` policy is read, so it can no longer panic. Patch: `fixes/F1.diff` (one patch for F1 and F2).
- **Root cause:** the same call, `flecs_remove_invalid` from `flecs_cmd_batch_for_entity` (src/commands.c 1031), reaches `flecs_throw_invalid_delete` (917-920, then on_delete.c 770-784) when the `(Rel, *)` record exists and the policy is Panic. Panic is documented for deleting a target that is in use; here nobody held `(Rel, tgt)`, and the queued call is a remove.
- **Test:** `batch_remove_dead_target_panic_record.c`: red on v4.2.0 (aborts, `fatal: flecs.c: 18164: abort(): (OnDelete, Panic) constraint violated while deleting entities with (#385,#387) (CONSTRAINT_VIOLATED)`), green with the patch (rc=0). Round 1's `batch_remove_dead_target_panic.c` (no `(Rel, *)` record) stays green.
- **Suites:** core, query, addons, collections and cpp with this patch (`F1.diff`, the same patch): unchanged from v4.2.0 (core 3870 / 0, query 4798 / 6, addons 643 / 0, collections 97 / 0, cpp 1919 / 0; see "flecs's suites").
- **Risk:** as F1. A queued *add* of a Panic pair whose target died before the merge still panics (REPORT.md calls that case arguable); the patch does not touch it.

### F3. A queued set of a pair whose target is deleted before the merge aborts the merge

- **Change:** the unbatched merge path checks a queued set, ensure, emplace or add-modified of a pair with `flecs_remove_invalid`, as it already does for a queued add: a pair whose relationship or target died before the merge is discarded, or deletes the entity when the relationship's `OnDeleteTarget` policy is Delete. Patch: `fixes/F3.diff` (src/commands.c).
- **Root cause:** in `flecs_commands_flush`, `EcsCmdAdd` goes through `flecs_remove_invalid` (src/commands.c 1404-1414), but `EcsCmdSet`/`EcsCmdEnsure`/`EcsCmdEmplace` (1428-1451) and `EcsCmdAddModified` (1460-1464) call `flecs_set_id_move`/`flecs_add_id` directly. Those reach `flecs_ensure` (entity.c 507-578) → `flecs_add_id_w_record` → `flecs_table_traverse_add` → `ecs_make_alive_id`, which asserts "second element of pair is not alive" (entity.c 2828-2829). When the same command is batched, `flecs_cmd_batch_for_entity` already drops it (commands.c 1031-1036), so the outcome depended on whether the entity had one queued command or several.
- **Test:** `staged_set_pair_dead_target.c` and `staged_set_pair_existing_dead_target.c`: both red on v4.2.0 (abort, `fatal: flecs.c: 11175: assert(!ecs_exists(world, t)): second element of pair is not alive (INVALID_PARAMETER)`), both green with the patch (rc=0: e alive, without the pair).
- **Suites:** core, query, addons, collections and cpp with this patch: unchanged from v4.2.0 (core 3870 / 0, query 4798 / 6, addons 643 / 0, collections 97 / 0, cpp 1919 / 0; see "flecs's suites").
- **Risk:** low. Only queued value commands for pairs take the new check (one or two entity-index lookups each); components that are not pairs keep the old path. With a Delete policy on the relationship, the entity is now deleted at the merge, as a batched set or a queued add already did. F1's patch edits another hunk of the same file; the two apply together.

### F4. Batched commands plus an observer that deletes its entity through it->stage: internal assert

- **Change:** after the batch's commit and the flush of the commands its observers queued, `flecs_cmd_batch_for_entity` stops when the entity is gone (`r->table == NULL`), as it already does after an `on_replace` hook (src/commands.c 1206-1209). Patch: `fixes/F4.diff` (src/commands.c, 6 lines).
- **Root cause:** the batch commits inside `flecs_commands_begin`/`end` (src/commands.c 1156-1158). The end flushes the observer's queued `ecs_delete`, which empties the entity's record. The batch then keeps using `r`: in the set-copy loop through `flecs_get_mut` (1191; asserts at entity.c 601 for a trivial component, at flecs.c 8947 `table != NULL` in the extra variant) and at `ecs_assert(r->table != NULL)` (1277). A release build dereferences the NULL table (1285).
- **Test:** `batch_observer_deletes_entity.c`: red on v4.2.0 (abort, `fatal: flecs.c: 6924: assert(r->table != NULL) (INTERNAL_ERROR)`), green with the patch (rc=0: the entity is deleted, as the observer asked). A variant whose second command is an `ecs_set` instead of an add (`fixes/checks/F4_batch_observer_deletes_entity_set.c`) aborts on v4.2.0 in the set-copy loop and passes with the patch.
- **Suites:** core, query, addons, collections and cpp with this patch: unchanged from v4.2.0 (core 3870 / 0, query 4798 / 6, addons 643 / 0, collections 97 / 0, cpp 1919 / 0; see "flecs's suites").
- **Risk:** low. The new path only runs when the entity is already deleted. Its queued set values stay on their commands, and the flush loop discards them because the entity is not alive (src/commands.c 1374-1378), which frees them.

### F5. ecs_set/ecs_ensure abort when an OnAdd observer deletes the entity through it->stage

- **Change:** `flecs_ensure` returns a NULL pointer instead of asserting when the commands it flushes after adding the component have deleted the entity; `ecs_set_id` then ends quietly, the merge's `flecs_set_id_move` destructs the queued value and returns, `ecs_ensure_id` reports its existing INVALID_OPERATION error ("was removed during the operation, make sure not to remove the component in hooks/observers"), and `ecs_cpp_set` checks the pointer before using it. Patch: `fixes/F5.diff` (src/entity.c, src/addons/flecs_cpp.c).
- **Root cause:** `flecs_ensure` (src/entity.c 563-577) adds the component, flushes the commands that the OnAdd observers queued (565-566) so that the pointer it returns is stable, and then asserts `r->table != NULL` (575, INTERNAL_ERROR). An observer that deletes the entity through `it->stage`, which the docs allow, empties the record in that flush. `ecs_add` on the same entity works; `ecs_set` and a queued `ecs_set` merged alone abort. Batched, the same set survives because OnAdd runs after the copy (commands.c 1279-1288).
- **Test:** `set_observer_deletes_entity.c` and `staged_set_observer_deletes_entity.c`: both red on v4.2.0 (abort, `fatal: flecs.c: 8921: assert(r->table != NULL) (INTERNAL_ERROR)`), both green with the patch (rc=0: the entity is deleted, as the observer asked). An `ecs_ensure` variant (`fixes/checks/F5_ensure_observer_deletes_entity.c`) now stops at the documented error of `ecs_ensure_id` (`component 'Position' ensured on entity '#386' was removed during the operation ... (INVALID_OPERATION)`) instead of the internal assert: `ecs_ensure` has no pointer to return for a deleted entity.
- **Suites:** core, query, addons, collections and cpp with this patch: unchanged from v4.2.0 (core 3870 / 0, query 4798 / 6, addons 643 / 0, collections 97 / 0, cpp 1919 / 0; see "flecs's suites"). The cpp suite covers `ecs_cpp_set`.
- **Risk:** low. The new branches run only when the entity is gone after the flush. `ecs_set` on an entity that an OnAdd observer deletes now returns without setting anything, like `ecs_add`. In the C++ API (`ecs_cpp_set`), the case remains an error, now INVALID_OPERATION with a message instead of the internal assert; supporting it there would need the C++ `write_component` to handle a NULL pointer.

### F6. An on_set hook that moves its entity makes OnSet observers run for another entity

- **Change:** after invoking the `on_set` hook, `flecs_notify_on_set_w_cr` looks the entity up again and emits OnSet with its current table, row and component pointer; it emits nothing when the hook deleted the entity or removed the component. Patch: `fixes/F6.diff` (src/component_actions.c).
- **Root cause:** `flecs_notify_on_set_w_cr` (src/component_actions.c 641-702) captures `table` and `row` before calling the hook (685) and emits OnSet with them afterwards (690-700). Tables are not locked for `on_set` hooks (flecs's own `ComponentLifecycle_locked_storage_on_set` adds a tag from one), so a hook that adds or removes something on its entity moves it, and the table's last entity is swapped into the old row. The observer then receives that other entity and its value, or, when the entity was alone, a row past the table's count.
- **Test:** `on_set_hook_moves_entity.c`: red on v4.2.0 (rc=1, `FAIL: OnSet observer got entity 388 (f=388), expected e=387` and `FAIL: OnSet observer saw x=2.000000, expected 99`), green with the patch (rc=0).
- **Suites:** core, query, addons, collections and cpp with this patch: unchanged from v4.2.0 (core 3870 / 0, query 4798 / 6, addons 643 / 0, collections 97 / 0, cpp 1919 / 0; see "flecs's suites").
- **Risk:** low. When the hook leaves the entity where it was, the only cost is one entity-index lookup per `on_set` hook call. `emit_on_set` (DontFragment, up-notify) is now computed from the table the entity is in after the hook. When an `on_set` hook deletes its entity or removes the component, OnSet observers are no longer invoked for it; before, they ran on whatever entity occupied the row.

### F7. Panic isn't enforced when another pair to the same target follows it in the type, or any pair has Delete

- **Change:** `flecs_get_delete_action` gives Panic precedence over Delete and Remove across all of a table's pairs to the deleted target, and Delete precedence over Remove, instead of keeping the last pair's policy. Patch: `fixes/F7.diff` (src/on_delete.c).
- **Root cause:** `flecs_get_delete_action` (src/on_delete.c 111-152) loops over the table's pairs with the target, overwrites `result` with each pair's `OnDeleteTarget` policy (129) and stops at the first Delete (130-133). A Panic pair is enforced only if no pair has Delete and the Panic pair is the last in type order. A pair whose relationship has a larger id, such as one created after the Panic relationship, therefore hides the Panic, and a ChildOf pair to the same target (Delete) deletes the entity instead of panicking.
- **Test:** `panic_target_order.c`: red on v4.2.0 (rc=1, `FAIL: deleting the target of a Panic relationship did not panic (e alive: 1, has (RPanic, t): 0)`), green with the patch (it panics; the test's abort handler exits 0). `panic_target_with_childof.c`: red on v4.2.0 (rc=1, `... did not panic (e alive: 0)`), green with the patch.
- **Suites:** core, query, addons, collections and cpp with this patch: unchanged from v4.2.0 (core 3870 / 0, query 4798 / 6, addons 643 / 0, collections 97 / 0, cpp 1919 / 0; see "flecs's suites"). The core suite includes OnDelete.
- **Risk:** low to medium. Programs that deleted the target of a Panic pair and relied on a later pair or a ChildOf pair to the same target to hide it now panic, as ComponentTraits.md "OnDeleteTarget" documents. Tables with only Remove and Delete pairs get the same action as before.

### F8. Entity ranges: make_alive of an id recycled while its range was inactive

- **Change:** when an id outside the active range is made alive, `flecs_entity_ranges_on_ensure` also removes it from its range's recycled list. Patch: `fixes/F8.diff`.
- **Root cause:** `flecs_entity_ranges_on_delete` (src/addons/entity_ranges.c 55-83) moves an id deleted while another range is active out of the dense array and into its own range's `recycled` vector (79-81). `ecs_make_alive` / `flecs_entity_index_ensure` (src/storage/entity_index.c 139-186) then makes that id alive again, and `flecs_entity_ranges_on_ensure` (src/addons/entity_ranges.c 39-53) only advances the range's `cur`: the now-alive id stays in `recycled`. Activating the range loads it as a not-alive slot over an entity that sits in a table (entity_ranges.c 129 asserts), and `ecs_new_from_range` hands it out again (entity_ranges.c 249-252, then entity.c 2796 asserts).
- **Test:**
  - `range_make_alive_recycled.c`: v4.2.0 aborts, `assert(r->table == NULL)` at flecs.c 24178 (entity_ranges.c 129), rc=134; patched rc=0 (e stays alive, the next id in b is new).
  - `range_new_from_range_duplicate.c`: v4.2.0 aborts, `assert(r->table == NULL)` at flecs.c 9007, rc=134; patched rc=0 (a new id, not the alive one).
- **Suites:** core, query, addons, collections and cpp with this patch: unchanged from v4.2.0 (core 3870 / 0, query 4798 / 6, addons 643 / 0, collections 97 / 0, cpp 1919 / 0; see "flecs's suites"). core's Entity, New_w_Count, Pairs and World suites and addons' Memory suite use ranges.
- **Risk:** low. The extra scan runs only when an id outside the active range gets a new dense slot (make_alive, instantiation's child ids, ensure); it is linear in that range's recycled list, which is only filled by deletes made while another range is active.

### F9. A queued set is written in place, and is lost if the component goes away before the merge

- **No fix.** Writing a queued set of a component the entity already has straight into its storage is flecs's intended behavior, and its own tests assert it, so a fix is a design decision; the small fix breaks ten of flecs's tests, and keeping the behavior while fixing the loss touches too much.
- **Root cause:** `flecs_defer_set_impl` (src/commands.c 629-712) looks up the entity's existing storage (`flecs_defer_get_existing`, 642-644). When the entity has the component and the world has one stage, it copies the value there at once and queues only an add (`EcsCmdAdd`, 663-679, for components without hooks or observers) or an add-modified (`EcsCmdAddModified`, 694-707). With two or more stages the same call queues the value (651-654). `flecs_defer_skip_removed` (379-406) only sees removes and clears queued for that entity, not a removal on the world, nor a queued `remove_all`/`delete_with`. When the component is removed before the merge, the queued add re-adds it default-constructed, and the set's value is gone. Manual.md "Deferred operations" says "The queued changes become visible when the stage is merged".
- **Tried:** always queueing the value (dropping the `world->stage_count != 1` condition at 651, the multi-stage behavior; `fixes/attempts/F9-always-queue-set.diff`). Both tests went green (`staged_set_value_lost.c`, `staged_set_after_remove_all.c`), but 10 of flecs's own tests failed: core `Commands.defer_set` ("set will not be deferred if the component exists": `ecs_get` on the stage must see the new value before the merge), `Commands.exists_set_w_ensure`, `Commands.defer_remove_two_set_other_get_before_merge`, four `Commands.on_replace_w_set_*existing*` tests (which count `on_replace` calls at the set, not at the merge), `SingleThreadStaging.clear_stage_after_merge`, and addons `Run.run_staging` and `Run.run_with_stage`.
- **What a fix would need:** either (a) flecs decides that queued sets are queued and updates those tests, which makes the single-stage case behave like the multi-stage one; or (b) the in-place write stays and the command also carries a copy of the value, applied at the merge only when the queued add actually re-adds the component (a new command state, handled in both the batched path, `flecs_cmd_batch_for_entity`, and the unbatched one, with the copy's destruction). Or (c) the docs say that on a single stage `ecs_set` writes in place when the entity has the component and that removing the component before the merge loses the value.
- **Tests:** `staged_set_value_lost.c` (rc=1, `FAIL: e has Position {-1.000000, -1.000000} after the merge, expected {1, 1}`) and `staged_set_after_remove_all.c` (rc=1, `FAIL: e has Position {-1.000000, -1.000000}, expected {2, 2}`) stay red.

### F11. Under batching, OnSet observers and on_set hooks see later values

- **Change:** two parts, one patch. (1) In a batch, only the first queued set or ensure of an id is copied into the component before the OnSet events; later sets of the same id stay queued and run in queue order, each copying its own value and emitting its own OnSet. (2) `ecs_ensure` on a stage, after a queued `ecs_set` of the same component, no longer returns the set command's storage: it queues an ensure whose value starts as a copy of the set's value. Patch: `fixes/F11.diff` (src/commands.c).
- **Root cause:** (1) `flecs_cmd_batch_for_entity` copies every Set/Ensure value of the entity into the component (src/commands.c 1179-1241) before any of the OnSet events, which run afterwards as `EcsCmdModified` commands at each set's place in the queue. With two sets of the same id, both OnSet calls see the last value, and so does the `on_set` hook. (2) `flecs_defer_ensure` returns `flecs_defer_find_cmd_value` (489-545, used at 567-574), which is a queued set's own value; writing through the ensure pointer rewrites what the set's OnSet will see. ObserversManual.md "OnSet order is maintained" promises code that is "agnostic to whether operations are deferred or executed immediately".
- **Test:** `batch_onset_values.c`: red on v4.2.0 (rc=1, `FAIL: OnSet calls for e saw x = 3.000000 then 3.000000, expected 1 then 3`), green with the patch (rc=0). `staged_ensure_rewrites_set.c`: red on v4.2.0 (rc=1, `FAIL: OnSet for set({99, 99}) saw x = 1.000000`), green with the patch (rc=0: OnSet sees 99, the final value is the ensure's 1).
- **Suites:** core, query, addons, collections and cpp with this patch: unchanged from v4.2.0 (core 3870 / 0, query 4798 / 6, addons 643 / 0, collections 97 / 0, cpp 1919 / 0; see "flecs's suites"). The core suite includes Commands.
- **Risk:** low to medium. A batch with one set per id behaves as before. With several sets of one id, the later ones are applied one by one (one more table lookup and OnSet each), and observers see every value in order. An ensure after a queued set allocates its own command value and copies the set's value into it (a copy constructor call); for a component with an `on_replace` hook, the merge then calls `on_replace` for the set and again for the ensure. An ensure after an ensure or emplace still returns the same storage. Multi-component OnSet observers still see a valid value for every component, because the first set of each id is still copied before any OnSet.

### F12. Batching runs an entity's later commands before other entities' earlier ones; a child survives its parent's deletion

- **Change:** the batch of an entity's commands is split before a remove or a clear that undoes a pair the same batch added, when that pair's relationship has `(OnDeleteTarget, Delete)` or `(OnDeleteTarget, Panic)`. The add is then applied at its own place in the queue, so the other entities' commands queued in between (such as deleting the parent) see the entity with the pair. Patch: `fixes/F12.diff` (src/commands.c: a helper and a check in the batch loop that use its existing `split` mechanism).
- **Root cause:** `flecs_commands_flush` runs all of an entity's queued commands as one batch at the position of its first command (src/commands.c 1351-1369, `flecs_cmd_batch_for_entity` 968-1134). In `[add (ChildOf, p) to c; delete p; remove (ChildOf, p) from c]`, c's add and remove cancel before p's delete runs, so c is not p's child when p is deleted and survives; in queue order c is deleted with p and the remove is discarded. ObserversManual.md allows batching to reorder events between entities, not to change which entities survive.
- **Test:** `batch_child_survives_parent_delete.c`: red on v4.2.0 (rc=1, `FAIL: child survived the deletion of its parent`), green with the patch (rc=0). The clear form from REPORT.md (`ecs_clear(stage, c)` instead of the remove, `fixes/checks/F12_batch_child_survives_parent_delete_clear.c`) is red on v4.2.0 and green with the patch too.
- **Suites:** core, query, addons, collections and cpp with this patch: unchanged from v4.2.0 (core 3870 / 0, query 4798 / 6, addons 643 / 0, collections 97 / 0, cpp 1919 / 0; see "flecs's suites"). The core suite includes Commands, Hierarchies and OnDelete.
- **Risk:** low. Only batches that add and then remove or clear a Delete or Panic pair (typically ChildOf) are split, which costs one more table move for that entity and emits the pair's OnAdd and OnRemove instead of nothing. Other batches are unchanged. A side effect on F10 (issue #2363): its add-then-clear case no longer emits an OnAdd for a ChildOf pair without the matching OnRemove, since the add now really happens; F10's other case, a ChildOf pair replaced in one batch, is unchanged. Not covered: the other reordering REPORT.md names, a queued `ecs_modified` that sees a component a later queued `ecs_add` of the same entity adds (one extra OnSet); that is an event difference, not a different set of surviving entities, and fixing it would mean not batching adds after a modified.

### F13. The generation wraps after 2^16 recycles

**No fix.** The wrap is the id layout, not a slip in the code. An entity id keeps its index in the low 32 bits and its generation in bits 32-47: `ECS_GENERATION_MASK` is `0xFFFF << 32` and `ECS_GENERATION_INC` adds 1 modulo 2^16 (include/flecs/private/api_defines.h 333-335). The top bits hold the id flags (`ECS_ID_FLAGS_MASK`, 331), and pairs put the relationship in the whole upper half, which is why the generation is stripped from pair elements. After 65,536 recycles of one index the generation comes back to the deleted handle's, and `ecs_is_alive` cannot tell them apart (src/storage/entity_index.c 125-137 compares the full 64-bit value).

- Any finite generation field wraps; widening it (e.g. into bits 48-59) changes the public id layout (`ECS_GENERATION`, `ecs_strip_generation`, serialized ids in JSON/REST, `ecs_set_version` users) and only moves the wrap further out. That is a design decision for flecs, not a small patch.
- What needs changing is the documentation: EntitiesComponents.md "Deletion" / "Liveliness Checking" (around line 97) should say that the version is 16 bits, so a stale handle can test alive again once its id has been recycled 65,536 times, and that applications holding handles for that long should not rely on `is_alive` alone.
- Test `generation_wraps.c` stays red with any patch that keeps the layout (v4.2.0: `FAIL: deleted handle 385 reports alive (current 385)`, rc=1).

### F14. Inside an on_add hook the entity doesn't have the component yet (lower confidence)

- **No fix.** Whether an `on_add` hook may query its own entity is a design question the docs do not answer in words, and making it true touches the core move path.
- **Root cause:** `flecs_move_entity` (src/entity.c 150-207) calls `flecs_table_move` (188-189) and repoints the entity's record only afterwards (190-191). `flecs_table_move` (src/storage/table.c 1817-1921) runs the constructor and the `on_add` hook of each added column inside its column loop (`flecs_table_invoke_add_hooks`, 1009-1033, called at 1890 and 1904), while the record still points at the source table, so `ecs_has` is false and `ecs_get` returns NULL inside the hook. The only statement is the lifecycle diagram (EntitiesComponents.md, `img/component-lifecycle.svg`: "table move → ctor → on_add hook"), which can be read either way; for removes the same diagram puts the `on_remove` hook before the table move, and the code matches it.
- **What a fix would need:** `flecs_table_move` would have to move every column first and run the `on_add` hooks in a second pass, after `flecs_move_entity` has repointed the record. Repointing the record before the move is not enough: an `on_add` hook for one column would then see the next columns before their values are moved, and `on_remove` hooks, which run in the same loop, would no longer see the removed component. Hooks also run from `flecs_table_append` and other paths that create rows, which would need the same treatment. Alternatively, the hooks section of EntitiesComponents.md could state that an `on_add` hook must use its iterator's fields, not lookups on the entity.
- **Test:** `on_add_hook_view.c` stays red (rc=1, `FAIL: ecs_has false inside on_add hook`, `FAIL: ecs_get NULL inside on_add hook`).

### F16. No sync point between a wildcard or Any write annotation and an overlapping read

- **Change:** the pipeline's write-state check compares a read with the recorded writes by overlap (an id exists that matches both, with Wildcard or Any on either side and in either pair element) instead of `ecs_id_match`, which only knows Wildcard and only on the pattern side. Patch: `fixes/F16.diff`.
- **Root cause:** `flecs_pipeline_get_write_state` (src/addons/pipeline/pipeline.c 61-105) tests `ecs_id_match(written, read)` (line 89) and `ecs_id_match(read, written_wildcard)` (line 98). `ecs_id_match` (src/id.c 12-84) treats `EcsWildcard` as a wildcard only in its second argument and never `EcsAny`, so `(Likes, *)` vs `(*, Bob)` and `(Likes, Bob)` vs `(Likes, _)` are judged disjoint and no merge is inserted before the reader.
- **Test:** `pipeline_wildcard_sync_point.c`: v4.2.0 rc=1, "FAIL (variant a): reader saw 1 entities in the first frame, expected 2" and the same for variant b; patched rc=0.
- **Suites:** core, query, addons, collections and cpp with this patch: unchanged from v4.2.0 (core 3870 / 0, query 4798 / 6, addons 643 / 0, collections 97 / 0, cpp 1919 / 0; see "flecs's suites").
- **Risk:** pipelines with such annotations get the sync points the docs promise, so frames can have more merges. A system whose own `[out]` annotation overlaps its own later read only through wildcards (`[out] (Likes, *)()`, `[in] (*, Bob)()`) now reaches F15's assert (`needs_merge == false`, pipeline.c 354), exactly as the exact-id form (`[out] (Likes, *)()`, `[in] (Likes, Bob)()`) already does on v4.2.0 (checked with a small program on both builds). Apply together with F15's upstream fix (PR #2417).

### F17. A system that disables itself makes the pipeline skip the next systems in that frame

- **Change:** when the schedule is rebuilt during a frame, the resume position starts at the beginning of the new schedule, so that when no system in the new schedule has run yet the frame resumes at its first system instead of at the stale position of the old schedule. Patch: `fixes/F17.diff` (6 lines).
- **Root cause:** `flecs_pipeline_build` (src/addons/pipeline/pipeline.c 450-458) sets `pq->cur_op`/`pq->cur_i` only at the last system in the new schedule whose `last_frame` is the current frame. When the system that ran left the schedule and no other system has run (the self-disabling system was the first of the frame), the old values remain: op 0 and the index of the system that ran. `flecs_pipeline_next_system` (475-489) then steps past the new op 0, which now holds the next system. In the three-system program the stale `cur_op` points past the shorter schedule and trips the assert at 467-470.
- **Test:**
  - `pipeline_disabled_system_skips_next.c`: v4.2.0 rc=1, "after one frame Init ran 1 times, Update ran 0 times"; patched rc=0.
  - `pipeline_disabled_system_skips_next_init.c`: v4.2.0 rc=1, same message; patched rc=0.
  - `pipeline_disabled_systems_assert.c`: v4.2.0 rc=1, `assert((pq->cur_op <= ecs_vec_last_t(...)))` (INTERNAL_ERROR) caught by the test's abort handler; patched rc=0 (A, B, C each ran once).
- **Suites:** core, query, addons, collections and cpp with this patch: unchanged from v4.2.0 (core 3870 / 0, query 4798 / 6, addons 643 / 0, collections 97 / 0, cpp 1919 / 0; see "flecs's suites"). The addons suite includes Pipeline, SystemMisc and MultiThread.
- **Risk:** only the case where no system of the new schedule has run in this frame changes: those systems now run in that frame. When some system of the new schedule has run, the position is the same as on v4.2.0. It does not fix F37 (reordering): see F37.

### F18. Change detection misses a write to a source entity that moved to another table

- **Change:** the change monitors of fields whose component is stored on another entity (a fixed source, or a source reached by up traversal) also store the id of the table the source was in, and a different table counts as a change. Patch: `fixes/F18.diff` (shared with F19: one change to the same monitor).
- **Root cause:** a table gets a dirty state only when a monitor first reads it, with every counter set to 1 (`src/storage/table.c` 1432-1450; new tables start without one, `src/storage/table_graph.c` 424), and `flecs_table_mark_dirty` does nothing for a table without one (`src/storage/table.c` 1397-1429). The monitors keep only the counter value of the source's old table, then compare it with the counter of the source's current table: the fixed-source monitor in `flecs_query_get_fixed_monitor` (`src/query/cache/change_detection.c` 142-201, stored at 192, compared at 194), and the up-source fields of the cache's match monitors (compared at 403-415, stored at 627-628). Counters of two different tables are unrelated, so after the move the old value 1 equals the new table's fresh 1 and the write is missed.
- **Test:**
  - `change_detection_fixed_source_moved.c`: red on v4.2.0 (rc=1, "FAIL: ecs_query_changed is false after Velocity was set on the fixed source"); green with the patch (rc=0).
  - `change_detection_parent_moved.c`: red on v4.2.0 (rc=1, "FAIL: ecs_query_changed is false after Velocity was set on the parent" and "FAIL: ecs_iter_changed is false for the child's table"); green with the patch (rc=0).
- **Suites:** core, query, addons, collections and cpp with this patch: unchanged from v4.2.0 (core 3870 / 0, query 4798 / 6, addons 643 / 0, collections 97 / 0, cpp 1919 / 0; see "flecs's suites").
- **Risk:**
  - A source that moves to another table (for example a tag added to the parent or to the fixed source) is now reported as changed even when the component was not written. This is conservative; before, whether such a move was reported depended on the two counters' values.
  - Match monitors (allocated only for change-detecting cached queries) grow by 8 bytes per field. The fixed monitor becomes an array of `ecs_query_fixed_monitor_t` (a private type in `src/query/types.h`).
  - Not covered: a source that leaves a table and comes back to the same table between two checks, with the write done while it was elsewhere, still compares equal (same table, unchanged counter).

### F19. Change detection on a fixed source that lacks the component: removal is missed, addition reads uninitialized memory

- **Change:** the fixed-source monitor records "the source doesn't have the component" as table 0 and counter 0 instead of skipping the field, so every read field is written when the monitor is filled and compared when it is checked. Patch: `fixes/F18.diff` (one patch with F18: both change `flecs_query_get_fixed_monitor`).
- **Root cause:** `flecs_query_get_fixed_monitor` (`src/query/cache/change_detection.c` 142-201) allocates the monitor with `flecs_alloc_n` (152-153), which does not zero it, and skips a field whose source has no table, no component record or no table record for the component (172-185), both when it fills the monitor (192) and when it compares it (194). After the source loses the component the field is skipped, so the removal is not reported; a field skipped at fill time and compared after the source gains the component reads a slot that was never written.
- **Test:**
  - `change_detection_fixed_source_removed.c`: red on v4.2.0 (rc=1, "FAIL: ecs_query_changed is false after the fixed source lost Velocity"); green with the patch (rc=0).
  - `change_detection_fixed_source_added.c`: rc=0 on v4.2.0 and with the patch. In this program the fixed monitor is not what decides: while `game` lacks Velocity the query has no result, so the cached part's match monitor is never synced and `ecs_query_changed` returns true from the cache alone.
  - To show the uninitialized read, `fixes/checks/F19_fixed_source_added_optional.c` is the same program with the fixed term made `EcsOptional`, so the query has a result and the cached part is in sync after the iteration. Red on v4.2.0 (rc=1, "FAIL: ecs_query_changed is false after the fixed source gained Velocity": the unwritten slot held 1, the same value as the new table's counter), green with the patch (rc=0). The same result with a `FLECS_USE_OS_ALLOC` build whose OS API malloc fills every block with int32 1s (both v4.2.0 and patched builds were made that way for this check).
- **Suites:** core, query, addons, collections and cpp with this patch (`F18.diff`, the same patch): unchanged from v4.2.0 (core 3870 / 0, query 4798 / 6, addons 643 / 0, collections 97 / 0, cpp 1919 / 0; see "flecs's suites").
- **Risk:** a fixed source that gains or loses a read component is now reported as changed, which is what Queries.md "Change Detection" documents ("Anything that causes adding or removing a component"). The other risks are F18's.

### F20. Monitors with up traversal report OnAdd for an entity that already matched, and OnRemove for one that still matches

- **Change:** events propagated down a hierarchy now carry an iterator flag (`EcsIterPropagated`), and a monitor that receives one skips it when the component can still be reached through the propagation source's own targets (`ecs_search_relation_for_entity` from `it->sources[0]`, up only, with the term's relationship). Patch: `fixes/F20.diff`.
- **Root cause:** `flecs_emit_propagate_id_for_range` (`src/observable.c` 310-376) invokes observers for entities whose table did not change and sets `it->other_table = NULL` (328). `flecs_multi_observer_invoke` (`src/observer.c` 654-773) decides whether a monitor event is a first match by evaluating the query on the previous table (743-756); a NULL previous table becomes the root table (694), which never matches an up term. So every propagated OnAdd or OnRemove counts as a transition, also when another ancestor still provides the component. Propagation reaches an entity only through ancestors that don't own the component (`src/observable.c` 361), so "another ancestor provides it" is exactly "the source's own ancestors provide it".
- **Test:**
  - `monitor_up_grandparent.c`: red on v4.2.0 (rc=1, "FAIL: OnAdd for an entity that already matched (3 OnAdd in total)" and "FAIL: OnRemove for an entity that still matches (1 OnRemove)"); green with the patch (rc=0).
  - Extra check `fixes/checks/F20_monitor_up_variants.c` (gp, p, c; add/remove Position on gp and p; ChildOf and Parent hierarchies; `up` and `self|up`): v4.2.0 fails all four variants; with the patch three pass. The fourth, Parent hierarchy with `self|up`, still fails, on a different path: p's own (not propagated) event evaluates the previous table without the entity's row (`src/observer.c` 745, `{ .table = prev_table }`), and a table with the Parent component can't resolve up traversal without the row. Not changed here.
- **Suites:** core, query, addons, collections and cpp with this patch: unchanged from v4.2.0 (core 3870 / 0, query 4798 / 6, addons 643 / 0, collections 97 / 0, cpp 1919 / 0; see "flecs's suites").
- **Risk:**
  - Adds a public iterator flag bit, `EcsIterPropagated` (bit 23), in `include/flecs/private/api_flags.h`; observers see it in `it->flags` during propagated events.
  - The skip looks only at the term that received the event. A monitor whose other terms also depend on the same source through the same relationship could be judged differently than a full evaluation of the before/after state would.

### F21. Instantiating a prefab with children makes a deleted entity handle alive again

- **Change:** when the id reserved for an instance child (instance + the prefab child's offset) was used before, `flecs_instantiate_alloc_child_id` gives it at least the generation the entity index would give it on recycling, instead of the instance's generation. Patch: `fixes/F21.diff`.
- **Root cause:** `flecs_instantiate_alloc_child_id` (src/addons/prefab/instantiate.c 45-71) checks only that no entity with the 32-bit id is alive (60-63), then takes the generation of the 64-bit `root_instance + prefab_offset` (65) and forces it with `flecs_entities_make_alive` / `flecs_entities_ensure` (66-67). For a deleted id the entity index already holds its next generation (`flecs_entity_index_remove`, src/storage/entity_index.c 210); `flecs_entity_index_make_alive` (220-228) overwrites it with the instance's, which is older when the id was recycled more often than the instance, so the deleted handle `b` is alive again as the instance's child.
- **Test:** `instantiate_resurrects_deleted_handle.c`: v4.2.0 `FAIL: the deleted handle b is alive again (parent: 387)`, rc=1; patched rc=0 (the child gets b's id with the next generation; b stays dead).
- **Suites:** core, query, addons, collections and cpp with this patch: unchanged from v4.2.0 (core 3870 / 0, query 4798 / 6, addons 643 / 0, collections 97 / 0, cpp 1919 / 0; see "flecs's suites"). The core suite includes Prefab's `*_offset_id*` tests, which pin the child id to instance + offset and its generation.
- **Risk:** low. The 32-bit child id is still instance + offset; only when that id was deleted before does the child's generation differ from the instance's (it gets the id's next generation). Applications that rebuild ids on another world (networking) already get different results there, since the old code resurrected an old handle. Not covered: an id deleted while another entity range was active sits in that range's recycled list, not in the dense array, so this check does not see its generation (see F8).

### F22. A batched set, remove and add of the same component keeps the set's value

- **Change:** when the batch meets a remove of an id (or a clear), it turns the entity's earlier queued sets and ensures of that id (of every id, for a clear) in the same batch into skipped commands, so a later add constructs the component instead of receiving the removed set's value. Patch: `fixes/F22.diff` (src/commands.c: a helper and two calls).
- **Root cause:** `flecs_cmd_batch_for_entity` (src/commands.c 968-1298) first computes the entity's final table, where the remove and the add cancel out (1096-1101 turn the remove into `EcsCmdSkip`). It then copies every Set/Ensure value into the component (1179-1245). The only check for a remove after the set, `if (dst.ptr)` (1193-1197), asks whether the *final* table has the component, which it does because of the add. In queue order the remove destroys the set's value and the add constructs a new one.
- **Test:** `batch_set_remove_add_value.c`: red on v4.2.0 (rc=1, `FAIL: e has Position {1.000000, 1.000000}, expected the constructed {-1, -1}`), green with the patch (rc=0).
- **Suites:** core, query, addons, collections and cpp with this patch: unchanged from v4.2.0 (core 3870 / 0, query 4798 / 6, addons 643 / 0, collections 97 / 0, cpp 1919 / 0; see "flecs's suites"). The core suite includes Commands.
- **Risk:** low. The walk runs only for batched removes and clears, over the entity's commands before them in the batch. A skipped set's value is destructed and freed by the flush, as for a set whose component is gone at the end of the batch. No OnSet is emitted for the dropped set; batching already elides the add/remove pair's events (ObserversManual.md "Bad Use Cases").

### F23. A queued ChildOf to a parent that was deleted, and whose id was recycled, attaches the child to the new entity

- **Change:** a queued add of a pair records the target as it is alive at that moment, with its generation, in a new `target` field of the command; at the merge `flecs_remove_invalid` treats the target as deleted when that recorded entity is no longer alive, even if its 32-bit id is alive again. Patch: `fixes/F23.diff` (src/commands.h, src/commands.c).
- **Root cause:** the command keeps the pair id (`cmd->id`), and a pair holds only the target's 32-bit id (`ecs_pair` and `ecs_entity_t_comb`, include/flecs/private/api_defines.h 357-363). At the merge, `flecs_remove_invalid` (src/commands.c 893-942) tests the target with `flecs_entities_is_valid` (907), which is true for a recycled id. The pair is added and the child becomes a child of the new entity, instead of being deleted as Manual.md "Deferred operations" says ("Commands that parent an entity to a deleted parent delete the child during the merge").
- **Test:** `staged_childof_recycled_parent.c`: red on v4.2.0 (rc=1, `FAIL: child alive after its parent was deleted; its parent is now the new entity q`), green with the patch (rc=0).
- **Suites:** core, query, addons, collections and cpp with this patch: unchanged from v4.2.0 (core 3870 / 0, query 4798 / 6, addons 643 / 0, collections 97 / 0, cpp 1919 / 0; see "flecs's suites").
- **Risk:** low. `ecs_cmd_1_t` grows from 16 to 24 bytes, so every queued command takes 8 more bytes. Queuing an add of a pair costs one entity-index lookup, and so does its merge. Only queued adds record the target (`flecs_defer_add`, the path of `ecs_add_pair`/`ecs_add_id`); a queued `ecs_set_pair` to a recycled target still takes the old path. The patch changes `flecs_remove_invalid`'s signature, so it conflicts textually with F3's patch (which calls it); see "Patches that touch the same code".

### F25. After `ecs_run_aperiodic(EcsAperiodicEmptyQueries)`, a system stays inactive when its query matches entities again

- **Change:** `ecs_run_aperiodic`, which the pipeline calls with flags 0 at the start of every frame, now tests the queries tagged `EcsEmpty` whose cache holds tables and removes the tag from those that have results. The test is F27's non-consuming one, so `fixes/F25.diff` contains `fixes/F27.diff`'s change: apply one or the other (F25.diff fixes both). Patch: `fixes/F25.diff`.
- **Root cause:** `flecs_process_empty_queries` (`src/world.c` 1338-1354) adds `EcsEmpty` to every query whose `ecs_query_is_true` is false, including queries whose cache holds only empty tables. The tag is removed in one place, `flecs_query_cache_add_table` (`src/query/cache/group.c` 216-245), and only when the cache had no table before (223, 240-243). v4.2.0 emits nothing when a cached table gets entities, so the tag stays, and the pipeline schedules only systems without it (`src/addons/pipeline/pipeline.c` 295-296). flecs.h (1929-1932) documents that the tag "is removed automatically when a query becomes non-empty".
- **Test:**
  - `pipeline_system_stays_inactive.c`: red on v4.2.0 (rc=1, "FAIL: Sys matches e but ran for 0 entities (EcsEmpty: 1)"); green with the patch (rc=0).
  - Extra check `fixes/checks/F25_new_table_joins_cache.c` (the report's second form: a new matching table joins a cache that still holds the empty one; then the system is deactivated again): red on v4.2.0 (rc=1), green with the patch (rc=0).
  - `query_is_true_consumes_change.c` (F27) is green with this patch too.
- **Suites:** core, query, addons, collections and cpp with this patch: unchanged from v4.2.0 (core 3870 / 0, query 4798 / 6, addons 643 / 0, collections 97 / 0, cpp 1919 / 0; see "flecs's suites"). The addons suite includes `SystemMisc_system_readeactivate*` and the Pipeline activation tests.
- **Risk:**
  - Per-frame cost: one `ecs_query_is_true` per query that `EcsAperiodicEmptyQueries` marked while it still had tables. Such a query costs about what running its system would, so the deactivation saves less than before (inactive systems still don't add sync points). Queries whose cache has no table are skipped: the existing mechanism reactivates them.
  - `ecs_run_aperiodic(world, 0)` was a no-op and now removes tags; flecs.h says 0 runs all actions. Uncached queries marked empty are now reactivated as well (before, nothing ever removed their tag).
  - Without F27's change this test would reset the change state of every such query each frame, which is why the two are in one patch.
  - Alternatives not taken: marking only queries without tables breaks `SystemMisc_system_readeactivate`, which documents deactivating a system whose table is empty; reintroducing per-table fill events for query caches would touch much more.

### F26. The worker threads' synchronization does not re-check its condition after a wait

- **Change:** every condition-variable wait in the worker synchronization now loops on its predicate: the main thread waits `while` not all workers are waiting, and workers wait until a new `workers_signal` counter, incremented by `flecs_signal_workers` under the mutex, has moved. Patch: `fixes/F26.diff` (src/addons/pipeline/worker.c, src/world.h: one new `int32_t` field in the private world struct).
- **Root cause:** `flecs_wait_for_sync` (src/addons/pipeline/worker.c 150-157) waits with `if`, not `while`, and then asserts the condition it did not re-check (156-157). `flecs_sync_worker` (22-30) and the start of `flecs_worker` (45-50) wait on `worker_cond` with no predicate at all, so a worker that wakes without a signal runs `flecs_run_pipeline_ops` again: during the main thread's merge, on a single-threaded op, or with no op (`pq->cur_op` NULL). POSIX and Windows condition variables may wake without a signal, and `ecs_os_cond_wait` may be the application's own.
- **Test:** `workers_spurious_wakeup.c`: red on v4.2.0 (rc=1, `fatal: flecs.c: 64383: assert(world->workers_waiting == (stage_count - 1)) (INTERNAL_ERROR)`, then `FAIL: aborted after a spurious wakeup ...`); green with the patch (rc=0). The test only wakes the main thread. A variant that wakes a worker instead (the same program with `!=` for `==` in its `cond_wait` wrapper, `fixes/checks/F26_workers_spurious_wakeup_worker.c`) segfaults on v4.2.0 (rc=139) and prints OK with the patch (rc=0).
- **Suites:** core, query, addons, collections and cpp with this patch: unchanged from v4.2.0 (core 3870 / 0, query 4798 / 6, addons 643 / 0, collections 97 / 0, cpp 1919 / 0; see "flecs's suites"). The addons suite includes MultiThread and MultiThreadStaging, with thread and task workers.
- **Risk:** low. The counter only changes when workers are signalled, under the same mutex as the waits; signals that a worker sees are unchanged, and a worker that is signalled before it waits still sees the counter moved. Task-based workers (`ecs_set_task_threads`) read the counter after `flecs_wait_for_workers` has seen them running, so they cannot miss the frame's signal. The private `ecs_world_t` grows by four bytes.

### F27. `ecs_query_is_true` and `ecs_query_count` clear the change state that `ecs_query_changed` reports

- **Change:** `ecs_query_is_true` and `ecs_query_count` create their iterator with a new flag, `EcsIterNoChangeDetection`, which skips the match-monitor syncs, the empty-table syncs, the fixed-monitor refresh and the fixed-field dirty marking, and they restore the cache's `prev_match_count` after creating it. Patch: `fixes/F27.diff` (also contained in `fixes/F25.diff`).
- **Root cause:** both functions iterate the query as if the application did:
  - creating the iterator sets `cache->prev_match_count = cache->match_count` (`src/query/cache/cache_iter.c` 36), which drops the record of tables matched or unmatched since the last iteration;
  - `ecs_query_is_true` (`src/query/api.c` 706-713) calls `ecs_iter_is_true` (`src/iter.c` 511-526): one `next`, then `ecs_iter_fini`, whose `flecs_query_iter_fini` (`src/query/engine/eval_iter.c` 670-686) syncs the first result's monitor (`flecs_query_sync_match_monitor`, `src/query/cache/change_detection.c` 581-633);
  - `ecs_query_count` (`src/query/api.c` 667-704) skips each result, but empty tables are synced while they are passed (`src/query/cache/cache_iter.c` 81-97) and the end of the iteration refreshes the fixed-source monitor (`src/query/engine/eval_iter.c` 596-605).
  flecs.h documents `ecs_query_changed` as "whether the query data changed since the last iteration" and both functions as tests, and `ecs_run_aperiodic(EcsAperiodicEmptyQueries)` calls `ecs_query_is_true` on every query.
- **Test:**
  - `query_is_true_consumes_change.c`: red on v4.2.0 (rc=1, "FAIL: after ecs_query_is_true, q1 no longer reports the set", "FAIL: after ecs_query_is_true, q2 no longer reports the unmatched table", "FAIL: after ecs_query_count, q2 no longer reports the unmatched table"); green with the patch (rc=0).
  - Extra check `fixes/checks/F27_count_fixed_source.c` (a set on a fixed source, then `ecs_query_count`, then iterating clears the state): red on v4.2.0 (rc=1, "FAIL: after ecs_query_count, the fixed source's set is no longer reported"), green with the patch (rc=0).
- **Suites:** core, query, addons, collections and cpp with this patch: unchanged from v4.2.0 (core 3870 / 0, query 4798 / 6, addons 643 / 0, collections 97 / 0, cpp 1919 / 0; see "flecs's suites").
- **Risk:**
  - Adds a public iterator flag bit, `EcsIterNoChangeDetection` (bit 24), in `include/flecs/private/api_flags.h`.
  - Code that relied on `ecs_query_count` or `ecs_query_is_true` to clear the changed state (undocumented) now sees changes until it iterates.
  - Not covered: an `order_by` query sorts when any iterator is created, including these two, and that sort syncs the monitors of re-sorted tables (`src/query/cache/cache_iter.c` 29-33, `src/query/cache/order_by.c` 257-271).

### F28. With an entity range active, instantiating a prefab with children creates instance children outside the range

**No fix.** flecs's own suite pins the behaviour the test calls wrong. `flecs_instantiate_alloc_child_id` (src/addons/prefab/instantiate.c 45-71) reserves `instance + offset` for each instance child, bypassing the active range on purpose: `World_range_prefab_spawn_deferred_after_range_switch` (test/core/src/World.c 816-850) creates an instance in range r2, merges while r1 is active, and asserts the child is 10001, next to its instance and outside the active range r1, and that r2's next id is then 10002. The F28 test's instance (id 387) lives in the default range [1, 4999] that `ecs_entity_range_new` created, and its child 388 is in that same range, so it is the same case as flecs's test.

- I made the change the test asks for (reserve the offset id only inside the active range, else `flecs_new_id`): `instantiate_child_outside_range.c` went green and `World.range_prefab_spawn_deferred_after_range_switch` failed (`(uint32_t)inst_child (387) != 10001`). So no patch.
- What needs changing is the documentation: EntitiesComponents.md "Ranges" and addons/entity_ranges.h say that while a range is active all new ids fall within it; they should say that instance children are reserved next to their instance (in the instance's range) unless that id is taken.
- A narrower defect the report also names is real: an instance at its range's last id reserves `max + 1`, outside every range of the instance, and the exhausted range does not assert. A fix that keeps flecs's test would reserve the offset id only when it is in the same range as the instance (`flecs_entity_index_find_range` of both ids) and otherwise call `flecs_new_id`; it does not make `instantiate_child_outside_range.c` green, so it is not included.
- Test: `instantiate_child_outside_range.c` stays red: `FAIL: instance child 388 is outside the active range [5000, 5010]`, rc=1.

### F29. A cached query (or a system) whose Or chain ends with a Sparse component crashes when it is created

- **Change:** the validator clears the cacheable flag of a Sparse term as soon as it sees the component is Sparse, before the Or-chain consistency check, so an Or chain that contains a Sparse term is left out of the cache whole. Patch: `fixes/F29.diff` (one change in `src/query/validator.c`; the same patch fixes F34).
- **Root cause:** `flecs_query_finalize_terms` (src/query/validator.c) makes each Or chain cache-consistent at lines 1075-1087 (a non-cacheable term clears the flag of the chain before it), but only clears the flag of Sparse terms later in the same loop, at 1234-1238. A fragmenting Sparse component passes the table-match test in `flecs_term_finalize` (837-859), so for `TagA || Position` the chain check sees Position as cacheable, and the sparse clearing then leaves `TagA ||` cacheable alone. `flecs_query_create_cache` (src/query/api.c 194-243) copies `[TagA ||]` into the cache's query, `ecs_query_init` (src/query/cache/cache.c 750) rejects it ("last term of query can't have OR operator", validator.c 1308-1312), and the error path finalizes a cache whose `query` is NULL (cache.c 680, 689; group.c 334): SIGSEGV.
- **Test:** `query_or_sparse_cache_crash.c`: v4.2.0 prints "creating the cached query" and dies with SIGSEGV (rc=139); with the patch rc=0 (the cached query is created and matches 2 entities, as the uncached control does).
- **Suites:** core, query, addons, collections and cpp with this patch: unchanged from v4.2.0 (core 3870 / 0, query 4798 / 6, addons 643 / 0, collections 97 / 0, cpp 1919 / 0; see "flecs's suites").
- **Risk:** low. Or chains that mix table terms with Sparse terms are now evaluated outside the cache instead of being split; results and the API are unchanged, such queries just get less from the cache. The error path that dereferences a NULL `cache->query` when the cache's own query is rejected (cache.c 750-753 with `flecs_query_cache_fini`) is still there; this patch only removes the way the validator reached it.

### F30. A call during an iteration that removes a table from the query's cache makes the iterator skip another table

**No fix.** There is no small change that makes the cache iterator survive a table leaving the cache in the middle of an iteration; this is a design question about which calls are allowed while a cached query is iterated.

- **Root cause:** the cache iterator walks a group's table vector by index (`qit->tables`, `qit->cur`; src/query/cache/cache_iter.c 41-123). A table leaves the cache during a call through `OnTableDelete` (src/query/cache/cache.c 601-603) or a rematch flushed at the end of the call, and `flecs_query_cache_remove_table_from_group` removes it with `ecs_vec_remove` (src/query/cache/group.c 190), which moves the group's last table into the hole. When the hole is before the cursor, that table is never returned. For a wildcard table, `qit->tables` points at the match's `wildcard_matches` vector, which the removal or rematch frees (src/query/cache/match.c 55-64), so the next `ecs_query_next` reads freed memory.
- **Test:** `query_iter_skips_table.c` stays red: "FAIL: e2 returned 1 times, e3 returned 0 times (expected 1 and 1)" (rc=1). The F36 and F40 patches don't change it.
- **Why no small fix:** an order-preserving removal shifts every later table one slot left, so the cursor skips one anyway; the cache doesn't know its iterators, so it can't move their cursors. A fix needs one of:
  - deferring cache changes (table removal, rematch, regrouping, group frees) while the cache is being iterated, which needs a per-cache iteration count that `ecs_iter_fini` reliably releases, and a queue of pending cache operations; or
  - iterators that keep stable identities (group id, table id), resynchronize after the cache changed, and a removal that keeps the iteration order, at O(n) index updates per removal (a cost on `ecs_delete_empty_tables` and pair-target deletes for large caches).
  Both change the core of the query cache. The alternative is documentation: Queries.md says only that the C++ `each`/`run` lock the iterated table and recommends iterating with a stage; it could state that while a cached query is iterated from C, calls that create, delete or rematch tables must be deferred (`ecs_defer_begin`/`ecs_defer_end`, or a stage merged after the iteration).

### F31. The pipeline keeps a stale schedule when its query's match changes outside the cache (a system in a disabled module's Parent hierarchy keeps running; custom pipelines with a fixed-source or DontFragment term too)

- **Change:** at the start of each frame the pipeline compares the active systems its query yields with the schedule's systems and forces a rebuild when they differ. Patch: `fixes/F31.diff`.
- **Root cause:** `flecs_pipeline_build` (src/addons/pipeline/pipeline.c 267-274) rebuilds only when the query cache's `match_count` changed. Results that are decided while iterating never change that count: uncached terms (fixed sources and DontFragment components, src/query/validator.c 837-859) and the per-entity filtering of tables with the Parent component (src/query/compiler/compiler.c 683-727; the rematch observer skips those tables, src/query/cache/cache.c 268-273). So disabling a module whose systems are in a Parent hierarchy, removing `Running` from a pipeline's fixed source, or removing a DontFragment tag from a system leaves the old schedule in place.
- **Test:**
  - `pipeline_parent_module_disabled.c`: v4.2.0 rc=1, "the system in the Parent hierarchy ran 2 times in the two frames after its module was disabled"; patched rc=0 (the ChildOf control still passes).
  - `pipeline_custom_uncached_term.c`: v4.2.0 rc=1, "variant 0 (System, Running(Game)): the system ran 3 times" and the same for variant 1 (DontFragment); patched rc=0.
- **Suites:** core, query, addons, collections and cpp with this patch: unchanged from v4.2.0 (core 3870 / 0, query 4798 / 6, addons 643 / 0, collections 97 / 0, cpp 1919 / 0; see "flecs's suites"). The addons suite includes Pipeline.
- **Risk:** one more iteration of the pipeline query per frame (at frame start only; not at sync points). Measured on a debug build with 200 term-less systems: 9.1 µs per frame on v4.2.0, 9.6 µs patched (about 0.5 µs, 5%). Changes picked up this way take effect at the next frame start, not mid-frame. Inactive systems (EcsEmpty) are not compared, as they are not in the schedule; an inactive system entering or leaving only through an uncached term does not trigger a rebuild (it only influences where merges go).

### F32. Overriding a DontFragment Inherit component inherited through two IsA levels constructs it instead of copying it

- **Change:** `flecs_table_search_relation_for_tgt` no longer stops at a target that does not own a DontFragment component: it searches that target's own relationship targets, as it already does for every other component. Patch: `fixes/F32.diff`.
- **Root cause:** adding a Sparse/DontFragment component calls `flecs_component_sparse_override` (src/storage/sparse_storage.c 415-443), which copies from the base that `ecs_search_relation(..., EcsIsA, EcsUp, &base)` returns, or constructs the value when none is found (433-434). In `flecs_table_search_relation_for_tgt` (src/search.c 204-248) a DontFragment component is looked up only in the direct target's sparse set (216-221); the `else` branch that recurses through the target's table and its own IsA pairs (222-232) is skipped. `ecs_get`/`ecs_has` use `flecs_get_base_component` (src/addons/prefab/instantiate.c 485-555), which does recurse, so the value read and the value the override copies disagree.
- **Test:** `override_dont_fragment_2_levels.c`: v4.2.0 `FAIL: DontFragment, 2 levels: after ecs_add the instance owns=1 Position = {0, 0}, expected the inherited {10, 20}`, rc=1; patched rc=0 (the Sparse and one-level controls still pass).
- **Suites:** core, query, addons, collections and cpp with this patch: unchanged from v4.2.0 (core 3870 / 0, query 4798 / 6, addons 643 / 0, collections 97 / 0, cpp 1919 / 0; see "flecs's suites"). The query suite includes the DontFragment and Sparse tests.
- **Risk:** `ecs_search_relation` (and with it `ecs_has_id`'s inheritance check, table override lookups, order_by and query traversal that use it) now finds a DontFragment component on a target's targets, at any depth, for any traversed relationship, the way it finds fragmenting components. Code that relied on the one-level lookup for DontFragment components would see the deeper base.

### F33. Worker threads of a multi-threaded change-detection system allocate a table's dirty state without synchronization (double allocation, a leak, a data race)

- **Change:** in `ecs_worker_next`, workers other than worker 0 mark each result of the shared chained query iterator with `EcsIterSkip`, so only worker 0 (the main thread) runs change detection for it (marking written fields dirty and syncing the match monitor, which lazily allocates the table's dirty state and the match's monitor); the trivial change-detection path checks the same flag first. Patch: `fixes/F33.diff`.
- **Root cause:** every worker iterates the whole chained query (`ecs_worker_next`, src/iter.c 1036-1095) and each `ecs_query_next` runs change detection on the previous result (src/query/engine/eval_iter.c 217-234, 492-500). That calls `flecs_query_sync_match_monitor` (src/query/cache/change_detection.c 581-633), which allocates `match->_monitor` when it is NULL (`flecs_query_get_match_monitor`, 79-138) and the table's dirty state when it is NULL (`flecs_table_get_dirty_state`, src/storage/table.c 1432-1450), both from non-thread-safe allocators, with no lock. Two workers that see NULL both allocate; one allocation leaks and counters written to it are lost.
- **Test:** `workers_dirty_state_double_alloc.c`: v4.2.0 rc=1, "the dirty state of one table was allocated 2 times by the worker threads of one system; all but one leak"; patched rc=0 (3 runs; each waits the test's 2-second rendezvous for a second allocation that no longer comes).
- **Suites:** core, query, addons, collections and cpp with this patch: unchanged from v4.2.0 (core 3870 / 0, query 4798 / 6, addons 643 / 0, collections 97 / 0, cpp 1919 / 0; see "flecs's suites"). Also `fixes/checks/F33_mt_change_detection.c`: with 4 threads, a multi-threaded `[inout] Position` system still makes another change-detecting query report the change after every frame, on both builds.
- **Risk:** the table is marked dirty once per iteration instead of once per worker (change detection compares counters for inequality, so the result is the same). Worker 0 gets a non-empty slice of every non-empty table, so every table is still synced. User code that calls `ecs_worker_iter` itself gets change detection only from the iterator with index 0. Not covered: at the end of the iteration every worker still writes the fixed-source monitor and the fixed fields' dirty counters (`flecs_query_update_fixed_monitor`, `flecs_query_mark_fixed_fields_dirty`, eval_iter.c 597-605); those write existing counters (no allocation), a remaining benign race.

### F34. A cached query whose Or chain starts with a table term and ends with a Sparse term, with a term after the chain, returns wrong entities, and compiling it writes 42 bytes before the op array

- **Change:** the same change as F29: a Sparse term's cacheable flag is cleared before the Or-chain consistency check, so the whole chain `TagA || Position` is compiled as an uncached Or block and only `TagC` goes to the cache. Patch: `fixes/F29.diff` (shared with F29; there is no separate F34 patch).
- **Root cause:** as F29 (src/query/validator.c 1075-1087 run before 1234-1238). With a term after the chain, the cache's query `TagA || TagC` is valid, so creation succeeds; the compiler (src/query/compiler/compiler_term.c 1179, 1222, 306-311) then compiles Position as the last term of an Or chain whose first term went into the cache, calls `flecs_query_end_block_or` with `lbl_begin == -1`, reads and writes `ops[-1]`, and links the Position op to label -1, so the query returns the first cached table if it has Position and nothing else.
- **Test:** `query_or_sparse_term_after_chain.c`: v4.2.0 prints "guard of a 384-byte block changed at offset 22 (42 bytes before the block)", "cached: 1 entities: e1", FAIL (rc=1); with the patch "cached: 2 entities: e2 e3", no guard change, rc=0.
- **Suites:** core, query, addons, collections and cpp with this patch (`F29.diff`, the same patch): unchanged from v4.2.0 (core 3870 / 0, query 4798 / 6, addons 643 / 0, collections 97 / 0, cpp 1919 / 0; see "flecs's suites").
- **Risk:** as F29.

### F35. While a cascade query is iterated, a call that changes a parent's depth returns a table again, or frees the group being iterated (a read of freed memory)

**No fix.** Both forms come from regrouping the cache while it is iterated, which the iterator is not built for; a fix is the same design change as F30.

- **Root cause:** a cascade query groups its tables by depth, iterated in ascending order through `group->next` (src/query/cache/cache_iter.c 49-66; ordered insert, src/query/cache/group.c 37-54). Reparenting enqueues a revalidation that the end of the call runs, and `flecs_query_cache_move_table_to_group` (group.c 249-274) appends the table to the group of its new depth and removes it from the old one.
  - First form: the table moves into a group after the current one, and the iterator returns it a second time when it reaches that group.
  - Second form: the table was alone in its group, so `flecs_query_cache_remove_group` (group.c 118-130) unlinks the group, sets its `next` to NULL (128) and frees it (`ecs_map_remove_free`, 109). The iterator still holds `qit->group` and `qit->tables = &group->tables`, and the next `ecs_query_next` reads them from the freed block (cache_iter.c 49-62).
- **Tests:** stay red with every patch here: `query_cascade_table_twice.c` "FAIL: c1 returned 2 times, c2 returned 1 times (expected 1 and 1); 4 results" (rc=1); `query_cascade_group_freed.c` "p1 is now a child of m; continuing the iteration" then SIGSEGV (rc=139).
- **Why no small fix:** the group struct could be kept alive and linked while iterated, but the cache has no record of live iterators, and an empty group left in the list breaks `flecs_query_cache_ensure_group` (which re-inserts a group with no tables) and the `on_group_delete` contract. Not returning a regrouped table twice needs either deferring regrouping while the cache is iterated or a record of the tables already returned. See F30 for the two designs and the documentation alternative (defer calls that change table depth or matching while a cached query is iterated from C).

### F36. With change detection on, a call during an iteration that adds a table to the iterated group reallocates the group's array, and the next ecs_query_next reads and writes the freed array

- **Change:** the iterator no longer trusts the `qit->elem` pointer when it syncs change detection: a new `flecs_query_cache_iter_elem` looks the current result's match up again through the cache's table map (and the wildcard vector index), and `flecs_query_change_detection` and `ecs_iter_changed` use it. Patch: `fixes/F36.diff`.
- **Root cause:** `flecs_query_cache_next` keeps a raw pointer to the current match in `qit->elem` (src/query/cache/cache_iter.c 104). A table added to the same group during the iteration is appended with `ecs_vec_append` (src/query/cache/group.c 159), which can reallocate the group's array and free the old one. The next `ecs_query_next` first runs change detection on the previous result and calls `flecs_query_sync_match_monitor(impl, qit->elem)` (src/query/engine/eval_iter.c 230), which reads and writes the freed array (and may store a newly allocated monitor in it). `ecs_iter_changed` reads the same pointer (src/query/cache/change_detection.c 704-707). The iteration itself is safe: `qit->tables` points at the group's `ecs_vec_t`, which is updated in place.
- **Test:** `query_iter_table_array_realloc.c`: v4.2.0 prints "created the 33rd table; continuing the iteration" and dies with SIGSEGV (rc=139, the free wrapper poisons the old array); with the patch rc=0 (e0 returned once, at least 32 results).
- **Suites:** core, query, addons, collections and cpp with this patch: unchanged from v4.2.0 (core 3870 / 0, query 4798 / 6, addons 643 / 0, collections 97 / 0, cpp 1919 / 0; see "flecs's suites"). The query suite includes ChangeDetection.
- **Risk:** low. Change-detecting cached queries do one table-map lookup per result when they sync a monitor. If the current table left the cache during the call, its monitor is not synced and `ecs_iter_changed` returns true (the table was unmatched, which `ecs_query_changed` documents as a change). Sorted queries keep using their slice copy, which only changes when an iterator is created. Other stale-pointer paths of the cache iterator (F30, F35) are not addressed.

### F37. A system whose commands reorder the phases makes the pipeline skip, in that frame, the systems now ordered before it (with or without ProgressTasks)

**No fix.** The resume logic after a mid-frame rebuild (src/addons/pipeline/pipeline.c 450-458) knows only "the last system in the new schedule that already ran in this frame", and resumes after it. When a merge reorders systems (here `Pa DependsOn Pb` moves S2 before S1), a system that was still to run can land before that point and is skipped (`pipeline_phase_reorder_skips.c`: v4.2.0 rc=1, "S2 ran 0 times in the first frame"; F17's patch does not change this).

What a fix would need, and why no small one is safe:
- Tried: resume at the first system of the new schedule that has not run in this frame, and skip systems that already ran (the skip decided from `last_frame`, written after each op so worker threads never read it while it changes). It turned F37 and F17's three tests green, but broke 9 of flecs's own addons tests: `Pipeline.single_threaded_pipeline_change`, `multi_threaded_pipeline_change`, `multi_threaded_pipeline_change_tasks`, `multi_threaded_pipeline_change_w_only_singlethreaded`, `multi_threaded_tasks_pipeline_change_w_only_singlethreaded`, `multi_threaded_no_staging_w_add_after_read`, `multi_threaded_tasks_no_staging_w_add_after_read`, `switch_from_threads_to_tasks` and `switch_from_tasks_to_threads`. All nine check one rule for systems that *join* the schedule mid-frame: a system that becomes active during the frame and sorts before the current position (for example `SysB` in `Pipeline_single_threaded_pipeline_change`, `SysA` in `Pipeline_multi_threaded_no_staging_w_add_after_read`) does not run until the next frame. The attempt is kept, unapplied, in `fixes/attempts/F37-resume-first-unrun.diff`.
- A correct fix has to tell "was already pending in the old schedule" (must still run: F37) from "joined the schedule behind the current position" (waits: flecs's tests). That needs per-frame pending state per system carried across rebuilds (the old schedule is reset in place by the rebuild), several rebuilds in one frame handled, and a per-system skip in `flecs_run_pipeline_ops` that worker threads read without races. That is a redesign of the resume protocol, and the intended behavior for reordering mid-frame is not documented; it is a design decision for flecs (run pending reordered systems this frame, or defer reorders to the next frame).

### F38. An instance of a prefab variant does not own a DontFragment component that the variant's base auto-overrides

- **Change:** `flecs_instantiate_override_dont_fragment` also walks the IsA targets of the base (recursively, with the same depth limit as `flecs_instantiate`), so a DontFragment component auto-overridden by a base of the base is added to the instance. Patch: `fixes/F38.diff`.
- **Root cause:** for components that fragment, `flecs_add_overrides_for_base` (src/storage/table_graph.c 718-791) adds every auto-overridden id of the base and, recursively, of the base's own IsA targets (780-789) to the instance's table type. A DontFragment auto override is never in a table type: that function only flags the table that holds the `AUTO_OVERRIDE` id (`EcsTableOverrideDontFragment`, 739-746). The override is then applied by `flecs_instantiate` (src/addons/prefab/instantiate.c 407-410), whose `flecs_instantiate_override_dont_fragment` (370-391) reads only the direct base's table; the variant's table has no `AUTO_OVERRIDE` id, and `flecs_instantiate_dont_fragment` (301-368) skips Inherit components of a direct IsA base, so the instance only inherits the variant's value.
- **Test:** `auto_override_dont_fragment_variant.c`: v4.2.0 `inst owns Defense: 0; value 50` / `FAIL: the instance of the variant does not own Defense`, rc=1; patched `inst owns Defense: 1; value 50`, rc=0 (both controls still hold).
- **Suites:** core, query, addons, collections and cpp with this patch: unchanged from v4.2.0 (core 3870 / 0, query 4798 / 6, addons 643 / 0, collections 97 / 0, cpp 1919 / 0; see "flecs's suites").
- **Risk:** instances of variants now own DontFragment components that a deeper base auto-overrides, copied from the nearest base that has a value (the variant's own value wins). Instantiating from a base that has IsA pairs walks its IsA chain once more; the type scan only runs on tables flagged `EcsTableOverrideDontFragment`, so the cost is a table lookup per level.

### F39. With a Parent hierarchy, instances made after a prefab child changes copy the child's old type; a Sparse component added to it aborts the next instantiation

- **Change:** each tree-spawner entry records the id of the prefab child's table it was computed from; `flecs_spawner_instantiate` rebuilds the spawner when a prefab child is no longer in that table. Patch: `fixes/F39.diff` (src/addons/prefab/tree_spawner.c, plus one field in `ecs_tree_spawner_child_t` in include/flecs.h).
- **Root cause:** a prefab whose children use `Parent` is instantiated through its `EcsTreeSpawner` (src/addons/prefab/instantiate.c 424-440). The first instantiation builds it (`flecs_prefab_spawner_build`, src/addons/prefab/tree_spawner.c 199-224): for each child, the table its instance children go to, computed from the child's table at that moment (`flecs_prefab_spawner_build_type`, 10-60; stored at 92-95). Later instantiations append instance children straight to the cached table (`flecs_spawner_instantiate`, 226-350), then `flecs_instantiate_sparse` walks the prefab child's *current* table (337-338) and asserts that the instance child has each Sparse component (instantiate.c 122-124). Nothing rebuilds the spawner when a prefab child's components change; only changes to the set of children are refused (`flecs_tree_spawner_assert_not_instantiated`, 166-196).
- **Test:**
  - `tree_spawner_stale_child_type.c`: v4.2.0 `Parent: i2's child has Velocity: 0 (owned 0)` / `FAIL: with a Parent hierarchy, i2's child lacks the Velocity its prefab child has`, rc=1; patched rc=0.
  - `tree_spawner_stale_sparse_assert.c`: v4.2.0 aborts with `assert(dst_ptr != NULL)` at flecs.c 64655 (instantiate.c 124) and prints `FAIL: aborted while instantiating the prefab a second time`, rc=1; patched rc=0.
- **Suites:** core, query, addons, collections and cpp with this patch: unchanged from v4.2.0 (core 3870 / 0, query 4798 / 6, addons 643 / 0, collections 97 / 0, cpp 1919 / 0; see "flecs's suites"). The suite objects were compiled against the unpatched flecs.h; the only suite source that names the spawner, NonFragmentingChildOf.c, only calls `ecs_has(..., EcsTreeSpawner)`, so the struct change does not affect it.
- **Risk:** `ecs_tree_spawner_child_t` is declared in the public flecs.h and grows by 8 bytes (a `uint64_t`); code that reads `EcsTreeSpawner` data directly must be recompiled. Each Parent-hierarchy instantiation now does one record lookup per prefab child to check the spawner; a change of a prefab child's components costs one spawner rebuild at the next instantiation. Table ids are unique for the world's life, so a recycled table address cannot pass the check.

### F40. While an order_by query is iterated, deleting an entity from a table with a later slice makes the iterator return rows past that table's count

- **Change:** when the iterator turns a sorted slice into a result, it clamps the slice's row count to the rows the table still has, and skips a slice that starts past the table's count. Patch: `fixes/F40.diff`.
- **Root cause:** an order_by query iterates `cache->table_slices`, copies of the cache's matches with a row range (`_offset`, `_count`) computed when the iterator is created (src/query/cache/order_by.c 195-209, called from `flecs_query_cache_iter_init`, src/query/cache/cache_iter.c 27-34). The iterator returns each slice's range as is (cache_iter.c 218-219, 374-375, 478-479) and only skips a slice when its table is empty (82-101). Deleting an entity during the iteration swap-removes a row and lowers the table's count (src/storage/table.c 1653-1704), so a later slice can cover rows past the count, which hold the stale entity id and value of the moved row.
- **Test:** `query_order_by_stale_rows.c`: v4.2.0 prints "FAIL: e3 returned 2 times (expected 1); a result extends past its table's count: 1" (rc=1); with the patch rc=0 (e3 once, no result past its table's count).
- **Suites:** core, query, addons, collections and cpp with this patch: unchanged from v4.2.0 (core 3870 / 0, query 4798 / 6, addons 643 / 0, collections 97 / 0, cpp 1919 / 0; see "flecs's suites"). The query suite includes the Sorting tests.
- **Risk:** low. Only results of slices that extend past their table's count change: they get shorter or are skipped. The order of the remaining rows is still the order computed when the iterator was created; a deleted row's place is taken by the table's last row, so an entity of the same table can still be missed or seen out of order after such a call, as the docs describe for entities that move during an iteration ("Sorting": sorting is decided when an iterator is created).

### F41. An IsA add gives no OnSet for an inherited Sparse or DontFragment component

- **Change:** two parts, one patch (src/observable.c). Patch: `fixes/F41.diff`.
  - `flecs_emit_forward_id` also emits the forwarded OnSet for a Sparse component. The component has no column, so the observers get the field size and read the value from the source, as they do when a set on the base is propagated.
  - A new `flecs_emit_forward_dont_fragment`, called by `flecs_emit` after it forwards a new `(IsA, b)` pair, emits OnSet for each DontFragment component with the Inherit trait that has OnSet observers. Its source is found the way `ecs_get` finds it (`flecs_emit_isa_source`: the table's IsA targets in type order, depth first, like `flecs_get_base_component`). The event is emitted only when b is the first of the entities' bases that provides the component, and entities that own the component get no self|up event (`flecs_emit_invoke_not_owned`).
- **Root cause:** `flecs_emit` (src/observable.c 1196-1237) forwards the ids reachable through a new IsA pair to the OnSet observers (`flecs_emit_forward`, 799-890).
  - The reachable ids are the Inherit ids of the base's table type, recursively through the base's own IsA pairs (`flecs_reachable_cache_ensure`, 708-780). A DontFragment component is in no table type, so it is never listed.
  - For a listed id, `flecs_emit_forward_id` (613-706) invokes the OnSet observers only when the id has a column in the source's table (685, `if (storage_i != -1)`). A Sparse component has none.
  - Instantiation emits nothing either: `flecs_instantiate_dont_fragment` skips Inherit components of a base the instance has an IsA pair to (src/addons/prefab/instantiate.c 313-316).
- **Test:** `isa_onset_sparse_dont_fragment.c`: v4.2.0 rc=1 ("OnSet events (one level, two levels): Position 1 1, Health (Sparse) 0 0, Defense (DontFragment) 0 0", "FAIL: an IsA add produced no OnSet for an inherited Sparse or DontFragment component"); patched rc=0 (1 1 for all three).
- **Extra check** `fixes/checks/F41_isa_onset_more.c`, red on v4.2.0 and green with the patch:
  - an entity that owns Health and Defense gets no self|up event when it gains the base, and an up-only observer gets one for each;
  - an entity whose first base has neither component gets one event each from the second base;
  - a DontFragment component without Inherit, copied at instantiation, still gets one owned event (as on v4.2.0).
- **Suites:** core, query, addons, collections and cpp with this patch: unchanged from v4.2.0 (core 3870 / 0, query 4798 / 6, addons 643 / 0, collections 97 / 0, cpp 1919 / 0; see "flecs's suites"). core includes the Observer, ObserverOnSet and Prefab suites.
- **Risk:**
  - Every IsA add in a world that has OnSet observers and DontFragment components walks the world's list of DontFragment components. For each with Inherit and OnSet observers, it searches the entities' bases. `flecs_instantiate_dont_fragment` already walks that list for every instantiation of a base with DontFragment components.
  - OnSet observers of Sparse and DontFragment components now get the events that ObserversManual.md "Adding an IsA pair" documents; before, they got none.
  - Not covered: inheritors of an entity that gains a base. The downward propagation of a new pair carries only OnAdd, for table components as well (REPORT-6.md lists it under "Not counted as findings").

### F42. Setting a DontFragment component on a base sends OnSet with the base's value to an instance that overrides it

- **Change:** `flecs_emit_propagate_id_for_range` decides per entity whether an entity owns a DontFragment component. It invokes the self|up observers only for the runs of entities in the range that don't own it (`flecs_emit_invoke_not_owned`), and doesn't propagate further from entities that own it. The up observers get every entity, as before and as for table components. Patch: `fixes/F42.diff` (src/observable.c).
- **Root cause:** a set on a base propagates OnSet down the IsA pairs (src/observable.c 1316: `flecs_propagate_entities`, 571-611; `flecs_emit_propagate`, 440-465; `flecs_emit_propagate_id`, 378-438). `flecs_emit_propagate_id_for_range` (310-376) skips the self|up observers and the further propagation only when the table owns the component (`owned`, 324), which it reads from the table type. A DontFragment component is in no table type, so an instance that overrides it in the sparse storage never counts as owning it, and gets the base's event and value.
- **Test:** `set_base_onset_dont_fragment_override.c`: v4.2.0 rc=1 ("OnSet events for inst after setting base: Position 0, Health 0, Defense 1; ecs_get(inst, Defense) = 7", "Defense event for inst: source base, value 60", FAIL); patched rc=0 (Defense 0).
- **Extra check** `fixes/checks/F42_dont_fragment_override_more.c`: i1 and i2 in one table, i1 overrides Defense; j IsA i1, k IsA i2; then base's Defense is set. Self|up events must reach only i2 and k, none i1 or j (whose value is i1's); an up-only observer must get i1 and i2. v4.2.0: i1 1, i2 1, j 1, k 1 (FAIL); patched: i1 0, i2 1, j 0, k 1, up-only i1 1, i2 1 (OK).
- **Suites:** core, query, addons, collections and cpp with this patch: unchanged from v4.2.0 (core 3870 / 0, query 4798 / 6, addons 643 / 0, collections 97 / 0, cpp 1919 / 0; see "flecs's suites"). query includes the DontFragment suite.
- **Risk:** low.
  - For DontFragment components only, one sparse lookup per entity of each propagated range; table and Sparse components keep the table check.
  - A range with owners is split into runs, so an observer can be called more than once for one table in one event (with the same event id; multi-component observers accept that for the same field).

### F43. OnSet events name a base that isn't the entity's primary source

- **Change:** OnSet events that come through IsA are emitted only through the entities' source of the component, the base that `ecs_get` reads it from (`flecs_emit_isa_source`: the table's IsA targets in type order, depth first, the order of `flecs_get_base_component`). Patch: `fixes/F43.diff` (src/observable.c).
  - **Adding an IsA pair:** `flecs_emit_forward` drops the OnSet of a reachable id unless the id's source is the entities' source and the new pair's target is the base they see it through. This covers a second base that doesn't become the primary source, and a variant whose reachable ids list the component once per base.
  - **Setting a base:** when the OnSet propagates down IsA, `flecs_emit_propagate_id` skips a table whose entities don't see the component from the set entity through that pair's target: an earlier base in type order provides it, or the same base is reached a second time through another path (a diamond). It doesn't propagate further from such a table either: the value of its entities, and of their inheritors, didn't change.
  - OnAdd and OnRemove forwarding and propagation are unchanged.
- **Root cause:**
  - `flecs_emit_forward_id` checks only whether the entity's own table has the component (`owned`, src/observable.c 662-663).
  - The reachable ids of `(IsA, v)` hold the component once for every base of v that provides it (`flecs_reachable_cache_ensure`, 729-764).
  - The propagation walks every `(IsA, b)` table (`flecs_emit_propagate_id`, 420-434; `flecs_emit_propagate_id_for_range`, 310-376).
  - `ecs_get` takes the first base in type order, depth first (`flecs_get_base_component`, src/addons/prefab/instantiate.c 485-555). ObserversManual.md "Adding an IsA pair" says no OnSet is generated when the new base doesn't become the primary source (the base with the lowest id).
- **Test:** `isa_second_base_onset.c`: v4.2.0 rc=1 ("1. second base added: 1 event(s) for inst, 1 from b2", "2. second base set: 1 event(s) for inst (its Position: 1)", "3. variant with two bases: 2 event(s) for i3, 1 from b1", FAIL); patched rc=0 (0, 0, and 1 from b1; the control still gets 1 from b1).
- **Extra check** `fixes/checks/F43_onset_source_more.c`, for table, Sparse and DontFragment storage, with the two bases created in both orders:
  - a diamond (e1 IsA e0; e2 IsA e0 and IsA e1; set e0): e2 gets one event, not two;
  - setting a base that isn't the primary source (inst IsA b1 and b2; set b2): neither inst nor its inheritor c gets an event (v4.2.0: one each), while setting b1 gives each one event from b1.
  - Red on v4.2.0, green with the patch.
- **Suites:** core, query, addons, collections and cpp with this patch: unchanged from v4.2.0 (core 3870 / 0, query 4798 / 6, addons 643 / 0, collections 97 / 0, cpp 1919 / 0; see "flecs's suites"). core includes the Observer and ObserverOnSet suites.
- **Risk:**
  - For each table that an OnSet reaches through IsA, and for each forwarded id that has OnSet observers, one search of the table's bases: a table-record lookup per base visited, one lookup for an entity with a single base that owns the component.
  - Applications that counted on the duplicate or non-primary OnSet events no longer get them.
  - The manual's "lowest entity id" is the type order of the direct bases. For deeper bases the patch follows `ecs_get`'s depth-first order, which is where the entity's value comes from.

### F44. A prefab with ChildOf and Parent children gives instances no copy of the ChildOf children

- **Change:** the ChildOf children of a prefab are instantiated also when the prefab has Parent children. Patch: `fixes/F44.diff` (src/addons/prefab/instantiate.c, tree_spawner.c, prefab.h).
  - `flecs_instantiate` runs the tree spawner, which only holds Parent children, and then the same ChildOf loop it runs for prefabs without Parent children. That loop is now a function, `flecs_instantiate_childof_children`; for an ordered parent it returns at once when no child has a ChildOf pair.
  - `flecs_spawner_instantiate`, after its spawn loop, calls the same function for each prefab child it spawned that has ChildOf children, with the spawned instance child as the parent. It copies the (prefab child, instance child) pairs first, because a nested instantiation can use another spawner, which reuses the `parents` array. It gets the instantiation depth as a new parameter, for the cycle check.
- **Root cause:** with a Parent child, `flecs_instantiate` uses the tree spawner and returns (src/addons/prefab/instantiate.c 429-443). The spawner keeps only children whose table has the Parent component (tree_spawner.c 82-84) and descends only into the children of the children it kept (101-113). ChildOf children are instantiated only by the loop after that return (446-458), so neither a ChildOf child next to a Parent child nor one below a Parent child gets a copy.
- **Test:** `prefab_mixed_children_instance.c`: v4.2.0 rc=1 ("children: mixed 1 (copy of the ChildOf child: 0), two ChildOf 2, two Parent 2; nested: 1 child with 0 grandchild"); patched rc=0 ("mixed 2 (copy of the ChildOf child: 1) ...; nested: 1 child with 1 grandchild").
- **Extra check** `fixes/checks/F44_mixed_children_more.c`, red on v4.2.0 and green with the patch:
  - two instances of a prefab whose Parent child comes before its ChildOf child (the second instance uses the cached spawner), with `ecs_get_target(inst, prefab_child)` of the Parent child;
  - three levels: a Parent child, its ChildOf child and that one's Parent child;
  - a ChildOf child below a ChildOf child below a Parent child.
  - v4.2.0: "copy of a 0", levels "1 0 0"; patched: every copy at every level, with its value.
- **Suites:** core, query, addons, collections and cpp with this patch: unchanged from v4.2.0 (core 3870 / 0, query 4798 / 6, addons 643 / 0, collections 97 / 0, cpp 1919 / 0; see "flecs's suites"). core includes the Prefab and NonFragmentingChildOf suites.
- **Risk:**
  - The copies of ChildOf children are created after the spawned ones, so the instance's ordered children list them after the Parent children; the prefab can interleave them.
  - `ecs_get_target(instance, prefab_child)` finds an instance child by its index in the ordered children (`flecs_get_prefab_instance_child`, src/addons/prefab/prefab.c 73-133). It keeps working for Parent children placed before every ChildOf child of the prefab, as on v4.2.0. For the others it reports that the children "have changed since prefab instantiation", as it did on v4.2.0, where the instance lacked those children.
  - Prefabs with only Parent children: one table-cache count per instantiation and one component-record lookup per spawned child.
  - `flecs_spawner_instantiate` (internal, src/addons/prefab/prefab.h) takes one more parameter.

### F45. Auto-overriding a DontFragment component on a prefab child aborts instantiation

- **Change:** an `AUTO_OVERRIDE` of a DontFragment component on a prefab child no longer becomes an id in the instance child's table type. Patch: `fixes/F45.diff` (src/addons/prefab/instantiate.c, tree_spawner.c, prefab.h).
  - Instead, the prefab child's table gets the flag `EcsTableOverrideDontFragment`, which `flecs_add_overrides_for_base` sets for the same id on a prefab (src/storage/table_graph.c 739-748).
  - The component is then added to the instance child the way a prefab's own DontFragment auto override is added to an instance, by `flecs_instantiate_override_dont_fragment` (now non-static): for ChildOf children through the `flecs_instantiate(child, instance_child)` call that already follows (instantiate.c 293), for Parent children by `flecs_spawner_instantiate`, before it copies the prefab child's DontFragment values.
- **Root cause:**
  - `flecs_instantiate_children` turns each `AUTO_OVERRIDE|C` id of the prefab child's type into C in the instance child's type (src/addons/prefab/instantiate.c 197-208), and `flecs_prefab_spawner_build_type` does the same for Parent children (tree_spawner.c 33-42).
  - The `AUTO_OVERRIDE|C` record has no trait flags, so nothing filters a DontFragment C, and `flecs_table_init` asserts that a table type cannot contain DontFragment components (src/storage/table.c 249-259).
  - On the prefab itself, `flecs_instantiate_override_dont_fragment` (instantiate.c 370-391) handles the id, which is why the control passes.
- **Test:** `prefab_child_auto_override_dont_fragment.c` (ChildOf child) and `prefab_parent_child_auto_override_dont_fragment.c` (Parent child): v4.2.0 both abort, `fatal: flecs.c: 41518: assert(!(id_cr->flags & EcsIdDontFragment)): table type cannot contain DontFragment components (INVALID_OPERATION)`, then the handler's FAIL, rc=1; patched both rc=0 (one child, which owns Defense {50}).
- **Extra check** `fixes/checks/F45_auto_override_dont_fragment_inherit.c`: the component also has the Inherit trait; both hierarchies, two instances each. Every instance child must own a copy of 50, and a set on the copy must leave the prefab child's value alone. v4.2.0 aborts; patched OK. With Inherit, a Parent child's instance child, which is `IsA` the prefab child, would only inherit the value without the spawner's new call.
- **Suites:** core, query, addons, collections and cpp with this patch: unchanged from v4.2.0 (core 3870 / 0, query 4798 / 6, addons 643 / 0, collections 97 / 0, cpp 1919 / 0; see "flecs's suites").
- **Risk:** low.
  - Only prefab children with a DontFragment auto override take the new path.
  - Parent hierarchies pay one more flag test per spawned child per instantiation.
  - The instance child gets the component through `ecs_add_id` and then the copy (OnAdd, then OnSet), as an instance of a prefab with the same auto override does.

### F46. During an order_by iteration, a deleted table's slice is reused by a new table, and its entities and freed arrays are returned

- **Change:** when a table leaves the cache of an order_by query, the cache clears the sorted slices that refer to it. Patch: `fixes/F46.diff` (src/query/cache/order_by.c, group.c, cache_iter.c, change_detection.c, cache.h; src/query/engine/eval_iter.c).
  - `flecs_query_cache_remove_table` (the table was deleted or no longer matches) calls a new `flecs_query_cache_remove_table_slices`, which zeroes those slices: no table, no arrays.
  - The iterator skips a cleared slice before it reads its table, and the change detection of the current result (`flecs_query_change_detection`, `ecs_iter_changed`) leaves a cleared slice alone; `ecs_iter_changed` reports it as changed (its table is gone).
  - The next iterator rebuilds the slices, since the removal changed the cache's `match_count`.
- **Root cause:**
  - An order_by query iterates `cache->table_slices`, struct copies of the cache's matches (the table pointer, `_trs`, columns, `_ids`, `_sources`, `_monitor`) made when the iterator is created (src/query/cache/order_by.c 195-205).
  - Deleting a table during the iteration removes its match and frees its arrays (group.c 302-326, match.c 18-67). `flecs_table_fini` returns the table's slot to the table store, and the next table created gets the same memory (src/storage/table.c 1268-1336).
  - The iterator skips only a slice whose table has no entities, and syncs that slice's freed monitor while it does (src/query/cache/cache_iter.c 81-99). Otherwise it returns the slice's rows of whatever table is now in that memory, with the slice's freed arrays (192-222).
- **Test:** `query_order_by_reused_table_slot.c`: v4.2.0 aborts in the debug build, `fatal: flecs.c: 85074: assert(columns[i] == expected): it->columns[0]=-27088 does not match expected 1` (in `flecs_iter_assert_columns`), and the handler prints FAIL, rc=1; patched rc=0 ("results: 2; [TagB] took the freed table's memory: 1": the iterator skips the cleared slice).
- **Memory checks** with AddressSanitizer and `FLECS_USE_OS_ALLOC`, so every block is its own malloc (`bin/asan-build.sh`, `bin/asan-run.sh`):
  - the finding's test: v4.2.0 `heap-use-after-free` (a read) in `flecs_query_cache_init_mapped_fields`; patched clean, rc=0;
  - `fixes/checks/F46_order_by_deleted_table_skip.c`, the form without a new table, calling `ecs_iter_changed` on every result: it prints OK on both builds without ASan; under ASan v4.2.0 has a `heap-use-after-free` (a write) in `flecs_query_sync_match_monitor`, and the patched build is clean (OK).
- **Suites:** core, query, addons, collections and cpp with this patch: unchanged from v4.2.0 (core 3870 / 0, query 4798 / 6, addons 643 / 0, collections 97 / 0, cpp 1919 / 0; see "flecs's suites"). query includes the OrderBy, OrderByEntireTable and ChangeDetection suites.
- **Risk:** low.
  - Removing a table from an order_by cache walks the cache's slices once. Tables are removed when they are deleted or stop matching.
  - Not covered: a rematch that keeps the table can free a match's `_ids` or `_sources` array (match.c 117-120, 139-142) or wildcard matches that a slice still points at, during an iteration.
  - Not covered: deleting the table of the current result from its own iteration, which other paths read as well (F30's class).

### F47. A multi-threaded order_by system: debug builds abort, release builds race

- **Change:** the code, not only the documentation: the pipeline sorts the queries once, before the workers start. Patch: `fixes/F47.diff` (src/addons/pipeline/pipeline.c, src/query/cache/order_by.c, cache_iter.c, cache.h).
  - Before a multithreaded op signals the workers, and before `ecs_readonly_begin`, `flecs_run_pipeline` calls a new `flecs_query_sort_for_workers` for every system of the op. For an order_by query, it sorts on the main thread and does what creating an iterator does after sorting (`prev_match_count`).
  - An iterator created while the world is in multithreaded mode doesn't sort; it uses those slices and leaves `prev_match_count` alone.
  - In debug builds, a worker thread that creates an iterator for an order_by query whose cache matched or unmatched tables since its last sort still gets the UNSUPPORTED assert, now saying that only the queries of multithreaded systems are sorted before the workers start.
- **Why this and not only the documentation:**
  - The documentation alone would leave the debug abort and the release data race (undefined behavior), unless system creation also refused the combination. Systems.md "Threading" says staging "makes it safe for multiple threads to iterate the same world without taking locks", and nothing says order_by is excluded.
  - The pipeline already has the right place for the sort. Between two ops only the main thread runs, and the world is merged. During a multithreaded op structural changes are deferred, so slices computed when the op starts stay valid until it ends.
  - The sort runs once per op instead of once per worker.
  - If flecs prefers to keep the combination unsupported, the documentation (Systems.md "Threading", Queries.md "Sorting") should say so, and `ecs_system_init` should reject `multi_threaded` with an order_by query in every build mode, since a release build has no assert.
- **Root cause:**
  - Each stage creates its own iterator for the system's query (src/addons/system/system.c 80-81). The main thread runs stage 0 while the workers run the others (src/addons/pipeline/pipeline.c 626-638).
  - Creating the iterator runs `flecs_query_cache_iter_init` (src/query/cache/cache_iter.c 11-37), which for an order_by query calls `flecs_query_cache_sort_tables` (order_by.c 228-321). That sorts each changed table in place, rebuilds the slice vector (215-225) and increments `match_count` (317).
  - The match monitors that decide whether a table changed are synced only after the table is iterated (src/query/engine/eval_iter.c 217-234), so every stage sees the table as changed and sorts it.
  - Debug builds stop at the UNSUPPORTED assert of `flecs_query_cache_build_sorted_table_range` (order_by.c 87-88). Release builds sort the same table on several threads at once.
- **Test:** `workers_order_by_sort_race.c` (debug build): v4.2.0 aborts, `fatal: flecs.c: 79891: assert(!(world->flags & EcsWorldMultiThreaded)): cannot sort query in multithreaded mode (UNSUPPORTED)`, then "FAIL: signal 6 during the frame", rc=1; patched rc=0 ("system runs: 2; compares during the frame: 448; two threads sorting at once: 0; table intact: 1"; the main thread sorts, and the test's 2-second rendezvous times out).
- **Release build with ThreadSanitizer** (`-DNDEBUG -fsanitize=thread`; `bin/tsan-build.sh`, `bin/tsan-run.sh`, `bin/tsan-pairs.py`), the same test:
  - v4.2.0, 2 runs: "two threads sorting at once: 1", FAIL, and 19 race reports in each. 18 of them have an access in `flecs_query_cache_build_sorted_tables`; others are in `flecs_query_cache_sort_tables` (the `match_count` increment), the lazy monitor allocation (`flecs_query_get_match_monitor`) and `flecs_table_get_dirty_state`.
  - Patched, 3 runs: "two threads sorting at once: 0; table intact: 1" each, and no report in a sort, slice or monitor-allocation function.
  - The reports left (1, 1 and 6 per run) are not about sorting: statistics counters that every worker increments without atomics (`q->eval_count` in `flecs_query_iter`, the world's `info` counters), the worker loop's read of `world->flags` against `ecs_frame_begin`, and F33's monitor sync. "Everything together" has the run with every patch.
- **Extra check** `fixes/checks/F47_mt_order_by_frames.c`: 4 threads, 300 entities in 3 tables, 20 frames, with new values and table moves between frames. In every frame each entity must be seen once and each worker must see its rows in ascending order; a single-threaded order_by system is the control. v4.2.0 aborts at the assert; patched OK.
- **Suites:** core, query, addons, collections and cpp with this patch: unchanged from v4.2.0 (core 3870 / 0, query 4798 / 6, addons 643 / 0, collections 97 / 0, cpp 1919 / 0; see "flecs's suites"). addons includes the MultiThread and MultiThreadStaging suites; query includes OrderBy.
- **Risk:**
  - The order of a multithreaded order_by system is computed when its op starts, not when each worker creates its iterator. Values that other systems of the same op write during the op don't change it; those systems run at the same time as it, so nothing orders them before it anyway.
  - An order_by query that isn't a query of the op's systems, iterated on a worker thread, isn't sorted there. If its cache changed since its last iteration, debug builds assert as before; release builds iterate the slices of its last sort.
  - Every op of multithreaded systems calls `flecs_query_sort_for_workers` once per system: a cache lookup, and the sort for order_by queries, which the stages did before.

## Findings without a fix

Each of these has its section above, with the code path and what a fix would need.

- **F9** (a queued set written in place is lost when the component goes away before the merge). The in-place write is intended: flecs's own tests assert it, for example `Commands.defer_set` ("set will not be deferred if the component exists").
  - Always queueing the value turns the finding's tests green, but breaks 10 of flecs's tests.
  - Keeping the in-place write and fixing the loss needs a new command state, handled in both the batched and the unbatched merge.
  - It is a design decision, or a documentation change: Manual.md says queued changes become visible at the merge.
- **F13** (the generation wraps after 2^16 recycles). The 16-bit generation is part of the public id layout, and any width wraps. The documentation should say that a stale handle can test alive again after 65,536 recycles of its id.
- **F14** (`on_add` hooks don't see the component on the entity). Hooks run inside `flecs_table_move`, before the entity's record points at the new table.
  - Making the entity visible to the hook needs a two-pass move: data first, then hooks, after the record is updated. `on_remove` hooks must keep seeing the old state.
  - The documentation says nothing in words. It could say that the hook must use its iterator.
- **F28** (instance children outside the active entity range). flecs's own test `World.range_prefab_spawn_deferred_after_range_switch` requires instance children next to their instance, outside the active range. The change the finding's test asks for breaks it, so the documentation of ranges should change instead.
- **F30** (a table leaving the cache during an iteration makes the iterator skip another one). The cache iterator walks vectors by index and holds pointers that calls made during the iteration move or free. There is no small fix. A fix needs one of:
  - cache changes deferred while a cached query is iterated;
  - iterators that resynchronize, with order-preserving removals;
  - a documented rule that such calls must be deferred during a C iteration.
- **F35** (cascade regrouping during an iteration returns a table twice, or frees the group being iterated). The same design question as F30, for groups.
- **F37** (a system whose commands reorder the phases makes the pipeline skip systems in that frame).
  - The tried fix resumed at the first system that had not run yet. It broke 9 of flecs's Pipeline tests, which require a system that joins the schedule mid-frame behind the current position to wait for the next frame.
  - Telling the two cases apart needs per-system pending state carried across rebuilds, readable by the worker threads.
  - It is a redesign of the resume protocol and a decision for flecs.
