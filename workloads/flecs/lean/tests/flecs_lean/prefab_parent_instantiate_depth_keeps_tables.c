/* Prediction F58: instantiating a prefab with Parent-storage children for
 * an instance at depth 6 or more (FLECS_TREE_SPAWNER_DEPTH_CACHE_SIZE)
 * keeps the instance children's tables alive for good; deleting the prefab
 * afterwards aborts in a debug build ("cannot delete component ...: tables
 * are keeping it alive (likely because of used prefab)"), and in a release
 * build the table stays.
 *
 *   base = prefab; c = ecs_new_w_parent(base) with tag Foo
 *   control: i = ecs_new_w_parent(root) (depth 1); IsA base;
 *            ecs_delete(i); ecs_delete(base)           works
 *   prediction: a chain of 7 Parent ancestors, i at depth 8; IsA base;
 *            ecs_delete(i); ecs_delete(base)           abort
 *
 * flecs_spawner_instantiate (addons/prefab/tree_spawner.c 226-349) takes
 * the spawner's vector for the instance's depth from the cache
 * spawner->data[depth] when depth < FLECS_TREE_SPAWNER_DEPTH_CACHE_SIZE
 * (6), else a temporary vector (246-251). flecs_spawner_transpose_depth
 * (120-149) fills it and calls flecs_table_keep on each child table (148).
 * The cached vectors' tables are released by EcsTreeSpawner_free
 * (prefab.c 10-27, through flecs_tree_spawner_fini when the prefab is
 * deleted); the temporary vector is freed without a release (348-350).
 * When the prefab is deleted its child c goes, and the cleanup of (IsA, c)
 * finds that table kept (flecs_component_release_tables,
 * storage/component_index.c 753-776); with force_delete set by ecs_delete
 * (entity.c 1356-1365) on_delete.c 729-735 asserts
 * ECS_INVALID_OPERATION. A release build leaves the table, with
 * (IsA, c) for a dead c, in the store.
 *
 * Documented: HierarchiesManual.md ("Prefab instantiation works with both
 * storages"); PrefabsManual.md (prefab hierarchies); deleting a prefab
 * whose instances are gone (flecs's own
 * NonFragmentingChildOf_delete_instantiated_prefab_non_fragmenting_child,
 * the depth-0 form). An abort confirms (the handler prints FAIL and exits
 * 1); in a release build, a table left over that the control does not
 * leave. main returns 0 when both worlds delete the prefab and leave the
 * same number of tables. */
#include "flecs.h"
#include <stdio.h>
#include <stdlib.h>
#include <signal.h>

static int stage; /* 0 control, 1 prediction */

static void on_signal(int sig) {
    if (stage == 1) {
        printf("FAIL: signal %d deleting the prefab after an instance at "
            "depth 8 was instantiated and deleted\n", sig);
    } else {
        printf("INCONCLUSIVE: signal %d in the control\n", sig);
    }
    fflush(stdout);
    _Exit(stage == 1 ? 1 : 2);
}

/* Returns the tables left over after the prefab is deleted and empty tables
 * are cleaned up, relative to the count before the instantiation. */
static int run(int ancestors) {
    ecs_world_t *world = ecs_mini();
    ECS_TAG(world, Foo);

    ecs_entity_t base = ecs_new_w_id(world, EcsPrefab);
    ecs_entity_t c = ecs_new_w_parent(world, base, NULL);
    ecs_add(world, c, Foo);

    ecs_entity_t p = ecs_new(world);
    for (int k = 1; k < ancestors; k ++) {
        p = ecs_new_w_parent(world, p, NULL);
    }
    ecs_entity_t i = ecs_new_w_parent(world, p, NULL);

    ecs_delete_empty_tables(world, &(ecs_delete_empty_tables_desc_t){
        .delete_generation = 1 });
    ecs_delete_empty_tables(world, &(ecs_delete_empty_tables_desc_t){
        .delete_generation = 1 });
    int before = ecs_get_world_info(world)->table_count;

    ecs_add_pair(world, i, EcsIsA, base);
    ecs_entities_t children = ecs_get_ordered_children(world, i);
    int ok = children.count == 1 && ecs_has(world, children.ids[0], Foo) &&
        ecs_has_pair(world, children.ids[0], EcsIsA, c);

    ecs_delete(world, i);
    ecs_delete(world, base);
    int deleted = !ecs_is_alive(world, base) && !ecs_is_alive(world, c);

    ecs_delete_empty_tables(world, &(ecs_delete_empty_tables_desc_t){
        .delete_generation = 1 });
    ecs_delete_empty_tables(world, &(ecs_delete_empty_tables_desc_t){
        .delete_generation = 1 });
    int after = ecs_get_world_info(world)->table_count;
    printf("%s: instance at depth %d; instance child as expected %d; prefab "
        "deleted %d; tables %d before the instantiation, %d after the "
        "cleanup\n", stage ? "prediction" : "control", ancestors, ok,
        deleted, before, after);
    ecs_fini(world);
    if (!ok || !deleted) {
        printf("INCONCLUSIVE: the %s did not go as set up\n",
            stage ? "prediction" : "control");
        exit(2);
    }
    return after - before;
}

int main(void) {
    signal(SIGABRT, on_signal);
    signal(SIGSEGV, on_signal);
    signal(SIGBUS, on_signal);

    stage = 0;
    int left0 = run(1);
    stage = 1;
    int left1 = run(8);
    printf("tables left over: control %d, prediction %d\n", left0, left1);
    if (left1 > left0) {
        printf("FAIL: the deep instantiation left %d table(s) that no "
            "delete or cleanup can free\n", left1 - left0);
        return 1;
    }
    return 0;
}
