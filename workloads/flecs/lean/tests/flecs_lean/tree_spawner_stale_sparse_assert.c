/* Prediction F39 (second form): with a Parent hierarchy, a Sparse component
 * added to a prefab child after the prefab was first instantiated makes the
 * next instantiation abort on an internal assert.
 *
 * As in tree_spawner_stale_child_type.c, later instances' children go to the
 * table the TreeSpawner cached at the first instantiation
 * (addons/prefab/tree_spawner.c 199-350). flecs_spawner_instantiate then
 * calls flecs_instantiate_sparse (instantiate.c 73-133) with the prefab
 * child's current table: for the Sparse component it gets the instance
 * child's value with flecs_sparse_get and asserts it exists (122-124:
 * `ecs_assert(dst_ptr != NULL, ECS_INTERNAL_ERROR, NULL)`); the cached table
 * does not have the component, so the instance child has none. A release
 * build copies into NULL.
 *
 * Program:
 *   Mass: Sparse (fragmenting)
 *   prefab; child = ecs_new_w_parent(prefab) with Position {1, 2}
 *   i1 = IsA prefab                  (builds the spawner)
 *   ecs_set(child, Mass, {5})
 *   i2 = IsA prefab                  abort (instantiate.c 123)
 * With a ChildOf hierarchy (control, run first) i2's child gets Mass {5}.
 *
 * Documented: ComponentTraits.md "OnInstantiate trait" (Copy) and "Sparse
 * trait" ("ECS operations and queries work as expected with sparse
 * components"); Manual.md "Error handling". An abort confirms the
 * prediction: the handler prints FAIL and exits 1. main returns 0 when i2's
 * child has Mass {5}. */
#include "flecs.h"
#include <stdio.h>
#include <stdlib.h>
#include <signal.h>

typedef struct { float x, y; } Position;
typedef struct { float value; } Mass;

static void on_abort(int sig) {
    (void)sig;
    printf("FAIL: aborted while instantiating the prefab a second time\n");
    fflush(stdout);
    _Exit(1);
}

static ecs_entity_t only_child(ecs_world_t *world, ecs_entity_t parent) {
    ecs_entity_t result = 0;
    int n = 0;
    ecs_iter_t it = ecs_children(world, parent);
    while (ecs_children_next(&it)) {
        for (int i = 0; i < it.count; i ++) { result = it.entities[i]; n ++; }
    }
    return n == 1 ? result : 0;
}

static int run(int parent_hierarchy) {
    ecs_world_t *world = ecs_mini();
    ECS_COMPONENT(world, Position);
    ECS_COMPONENT(world, Mass);
    ecs_add_id(world, ecs_id(Mass), EcsSparse);

    ecs_entity_t prefab = ecs_new_w_id(world, EcsPrefab);
    ecs_entity_t child = parent_hierarchy
        ? ecs_new_w_parent(world, prefab, NULL)
        : ecs_new_w_pair(world, EcsChildOf, prefab);
    ecs_set(world, child, Position, {1, 2});

    ecs_entity_t i1 = ecs_new_w_pair(world, EcsIsA, prefab);
    if (!only_child(world, i1)) {
        ecs_fini(world);
        return -1;
    }

    ecs_set(world, child, Mass, {5});

    if (parent_hierarchy) {
        signal(SIGABRT, on_abort);
    }
    ecs_entity_t i2 = ecs_new_w_pair(world, EcsIsA, prefab);
    signal(SIGABRT, SIG_DFL);
    ecs_entity_t c2 = only_child(world, i2);
    int ok = 0;
    if (c2) {
        const Mass *m = ecs_get(world, c2, Mass);
        ok = m && m->value == 5;
    }
    ecs_fini(world);
    return ok;
}

int main(void) {
    int control = run(0);
    if (control != 1) {
        printf("INCONCLUSIVE: the ChildOf control (%d) failed\n", control);
        return 2;
    }
    int parent = run(1);
    if (parent != 1) {
        printf("FAIL: with a Parent hierarchy, i2's child lacks Mass {5} (%d)\n",
            parent);
        return 1;
    }
    return 0;
}
