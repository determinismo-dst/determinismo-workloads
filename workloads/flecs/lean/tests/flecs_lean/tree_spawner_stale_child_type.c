/* Prediction F39 (first form): with a Parent hierarchy, a component added to
 * a prefab child after the prefab was first instantiated is missing from the
 * children of later instances.
 *
 * A prefab whose children use the Parent component is instantiated through a
 * TreeSpawner (addons/prefab/instantiate.c 424-440). The first instantiation
 * builds it (flecs_prefab_spawner_build, tree_spawner.c 199-224): for every
 * prefab child, the table its instance children go to, computed from the
 * child's table at that moment (flecs_prefab_spawner_build_type, 10-60).
 * Later instantiations put each instance child straight into that cached
 * table (flecs_spawner_instantiate, 226-350). Nothing rebuilds the spawner
 * when a prefab child's components change; only changes to the set of
 * children are refused (flecs_tree_spawner_assert_not_instantiated,
 * 166-197, called from storage/non_fragmenting_childof.c 49, 75, 255).
 *
 * Program:
 *   prefab; child = ecs_new_w_parent(prefab) with Position {1, 2}
 *   i1 = IsA prefab                  (builds the spawner)
 *   ecs_set(child, Velocity, {3, 4}) (the prefab child changes)
 *   i2 = IsA prefab                  i2's child has no Velocity
 * Control: the same with a ChildOf hierarchy (ecs_new_w_pair(ChildOf,
 * prefab)), whose instantiation reads each child's current table
 * (instantiate.c 135-299): i2's child owns Velocity {3, 4}.
 *
 * Documented: ComponentTraits.md "OnInstantiate trait": the default is
 * "Copy, which means that the component is copied to the instance";
 * HierarchiesManual.md "Parent storage details": the TreeSpawner caches "the
 * structure and tables of the prefab hierarchy" as a performance measure,
 * with Parent and ChildOf hierarchies otherwise alike. main returns 0 when
 * i2's child has Velocity {3, 4} in both hierarchies. */
#include "flecs.h"
#include <stdio.h>
#include <stdlib.h>

typedef struct { float x, y; } Position;
typedef struct { float x, y; } Velocity;

static ecs_entity_t only_child(ecs_world_t *world, ecs_entity_t parent) {
    ecs_entity_t result = 0;
    int n = 0;
    ecs_iter_t it = ecs_children(world, parent);
    while (ecs_children_next(&it)) {
        for (int i = 0; i < it.count; i ++) { result = it.entities[i]; n ++; }
    }
    return n == 1 ? result : 0;
}

/* 1: Velocity present with {3, 4}; 0: missing or wrong; -1: setup failed */
static int run(int parent_hierarchy) {
    ecs_world_t *world = ecs_mini();
    ECS_COMPONENT(world, Position);
    ECS_COMPONENT(world, Velocity);

    ecs_entity_t prefab = ecs_new_w_id(world, EcsPrefab);
    ecs_entity_t child = parent_hierarchy
        ? ecs_new_w_parent(world, prefab, NULL)
        : ecs_new_w_pair(world, EcsChildOf, prefab);
    ecs_set(world, child, Position, {1, 2});

    ecs_entity_t i1 = ecs_new_w_pair(world, EcsIsA, prefab);
    ecs_entity_t c1 = only_child(world, i1);
    if (!c1 || !ecs_has(world, c1, Position)) {
        printf("%s: setup: i1's child missing or without Position\n",
            parent_hierarchy ? "Parent" : "ChildOf");
        ecs_fini(world);
        return -1;
    }

    ecs_set(world, child, Velocity, {3, 4});

    ecs_entity_t i2 = ecs_new_w_pair(world, EcsIsA, prefab);
    ecs_entity_t c2 = only_child(world, i2);
    int ok = -1;
    if (c2) {
        const Velocity *v = ecs_get(world, c2, Velocity);
        printf("%s: i2's child has Velocity: %d (owned %d)%s\n",
            parent_hierarchy ? "Parent" : "ChildOf", v != NULL,
            ecs_owns(world, c2, Velocity), v ? "" : "");
        ok = v && v->x == 3 && v->y == 4;
    }
    ecs_fini(world);
    return ok;
}

int main(void) {
    int control = run(0);
    int parent = run(1);
    if (control != 1 || parent == -1) {
        printf("INCONCLUSIVE: the ChildOf control (%d) or the setup failed\n",
            control);
        return 2;
    }
    if (parent != 1) {
        printf("FAIL: with a Parent hierarchy, i2's child lacks the Velocity its "
            "prefab child has\n");
        return 1;
    }
    return 0;
}
