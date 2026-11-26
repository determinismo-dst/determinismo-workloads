/* Check for F45: a prefab child auto-overrides a DontFragment component that
 * has the (OnInstantiate, Inherit) trait, with ChildOf and with Parent
 * children, and two instances of each prefab (the second one reuses the tree
 * spawner). Every instance child must own its own copy of the prefab child's
 * value, and a set on the copy must not change the prefab child's value.
 * main returns 0 when that holds. */
#include "flecs.h"
#include <stdio.h>

typedef struct { int value; } Defense;

static ecs_entity_t only_child(ecs_world_t *world, ecs_entity_t parent, int *n) {
    ecs_entity_t c = 0;
    *n = 0;
    ecs_iter_t it = ecs_children(world, parent);
    while (ecs_children_next(&it)) {
        for (int i = 0; i < it.count; i ++) { c = it.entities[i]; (*n) ++; }
    }
    return c;
}

int main(void) {
    ecs_world_t *world = ecs_mini();
    ECS_COMPONENT(world, Defense);
    ecs_add_id(world, ecs_id(Defense), EcsDontFragment);
    ecs_add_pair(world, ecs_id(Defense), EcsOnInstantiate, EcsInherit);

    int failed = 0;
    for (int parent_hierarchy = 0; parent_hierarchy < 2; parent_hierarchy ++) {
        ecs_entity_t P = ecs_new_w_id(world, EcsPrefab);
        ecs_entity_t child = parent_hierarchy
            ? ecs_new_w_parent(world, P, NULL)
            : ecs_new_w_pair(world, EcsChildOf, P);
        ecs_set(world, child, Defense, {50});
        ecs_auto_override(world, child, Defense);

        for (int k = 0; k < 2; k ++) {
            ecs_entity_t inst = ecs_new_w_pair(world, EcsIsA, P);
            int n;
            ecs_entity_t ic = only_child(world, inst, &n);
            const Defense *d = ic ? ecs_get(world, ic, Defense) : NULL;
            int owns = ic ? ecs_owns(world, ic, Defense) : 0;
            printf("%s, instance %d: %d child(ren); owns Defense %d, value %d\n",
                parent_hierarchy ? "Parent" : "ChildOf", k + 1, n, owns,
                d ? d->value : -1);
            if (n != 1 || !owns || !d || d->value != 50) {
                failed = 1;
                continue;
            }
            ecs_set(world, ic, Defense, {7});
            const Defense *pd = ecs_get(world, child, Defense);
            if (!pd || pd->value != 50) {
                printf("  the set on the instance child changed the prefab "
                    "child's value\n");
                failed = 1;
            }
        }
    }

    if (failed) {
        printf("FAIL: an instance child does not own a copy of the "
            "auto-overridden DontFragment component\n");
    } else {
        printf("OK\n");
    }
    ecs_fini(world);
    return failed;
}
