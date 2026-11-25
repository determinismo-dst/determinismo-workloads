/* Prediction F32: overriding a DontFragment component with the
 * (OnInstantiate, Inherit) trait constructs it instead of copying the
 * inherited value, when the instance inherits it through a base that
 * inherits it too.
 *
 *   base:  Position = {10, 20}
 *   mid:   (IsA, base)        inherits Position
 *   inst:  (IsA, mid)         ecs_get(inst, Position) == {10, 20}
 *   ecs_add(world, inst, Position)   -> inst owns {0, 0}, not {10, 20}
 *
 * Adding a Sparse or DontFragment component runs
 * flecs_component_sparse_insert (storage/sparse_storage.c 445-489), which
 * initializes the value with flecs_component_sparse_override (415-443): it
 * copies from the base that ecs_search_relation(..., EcsIsA, EcsUp) finds,
 * or constructs the component when none is found. For a DontFragment
 * component, flecs_table_search_relation_for_tgt (search.c 204-248) checks
 * the target's sparse set and stops (216-221); it does not follow the
 * target's own IsA pairs as it does for other components (222-232). mid
 * does not own Position, so no base is found.
 *
 * ecs_get and ecs_has use flecs_get_base_component
 * (addons/prefab/instantiate.c 485-555), which does follow them (531-538),
 * so before the add the instance has and reads {10, 20}.
 *
 * Documented: PrefabsManual.md "Component Overriding" (the override "is
 * initialized with the value from the prefab component"); ComponentTraits.md
 * "OnInstantiate trait" (an Inherit component "can be overridden manually by
 * adding the component to the instance ... the component is copied from the
 * base entity").
 *
 * Controls: the same chain with a fragmenting Sparse component, and a single
 * IsA level with DontFragment, copy the value. */
#include "flecs.h"
#include <stdio.h>
#include <stdlib.h>

typedef struct { float x, y; } Position;

/* 0: DontFragment, 2 levels; 1: Sparse, 2 levels; 2: DontFragment, 1 level */
static int run(int variant, float *x_out, float *y_out, int *had_before) {
    ecs_world_t *world = ecs_mini();
    ECS_COMPONENT(world, Position);
    ecs_add_id(world, ecs_id(Position), EcsSparse);
    ecs_add_pair(world, ecs_id(Position), EcsOnInstantiate, EcsInherit);
    if (variant != 1) {
        ecs_add_id(world, ecs_id(Position), EcsDontFragment);
    }

    ecs_entity_t base = ecs_new(world);
    ecs_set(world, base, Position, {10, 20});

    ecs_entity_t inst;
    if (variant == 2) {
        inst = ecs_new_w_pair(world, EcsIsA, base);
    } else {
        ecs_entity_t mid = ecs_new_w_pair(world, EcsIsA, base);
        if (ecs_owns(world, mid, Position)) {
            ecs_fini(world);
            return -1;  /* setup: mid must inherit, not own */
        }
        inst = ecs_new_w_pair(world, EcsIsA, mid);
    }

    const Position *p = ecs_get(world, inst, Position);
    *had_before = ecs_has(world, inst, Position) && p && p->x == 10 && p->y == 20
        && !ecs_owns(world, inst, Position);

    ecs_add(world, inst, Position);
    p = ecs_get(world, inst, Position);
    int owns = ecs_owns(world, inst, Position);
    *x_out = p ? p->x : -1;
    *y_out = p ? p->y : -1;
    ecs_fini(world);
    return owns;
}

int main(void) {
    int failed = 0;
    const char *names[] = { "DontFragment, 2 levels", "Sparse, 2 levels",
        "DontFragment, 1 level" };
    for (int v = 0; v < 3; v ++) {
        float x, y; int before;
        int owns = run(v, &x, &y, &before);
        if (owns < 0 || !before) {
            printf("INCONCLUSIVE: %s: setup did not hold\n", names[v]);
            return 2;
        }
        if (!owns || x != 10 || y != 20) {
            printf("%s: %s: after ecs_add the instance owns=%d Position = "
                "{%g, %g}, expected the inherited {10, 20}\n",
                v == 0 ? "FAIL" : "FAIL (control)", names[v], owns,
                (double)x, (double)y);
            failed = 1;
        }
    }
    return failed;
}
