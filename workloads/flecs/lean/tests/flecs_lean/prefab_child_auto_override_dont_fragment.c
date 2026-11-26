/* Prediction F45: auto-overriding a DontFragment component on a prefab
 * child makes the prefab's instantiation abort on an internal assert, in
 * both hierarchy storages. On the prefab itself the auto override works.
 *
 *   Defense: DontFragment
 *   control: P0 prefab, Defense {50}, ecs_auto_override(P0, Defense);
 *            inst0 = IsA P0: inst0 owns Defense {50}
 *   P: prefab; child = ChildOf P (or Parent P: FLECS_LEAN_PARENT_CHILD),
 *      Defense {50}, ecs_auto_override(child, Defense)
 *   inst = IsA P                 abort: "table type cannot contain
 *                                DontFragment components"
 *
 * ecs_auto_override adds `ECS_AUTO_OVERRIDE | Defense` to the child's type.
 * Instantiating the child turns that id into the plain id Defense in the
 * instance child's table type: flecs_instantiate_children
 * (addons/prefab/instantiate.c 191-202, flecs_child_type_insert) for a
 * ChildOf child, flecs_prefab_spawner_build_type (tree_spawner.c 33-42) for
 * a Parent child. The record of `ECS_AUTO_OVERRIDE | Defense` has no trait
 * flags (flecs_component_get_flags_intern, storage/component_index.c
 * 287-291), so nothing filters it, and flecs_table_init asserts that a
 * table type has no DontFragment component (storage/table.c 249-259). For
 * the prefab itself the override goes through
 * flecs_instantiate_override_dont_fragment (instantiate.c 370-391), which
 * adds the component with ecs_add_id.
 *
 * Documented: PrefabsManual.md "Auto Overriding" (a component flagged "to be
 * always overridden on instantiation") and "Prefab Hierarchies";
 * ComponentTraits.md "DontFragment trait"; Manual.md "Error handling". An
 * abort confirms the prediction: the handler prints FAIL and exits 1. main
 * returns 0 when the instance child owns Defense {50}. This file tests a
 * ChildOf child; prefab_parent_child_auto_override_dont_fragment.c includes
 * it with FLECS_LEAN_PARENT_CHILD set, for a Parent child. */
#include "flecs.h"
#include <stdio.h>
#include <stdlib.h>
#include <signal.h>

#ifndef FLECS_LEAN_PARENT_CHILD
#define FLECS_LEAN_PARENT_CHILD 0
#endif

typedef struct { int value; } Defense;

static void on_abort(int sig) {
    (void)sig;
    printf("FAIL: aborted while instantiating a prefab whose child "
        "auto-overrides a DontFragment component\n");
    fflush(stdout);
    _Exit(1);
}

int main(void) {
    int parent_hierarchy = FLECS_LEAN_PARENT_CHILD;

    ecs_world_t *world = ecs_mini();
    ECS_COMPONENT(world, Defense);
    ecs_add_id(world, ecs_id(Defense), EcsDontFragment);

    /* control: the auto override on the prefab itself */
    ecs_entity_t P0 = ecs_new_w_id(world, EcsPrefab);
    ecs_set(world, P0, Defense, {50});
    ecs_auto_override(world, P0, Defense);
    ecs_entity_t inst0 = ecs_new_w_pair(world, EcsIsA, P0);
    const Defense *d0 = ecs_get(world, inst0, Defense);
    if (!ecs_owns(world, inst0, Defense) || !d0 || d0->value != 50) {
        printf("INCONCLUSIVE: the instance of P0 does not own Defense {50}\n");
        return 2;
    }

    ecs_entity_t P = ecs_new_w_id(world, EcsPrefab);
    ecs_entity_t child = parent_hierarchy
        ? ecs_new_w_parent(world, P, NULL)
        : ecs_new_w_pair(world, EcsChildOf, P);
    ecs_set(world, child, Defense, {50});
    ecs_auto_override(world, child, Defense);

    printf("%s child: instantiating\n", parent_hierarchy ? "Parent" : "ChildOf");
    fflush(stdout);
    signal(SIGABRT, on_abort);
    ecs_entity_t inst = ecs_new_w_pair(world, EcsIsA, P);
    signal(SIGABRT, SIG_DFL);

    ecs_entity_t ichild = 0;
    int n = 0;
    ecs_iter_t it = ecs_children(world, inst);
    while (ecs_children_next(&it)) {
        for (int i = 0; i < it.count; i ++) { ichild = it.entities[i]; n ++; }
    }

    int failed = 0;
    const Defense *d = ichild ? ecs_get(world, ichild, Defense) : NULL;
    if (n != 1 || !ecs_owns(world, ichild, Defense) || !d || d->value != 50) {
        printf("FAIL: the instance has %d children; the child owns Defense: %d "
            "(value %d)\n", n, ichild ? ecs_owns(world, ichild, Defense) : 0,
            d ? d->value : -1);
        failed = 1;
    }
    ecs_fini(world);
    return failed;
}
