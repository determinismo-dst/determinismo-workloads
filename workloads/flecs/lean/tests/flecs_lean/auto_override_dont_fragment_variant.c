/* Prediction F38: an instance of a prefab variant does not own a
 * DontFragment component that the variant's base auto-overrides; it inherits
 * it instead.
 *
 *   Defense: DontFragment, (OnInstantiate, Inherit)
 *   SpaceShip: prefab, Defense = 50, auto override Defense
 *   Freighter: prefab, IsA SpaceShip          (Freighter owns Defense: its
 *                                              own instantiation overrides it)
 *   inst = IsA Freighter                       ecs_owns(inst, Defense): false
 *
 * For a fragmenting component the table graph handles auto overrides through
 * every IsA level: flecs_add_overrides_for_base (storage/table_graph.c
 * 718-791) adds each AUTO_OVERRIDE id of the base's type to the instance's
 * type and recurses into the base's own IsA targets (780-789). For a
 * DontFragment component it adds nothing and only flags the table that holds
 * the AUTO_OVERRIDE id (EcsTableOverrideDontFragment, 739-746); the override
 * is then done by flecs_instantiate (addons/prefab/instantiate.c 393-415),
 * whose flecs_instantiate_override_dont_fragment (370-391) reads only the
 * direct base's table. Freighter's table has no AUTO_OVERRIDE id, so inst
 * gets nothing; flecs_instantiate_dont_fragment (301-368) skips Inherit
 * components of a base the instance has an IsA to. inst inherits Freighter's
 * Defense.
 *
 * Controls: an instance of SpaceShip owns Defense (one level); with Defense a
 * plain (table) component, inst owns it.
 *
 * Documented: PrefabsManual.md "Auto Overriding" (a component flagged "to be
 * always overridden on instantiation"; `ecs_owns(world, inst, Defense); //
 * true`) and "Prefab Variants" (prefabs inherit from each other);
 * ComponentTraits.md "DontFragment trait" (the same storage as Sparse) and
 * "Sparse trait" ("ECS operations and queries work as expected with sparse
 * components"). main returns 0 when inst owns Defense, with the value 50. */
#include "flecs.h"
#include <stdio.h>
#include <stdlib.h>

typedef struct { int value; } Defense;
typedef struct { int value; } Armor;

int main(void) {
    ecs_world_t *world = ecs_mini();
    ECS_COMPONENT(world, Defense);
    ECS_COMPONENT(world, Armor);
    ecs_add_id(world, ecs_id(Defense), EcsDontFragment);
    ecs_add_pair(world, ecs_id(Defense), EcsOnInstantiate, EcsInherit);
    ecs_add_pair(world, ecs_id(Armor), EcsOnInstantiate, EcsInherit);

    ecs_entity_t ship = ecs_new_w_id(world, EcsPrefab);
    ecs_set(world, ship, Defense, {50});
    ecs_auto_override(world, ship, Defense);
    ecs_set(world, ship, Armor, {50});
    ecs_auto_override(world, ship, Armor);

    ecs_entity_t freighter = ecs_new_w_id(world, EcsPrefab);
    ecs_add_pair(world, freighter, EcsIsA, ship);

    ecs_entity_t inst1 = ecs_new_w_pair(world, EcsIsA, ship);
    ecs_entity_t inst = ecs_new_w_pair(world, EcsIsA, freighter);

    int failed = 0;
    if (!ecs_owns(world, inst1, Defense) || !ecs_owns(world, inst, Armor)) {
        printf("INCONCLUSIVE: a control does not own its component "
            "(one level: %d, table component through the variant: %d)\n",
            ecs_owns(world, inst1, Defense), ecs_owns(world, inst, Armor));
        failed = 2;
    } else {
        const Defense *d = ecs_get(world, inst, Defense);
        printf("inst owns Defense: %d; value %d\n",
            ecs_owns(world, inst, Defense), d ? d->value : -1);
        if (!ecs_owns(world, inst, Defense)) {
            printf("FAIL: the instance of the variant does not own Defense\n");
            failed = 1;
        } else if (!d || d->value != 50) {
            printf("FAIL: the instance's Defense is not 50\n");
            failed = 1;
        }
    }
    ecs_fini(world);
    return failed;
}
