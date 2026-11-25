/* Prediction F21: instantiating a prefab that has a child makes a deleted
 * entity handle alive again. The instance child gets the id
 * instance + (child - prefab), and when that id is not alive it is made alive
 * with the instance's generation (instantiate.c 45-71:
 * flecs_instantiate_alloc_child_id calls flecs_entities_make_alive and
 * flecs_entities_ensure on root_instance + prefab_offset). If that id belonged
 * to an entity deleted earlier, its old handle is alive again and now names
 * the instance's child. When the deleted id had been recycled more often than
 * the instance, its generation goes backwards.
 *
 * Documented: EntitiesComponents.md "Liveliness Checking" (a deleted entity
 * is not alive; the generation prevents a recycled id from matching an old
 * handle); PrefabsManual.md "Prefab Hierarchies" (children are copied to the
 * instance). */
#include "flecs.h"
#include <stdio.h>

int main(void) {
    ecs_world_t *world = ecs_mini();

    ecs_entity_t prefab = ecs_new_w_id(world, EcsPrefab);
    ecs_entity_t pchild = ecs_new_w_pair(world, EcsChildOf, prefab);
    ecs_add_id(world, pchild, EcsPrefab);

    ecs_entity_t inst = ecs_new(world);
    ecs_entity_t b = ecs_new(world);
    if ((uint32_t)pchild != (uint32_t)prefab + 1 || (uint32_t)b != (uint32_t)inst + 1) {
        printf("INCONCLUSIVE: ids are not consecutive\n");
        return 2;
    }

    ecs_delete(world, b);
    if (ecs_is_alive(world, b)) {
        printf("INCONCLUSIVE: b alive after delete\n");
        return 2;
    }

    ecs_add_pair(world, inst, EcsIsA, prefab);   /* instantiates pchild under inst */

    int failed = 0;
    if (ecs_is_alive(world, b)) {
        printf("FAIL: the deleted handle b is alive again (parent: %u)\n",
            (uint32_t)ecs_get_target(world, b, EcsChildOf, 0));
        failed = 1;
    }

    ecs_fini(world);
    return failed;
}
