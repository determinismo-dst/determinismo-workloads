/* Prediction F28: with an entity range active, instantiating a prefab that
 * has a child creates the instance child outside the range: the instance
 * child's id is the instance's id plus the prefab child's offset from the
 * prefab (flecs_instantiate_alloc_child_id, instantiate.c 45-71), which is
 * made alive directly (flecs_entities_make_alive + flecs_entities_ensure)
 * instead of being issued by the active range. An instance created before
 * the range was set gets a child next to it, outside the range (an instance
 * at the range's last id gets max + 1, and nothing asserts).
 *
 * This is the function behind F21 (a deleted handle made alive again); here
 * the same allocation bypasses the active range.
 *
 * Documented: EntitiesComponents.md "Ranges": "While a range is active, both
 * newly issued and recycled ids fall within the range"; "When the active
 * range runs out of available ids, operations that create new entities will
 * assert" (also entity_ranges.h 54-62). */
#include "flecs.h"
#include <stdio.h>

int main(void) {
    ecs_world_t *world = ecs_mini();

    ecs_entity_t prefab = ecs_new_w_id(world, EcsPrefab);
    ecs_entity_t pchild = ecs_new_w_pair(world, EcsChildOf, prefab);
    if ((uint32_t)pchild != (uint32_t)prefab + 1) {
        printf("INCONCLUSIVE: the prefab child is not at offset 1\n");
        return 2;
    }

    ecs_entity_t b = ecs_new(world);   /* created before the range */

    /* A range with room for new ids */
    const ecs_entity_range_t *range = ecs_entity_range_new(world, 5000, 5010);
    ecs_entity_range_set(world, range);
    ecs_entity_t a = ecs_new(world);
    if ((uint32_t)a != 5000) {
        printf("INCONCLUSIVE: the range issued %u\n", (uint32_t)a);
        return 2;
    }

    ecs_add_pair(world, b, EcsIsA, prefab);   /* instantiates pchild under b:
                                               * a new entity, id b + 1 */

    int failed = 0, children = 0;
    ecs_iter_t it = ecs_children(world, b);
    while (ecs_children_next(&it)) {
        for (int i = 0; i < it.count; i ++) {
            uint32_t c = (uint32_t)it.entities[i];
            children ++;
            if (c < 5000 || c > 5001) {
                printf("FAIL: instance child %u is outside the active range [5000, 5010]\n", c);
                failed = 1;
            }
        }
    }
    if (!children) {
        printf("INCONCLUSIVE: no instance child was created\n");
        failed = 2;
    }

    ecs_fini(world);
    if (!failed) printf("OK\n");
    return failed;
}
