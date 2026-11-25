/* Prediction: make_alive of an id that was deleted while its range was not
 * active leaves the id in that range's recycled list; switching back to the
 * range aborts (entity_ranges.c 129, "r->table == NULL"), and in a release
 * build the entity would stop being alive.
 *
 * Documented: EntitiesComponents.md "Manual Ids" (make_alive guarantees the
 * id is alive after the call; it may be used while the id is not in use) and
 * "Ranges" (each range keeps its own recycled ids; switching ranges is
 * allowed at any time). */
#include "flecs.h"
#include <stdio.h>

int main(void) {
    ecs_world_t *world = ecs_mini();

    const ecs_entity_range_t *a = ecs_entity_range_new(world, 5000, 6000);
    const ecs_entity_range_t *b = ecs_entity_range_new(world, 7000, 8000);

    ecs_entity_range_set(world, b);
    ecs_entity_t e = ecs_new(world);        /* 7000 */
    ecs_entity_range_set(world, a);
    ecs_delete(world, e);                   /* recycled into b's list */
    ecs_make_alive(world, e);               /* 7000 is not in use: allowed */

    int failed = 0;
    if (!ecs_is_alive(world, e)) { printf("FAIL: make_alive did not make e alive\n"); failed = 1; }

    ecs_entity_range_set(world, b);         /* predicted: aborts here */

    if (!ecs_is_alive(world, e)) { printf("FAIL: e no longer alive after switching ranges\n"); failed = 1; }
    ecs_entity_t n = ecs_new(world);
    if ((uint32_t)n == (uint32_t)e) {
        printf("FAIL: new entity reuses the id of alive entity e\n"); failed = 1;
    }
    ecs_fini(world);
    return failed;
}
