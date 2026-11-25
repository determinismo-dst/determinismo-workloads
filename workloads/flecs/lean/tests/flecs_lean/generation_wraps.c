/* Prediction: the generation of an entity id is 16 bits
 * (ECS_GENERATION_MASK, api_defines.h 333-335), so after 65536 delete/new
 * cycles of the same id the handle of the first, deleted incarnation is
 * alive again: ecs_is_alive() returns true for a deleted entity, and
 * operations on the stale handle act on the new entity.
 *
 * Documented: EntitiesComponents.md "Deletion" (recycled ids get a new
 * version "so that the Flecs API can tell whether an entity id is alive or
 * not"; ecs_add on the deleted handle "Fails, 500v0 is not alive") and
 * "Liveliness Checking" (ecs_is_alive(world, e1) is false after delete). */
#include "flecs.h"
#include <stdio.h>

int main(void) {
    ecs_world_t *world = ecs_mini();
    ecs_entity_t first = ecs_new(world);
    ecs_delete(world, first);

    ecs_entity_t cur = 0;
    for (int i = 0; i < 65536; i ++) {
        cur = ecs_new(world);                 /* recycles the same id */
        if ((uint32_t)cur != (uint32_t)first) {
            printf("SKIP: id not recycled\n");
            return 0;
        }
        if (i != 65535) ecs_delete(world, cur);
    }

    int failed = 0;
    if (ecs_is_alive(world, first)) {
        printf("FAIL: deleted handle %llu reports alive (current %llu)\n",
            (unsigned long long)first, (unsigned long long)cur);
        failed = 1;
    }
    ecs_fini(world);
    return failed;
}
