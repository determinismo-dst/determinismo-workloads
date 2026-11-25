/* Prediction F23: a queued (ChildOf, p) whose parent p is deleted before the
 * merge, and whose id is then recycled by a new entity q, parents the child
 * to q at the merge instead of deleting it.
 *
 * The command stores the pair id, which keeps only the 32-bit target
 * (ecs_pair, api_defines.h 357-361). At the merge flecs_remove_invalid
 * (commands.c 893-942) checks the target with flecs_entities_is_valid, which
 * is true for the recycled id, so the pair is added and the child joins the
 * unrelated entity q.
 *
 * Documented: Manual.md "Deferred operations" ("Commands that parent an
 * entity to a deleted parent delete the child during the merge");
 * EntitiesComponents.md "Deleting Entities" (the version in the upper bits
 * tells a recycled id from the deleted entity). */
#include "flecs.h"
#include <stdio.h>

int main(void) {
    ecs_world_t *world = ecs_mini();

    ecs_entity_t p = ecs_new(world);
    ecs_entity_t c = ecs_new(world);

    ecs_world_t *stage = ecs_get_stage(world, 0);
    ecs_add_pair(stage, c, EcsChildOf, p);
    ecs_delete(world, p);
    ecs_entity_t q = ecs_new(world);              /* recycles p's id */
    if ((uint32_t)q != (uint32_t)p) {
        printf("INCONCLUSIVE: the id was not recycled\n");
        return 2;
    }
    ecs_merge(stage);

    int failed = 0;
    if (ecs_is_alive(world, c)) {
        printf("FAIL: child alive after its parent was deleted; its parent is now %s\n",
            ecs_get_target(world, c, EcsChildOf, 0) == q ? "the new entity q" : "another entity");
        failed = 1;
    }
    ecs_fini(world);
    return failed;
}
