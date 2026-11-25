/* Prediction: with a relationship that has (OnDeleteTarget, Panic), a queued
 * remove of (Rel, tgt) panics during the merge when tgt was deleted earlier in
 * the same merge and the entity has another command in the queue -- though
 * no entity had (Rel, tgt), so deleting tgt itself was legal.
 *
 * Documented: ComponentTraits.md "OnDeleteTarget" (Panic throws when a
 * target of the relationship is deleted while in use); EntitiesComponents.md
 * "Operations" (remove of an absent component does nothing). */
#include "flecs.h"
#include <stdio.h>
#include <stdlib.h>

static void on_abort(void) {
    printf("FAIL: merge panicked on the remove of a pair nobody had\n");
    exit(1);
}

int main(void) {
    ecs_os_set_api_defaults();
    ecs_os_api_t os_api = ecs_os_get_api();
    os_api.abort_ = on_abort;
    ecs_os_set_api(&os_api);

    ecs_world_t *world = ecs_mini();
    ecs_entity_t Rel = ecs_new(world);
    ecs_add_pair(world, Rel, EcsOnDeleteTarget, EcsPanic);
    ecs_entity_t Tag = ecs_new(world);
    ecs_entity_t tgt = ecs_new(world);
    ecs_entity_t e = ecs_new(world);

    ecs_world_t *stage = ecs_get_stage(world, 0);
    ecs_delete(stage, tgt);          /* legal: nobody has (Rel, tgt) */
    ecs_add_id(stage, e, Tag);
    ecs_remove_pair(stage, e, Rel, tgt);
    ecs_merge(stage);

    int failed = 0;
    if (!ecs_is_alive(world, e) || !ecs_has_id(world, e, Tag)) {
        printf("FAIL: entity state after merge is wrong\n");
        failed = 1;
    }
    ecs_fini(world);
    return failed;
}
