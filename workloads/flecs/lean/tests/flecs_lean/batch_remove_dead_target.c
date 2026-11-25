/* Prediction: a queued remove of (ChildOf, parent) deletes the entity when
 * the parent is deleted earlier in the same merge and the entity has another
 * command in the queue (command batching), though the entity never was a
 * child of the parent.  Alone, the same remove is a no-op.
 *
 * Documented: Manual.md "Deferred operations" (queued changes become
 * visible when the stage is merged; commands for deleted entities are
 * discarded; commands that *parent* an entity to a deleted parent delete the
 * child) and EntitiesComponents.md "Operations" (remove: "If entity doesn't
 * have the component, remove does nothing").  Batching must not change the
 * outcome (ObserversManual.md "Event order is undefined between entities":
 * batching is allowed to reorder events, not to change state). */
#include "flecs.h"
#include <stdio.h>

int main(void) {
    ecs_world_t *world = ecs_mini();
    ecs_entity_t Tag = ecs_new(world);
    ecs_entity_t parent = ecs_new(world);
    ecs_entity_t e = ecs_new(world);
    ecs_entity_t lone = ecs_new(world);

    ecs_world_t *stage = ecs_get_stage(world, 0);
    ecs_delete(stage, parent);
    ecs_add_id(stage, e, Tag);
    ecs_remove_pair(stage, e, EcsChildOf, parent);
    ecs_remove_pair(stage, lone, EcsChildOf, parent);
    ecs_merge(stage);

    int failed = 0;
    if (!ecs_is_alive(world, lone)) {
        printf("FAIL: lone entity deleted by remove of a pair it never had\n");
        failed = 1;
    }
    if (!ecs_is_alive(world, e)) {
        printf("FAIL: entity deleted by remove of (ChildOf, deleted parent) it never had\n");
        failed = 1;
    } else if (!ecs_has_id(world, e, Tag)) {
        printf("FAIL: entity lost the queued Tag\n");
        failed = 1;
    }

    ecs_fini(world);
    return failed;
}
