/* Prediction: ecs_set_pair on a stage, whose target is deleted before the
 * merge, aborts the merge ("second element of pair is not alive",
 * entity.c 2828) when it is the entity's only queued command.  With a second
 * command for the same entity the batched path drops the set silently.
 *
 * Documented: Manual.md "Deferred operations" (commands are enqueued and run
 * at merge; commands targeting deleted entities are discarded);
 * Relationships.md "Cleanup properties" (when a target is deleted, by default
 * the relationship is removed from entities that have it).  The set was valid
 * when it was enqueued, so the merge must not abort. */
#include "flecs.h"
#include <stdio.h>

typedef struct { float x, y; } Position;

int main(void) {
    ecs_world_t *world = ecs_mini();
    ECS_COMPONENT(world, Position);
    ecs_entity_t tgt = ecs_new(world);
    ecs_entity_t e = ecs_new(world);

    ecs_world_t *stage = ecs_get_stage(world, 0);
    ecs_set_pair(stage, e, Position, tgt, {1, 2});
    ecs_delete(world, tgt);
    ecs_merge(stage);   /* predicted: aborts here */

    int failed = 0;
    if (!ecs_is_alive(world, e)) { printf("FAIL: entity deleted\n"); failed = 1; }
    if (ecs_is_alive(world, e) && ecs_has_pair(world, e, ecs_id(Position), tgt)) {
        printf("FAIL: entity has a pair with a deleted target\n"); failed = 1;
    }
    ecs_fini(world);
    return failed;
}
