/* Prediction: an ecs_set_pair on a stage for a pair the entity already has
 * (queued as AddModified, commands.c 694-707) aborts the merge
 * ("second element of pair is not alive", entity.c 2828) when the target's
 * deletion is queued before it: the delete removes the pair through cleanup,
 * then flecs_add_id re-adds the pair with the dead target.
 *
 * Documented: Manual.md "Deferred operations" (commands run in order at
 * merge; commands for deleted entities are discarded); Relationships.md
 * "Cleanup properties" (deleting a target removes the pairs).  Both calls
 * were valid when enqueued. */
#include "flecs.h"
#include <stdio.h>

typedef struct { float x, y; } Position;

int main(void) {
    ecs_world_t *world = ecs_mini();
    ECS_COMPONENT(world, Position);
    ecs_entity_t tgt = ecs_new(world);
    ecs_entity_t e = ecs_new(world);
    ecs_set_pair(world, e, Position, tgt, {1, 1});

    ecs_world_t *stage = ecs_get_stage(world, 0);
    ecs_delete(stage, tgt);
    ecs_set_pair(stage, e, Position, tgt, {2, 2});
    ecs_merge(stage);   /* predicted: aborts here */

    int failed = 0;
    if (!ecs_is_alive(world, e)) { printf("FAIL: e deleted\n"); failed = 1; }
    else if (ecs_has_pair(world, e, ecs_id(Position), tgt)) {
        printf("FAIL: e has a pair with a deleted target\n"); failed = 1;
    }
    ecs_fini(world);
    return failed;
}
