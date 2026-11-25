/* Prediction F22: queued set, remove and add of the same component on one
 * entity, merged as a batch, leave the value of the set; applied in order the
 * remove destroys it and the add constructs a new one.
 *
 * flecs_cmd_batch_for_entity (commands.c 968-1298) computes the final table
 * (the remove and the add cancel out) and then copies the value of every
 * Set/Ensure command of the entity (1179-1241) without checking for a later
 * remove of the same id. The ctor hook gives the documented value of the add.
 *
 * Documented: Manual.md "Deferred operations" (queued operations are applied
 * in order when the stage is merged); EntitiesComponents.md "Operations"
 * (remove removes the component; add constructs it). Found while searching
 * the round 1 model with round 2's observer generator. */
#include "flecs.h"
#include <stdio.h>

typedef struct { float x, y; } Position;

static void ctor_sentinel(void *ptr, int32_t count, const ecs_type_info_t *ti) {
    (void)ti;
    Position *p = ptr;
    for (int i = 0; i < count; i ++) { p[i].x = -1; p[i].y = -1; }
}

int main(void) {
    ecs_world_t *world = ecs_mini();
    ECS_COMPONENT(world, Position);
    ecs_set_hooks(world, Position, { .ctor = ctor_sentinel });

    ecs_entity_t e = ecs_new(world);

    ecs_world_t *stage = ecs_get_stage(world, 0);
    ecs_set(stage, e, Position, {1, 1});
    ecs_remove(stage, e, Position);
    ecs_add(stage, e, Position);
    ecs_merge(stage);

    int failed = 0;
    const Position *p = ecs_get(world, e, Position);
    if (!p) { printf("FAIL: e has no Position after the merge\n"); failed = 1; }
    else if (p->x != -1 || p->y != -1) {
        printf("FAIL: e has Position {%f, %f}, expected the constructed {-1, -1}\n",
            (double)p->x, (double)p->y);
        failed = 1;
    }
    ecs_fini(world);
    return failed;
}
