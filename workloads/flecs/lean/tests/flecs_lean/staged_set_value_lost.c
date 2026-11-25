/* Prediction: a queued ecs_set is lost when the component is removed from the
 * entity (on the world) before the merge.  For a component without OnSet
 * hooks/observers, ecs_set on a stage writes straight into the entity's
 * current storage when the entity has the component (commands.c 663-679) and
 * queues only an "add"; the remove drops the written value and the merge
 * re-adds the component default-constructed.  With more than one stage, the
 * same call queues the value instead (commands.c 651-654) and the merge
 * applies it.
 *
 * Documented: Manual.md "Deferred operations" ("Pass the world to execute
 * operations immediately"; "The queued changes become visible when the stage
 * is merged"); EntitiesComponents.md "Operations" (set sets the value). */
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

    ecs_entity_t e = ecs_insert(world, ecs_value(Position, {0, 0}));

    ecs_world_t *stage = ecs_get_stage(world, 0);
    ecs_set(stage, e, Position, {1, 1});
    ecs_remove(world, e, Position);
    ecs_merge(stage);

    int failed = 0;
    const Position *p = ecs_get(world, e, Position);
    if (!p) { printf("FAIL: e has no Position after the merge\n"); failed = 1; }
    else if (p->x != 1 || p->y != 1) {
        printf("FAIL: e has Position {%f, %f} after the merge, expected {1, 1}\n", p->x, p->y);
        failed = 1;
    }
    ecs_fini(world);
    return failed;
}
