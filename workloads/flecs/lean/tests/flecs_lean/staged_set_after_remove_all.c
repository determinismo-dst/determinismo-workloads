/* Prediction: a value set on a stage is lost when a remove_all of the same
 * component is queued before it.  For a component without OnSet
 * hooks/observers, ecs_set on a stage writes straight into the entity's
 * current storage when the entity has the component (commands.c 663-679) and
 * only queues an "add"; flecs_defer_skip_removed (379-406) does not look at
 * queued remove_all/delete_with commands.  At merge the remove_all drops the
 * written value and the "add" re-adds the component default-constructed.
 *
 * Documented: Manual.md "Deferred operations" (queued changes become visible
 * when the stage is merged, in order); EntitiesComponents.md "Operations"
 * (set sets the value of the component).  Replayed in order on the world,
 * the calls end with Position == {2, 2}. */
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

    ecs_entity_t e = ecs_insert(world, ecs_value(Position, {1, 1}));

    ecs_world_t *stage = ecs_get_stage(world, 0);
    ecs_remove_all(stage, ecs_id(Position));
    ecs_set(stage, e, Position, {2, 2});
    ecs_merge(stage);

    int failed = 0;
    const Position *p = ecs_get(world, e, Position);
    if (!p) {
        printf("FAIL: e has no Position after the merge\n");
        failed = 1;
    } else if (p->x != 2 || p->y != 2) {
        printf("FAIL: e has Position {%f, %f}, expected {2, 2}\n", p->x, p->y);
        failed = 1;
    }
    ecs_fini(world);
    return failed;
}
