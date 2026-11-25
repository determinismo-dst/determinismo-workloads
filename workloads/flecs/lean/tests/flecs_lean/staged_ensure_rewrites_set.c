/* Prediction: ecs_ensure on a stage, after a queued ecs_set of the same
 * component on an entity that does not have it yet, returns the set
 * command's own storage (flecs_defer_find_cmd_value, commands.c 489-545,
 * used by flecs_defer_ensure 567-574).  Writing through it rewrites the
 * queued set, so at merge the OnSet observer for that set sees the ensure's
 * value, not the value passed to set.
 *
 * Documented: Manual.md "Deferred operations" (ensure on a stage returns
 * temporary storage applied at merge); ObserversManual.md "OnSet Events" and
 * "OnSet order is maintained" (each set is an OnSet event, deferred or not).
 * Replayed in order: OnSet sees 99, then the ensure writes 1. */
#include "flecs.h"
#include <stdio.h>

typedef struct { float x, y; } Position;

static float seen_x = -1;
static int seen_count;

static void on_set(ecs_iter_t *it) {
    Position *p = ecs_field(it, Position, 0);
    seen_x = p[0].x;
    seen_count ++;
}

int main(void) {
    ecs_world_t *world = ecs_mini();
    ECS_COMPONENT(world, Position);
    ecs_observer(world, {
        .query.terms = {{ ecs_id(Position) }},
        .events = { EcsOnSet },
        .callback = on_set
    });

    ecs_entity_t e = ecs_new(world);
    ecs_world_t *stage = ecs_get_stage(world, 0);
    ecs_set(stage, e, Position, {99, 99});
    Position *p = ecs_ensure(stage, e, Position);
    p->x = 1; p->y = 1;
    ecs_merge(stage);

    int failed = 0;
    if (seen_count != 1) { printf("FAIL: OnSet ran %d times\n", seen_count); failed = 1; }
    if (seen_x != 99) { printf("FAIL: OnSet for set({99, 99}) saw x = %f\n", seen_x); failed = 1; }
    const Position *v = ecs_get(world, e, Position);
    if (!v || v->x != 1) { printf("FAIL: final value is not the ensure's\n"); failed = 1; }
    ecs_fini(world);
    return failed;
}
