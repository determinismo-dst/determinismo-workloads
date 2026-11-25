/* flecs_lean: valgrind (an uninitialized read; ci-flecs-lean runs it under valgrind) */
/* Prediction F19 (uninitialized read): when a change-detecting query's
 * fixed source does not have the component the first time the query's
 * fixed-source monitor is filled, that monitor slot is never written
 * (flecs_alloc_n does not zero it, change_detection.c 152-153 and 184).
 * After the source gains the component, ecs_query_changed compares the
 * uninitialized slot with the dirty counter (change_detection.c 194).
 *
 * The answer depends on stale allocator memory, so this program usually
 * returns 0. Run it under valgrind (--error-exitcode=1) or MemorySanitizer:
 * a "conditional jump depends on uninitialised value" in
 * flecs_query_get_fixed_monitor confirms the prediction, as does a non-zero
 * return.
 *
 * Documented: Queries.md "Change Detection" (adding a component is
 * detected); reading uninitialized memory is never allowed. */
#include "flecs.h"
#include <stdio.h>

typedef struct { float x, y; } Position;
typedef struct { float x, y; } Velocity;

int main(void) {
    ecs_world_t *world = ecs_mini();
    ECS_COMPONENT(world, Position);
    ECS_COMPONENT(world, Velocity);

    ecs_entity_t game = ecs_new(world);           /* no Velocity yet */
    ecs_insert(world, ecs_value(Position, {0, 0}));

    ecs_query_t *q = ecs_query(world, {
        .terms = {
            { ecs_id(Position), .inout = EcsIn },
            { ecs_id(Velocity), .src.id = game, .inout = EcsIn }
        },
        .cache_kind = EcsQueryCacheAuto,
        .flags = EcsQueryDetectChanges
    });

    ecs_query_changed(q);                         /* fills the fixed monitor */
    ecs_iter_t it = ecs_query_iter(world, q);
    while (ecs_query_next(&it)) { }

    ecs_set(world, game, Velocity, {1, 1});       /* the source gains Velocity */

    int failed = 0;
    if (!ecs_query_changed(q)) {                  /* reads the unwritten slot */
        printf("FAIL: ecs_query_changed is false after the fixed source gained Velocity\n");
        failed = 1;
    }

    ecs_query_fini(q);
    ecs_fini(world);
    return failed;
}
