/* Prediction F19 (removal): a query with change detection that reads
 * Velocity from a fixed source does not report a change when the source
 * loses Velocity; the query's results go from one entity to none.
 *
 * flecs_query_get_fixed_monitor (change_detection.c 142-201) skips a field
 * whose source has no table record for the component ("Entity doesn't have
 * the component"), both when it fills the monitor and when it compares it,
 * so the removal is never compared.
 *
 * Documented: Queries.md "Change Detection": "Anything that causes adding or
 * removing a component, tag or pair" is detected. */
#include "flecs.h"
#include <stdio.h>

typedef struct { float x, y; } Position;
typedef struct { float x, y; } Velocity;

int main(void) {
    ecs_world_t *world = ecs_mini();
    ECS_COMPONENT(world, Position);
    ECS_COMPONENT(world, Velocity);

    ecs_entity_t game = ecs_insert(world, ecs_value(Velocity, {1, 1}));
    ecs_insert(world, ecs_value(Position, {0, 0}));

    ecs_query_t *q = ecs_query(world, {
        .terms = {
            { ecs_id(Position), .inout = EcsIn },
            { ecs_id(Velocity), .src.id = game, .inout = EcsIn }
        },
        .cache_kind = EcsQueryCacheAuto,
        .flags = EcsQueryDetectChanges
    });

    ecs_query_changed(q);
    ecs_iter_t it = ecs_query_iter(world, q);
    int before = 0;
    while (ecs_query_next(&it)) { before += it.count; }
    if (before != 1 || ecs_query_changed(q)) {
        printf("INCONCLUSIVE: setup (results %d)\n", before);
        return 2;
    }

    ecs_remove(world, game, Velocity);

    int failed = 0;
    if (!ecs_query_changed(q)) {
        printf("FAIL: ecs_query_changed is false after the fixed source lost Velocity\n");
        failed = 1;
    }

    ecs_query_fini(q);
    ecs_fini(world);
    return failed;
}
