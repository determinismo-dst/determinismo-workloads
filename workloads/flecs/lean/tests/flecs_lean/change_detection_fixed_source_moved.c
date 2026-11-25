/* Prediction F18 (fixed source): a query with change detection that reads
 * Velocity from a fixed source does not report a change after the source
 * entity moved to another table (here: it got a tag) and Velocity was set.
 *
 * The query's fixed-source monitor holds the dirty counter of the column in
 * the source's old table (change_detection.c 142-201). The new table has no
 * dirty state yet, so ecs_set marks nothing (table.c 1397-1429), and when
 * the monitor is checked the new table's dirty state is allocated with every
 * counter at 1 (table.c 1432-1450), equal to the old counter.
 *
 * Documented: Queries.md "Change Detection": "Setting a component value with
 * set" is detected; "A query with change detection enabled will only report
 * a change for the components it matched with" (Velocity is matched). */
#include "flecs.h"
#include <stdio.h>

typedef struct { float x, y; } Position;
typedef struct { float x, y; } Velocity;

int main(void) {
    ecs_world_t *world = ecs_mini();
    ECS_COMPONENT(world, Position);
    ECS_COMPONENT(world, Velocity);
    ECS_TAG(world, Tag);

    ecs_entity_t game = ecs_insert(world, ecs_value(Velocity, {1, 1}));
    ecs_entity_t e = ecs_insert(world, ecs_value(Position, {0, 0}));
    (void)e;

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
    while (ecs_query_next(&it)) { }
    if (ecs_query_changed(q)) {
        printf("INCONCLUSIVE: query reports a change right after iterating\n");
        return 2;
    }

    ecs_add(world, game, Tag);                    /* game moves to [Velocity, Tag] */
    ecs_set(world, game, Velocity, {2, 2});       /* documented as detected */

    int failed = 0;
    if (!ecs_query_changed(q)) {
        printf("FAIL: ecs_query_changed is false after Velocity was set on the fixed source\n");
        failed = 1;
    }

    ecs_query_fini(q);
    ecs_fini(world);
    return failed;
}
