/* Prediction F18 (up source): a query with change detection that reads
 * Velocity from the parent (Velocity(up)) does not report a change after the
 * parent moved to another table (here: it got a tag) and Velocity was set on
 * it. Neither ecs_query_changed nor ecs_iter_changed reports it.
 *
 * The match monitor of the child's table holds the dirty counter of the
 * column in the parent's old table; flecs_query_check_match_monitor
 * (change_detection.c 329-419) compares it with the counter of the parent's
 * current table, whose dirty state is allocated on the check with every
 * counter at 1 (table.c 1432-1450). The set itself marked nothing because the
 * parent's new table had no dirty state (table.c 1397-1429).
 *
 * Documented: Queries.md "Change Detection" ("Setting a component value with
 * set" is detected; changes are reported for the components the query
 * matched with). flecs's own test ChangeDetection_query_changed_w_only_parent_
 * after_set expects a set on the parent to be detected. */
#include "flecs.h"
#include <stdio.h>

typedef struct { float x, y; } Position;
typedef struct { float x, y; } Velocity;

int main(void) {
    ecs_world_t *world = ecs_mini();
    ECS_COMPONENT(world, Position);
    ECS_COMPONENT(world, Velocity);
    ECS_TAG(world, Tag);

    ecs_entity_t parent = ecs_insert(world, ecs_value(Velocity, {1, 1}));
    ecs_entity_t child = ecs_insert(world, ecs_value(Position, {0, 0}));
    ecs_add_pair(world, child, EcsChildOf, parent);

    ecs_query_t *q = ecs_query(world, {
        .terms = {
            { ecs_id(Position), .inout = EcsIn },
            { ecs_id(Velocity), .src.id = EcsUp, .trav = EcsChildOf, .inout = EcsIn }
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

    ecs_add(world, parent, Tag);                  /* parent moves tables */
    ecs_set(world, parent, Velocity, {2, 2});     /* documented as detected */

    int failed = 0;
    if (!ecs_query_changed(q)) {
        printf("FAIL: ecs_query_changed is false after Velocity was set on the parent\n");
        failed = 1;
    }

    it = ecs_query_iter(world, q);
    int results = 0;
    while (ecs_query_next(&it)) {
        results ++;
        const Velocity *v = ecs_field(&it, Velocity, 1);
        if (v->x != 2) {
            printf("FAIL: iteration read Velocity.x = %f\n", (double)v->x);
            failed = 1;
        }
        if (!ecs_iter_changed(&it)) {
            printf("FAIL: ecs_iter_changed is false for the child's table\n");
            failed = 1;
        }
    }
    if (results != 1) {
        printf("FAIL: %d results\n", results);
        failed = 1;
    }

    ecs_query_fini(q);
    ecs_fini(world);
    return failed;
}
