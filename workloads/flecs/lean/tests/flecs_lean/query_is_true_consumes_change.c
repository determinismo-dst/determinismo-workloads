/* Prediction F27: ecs_query_is_true and ecs_query_count, which only test or
 * count a query's results, clear the change state that ecs_query_changed
 * reports.
 *
 * Both create an iterator: flecs_query_cache_iter_init sets
 * cache->prev_match_count = cache->match_count (cache_iter.c 36), which
 * drops the record of tables matched or unmatched since the last iteration.
 * ecs_query_is_true takes the first result and finishes the iterator
 * (iter.c 511-526); the iterator's fini runs change detection on that result
 * (flecs_query_iter_fini, eval_iter.c 670-686, then
 * flecs_query_sync_match_monitor, change_detection.c 581-633), so a change
 * to the first table is no longer reported either. ecs_query_count skips
 * every result but still resets prev_match_count.
 *
 * Documented: flecs.h 4797-4810, ecs_query_changed: "Return whether the
 * query data changed since the last iteration. The operation will return
 * true after: ... new tables have been matched or unmatched ... matched
 * components were changed"; "The changed state of a table is reset after it
 * is iterated." Queries.md "Change Detection": "Setting a component value
 * with set" is detected, and "the query state for that table will remain
 * changed until the table is iterated by the query". ecs_query_is_true
 * (flecs.h 4955-4961) and ecs_query_count (4945-4953) are documented as
 * tests, not iterations. */
#include "flecs.h"
#include <stdio.h>

typedef struct { float x, y; } Position;
typedef struct { float x, y; } Velocity;

static void iterate_all(ecs_query_t *q) {
    ecs_iter_t it = ecs_query_iter(q->world, q);
    while (ecs_query_next(&it)) { }
}

int main(void) {
    ecs_world_t *world = ecs_mini();
    ECS_COMPONENT(world, Position);
    ECS_COMPONENT(world, Velocity);
    int failed = 0;

    /* Part 1: a set, then ecs_query_is_true */
    ecs_query_t *q1 = ecs_query(world, {
        .terms = {{ .id = ecs_id(Position), .inout = EcsIn }},
        .cache_kind = EcsQueryCacheAuto,
        .flags = EcsQueryDetectChanges
    });
    ecs_entity_t e = ecs_insert(world, ecs_value(Position, {1, 1}));
    ecs_query_changed(q1);
    iterate_all(q1);
    if (ecs_query_changed(q1)) {
        printf("INCONCLUSIVE: q1 changed right after iterating\n");
        return 2;
    }
    ecs_set(world, e, Position, {2, 2});
    if (!ecs_query_changed(q1)) {
        printf("INCONCLUSIVE: q1 does not report the set\n");
        return 2;
    }
    (void)ecs_query_is_true(q1);
    if (!ecs_query_changed(q1)) {
        printf("FAIL: after ecs_query_is_true, q1 no longer reports the set\n");
        failed = 1;
    }

    /* Part 2: a table unmatched (up traversal), then ecs_query_is_true and
     * ecs_query_count */
    for (int probe = 0; probe < 2; probe ++) {
        ecs_query_t *q2 = ecs_query(world, {
            .terms = {
                { .id = ecs_id(Position), .inout = EcsIn },
                { .id = ecs_id(Velocity), .src.id = EcsUp, .trav = EcsChildOf, .inout = EcsIn }
            },
            .cache_kind = EcsQueryCacheAuto,
            .flags = EcsQueryDetectChanges
        });
        ecs_entity_t p = ecs_insert(world, ecs_value(Velocity, {1, 1}));
        ecs_entity_t c = ecs_insert(world, ecs_value(Position, {1, 1}));
        ecs_add_pair(world, c, EcsChildOf, p);
        ecs_query_changed(q2);
        iterate_all(q2);
        if (ecs_query_changed(q2)) {
            printf("INCONCLUSIVE: q2 changed right after iterating\n");
            return 2;
        }
        ecs_remove(world, p, Velocity);   /* c's table is unmatched */
        if (!ecs_query_changed(q2)) {
            printf("INCONCLUSIVE: q2 does not report the unmatched table\n");
            return 2;
        }
        if (probe == 0) {
            (void)ecs_query_is_true(q2);
        } else {
            (void)ecs_query_count(q2);
        }
        if (!ecs_query_changed(q2)) {
            printf("FAIL: after %s, q2 no longer reports the unmatched table\n",
                probe == 0 ? "ecs_query_is_true" : "ecs_query_count");
            failed = 1;
        }
        ecs_query_fini(q2);
    }

    ecs_fini(world);
    if (!failed) printf("OK\n");
    return failed;
}
