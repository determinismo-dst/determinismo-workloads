/* Prediction F30: while a cached query is iterated, a call that removes a
 * table from the query's cache moves the cache's last table into the
 * removed one's slot, and the iterator, which keeps an index into that
 * vector, never returns the moved table. Its entities matched before and
 * after the call and did not move.
 *
 * Here the call deletes an entity x that is the target of a relationship:
 * cleanup deletes the (empty) table [Position, (R, x)], which sits before
 * the iterated table in the cache.
 *
 *   q = Position (cached)
 *   cache: T1 = [Position, (R, x)] (empty), T2 = [Position] {e2},
 *          T3 = [Position, Velocity] {e3}
 *   iterate: T1 is skipped (empty), T2 is returned; with T2 locked, as the
 *   C++ each does, ecs_delete(x) deletes T1;
 *   flecs_query_cache_remove_table_from_group (query/cache/group.c 176-213)
 *   calls ecs_vec_remove, which moves T3 into slot 0; the iterator's cursor
 *   (cache_iter.c 230-262, qit->cur == 2) is past the end; e3 is never
 *   returned.
 *
 * Documented: Queries.md "Iteration" (C++ tab): moving entities "can cause
 * unwanted side effects while iterating a table, like iterating an entity
 * twice, or missing an entity. To prevent this from happening, a table is
 * locked by the C++ each and run functions, meaning no entities can be moved
 * from or to it." The iterated table is locked here and no entity moves,
 * yet an entity is missed. */
#include "flecs.h"
#include <stdio.h>
#include <stdlib.h>

typedef struct { float x, y; } Position;
typedef struct { float x, y; } Velocity;

int main(void) {
    ecs_world_t *world = ecs_mini();
    ECS_COMPONENT(world, Position);
    ECS_COMPONENT(world, Velocity);
    ECS_TAG(world, R);

    ecs_query_t *q = ecs_query(world, {
        .terms = {{ ecs_id(Position) }},
        .cache_kind = EcsQueryCacheAuto
    });

    ecs_entity_t x = ecs_new(world);

    /* T1 = [Position, (R, x)], first in the cache */
    ecs_entity_t e1 = ecs_new_w_pair(world, R, x);
    ecs_set(world, e1, Position, {1, 1});
    /* T2 = [Position] */
    ecs_entity_t e2 = ecs_insert(world, ecs_value(Position, {2, 2}));
    /* T3 = [Position, Velocity] */
    ecs_entity_t e3 = ecs_insert(world, ecs_value(Velocity, {0, 0}));
    ecs_set(world, e3, Position, {3, 3});
    /* T1 stays in the cache, empty */
    ecs_delete(world, e1);

    /* Control: a plain iteration returns e2 and e3 */
    int n = 0;
    ecs_iter_t it0 = ecs_query_iter(world, q);
    while (ecs_query_next(&it0)) n += it0.count;
    if (n != 2) {
        printf("INCONCLUSIVE: setup iteration returned %d entities\n", n);
        return 2;
    }

    int seen2 = 0, seen3 = 0, results = 0;
    ecs_iter_t it = ecs_query_iter(world, q);
    while (ecs_query_next(&it)) {
        for (int i = 0; i < it.count; i ++) {
            if (it.entities[i] == e2) seen2 ++;
            if (it.entities[i] == e3) seen3 ++;
        }
        results ++;
        if (results == 1) {
            ecs_table_t *t = it.table;
            ecs_table_lock(world, t);
            ecs_delete(world, x);
            ecs_table_unlock(world, t);
        }
    }

    int failed = 0;
    if (results < 1 || !ecs_is_alive(world, e3) || !ecs_has(world, e3, Position)) {
        printf("INCONCLUSIVE: setup did not hold\n");
        failed = 2;
    } else if (seen2 != 1 || seen3 != 1) {
        printf("FAIL: e2 returned %d times, e3 returned %d times (expected 1 "
            "and 1); neither moved, the call deleted another table\n",
            seen2, seen3);
        failed = 1;
    }
    ecs_query_fini(q);
    ecs_fini(world);
    return failed;
}
