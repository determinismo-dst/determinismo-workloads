/* Prediction F35 (first form): while a cascade query is iterated, a call
 * that changes the depth of a parent moves an already returned table to a
 * later group, and the iteration returns its entities again.
 *
 * A cascade query groups its cached tables by ChildOf depth
 * (flecs_query_cache_group_by_cascade, query/cache/cache.c 179-191) in
 * ascending order (EcsQueryGroupByOrdered, cache.c 866-872, group.c 37-54).
 * The iterator walks one group's table vector, then follows group->next
 * (cache_iter.c 41-123). Reparenting an entity changes the depth of its
 * children's (ChildOf, parent) record (component_index.c 1166-1231); the
 * ancestry observer enqueues a revalidation of the children's tables
 * (cache.c 334-430), which the end of the call runs
 * (flecs_query_revalidate_table, match.c 328-365):
 * flecs_query_cache_move_table_to_group (group.c 249-274) appends the table
 * to the group of its new depth and removes it from the old one.
 *
 * Program (the query is created first, so tables are cached in creation
 * order):
 *   p2, p1 roots with Position             group 0: [Position]
 *   c2 child of p2, c1 child of p1          group 1: [Position, (ChildOf, p2)],
 *                                                    [Position, (ChildOf, p1)]
 *   iterate; after the third result (c1's table, the last one of group 1;
 *   the table is locked, as the C++ each locks it), p1 becomes a child of
 *   p2: p1 moves to c2's table, c1's table moves to the new group 2, which
 *   comes after group 1. The iteration then reaches group 2 and returns c1
 *   a second time.
 *
 * Documented: Queries.md "Iteration" (C++): moving entities "can cause
 * unwanted side effects while iterating a table, like iterating an entity
 * twice, or missing an entity. To prevent this from happening, a table is
 * locked by the C++ each and run functions, meaning no entities can be moved
 * from or to it." c1 does not move; its table is locked. Queries.md
 * "Cascade": breadth-first order. main returns 0 when c1 and c2 are returned
 * once. */
#include "flecs.h"
#include <stdio.h>
#include <stdlib.h>

typedef struct { float x, y; } Position;

int main(void) {
    ecs_world_t *world = ecs_mini();
    ECS_COMPONENT(world, Position);

    ecs_query_t *q = ecs_query(world, {
        .terms = {
            { ecs_id(Position) },
            { ecs_id(Position), .src.id = EcsCascade, .oper = EcsOptional }
        },
        .cache_kind = EcsQueryCacheAuto
    });

    ecs_entity_t p2 = ecs_insert(world, ecs_value(Position, {0, 0}));
    ecs_entity_t c2 = ecs_new_w_pair(world, EcsChildOf, p2);
    ecs_set(world, c2, Position, {1, 1});
    ecs_entity_t p1 = ecs_insert(world, ecs_value(Position, {2, 2}));
    ecs_entity_t c1 = ecs_new_w_pair(world, EcsChildOf, p1);
    ecs_set(world, c1, Position, {3, 3});

    /* Control: three results, roots first */
    int results0 = 0, n0 = 0;
    ecs_iter_t it0 = ecs_query_iter(world, q);
    while (ecs_query_next(&it0)) { results0 ++; n0 += it0.count; }
    if (results0 != 3 || n0 != 4) {
        printf("INCONCLUSIVE: setup iteration returned %d results, %d entities\n",
            results0, n0);
        return 2;
    }

    int seen_c1 = 0, seen_c2 = 0, results = 0;
    ecs_iter_t it = ecs_query_iter(world, q);
    while (ecs_query_next(&it)) {
        results ++;
        for (int i = 0; i < it.count; i ++) {
            if (it.entities[i] == c1) seen_c1 ++;
            if (it.entities[i] == c2) seen_c2 ++;
        }
        if (results == 3) {
            if (it.count != 1 || it.entities[0] != c1) {
                printf("INCONCLUSIVE: the third result is not c1's table\n");
                return 2;
            }
            ecs_table_t *t = it.table;
            ecs_table_lock(world, t);
            ecs_add_pair(world, p1, EcsChildOf, p2);
            ecs_table_unlock(world, t);
        }
        if (results > 10) break;
    }

    int failed = 0;
    if (ecs_get_target(world, p1, EcsChildOf, 0) != p2 ||
        ecs_get_target(world, c1, EcsChildOf, 0) != p1)
    {
        printf("INCONCLUSIVE: the hierarchy is not as expected\n");
        failed = 2;
    } else if (seen_c1 != 1 || seen_c2 != 1) {
        printf("FAIL: c1 returned %d times, c2 returned %d times (expected 1 "
            "and 1); %d results\n", seen_c1, seen_c2, results);
        failed = 1;
    }
    ecs_query_fini(q);
    ecs_fini(world);
    return failed;
}
