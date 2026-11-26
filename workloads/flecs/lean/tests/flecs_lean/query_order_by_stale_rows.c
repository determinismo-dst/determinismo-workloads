/* Prediction F40: while an order_by query is iterated, a call that deletes
 * an entity from a table with a later slice makes the iterator return rows
 * past the table's count: an entity is returned twice, the second time from
 * a stale copy.
 *
 * An order_by query iterates `cache->table_slices` (query/cache/cache_iter.c
 * 27-34): copies of the cache's matches, each with a row range, built when
 * the iteration starts (flecs_query_cache_sort_tables and
 * flecs_query_cache_build_sorted_table_range, order_by.c 81-321). The
 * iterator returns each slice's range (cache_iter.c 356-378 sets the range
 * of $this); it skips a slice only when its table is empty (82-98). Deleting
 * a row moves the table's last row into it and decrements the count
 * (flecs_table_delete, storage/table.c 1666-1704); the vector slot of the old
 * last row keeps its entity id and component value.
 *
 * Program (sorted on Position.x):
 *   T1 = [Position]: e0 (1), e2 (3), e3 (4); T2 = [Position, Tag]: e1 (2)
 *   slices: T1 row 0 (e0), T2 row 0 (e1), T1 rows 1-2 (e2, e3)
 *   after the second result (T2, locked as the C++ each locks it), delete e2:
 *   e3 moves to T1 row 1, T1's count is 2. The last slice still covers rows
 *   1-2: the iterator returns e3 (row 1) and e3 again (row 2, past the
 *   count).
 *
 * Documented: Queries.md "Iteration" (C++): a table is locked so that "no
 * entities can be moved from or to it", which prevents "iterating an entity
 * twice, or missing an entity"; e3 stays in its table, which the call does
 * not lock (only T2 is iterated at that moment). Queries.md "Sorting".
 * main returns 0 when e3 is returned once and no result extends past its
 * table's count. */
#include "flecs.h"
#include <stdio.h>
#include <stdlib.h>

typedef struct { float x, y; } Position;

static int compare_x(ecs_entity_t e1, const void *p1, ecs_entity_t e2,
    const void *p2)
{
    (void)e1; (void)e2;
    const Position *a = p1, *b = p2;
    return (a->x > b->x) - (a->x < b->x);
}

int main(void) {
    ecs_world_t *world = ecs_mini();
    ECS_COMPONENT(world, Position);
    ECS_TAG(world, Tag);

    ecs_query_t *q = ecs_query(world, {
        .terms = {{ ecs_id(Position), .inout = EcsIn }},
        .order_by = ecs_id(Position),
        .order_by_callback = compare_x,
        .cache_kind = EcsQueryCacheAuto
    });

    ecs_entity_t e0 = ecs_insert(world, ecs_value(Position, {1, 0}));
    ecs_entity_t e1 = ecs_new_w_id(world, Tag);
    ecs_set(world, e1, Position, {2, 0});
    ecs_entity_t e2 = ecs_insert(world, ecs_value(Position, {3, 0}));
    ecs_entity_t e3 = ecs_insert(world, ecs_value(Position, {4, 0}));
    (void)e0;

    /* Control: three slices, values in order */
    int results0 = 0, n0 = 0;
    float last = 0;
    int ordered = 1;
    ecs_iter_t it0 = ecs_query_iter(world, q);
    while (ecs_query_next(&it0)) {
        const Position *p = ecs_field(&it0, Position, 0);
        results0 ++;
        for (int i = 0; i < it0.count; i ++) {
            if (p[i].x < last) ordered = 0;
            last = p[i].x;
            n0 ++;
        }
    }
    if (results0 != 3 || n0 != 4 || !ordered) {
        printf("INCONCLUSIVE: setup iteration returned %d results, %d entities, "
            "ordered %d\n", results0, n0, ordered);
        return 2;
    }

    int seen_e3 = 0, results = 0, past_count = 0;
    ecs_iter_t it = ecs_query_iter(world, q);
    while (ecs_query_next(&it)) {
        results ++;
        if (it.offset + it.count > ecs_table_count(it.table)) past_count = 1;
        for (int i = 0; i < it.count; i ++) {
            if (it.entities[i] == e3) seen_e3 ++;
        }
        if (results == 2) {
            if (it.count != 1 || it.entities[0] != e1) {
                printf("INCONCLUSIVE: the second result is not e1\n");
                return 2;
            }
            ecs_table_t *t = it.table;
            ecs_table_lock(world, t);
            ecs_delete(world, e2);
            ecs_table_unlock(world, t);
        }
        if (results > 10) break;
    }

    int failed = 0;
    if (seen_e3 != 1 || past_count) {
        printf("FAIL: e3 returned %d times (expected 1); a result extends past "
            "its table's count: %d\n", seen_e3, past_count);
        failed = 1;
    }
    ecs_query_fini(q);
    ecs_fini(world);
    return failed;
}
