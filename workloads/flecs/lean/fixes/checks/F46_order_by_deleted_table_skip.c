/* Check for F46, the form without a new table: while an order_by query is
 * iterated, a call deletes a table that has a later slice, and no table is
 * created after it. The iterator then reaches the slice of the deleted table,
 * whose table memory is zeroed (count 0), and the empty-table path syncs the
 * slice's monitor, which the cache freed. ecs_iter_changed is called for every
 * result. Build with -fsanitize=address -DFLECS_USE_OS_ALLOC to see the
 * write to freed memory; main returns 0 when every remaining entity is
 * returned once and no result has an entity without Position. */
#include "flecs.h"
#include <stdio.h>

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
    ecs_add_pair(world, Tag, EcsOnDelete, EcsDelete);

    ecs_query_t *q = ecs_query(world, {
        .terms = {{ ecs_id(Position), .inout = EcsIn }},
        .order_by = ecs_id(Position),
        .order_by_callback = compare_x,
        .cache_kind = EcsQueryCacheAuto
    });

    ecs_entity_t e0 = ecs_insert(world, ecs_value(Position, {1, 0}));
    ecs_entity_t e1 = ecs_insert(world, ecs_value(Position, {2, 0}));
    ecs_add(world, e1, Tag);
    ecs_entity_t e2 = ecs_insert(world, ecs_value(Position, {3, 0}));

    ecs_iter_t it0 = ecs_query_iter(world, q);
    while (ecs_query_next(&it0)) { }

    int n0 = 0, n2 = 0, bad = 0, results = 0, changed = 0;
    ecs_iter_t it = ecs_query_iter(world, q);
    while (ecs_query_next(&it)) {
        results ++;
        changed += ecs_iter_changed(&it);
        for (int i = 0; i < it.count; i ++) {
            if (it.entities[i] == e0) n0 ++;
            if (it.entities[i] == e2) n2 ++;
            if (!ecs_is_alive(world, it.entities[i]) ||
                !ecs_has(world, it.entities[i], Position)) bad = 1;
        }
        if (results == 1) {
            ecs_table_t *t = it.table;
            ecs_table_lock(world, t);
            ecs_delete(world, Tag);
            ecs_table_unlock(world, t);
        }
        if (results > 10) break;
    }

    /* A second iteration after the delete: the slices are rebuilt */
    int results2 = 0;
    ecs_iter_t it2 = ecs_query_iter(world, q);
    while (ecs_query_next(&it2)) results2 += it2.count;

    printf("results %d (e0 %d, e2 %d, changed %d), bad %d, e1 alive %d; "
        "next iteration: %d entities\n", results, n0, n2, changed, bad,
        ecs_is_alive(world, e1), results2);
    int failed = bad || n0 != 1 || n2 != 1 || results2 != 2;
    printf(failed ? "FAIL\n" : "OK\n");
    ecs_query_fini(q);
    ecs_fini(world);
    return failed;
}
