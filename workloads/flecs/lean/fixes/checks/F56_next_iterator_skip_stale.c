/* F56 check (memory): a table deleted during an order_by iteration, after
 * its slice was returned, and no table created afterwards. The next iterator
 * must not keep the freed table's slice: on v4.2.0 its skip syncs the freed
 * monitor (a write to freed memory, which AddressSanitizer reports with
 * FLECS_USE_OS_ALLOC). The two iterators must return the remaining entities
 * in order. */
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
        .order_by = ecs_id(Position), .order_by_callback = compare_x,
        .cache_kind = EcsQueryCacheAuto });
    ecs_insert(world, ecs_value(Position, {1, 0}));
    ecs_entity_t e1 = ecs_insert(world, ecs_value(Position, {2, 0}));
    ecs_add(world, e1, Tag);
    ecs_insert(world, ecs_value(Position, {3, 0}));

    int results = 0;
    ecs_iter_t it = ecs_query_iter(world, q);
    while (ecs_query_next(&it)) {
        if (++ results == 3) {
            ecs_table_lock(world, it.table);
            ecs_delete(world, Tag);
            ecs_table_unlock(world, it.table);
        }
    }

    int ok = 1;
    for (int pass = 0; pass < 2; pass ++) {
        float last = 0; int n = 0;
        it = ecs_query_iter(world, q);
        while (ecs_query_next(&it)) {
            const Position *p = ecs_field(&it, Position, 0);
            for (int i = 0; i < it.count; i ++) {
                if (p[i].x < last) ok = 0;
                last = p[i].x; n ++;
            }
        }
        printf("iterator %d: %d entities, in order %d\n", pass + 2, n, ok);
        ok &= n == 2;
    }
    ecs_query_fini(q);
    ecs_fini(world);
    printf(ok ? "OK\n" : "FAIL\n");
    return ok ? 0 : 1;
}
