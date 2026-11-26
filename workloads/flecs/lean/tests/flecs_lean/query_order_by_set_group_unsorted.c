/* Prediction F61: ecs_iter_set_group on a query with both group_by and
 * order_by returns the group's entities table by table, not in order.
 *
 *   group_by (Rel, *) target; order_by Position.x
 *   group TgtA: table [Position, (Rel, TgtA)] with x = 1, 3 and table
 *               [Position, (Rel, TgtA), Tag] with x = 2, 4;
 *   group TgtB: one entity, x = 0
 *   control: a full iteration returns group TgtA as 1, 2, 3, 4
 *   prediction: ecs_iter_set_group(&it, TgtA) returns 1, 3, 2, 4
 *
 * Code path (flecs v4.2.0): flecs_query_cache_iter_init (query/cache/
 * cache_iter.c 11-37) sorts and points the iterator at the sorted slices,
 * which flecs_query_cache_build_sorted_tables (order_by.c 212-222) builds
 * group by group, merging each group's tables (91-208).
 * ecs_iter_set_group (query/api.c 758-795) then replaces them with
 * &group->tables (787-791): the group's matches in insertion order, each a
 * whole table, sorted only within itself.
 *
 * Documented: Queries.md "Sorting": "Sorted queries use a two-step process
 * to return entities in a sorted order ... This second step is necessary to
 * support datasets where ordered results have entities interleaved from
 * multiple tables"; flecs.h ecs_iter_set_group: "This operation limits the
 * results returned by the query to only the selected group ID". flecs's
 * own GroupBy_group_by_w_sort_reverse_group_creation expects the sorted
 * results group by group.
 *
 * Build: the default debug build. main returns 0 when the group comes in
 * order. */
#include "flecs.h"
#include <stdio.h>
#include <stdlib.h>

typedef struct { float x, y; } Position;

static int cmp_x(ecs_entity_t e1, const void *p1, ecs_entity_t e2,
    const void *p2)
{
    (void)e1; (void)e2;
    float a = ((const Position*)p1)->x, b = ((const Position*)p2)->x;
    return (a > b) - (a < b);
}

static uint64_t group_by_tgt(ecs_world_t *world, ecs_table_t *table,
    ecs_id_t id, void *ctx)
{
    (void)ctx;
    ecs_id_t match;
    if (ecs_search(world, table, ecs_pair(id, EcsWildcard), &match) != -1) {
        return ecs_pair_second(world, match);
    }
    return 0;
}

static int collect(ecs_iter_t *it, float *out, int max) {
    int n = 0;
    while (ecs_query_next(it)) {
        const Position *p = ecs_field(it, Position, 0);
        for (int i = 0; i < it->count && n < max; i ++) {
            out[n ++] = p[i].x;
        }
    }
    return n;
}

int main(void) {
    ecs_world_t *world = ecs_mini();
    ECS_COMPONENT(world, Position);
    ECS_TAG(world, Rel);
    ECS_TAG(world, TgtA);
    ECS_TAG(world, TgtB);
    ECS_TAG(world, Tag);

    float xs_a[] = {1, 3}, xs_b[] = {2, 4};
    for (int i = 0; i < 2; i ++) {
        ecs_entity_t e = ecs_new_w_pair(world, Rel, TgtA);
        ecs_set(world, e, Position, {xs_a[i], 0});
    }
    for (int i = 0; i < 2; i ++) {
        ecs_entity_t e = ecs_new_w_pair(world, Rel, TgtA);
        ecs_add(world, e, Tag);
        ecs_set(world, e, Position, {xs_b[i], 0});
    }
    {
        ecs_entity_t e = ecs_new_w_pair(world, Rel, TgtB);
        ecs_set(world, e, Position, {0, 0});
    }

    ecs_query_t *q = ecs_query(world, {
        .terms = {{ ecs_id(Position), .inout = EcsIn },
                  { ecs_pair(Rel, EcsWildcard) }},
        .order_by = ecs_id(Position),
        .order_by_callback = cmp_x,
        .group_by = Rel,
        .group_by_callback = group_by_tgt
    });
    if (!q) {
        printf("INCONCLUSIVE: the query was not created\n");
        return 2;
    }

    float all[8], grp[8];
    ecs_iter_t it = ecs_query_iter(world, q);
    int n = collect(&it, all, 8);
    printf("control (full iteration):");
    for (int i = 0; i < n; i ++) printf(" %g", all[i]);
    printf("\n");
    /* group TgtA's values in the full iteration */
    float ga[8]; int na = 0;
    for (int i = 0; i < n; i ++) if (all[i] != 0) ga[na ++] = all[i];
    for (int i = 1; i < na; i ++) {
        if (ga[i - 1] > ga[i]) {
            printf("INCONCLUSIVE: the full iteration is not sorted\n");
            return 2;
        }
    }

    it = ecs_query_iter(world, q);
    ecs_iter_set_group(&it, TgtA);
    int m = collect(&it, grp, 8);
    printf("prediction (ecs_iter_set_group TgtA):");
    for (int i = 0; i < m; i ++) printf(" %g", grp[i]);
    printf(" (expected 1 2 3 4)\n");

    int failed = 0;
    if (m != 4) {
        printf("INCONCLUSIVE: the group has %d entities\n", m);
        failed = 2;
    } else {
        for (int i = 1; i < m; i ++) {
            if (grp[i - 1] > grp[i]) {
                printf("FAIL: the group's entities are not in order\n");
                failed = 1;
                break;
            }
        }
    }

    ecs_query_fini(q);
    ecs_fini(world);
    return failed;
}
