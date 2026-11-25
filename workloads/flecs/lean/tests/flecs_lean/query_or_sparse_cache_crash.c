/* Prediction F29: creating a cached query whose Or chain ends with a Sparse
 * component crashes.
 *
 *   TagA || Position     (Position has the Sparse trait), cache kind Auto
 *
 * flecs_query_finalize_terms (query/validator.c 965-1312) makes the Or chain
 * consistent (1075-1087: a chain is cacheable as a whole or not at all)
 * before it clears the cacheable flag of sparse terms (1234-1238). So TagA
 * stays cacheable and Position does not. flecs_query_create_cache
 * (api.c 194-243) gives the cache only TagA, with its Or operator. The
 * cache's own query is then rejected: "last term of query can't have OR
 * operator" (validator.c 1308-1312). flecs_query_cache_init returns NULL
 * after setting impl->cache (cache.c 735-753), and the error path of
 * flecs_query_init (api.c 451-457) runs flecs_query_cache_fini on a cache
 * whose query is NULL: flecs_query_cache_remove_all_tables (group.c 334)
 * and cache.c 689 dereference cache->query.
 *
 * Documented: ComponentTraits.md "Sparse trait" ("ECS operations and
 * queries work as expected with sparse components"); Queries.md "Or"
 * operator; Manual.md "Error handling" (no crash). The same query without
 * a cache works (flecs's own Sparse tests use Or chains before a sparse
 * term, not with one).
 *
 * The test creates the query uncached first (control), then cached. A
 * SIGSEGV or abort confirms the prediction. */
#include "flecs.h"
#include <stdio.h>
#include <stdlib.h>

typedef struct { float x, y; } Position;

int main(void) {
    ecs_world_t *world = ecs_mini();
    ECS_COMPONENT(world, Position);
    ECS_TAG(world, TagA);
    ecs_add_id(world, ecs_id(Position), EcsSparse);

    ecs_entity_t e1 = ecs_new_w_id(world, TagA);
    ecs_entity_t e2 = ecs_insert(world, ecs_value(Position, {1, 2}));
    (void)e1; (void)e2;

    ecs_query_t *q0 = ecs_query(world, {
        .terms = {
            { .id = TagA, .oper = EcsOr },
            { .id = ecs_id(Position) }
        },
        .cache_kind = EcsQueryCacheNone
    });
    if (!q0) {
        printf("INCONCLUSIVE: the uncached query was rejected\n");
        return 2;
    }
    ecs_query_fini(q0);

    printf("creating the cached query\n");
    fflush(stdout);
    ecs_query_t *q = ecs_query(world, {
        .terms = {
            { .id = TagA, .oper = EcsOr },
            { .id = ecs_id(Position) }
        },
        .cache_kind = EcsQueryCacheAuto
    });

    int failed = 0;
    if (!q) {
        printf("FAIL: the cached query was rejected\n");
        failed = 1;
    } else {
        int count = 0;
        ecs_iter_t it = ecs_query_iter(world, q);
        while (ecs_query_next(&it)) count += it.count;
        if (count != 2) {
            printf("FAIL: the cached query matched %d entities, expected 2\n",
                count);
            failed = 1;
        }
        ecs_query_fini(q);
    }
    ecs_fini(world);
    return failed;
}
