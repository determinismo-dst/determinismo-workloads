/* Prediction F55, corrected in round 8 (the default allocator). Build
 * flecs.c and this file normally (debug or release; not with
 * FLECS_USE_OS_ALLOC or FLECS_SANITIZE, which return 2, INCONCLUSIVE).
 *
 *   Tag: OnDelete Delete; tags A, B, C, D
 *   [Position]: e0 (1), e2 (3); [Position, Tag]: e1 (2); order_by Position
 *   after the first result (its table locked): ecs_delete(world, Tag)
 *   the next ecs_query_next skips the stale slice of [Position, Tag]
 *   after the iteration: four entities with Position and A, B, C, D
 *   (four new matched tables); ecs_query_iter: crash
 *
 * Deleting Tag frees [Position, Tag]; the query cache drops its match and
 * returns its monitor to cache->allocators.monitors (match.c 41-43). With
 * the default allocator a freed chunk's first 8 bytes are its free-list
 * link (flecs_bfree_w_dbg_info, block_allocator.c 274: chunk->next =
 * ba->head), and the monitor of a one-field query is 8 bytes (cache.c
 * 620-621). The skip of the stale slice syncs the freed monitor
 * (cache_iter.c 81-99, flecs_query_sync_match_monitor, change_detection.c
 * 581-633):
 *   - monitor[0] = dirty_state[0] (606): the link's low half becomes 1;
 *   - monitor[1] is the link's high half, not -1, so the term loop reads
 *     the freed base.columns, whose first bytes are the columns
 *     allocator's link (flecs_query_get_column_for_field, 30-75: a column
 *     that is a multiple of 16, never -1), and stores dirty_state[column+1],
 *     read past the 1-int block just planted in the zeroed table slot,
 *     into monitor[1] (627-628): the link's high half.
 * The link is now a wild pointer. The next monitors are allocated when the
 * next iterator sorts (flecs_query_cache_sort_tables, order_by.c 247-276:
 * flecs_query_check_table_monitor -> flecs_query_get_match_monitor,
 * change_detection.c 79-138, flecs_balloc): the first new match pops the
 * corrupted chunk, the second pops the wild pointer
 * (flecs_balloc_w_dbg_info, block_allocator.c 141-190: ba->head =
 * ba->head->next), which crashes, or hands out a monitor at a wild address
 * that the sort and the syncs then write.
 *
 * A control world, run first, deletes Tag outside the iteration. A crash
 * or an abort in the prediction confirms (the handler prints FAIL and
 * exits 1). The FLECS_SANITIZE build puts a 16-byte header before each
 * chunk's data, so the link is not hit; with FLECS_USE_OS_ALLOC there are
 * no free lists (see query_order_by_skip_leaks_dirty_state.c for those).
 *
 * Documented: Manual.md "Error handling"; Queries.md "Iteration" (the
 * delete does not touch the locked table) and "Sorting". main returns 0
 * when the prediction world runs to the end. */
#include "flecs.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <signal.h>

typedef struct { float x, y; } Position;

static int compare_x(ecs_entity_t e1, const void *p1, ecs_entity_t e2,
    const void *p2)
{
    (void)e1; (void)e2;
    const Position *a = p1, *b = p2;
    return (a->x > b->x) - (a->x < b->x);
}

static int stage; /* 0 control, 1 prediction */
static const char *where = "setup";

static void on_signal(int sig) {
    if (stage == 1) {
        printf("FAIL: signal %d (%s) after the skip of the stale slice "
            "wrote the freed monitor\n", sig, where);
    } else {
        printf("INCONCLUSIVE: signal %d in the control (%s)\n", sig, where);
    }
    fflush(stdout);
    _Exit(stage == 1 ? 1 : 2);
}

static int run(int delete_during) {
    ecs_world_t *world = ecs_mini();
    ECS_COMPONENT(world, Position);
    ECS_TAG(world, Tag);
    ECS_TAG(world, A);
    ECS_TAG(world, B);
    ECS_TAG(world, C);
    ECS_TAG(world, D);
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
    (void)e2;

    where = "first iteration";
    ecs_iter_t it0 = ecs_query_iter(world, q);
    while (ecs_query_next(&it0)) { }

    if (!delete_during) ecs_delete(world, Tag);

    where = "the iteration with the delete";
    int results = 0;
    ecs_iter_t it = ecs_query_iter(world, q);
    while (ecs_query_next(&it)) {
        results ++;
        if (results == 1 && delete_during) {
            if (it.count != 1 || it.entities[0] != e0) {
                printf("INCONCLUSIVE: the first result is not e0\n");
                exit(2);
            }
            ecs_table_t *t = it.table;
            ecs_table_lock(world, t);
            ecs_delete(world, Tag);
            ecs_table_unlock(world, t);
        }
        if (results > 10) break;
    }
    if (ecs_is_alive(world, e1)) {
        printf("INCONCLUSIVE: e1 survived the delete of Tag\n");
        exit(2);
    }

    where = "the new tables";
    ecs_entity_t tags[4] = { A, B, C, D };
    for (int k = 0; k < 4; k ++) {
        ecs_entity_t e = ecs_insert(world, ecs_value(Position, {10.0f + k, 0}));
        ecs_add_id(world, e, tags[k]);
    }

    where = "ecs_query_iter after the new tables (their monitors)";
    int n = 0;
    float sum = 0;
    ecs_iter_t it2 = ecs_query_iter(world, q);
    where = "the iteration after the new tables";
    while (ecs_query_next(&it2)) {
        const Position *p = ecs_field(&it2, Position, 0);
        for (int i = 0; i < it2.count; i ++) { sum += p[i].x; n ++; }
    }
    printf("%s: %d entities after the new tables (sum of x %.0f)\n",
        delete_during ? "prediction" : "control", n, (double)sum);

    where = "ecs_query_fini";
    ecs_query_fini(q);
    where = "ecs_fini";
    ecs_fini(world);
    return n;
}

int main(void) {
    const ecs_build_info_t *bi = ecs_get_build_info();
    for (const char **f = bi->flags; f && *f; f ++) {
        if (!strcmp(*f, "FLECS_USE_OS_ALLOC")) {
            printf("INCONCLUSIVE: build without FLECS_USE_OS_ALLOC\n");
            return 2;
        }
    }
    if (bi->sanitize) {
        printf("INCONCLUSIVE: build without FLECS_SANITIZE\n");
        return 2;
    }

    signal(SIGSEGV, on_signal);
    signal(SIGBUS, on_signal);
    signal(SIGABRT, on_signal);

    stage = 0;
    int n = run(0);
    if (n != 6) {
        printf("INCONCLUSIVE: the control returned %d entities, not 6\n", n);
        return 2;
    }
    stage = 1;
    n = run(1);
    printf("the prediction world ran to the end (%d entities): no crash "
        "seen\n", n);
    return 0;
}
