/* Prediction F56: a matched table deleted during an order_by iteration
 * keeps its slice in the iterators created after that iteration; a table
 * created later in the freed memory is returned by the next iterator.
 *
 *   Tag: OnDelete Delete; Velocity (not used before)
 *   [Position]: e0 (1), e2 (3); [Position, Tag]: e1 (2); order_by Position
 *   slices: [Position] row 0, [Position, Tag] row 0, [Position] row 1
 *   iteration 1: after the third (last) result, e2 (its table locked):
 *     ecs_delete(world, Tag)       deletes e1 and frees [Position, Tag],
 *                                  whose slice was already returned
 *   after iteration 1: ev = ecs_new_w_id(world, Velocity)
 *                                  [Velocity] takes the freed memory
 *   iteration 2 (a new iterator): e0, then ev (no Position), then e2
 *
 * The delete removes the table from the query cache:
 * flecs_query_cache_remove_table_from_group increments cache->match_count
 * (group.c 176-181). The last ecs_query_next of iteration 1 first syncs the
 * monitor of the result it returned (eval_iter.c 494-502 ->
 * flecs_query_change_detection, 217-232), and flecs_query_sync_match_monitor
 * ends with cache->prev_match_count = cache->match_count (change_detection.c
 * 632). Iteration 2's ecs_query_iter calls flecs_query_cache_sort_tables
 * (cache_iter.c 27-34), which rebuilds the slices only when a match's
 * monitor reports a change or match_count != prev_match_count (order_by.c
 * 247-321, 315): neither holds, so cache->table_slices still has the slice
 * of the freed table (a struct copy with its table pointer, order_by.c
 * 195-205). The store gave the freed ecs_table_t memory to [Velocity]
 * (sparse.c 137-150, 380-393; table_graph.c 443), whose count is 1, so the
 * slice is not skipped (cache_iter.c 81-99): the iterator returns ev with
 * the slice's freed _trs and columns. A debug build may abort in
 * flecs_iter_assert_columns (eval_iter.c 253-273) before the result
 * reaches the caller; a crash or an abort also confirms (the handler
 * prints FAIL and exits 1).
 *
 * Round 6's F46 needed the new table to be created during the iteration;
 * here iteration 1 ends normally and the stale slice is used by a new
 * iterator. Controls, each in its own world, run first: Tag deleted before
 * iteration 1 (the slices are rebuilt), and Tag deleted after the last
 * result followed by a new entity in [Position] before iteration 2 (its
 * monitor reports the change, so the slices are rebuilt).
 *
 * Documented: Queries.md "Sorting" ("A query determines whether a sort
 * operation is needed when an iterator is created for it"), "Iteration"
 * (the iterator returns the entities that match the query; the delete
 * does not touch the locked table); Manual.md "Error handling". The
 * program reads no field of the stale result. main returns 0 when every
 * entity of iteration 2 has Position. */
#include "flecs.h"
#include <stdio.h>
#include <stdlib.h>
#include <signal.h>

typedef struct { float x, y; } Position;
typedef struct { float x, y; } Velocity;

static int compare_x(ecs_entity_t e1, const void *p1, ecs_entity_t e2,
    const void *p2)
{
    (void)e1; (void)e2;
    const Position *a = p1, *b = p2;
    return (a->x > b->x) - (a->x < b->x);
}

static int stage; /* 0, 1 controls; 2 the prediction's iteration 2 */

static void on_signal(int sig) {
    if (stage == 2) {
        printf("FAIL: signal %d while a new iterator used the slice of the "
            "table freed during the previous iteration\n", sig);
    } else {
        printf("INCONCLUSIVE: signal %d in stage %d\n", sig, stage);
    }
    fflush(stdout);
    _Exit(stage == 2 ? 1 : 2);
}

/* mode 0: delete before iteration 1; 1: after its last result; 2: after its
 * last result, then a new entity in [Position] before iteration 2.
 * Returns the number of entities without Position in iteration 2. */
static int run(int mode, int *results_out, int *reused_out) {
    ecs_world_t *world = ecs_mini();
    ECS_COMPONENT(world, Position);
    ECS_COMPONENT(world, Velocity);
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
    ecs_table_t *t_tag = ecs_get_table(world, e1);

    if (mode == 0) ecs_delete(world, Tag);

    int results = 0;
    ecs_iter_t it = ecs_query_iter(world, q);
    while (ecs_query_next(&it)) {
        results ++;
        if (mode != 0 && results == 3) {
            if (it.count != 1 || it.entities[0] != e2) {
                printf("INCONCLUSIVE: the third result is not e2\n");
                exit(2);
            }
            ecs_table_t *t = it.table;
            ecs_table_lock(world, t);
            ecs_delete(world, Tag);
            ecs_table_unlock(world, t);
        }
        if (results > 10) break;
    }
    if (mode != 0 && results != 3) {
        printf("INCONCLUSIVE: iteration 1 had %d results, not 3\n", results);
        exit(2);
    }
    if (ecs_is_alive(world, e1)) {
        printf("INCONCLUSIVE: e1 survived the delete of Tag\n");
        exit(2);
    }

    ecs_entity_t ev = ecs_new_w_id(world, ecs_id(Velocity));
    *reused_out = ecs_get_table(world, ev) == t_tag;
    if (mode == 2) ecs_insert(world, ecs_value(Position, {4, 0}));

    if (mode == 1) stage = 2;
    int bad = 0, n = 0, saw_ev = 0;
    ecs_iter_t it2 = ecs_query_iter(world, q);
    while (ecs_query_next(&it2)) {
        for (int i = 0; i < it2.count; i ++) {
            ecs_entity_t e = it2.entities[i];
            n ++;
            if (e == ev) saw_ev ++;
            if (!ecs_has(world, e, Position)) bad ++;
        }
        if (n > 20) break;
    }
    if (mode == 1) stage = 1;
    *results_out = n;
    printf("mode %d: iteration 2 returned %d entities (ev %d, without "
        "Position %d); [Velocity] took the freed table's memory: %d\n",
        mode, n, saw_ev, bad, *reused_out);
    (void)e0;
    ecs_query_fini(q);
    ecs_fini(world);
    return bad;
}

int main(void) {
    signal(SIGSEGV, on_signal);
    signal(SIGBUS, on_signal);
    signal(SIGABRT, on_signal);

    int n = 0, reused = 0;
    stage = 0;
    if (run(0, &n, &reused) || n != 2) {
        printf("INCONCLUSIVE: control 0 (delete before iteration 1)\n");
        return 2;
    }
    if (run(2, &n, &reused) || n != 3) {
        printf("INCONCLUSIVE: control 2 (a row added to [Position])\n");
        return 2;
    }
    stage = 1;
    int bad = run(1, &n, &reused);
    if (bad) {
        printf("FAIL: a new iterator returned %d entity(ies) without "
            "Position, through the slice of the table freed during the "
            "previous iteration\n", bad);
        return 1;
    }
    if (!reused) {
        printf("INCONCLUSIVE: [Velocity] did not take the freed memory\n");
        return 2;
    }
    printf("iteration 2 returned only entities with Position\n");
    return 0;
}
