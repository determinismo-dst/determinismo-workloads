/* Prediction F46: while an order_by query is iterated, a call that deletes a
 * table with a later slice, followed by a call that creates a table, makes
 * the iterator return the new table's entities, which do not match the
 * query, through the stale slice (and with the slice's freed arrays).
 *
 *   Tag: OnDelete Delete; TagB
 *   [Position]: e0 (1), e2 (3); [Position, Tag]: e1 (2)
 *   slices: [Position] row 0, [Position, Tag] row 0, [Position] row 1
 *   after the first result (its table locked):
 *     ecs_delete(world, Tag)       deletes e1 and frees [Position, Tag]
 *     eB = ecs_new_w_id(TagB)      table [TagB] takes the freed memory
 *   the second result is eB, from table [TagB], which has no Position
 *
 * Tables live in a sparse set (world->store.tables): flecs_table_fini
 * removes the table with flecs_sparse_remove_w_gen_t (storage/table.c
 * 1333-1336), which zeroes the element and moves its dense index to the
 * first unused position (datastructures/sparse.c 365-395);
 * flecs_sparse_add_t (table_graph.c 443) hands that index out first
 * (flecs_sparse_new_index, sparse.c 137-150), so the next table created
 * gets the same ecs_table_t memory. The query cache drops the freed
 * table's match and frees its arrays (cache.c 601-604, group.c 302-326,
 * match.c 18-67). The slices are struct copies of the matches, built when
 * the iterator was created (order_by.c 195-205): the iterator only skips a
 * slice whose table has count 0 (cache_iter.c 81-99), and otherwise
 * returns the slice's range of whatever table is in that memory, with the
 * slice's _trs, columns, _ids and _sources (192-222).
 *
 * An order_by query has change detection from its first iterator on
 * (flecs_query_check_table_monitor creates the match monitors and sets
 * EcsQueryHasChangeDetection, change_detection.c 79-138), so the next
 * ecs_query_next also syncs the stale slice's monitor, a block the cache
 * freed (eval_iter.c 217-234): a crash after the FAIL line, or an abort,
 * also confirms (the handler prints FAIL and exits 1).
 *
 * Documented: Queries.md "Iteration" (the iterator returns entities that
 * match the query; the C++ each locks the iterated table, and this call
 * moves no entity from or to it) and "Sorting"; Manual.md "Error
 * handling". main returns 0 when no result contains an entity without
 * Position. The program reads no field after the calls (the slice's
 * arrays are freed). */
#include "flecs.h"
#include <stdio.h>
#include <stdlib.h>
#include <signal.h>

typedef struct { float x, y; } Position;

static int compare_x(ecs_entity_t e1, const void *p1, ecs_entity_t e2,
    const void *p2)
{
    (void)e1; (void)e2;
    const Position *a = p1, *b = p2;
    return (a->x > b->x) - (a->x < b->x);
}

static void on_crash(int sig) {
    printf("FAIL: signal %d while iterating the stale slices\n", sig);
    fflush(stdout);
    _Exit(1);
}

int main(void) {
    ecs_world_t *world = ecs_mini();
    ECS_COMPONENT(world, Position);
    ECS_TAG(world, Tag);
    ECS_TAG(world, TagB);
    ecs_add_pair(world, Tag, EcsOnDelete, EcsDelete);

    ecs_query_t *q = ecs_query(world, {
        .terms = {{ ecs_id(Position), .inout = EcsIn }},
        .order_by = ecs_id(Position),
        .order_by_callback = compare_x,
        .cache_kind = EcsQueryCacheAuto
    });

    ecs_entity_t e0 = ecs_insert(world, ecs_value(Position, {1, 0}));
    /* Position first, then Tag: no [Tag] table, so the delete of Tag frees
     * exactly one table */
    ecs_entity_t e1 = ecs_insert(world, ecs_value(Position, {2, 0}));
    ecs_add(world, e1, Tag);
    ecs_entity_t e2 = ecs_insert(world, ecs_value(Position, {3, 0}));
    ecs_table_t *t_tag = ecs_get_table(world, e1);
    (void)e2;

    /* setup: three slices */
    int results0 = 0;
    ecs_iter_t it0 = ecs_query_iter(world, q);
    while (ecs_query_next(&it0)) results0 ++;
    if (results0 != 3) {
        printf("INCONCLUSIVE: %d slices instead of 3\n", results0);
        return 2;
    }

    signal(SIGABRT, on_crash);
    signal(SIGSEGV, on_crash);
    signal(SIGBUS, on_crash);
    int results = 0, bad = 0, reused = -1;
    ecs_entity_t eB = 0;
    ecs_iter_t it = ecs_query_iter(world, q);
    while (ecs_query_next(&it)) {
        results ++;
        for (int i = 0; i < it.count; i ++) {
            if (!ecs_has(world, it.entities[i], Position)) {
                printf("result %d: entity %u%s has no Position (its table "
                    "is %s)\n", results, (unsigned)it.entities[i],
                    it.entities[i] == eB ? " (eB)" : "",
                    it.table == t_tag ? "the reused memory" : "another");
                fflush(stdout);
                bad = 1;
            }
        }
        if (results == 1) {
            if (it.count != 1 || it.entities[0] != e0) {
                printf("INCONCLUSIVE: the first result is not e0\n");
                return 2;
            }
            ecs_table_t *t = it.table;
            ecs_table_lock(world, t);
            ecs_delete(world, Tag);
            eB = ecs_new_w_id(world, TagB);
            reused = ecs_get_table(world, eB) == t_tag;
            ecs_table_unlock(world, t);
        }
        if (results > 10) break;
    }

    signal(SIGABRT, SIG_DFL);
    signal(SIGSEGV, SIG_DFL);
    signal(SIGBUS, SIG_DFL);
    printf("results: %d; [TagB] took the freed table's memory: %d\n",
        results, reused);
    int failed = 0;
    if (ecs_is_alive(world, e1)) {
        printf("INCONCLUSIVE: e1 survived the delete of Tag\n");
        failed = 2;
    } else if (bad) {
        printf("FAIL: the iterator returned an entity without Position from "
            "a slice of a deleted table whose memory a new table reused\n");
        failed = 1;
    } else if (reused != 1) {
        printf("INCONCLUSIVE: the new table did not reuse the freed memory\n");
        failed = 2;
    }
    ecs_query_fini(q);
    ecs_fini(world);
    return failed;
}
