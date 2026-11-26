/* Prediction F35 (second form): while a cascade query is iterated, a call
 * that empties the group being iterated frees that group; the next
 * ecs_query_next reads the freed group, and the entities of later groups
 * are not returned.
 *
 * Group moves happen as in query_cascade_table_twice.c. When the moved table
 * was the last one of its group, flecs_query_cache_remove_table_from_group
 * (query/cache/group.c 176-213) removes the group:
 * flecs_query_cache_remove_group (118-130) unlinks it, sets its next to
 * NULL, finalizes its table vector and, for a group other than the default
 * one, frees it (ecs_map_remove_free, 109, an ecs_os_free; the group was
 * ecs_os_calloc'd by ecs_map_insert_alloc_t, 64-66). The iterator still
 * points at it (qit->group, qit->tables = &group->tables): the next
 * flecs_query_cache_next (cache_iter.c 41-123) reads its table count and its
 * next field from freed memory.
 *
 * Program (query created first):
 *   x root without Position; m child of x without Position
 *   p1 root with Position                  group 0
 *   c1 child of p1                         group 1 (alone)
 *   g child of m                           group 2
 *   iterate; after the second result (c1's table, locked), p1 becomes a
 *   child of m: p1 moves into g's table (it exists), c1's table moves to the
 *   new group 3, and group 1, now empty, is freed while the iterator is in
 *   it.
 *
 * To make the read of freed memory deterministic, the OS API's free is
 * replaced: it fills the block with 0xA5 and keeps it (sizes come from a
 * header the wrapped malloc/calloc/realloc add). The freed group's table
 * count then reads as a negative number and its next as 0xA5A5A5A5A5A5A5A5:
 * the iterator follows that pointer and the program crashes. Without the
 * wrapper the read is of freed heap memory (valgrind: invalid read), and the
 * group's next was set to NULL before the free, so the iteration usually
 * just ends, without g.
 *
 * Documented: Queries.md "Iteration" (C++): a table is locked so that "no
 * entities can be moved from or to it", to avoid "iterating an entity twice,
 * or missing an entity"; g does not move. Manual.md "Error handling" (no
 * crash). main returns 0 when g is returned once and nothing crashes; a
 * crash or a non-zero return confirms the prediction. */
#include "flecs.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct { float x, y; } Position;

#define HDR 16

static void* p_malloc(ecs_size_t size) {
    unsigned char *b = malloc((size_t)size + HDR);
    if (!b) return NULL;
    *(size_t*)b = (size_t)size;
    return b + HDR;
}

static void* p_calloc(ecs_size_t size) {
    unsigned char *b = calloc(1, (size_t)size + HDR);
    if (!b) return NULL;
    *(size_t*)b = (size_t)size;
    return b + HDR;
}

static void p_free(void *ptr) {
    if (!ptr) return;
    unsigned char *b = (unsigned char*)ptr - HDR;
    memset(ptr, 0xA5, *(size_t*)b);
    /* kept: a freed block is never reused, so a stale pointer reads 0xA5 */
}

static void* p_realloc(void *ptr, ecs_size_t size) {
    if (!ptr) return p_malloc(size);
    unsigned char *b = (unsigned char*)ptr - HDR;
    size_t old = *(size_t*)b;
    void *n = p_malloc(size);
    if (!n) return NULL;
    memcpy(n, ptr, old < (size_t)size ? old : (size_t)size);
    p_free(ptr);
    return n;
}

int main(void) {
    ecs_set_os_api_impl();
    ecs_os_api.malloc_ = p_malloc;
    ecs_os_api.calloc_ = p_calloc;
    ecs_os_api.realloc_ = p_realloc;
    ecs_os_api.free_ = p_free;

    ecs_world_t *world = ecs_mini();
    ECS_COMPONENT(world, Position);

    ecs_query_t *q = ecs_query(world, {
        .terms = {
            { ecs_id(Position) },
            { ecs_id(Position), .src.id = EcsCascade, .oper = EcsOptional }
        },
        .cache_kind = EcsQueryCacheAuto
    });

    ecs_entity_t x = ecs_new(world);
    ecs_entity_t m = ecs_new_w_pair(world, EcsChildOf, x);
    ecs_entity_t p1 = ecs_insert(world, ecs_value(Position, {1, 1}));
    ecs_entity_t c1 = ecs_new_w_pair(world, EcsChildOf, p1);
    ecs_set(world, c1, Position, {2, 2});
    ecs_entity_t g = ecs_new_w_pair(world, EcsChildOf, m);
    ecs_set(world, g, Position, {3, 3});

    /* Control: three results (depths 0, 1, 2) */
    int results0 = 0;
    ecs_iter_t it0 = ecs_query_iter(world, q);
    while (ecs_query_next(&it0)) results0 ++;
    if (results0 != 3) {
        printf("INCONCLUSIVE: setup iteration returned %d results\n", results0);
        return 2;
    }

    int seen_g = 0, results = 0;
    ecs_iter_t it = ecs_query_iter(world, q);
    while (ecs_query_next(&it)) {
        results ++;
        for (int i = 0; i < it.count; i ++) {
            if (it.entities[i] == g) seen_g ++;
        }
        if (results == 2) {
            if (it.count != 1 || it.entities[0] != c1) {
                printf("INCONCLUSIVE: the second result is not c1's table\n");
                return 2;
            }
            ecs_table_t *t = it.table;
            ecs_table_lock(world, t);
            ecs_add_pair(world, p1, EcsChildOf, m);
            ecs_table_unlock(world, t);
            printf("p1 is now a child of m; continuing the iteration\n");
            fflush(stdout);
        }
        if (results > 10) break;
    }

    int failed = 0;
    if (seen_g != 1) {
        printf("FAIL: g returned %d times (expected 1); g did not move\n", seen_g);
        failed = 1;
    }
    ecs_query_fini(q);
    ecs_fini(world);
    return failed;
}
