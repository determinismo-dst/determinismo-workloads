/* Prediction F36: while a cached query with change detection is iterated, a
 * call that creates a table the query matches can reallocate the group's
 * table array; the next ecs_query_next then reads and writes the freed array
 * through qit->elem.
 *
 * flecs_query_cache_next (query/cache/cache_iter.c 41-123) stores a pointer
 * to the current match in qit->elem (104). A new matching table is appended
 * to its group (flecs_query_cache_add_table_to_group, group.c 150-171:
 * ecs_vec_append); a full vector is reallocated (vec.c 366-379 -> 179-215:
 * capacities 2, 4, 8, ...; flecs_brealloc frees the old chunk,
 * block_allocator.c 287-326). The next ecs_query_next starts with change
 * detection on the previous result (eval_iter.c 217-234, 492-500): when the
 * query has EcsQueryHasChangeDetection it calls
 * flecs_query_sync_match_monitor(impl, qit->elem) (change_detection.c
 * 581-633), which reads match->_monitor and match->base.table and writes the
 * monitor (and allocates one into the freed match when it has none).
 *
 * Program: a cache match is 80 bytes; with 32 tables the array is 2560
 * bytes, a size the block allocator takes straight from the OS
 * (block_allocator.c 150-158, chunks_per_block 1) and frees with
 * ecs_os_free. The query is created first; then [Position] (e0) and 31
 * tables [Position, Tag_i] fill the array (32 of 32). ecs_query_changed
 * turns change detection on. During the iteration, after the first result
 * ([Position], locked as the C++ each locks it), an entity that has only
 * Tag_31 gets Position: [Position, Tag_31] is the 33rd table, the array grows
 * to 64 and the old one is freed.
 *
 * To make the stale access deterministic the OS API's free fills the block
 * with 0xA5 and keeps it: the next ecs_query_next reads base.table as
 * 0xA5A5A5A5A5A5A5A5 and crashes in flecs_table_get_dirty_state. Without
 * the wrapper the reads and writes go to freed heap memory (valgrind:
 * invalid read/write).
 *
 * Documented: Queries.md "Iteration" (C++ each locks the iterated table; no
 * entity of it moves) and "Change Detection"; Manual.md "Error handling".
 * main returns 0 when every entity is returned once and nothing crashes. */
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

#define NTAG 32

int main(void) {
    ecs_set_os_api_impl();
    ecs_os_api.malloc_ = p_malloc;
    ecs_os_api.calloc_ = p_calloc;
    ecs_os_api.realloc_ = p_realloc;
    ecs_os_api.free_ = p_free;

    ecs_world_t *world = ecs_mini();
    ECS_COMPONENT(world, Position);

    ecs_entity_t tags[NTAG];
    for (int i = 0; i < NTAG; i ++) tags[i] = ecs_new(world);

    ecs_query_t *q = ecs_query(world, {
        .terms = {{ ecs_id(Position), .inout = EcsIn }},
        .cache_kind = EcsQueryCacheAuto,
        .flags = EcsQueryDetectChanges
    });

    ecs_entity_t e0 = ecs_insert(world, ecs_value(Position, {0, 0}));
    for (int i = 0; i < NTAG - 1; i ++) {
        ecs_entity_t e = ecs_new_w_id(world, tags[i]);
        ecs_set(world, e, Position, {1, 1});
    }
    ecs_entity_t late = ecs_new_w_id(world, tags[NTAG - 1]);

    int results0 = 0;
    ecs_iter_t it0 = ecs_query_iter(world, q);
    while (ecs_query_next(&it0)) results0 ++;
    if (results0 != NTAG) {
        printf("INCONCLUSIVE: setup iteration returned %d tables, expected %d\n",
            results0, NTAG);
        return 2;
    }

    ecs_query_changed(q); /* turns on EcsQueryHasChangeDetection */

    int results = 0, seen_e0 = 0;
    ecs_iter_t it = ecs_query_iter(world, q);
    while (ecs_query_next(&it)) {
        results ++;
        for (int i = 0; i < it.count; i ++) if (it.entities[i] == e0) seen_e0 ++;
        if (results == 1) {
            if (it.count != 1 || it.entities[0] != e0) {
                printf("INCONCLUSIVE: the first result is not e0's table\n");
                return 2;
            }
            ecs_table_t *t = it.table;
            ecs_table_lock(world, t);
            ecs_set(world, late, Position, {2, 2});
            ecs_table_unlock(world, t);
            printf("created the 33rd table; continuing the iteration\n");
            fflush(stdout);
        }
        if (results > 100) break;
    }

    int failed = 0;
    if (seen_e0 != 1 || results < NTAG) {
        printf("FAIL: e0 returned %d times, %d results (expected 1 and at least "
            "%d)\n", seen_e0, results, NTAG);
        failed = 1;
    }
    ecs_query_fini(q);
    ecs_fini(world);
    return failed;
}
