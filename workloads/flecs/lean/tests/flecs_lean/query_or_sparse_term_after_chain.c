/* Prediction F34: a cached query `TagA || Position, TagC`, with Position a
 * Sparse component, returns at most one table, may return an entity without
 * TagC, and its compilation writes before the start of the op array.
 *
 * The validator (query/validator.c 1075-1087, 1234-1238) leaves TagA and
 * TagC cacheable and Position not (F29). The query is created (the cache's
 * own query, `TagA || TagC`, is valid) and compiled
 * (query/compiler/compiler.c 1047-1340):
 *   0 SetIds, 1 Cache (TagA and TagC), then Position, alone:
 * flecs_query_compile_term (compiler_term.c 1152-1563) sees Position as the
 * last term of an Or chain whose first term it never compiled: is_or is
 * true, first_or false, last_or true. No Or block was begun, so
 * flecs_query_end_block_or (282-360) runs with ctx->cur->lbl_begin == -1:
 *   - it reads ops[-1].flags and writes ops[-1].next (306-309), before the
 *     start of the op vector (stage->operations, an ecs_os_realloc'd array);
 *   - it sets the Position op's prev and the End's prev to -1 (310-311).
 * At run time (engine/eval.c 1733-1785) the Cache op yields the cache's
 * first non-empty table; the Position op tests it; on failure it jumps to
 * label -1, which ends the iteration; on success the End and the Yield
 * follow, and the next ecs_query_next redoes the End, whose prev is -1: the
 * iteration ends. So the query returns the first cached table if it has
 * Position, else nothing; TagC is never tested.
 *
 * Program: the query is created on an empty world, so the cache holds tables
 * in creation order: [TagA] (empty), [TagA, Position] (e1),
 * [TagA, TagC] (e2), [Position, TagC] (e3).
 *   documented (Queries.md "Or"): e2 and e3;
 *   predicted: e1 only.
 * The same query without a cache (control) returns e2 and e3.
 *
 * The out-of-bounds write is made visible with the OS API: every block gets
 * a 64-byte zeroed guard before it; a free or realloc that finds the guard
 * changed reports it (ops[-1].next lands 42 bytes before the array). With
 * the guard zeroed, ops[-1].flags reads 0, so the compiler takes the same
 * path every run.
 *
 * Documented: Queries.md "Or" operator; ComponentTraits.md "Sparse trait"
 * ("ECS operations and queries work as expected with sparse components").
 * main returns 0 when the cached query returns e2 and e3 and no guard was
 * touched. */
#include "flecs.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct { float x, y; } Position;

#define GUARD 64
#define CANARY 48
static int corrupted;

static void guard_check(void *base) {
    unsigned char *b = base;
    for (int i = 0; i < CANARY; i ++) {
        if (b[i] != 0) {
            if (!corrupted) {
                printf("guard of a %lu-byte block changed at offset %d (%d bytes "
                    "before the block)\n", (unsigned long)*(size_t*)(b + CANARY),
                    i, GUARD - i);
            }
            corrupted = 1;
            return;
        }
    }
}

static void* g_malloc(ecs_size_t size) {
    unsigned char *b = malloc((size_t)size + GUARD);
    if (!b) return NULL;
    memset(b, 0, GUARD);
    *(size_t*)(b + CANARY) = (size_t)size;
    return b + GUARD;
}

static void* g_calloc(ecs_size_t size) {
    unsigned char *b = calloc(1, (size_t)size + GUARD);
    if (!b) return NULL;
    *(size_t*)(b + CANARY) = (size_t)size;
    return b + GUARD;
}

static void* g_realloc(void *ptr, ecs_size_t size) {
    if (!ptr) return g_malloc(size);
    unsigned char *b = (unsigned char*)ptr - GUARD;
    guard_check(b);
    b = realloc(b, (size_t)size + GUARD);
    if (!b) return NULL;
    *(size_t*)(b + CANARY) = (size_t)size;
    return b + GUARD;
}

static void g_free(void *ptr) {
    if (!ptr) return;
    unsigned char *b = (unsigned char*)ptr - GUARD;
    guard_check(b);
    free(b);
}

static int contains(ecs_entity_t *v, int n, ecs_entity_t e) {
    for (int i = 0; i < n; i ++) if (v[i] == e) return 1;
    return 0;
}

static int run(ecs_world_t *world, ecs_query_t *q, ecs_entity_t *out) {
    int n = 0;
    ecs_iter_t it = ecs_query_iter(world, q);
    while (ecs_query_next(&it)) {
        for (int i = 0; i < it.count && n < 16; i ++) out[n ++] = it.entities[i];
    }
    return n;
}

int main(void) {
    ecs_set_os_api_impl();
    ecs_os_api.malloc_ = g_malloc;
    ecs_os_api.calloc_ = g_calloc;
    ecs_os_api.realloc_ = g_realloc;
    ecs_os_api.free_ = g_free;

    ecs_world_t *world = ecs_mini();
    ECS_COMPONENT(world, Position);
    ECS_TAG(world, TagA);
    ECS_TAG(world, TagC);
    ecs_add_id(world, ecs_id(Position), EcsSparse);

    ecs_query_desc_t desc = {
        .terms = {
            { .id = TagA, .oper = EcsOr },
            { .id = ecs_id(Position) },
            { .id = TagC }
        },
        .cache_kind = EcsQueryCacheAuto
    };
    ecs_query_t *q = ecs_query_init(world, &desc);
    desc.cache_kind = EcsQueryCacheNone;
    ecs_query_t *q0 = ecs_query_init(world, &desc);
    if (!q || !q0) {
        printf("INCONCLUSIVE: a query was rejected\n");
        return 2;
    }

    ecs_entity_t e1 = ecs_new_w_id(world, TagA);
    ecs_set(world, e1, Position, {1, 2});
    ecs_entity_t e2 = ecs_new_w_id(world, TagA);
    ecs_add_id(world, e2, TagC);
    ecs_entity_t e3 = ecs_insert(world, ecs_value(Position, {3, 4}));
    ecs_add_id(world, e3, TagC);

    int failed = 0;
    ecs_entity_t got[16], ref[16];
    int n0 = run(world, q0, ref);
    printf("uncached: %d entities:", n0);
    for (int i = 0; i < n0; i ++) printf(" %s", ref[i] == e1 ? "e1" :
        ref[i] == e2 ? "e2" : ref[i] == e3 ? "e3" : "?");
    printf("\n");
    if (n0 != 2 || !contains(ref, n0, e2) || !contains(ref, n0, e3)) {
        printf("INCONCLUSIVE: the uncached query did not return e2 and e3\n");
        return 2;
    }

    int n = run(world, q, got);
    printf("cached: %d entities:", n);
    for (int i = 0; i < n; i ++) printf(" %s", got[i] == e1 ? "e1" :
        got[i] == e2 ? "e2" : got[i] == e3 ? "e3" : "?");
    printf("\n");
    if (n != 2 || !contains(got, n, e2) || !contains(got, n, e3)) {
        printf("FAIL: the cached query does not return e2 and e3\n");
        failed = 1;
    }

    ecs_query_fini(q);
    ecs_query_fini(q0);
    ecs_fini(world);

    if (corrupted) {
        printf("FAIL: a block's guard was overwritten (write before the start "
            "of an array)\n");
        failed = 1;
    }
    return failed;
}
