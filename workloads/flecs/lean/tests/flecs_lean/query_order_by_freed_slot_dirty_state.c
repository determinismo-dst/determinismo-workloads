/* Prediction F55 (build flecs.c and this file with -DFLECS_USE_OS_ALLOC, so
 * that every flecs allocation is one OS allocation the test can guard):
 * skipping the slice of a table deleted while an order_by query is
 * iterated plants a one-element dirty state in the table store's zeroed
 * slot; the next table created in that slot keeps it, and the first
 * ecs_set on that table writes past it.
 *
 *   Tag: OnDelete Delete; Velocity (not used before)
 *   [Position]: e0 (1), e2 (3); [Position, Tag]: e1 (2); order_by Position
 *   slices: [Position] row 0, [Position, Tag] row 0, [Position] row 1
 *   after the first result (its table locked): ecs_delete(world, Tag)
 *   the iteration goes on: the second slice is skipped, e2 is returned
 *   after it: ev = ecs_new_w_id(world, ecs_id(Velocity))  (a new table)
 *             ecs_set(world, ev, Velocity, {1, 2})
 *
 * Deleting Tag deletes e1 and frees [Position, Tag]: flecs_table_fini zeroes
 * its ecs_table_t in world->store.tables (storage/table.c 1333-1336;
 * datastructures/sparse.c 391-393). The iterator skips the stale slice of
 * that table because its count, read from the zeroed memory, is 0, but
 * first syncs the slice's monitor (cache_iter.c 81-99:
 * flecs_query_sync_match_monitor), which calls flecs_table_get_dirty_state
 * on the zeroed table (change_detection.c 600-606): dirty_state is NULL, so
 * it allocates column_count + 1 = 1 int32 and stores the pointer in the
 * zeroed slot (storage/table.c 1432-1450). flecs_table_new takes the slot
 * freed last (table_graph.c 443: flecs_sparse_add_t, which does not zero it,
 * sparse.c 258-269), and neither it nor flecs_table_init sets dirty_state:
 * [Velocity] starts with the one-element block. ecs_set marks the column
 * dirty (ecs_set_id, entity.c 2026, flecs_copy_id, 833: flecs_table_mark_dirty,
 * storage/table.c 1397-1429):
 * dirty_state[1]++, past the block. Without FLECS_USE_OS_ALLOC the block is
 * a 16-byte chunk of the world's allocator: a table with 4 or more columns
 * then writes into the next chunk, and the table's free returns the chunk to
 * the wrong size class (storage/table.c 1318).
 *
 * The OS API is wrapped: each block has a header and a 16-byte guard after
 * it; a freed block is filled with 0xFF and kept (so the freed monitor the
 * same skip writes, F46, reads -1 and is not reused). A changed guard on a
 * 4-byte block confirms the prediction.
 *
 * Documented: Manual.md "Error handling" (no memory errors); Queries.md
 * "Iteration" (the iterated table is locked; the delete does not touch it)
 * and "Sorting". main returns 0 when no guard changes. */
#include "flecs.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <signal.h>

typedef struct { float x, y; } Position;
typedef struct { float x, y; } Velocity;

#define GUARD 16

typedef struct Hdr {
    struct Hdr *next, *prev;
    size_t size;
    int freed;
    int pad;
} Hdr;

static Hdr *blocks;

static void guard_set(Hdr *h) {
    memset((unsigned char*)(h + 1) + h->size, 0x5A, GUARD);
}

static int guard_ok(const Hdr *h) {
    const unsigned char *g = (const unsigned char*)(h + 1) + h->size;
    for (int i = 0; i < GUARD; i ++) if (g[i] != 0x5A) return 0;
    return 1;
}

static void* p_malloc(ecs_size_t size) {
    Hdr *h = malloc(sizeof(Hdr) + (size_t)size + GUARD);
    if (!h) return NULL;
    h->size = (size_t)size;
    h->freed = 0;
    h->prev = NULL;
    h->next = blocks;
    if (blocks) blocks->prev = h;
    blocks = h;
    guard_set(h);
    return h + 1;
}

static void* p_calloc(ecs_size_t size) {
    void *p = p_malloc(size);
    if (p) memset(p, 0, (size_t)size);
    return p;
}

static int bad_free;

static void p_free(void *ptr) {
    if (!ptr) return;
    Hdr *h = (Hdr*)ptr - 1;
    if (!guard_ok(h)) {
        bad_free ++;
        printf("guard of a %zu-byte block changed (seen when it is freed)\n",
            h->size);
    }
    h->freed = 1;
    memset(ptr, 0xFF, h->size); /* kept, never reused */
}

static void* p_realloc(void *ptr, ecs_size_t size) {
    if (!ptr) return p_malloc(size);
    Hdr *h = (Hdr*)ptr - 1;
    void *n = p_malloc(size);
    if (!n) return NULL;
    memcpy(n, ptr, h->size < (size_t)size ? h->size : (size_t)size);
    p_free(ptr);
    return n;
}

/* the live blocks whose guard changed; the size of the first */
static int scan(size_t *size_out) {
    int n = 0;
    for (Hdr *h = blocks; h; h = h->next) {
        if (!h->freed && !guard_ok(h)) {
            if (!n && size_out) *size_out = h->size;
            n ++;
        }
    }
    return n;
}

static int compare_x(ecs_entity_t e1, const void *p1, ecs_entity_t e2,
    const void *p2)
{
    (void)e1; (void)e2;
    const Position *a = p1, *b = p2;
    return (a->x > b->x) - (a->x < b->x);
}

static void on_crash(int sig) {
    printf("FAIL: signal %d after the stale slice was skipped\n", sig);
    fflush(stdout);
    _Exit(1);
}

int main(void) {
    ecs_set_os_api_impl();
    ecs_os_api.malloc_ = p_malloc;
    ecs_os_api.calloc_ = p_calloc;
    ecs_os_api.realloc_ = p_realloc;
    ecs_os_api.free_ = p_free;

    int os_alloc = 0;
    const ecs_build_info_t *bi = ecs_get_build_info();
    for (const char **f = bi->flags; f && *f; f ++) {
        if (!strcmp(*f, "FLECS_USE_OS_ALLOC")) os_alloc = 1;
    }
    if (!os_alloc) {
        printf("INCONCLUSIVE: build flecs.c with -DFLECS_USE_OS_ALLOC\n");
        return 2;
    }

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

    int results0 = 0;
    ecs_iter_t it0 = ecs_query_iter(world, q);
    while (ecs_query_next(&it0)) results0 ++;
    if (results0 != 3) {
        printf("INCONCLUSIVE: %d slices instead of 3\n", results0);
        return 2;
    }

    signal(SIGSEGV, on_crash);
    signal(SIGBUS, on_crash);
    signal(SIGABRT, on_crash);
    int results = 0, saw_e2 = 0;
    ecs_iter_t it = ecs_query_iter(world, q);
    while (ecs_query_next(&it)) {
        results ++;
        if (results == 1) {
            if (it.count != 1 || it.entities[0] != e0) {
                printf("INCONCLUSIVE: the first result is not e0\n");
                return 2;
            }
            ecs_table_t *t = it.table;
            ecs_table_lock(world, t);
            ecs_delete(world, Tag);
            ecs_table_unlock(world, t);
        } else {
            for (int i = 0; i < it.count; i ++) {
                if (it.entities[i] == e2) saw_e2 ++;
            }
        }
        if (results > 10) break;
    }
    size_t sz = 0;
    int before = scan(NULL);

    ecs_entity_t ev = ecs_new_w_id(world, ecs_id(Velocity));
    int reused = ecs_get_table(world, ev) == t_tag;
    ecs_set(world, ev, Velocity, {1, 2});
    int after = scan(&sz);
    signal(SIGSEGV, SIG_DFL);
    signal(SIGBUS, SIG_DFL);
    signal(SIGABRT, SIG_DFL);

    printf("results %d (e2 %d); [Velocity] took the freed table's memory: %d;"
        " changed guards before the set %d, after it %d (first: %zu-byte "
        "block)\n", results, saw_e2, reused, before, after, sz);
    int failed = 0;
    if (ecs_is_alive(world, e1) || saw_e2 != 1) {
        printf("INCONCLUSIVE: the iteration did not go as set up\n");
        failed = 2;
    } else if (after > before) {
        printf("FAIL: ecs_set on the table that took the freed slot wrote "
            "past a %zu-byte block (its dirty state)\n", sz);
        failed = 1;
    } else if (!reused) {
        printf("INCONCLUSIVE: the new table did not reuse the freed "
            "memory\n");
        failed = 2;
    }
    ecs_query_fini(q);
    ecs_fini(world);
    if (!failed && bad_free) {
        printf("FAIL: a block's guard changed (seen at ecs_fini)\n");
        failed = 1;
    }
    return failed;
}
