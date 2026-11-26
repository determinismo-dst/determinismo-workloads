/* Prediction F55, corrected in round 8 (the leak form). Build flecs.c and
 * this file either with -DFLECS_USE_OS_ALLOC (the wrapper below tracks
 * every block) or with -DFLECS_SANITIZE (flecs's own leak check aborts in
 * ecs_fini); a plain build returns 2 (INCONCLUSIVE).
 *
 *   Tag: OnDelete Delete; Velocity (not used before)
 *   [Position]: e0 (1), e2 (3); [Position, Tag]: e1 (2); order_by Position
 *   slices: [Position] row 0, [Position, Tag] row 0, [Position] row 1
 *   after the first result (its table locked): ecs_delete(world, Tag)
 *   the next ecs_query_next skips the second slice and returns e2
 *   after the iteration: ev = ecs_new_w_id(world, Velocity) (takes the slot)
 *
 * Deleting Tag frees [Position, Tag]: flecs_table_fini zeroes its ecs_table_t
 * in world->store.tables (storage/table.c 1333-1336; sparse.c 391-393).
 * The skip of its stale slice (count 0, read from the zeroed memory) first
 * syncs the slice's monitor (cache_iter.c 81-99,
 * flecs_query_sync_match_monitor), which calls flecs_table_get_dirty_state
 * on the zeroed table (change_detection.c 600-606): dirty_state is NULL, so
 * it allocates column_count + 1 = 1 int32 and stores the pointer in the
 * zeroed slot (storage/table.c 1432-1450). Round 7 predicted that the next
 * table created in the slot keeps that block and that ecs_set writes past
 * it; the real flecs did not, because flecs_init_table sets
 * table->dirty_state = NULL for every new table (table_graph.c 418-430,
 * line 424). So the block is lost: the new table forgets it, and a dead
 * slot is never finalized. Nothing frees it.
 *
 * With FLECS_USE_OS_ALLOC every flecs allocation is one ecs_os_malloc: the
 * wrapper tags the blocks allocated during the ecs_query_next call that
 * skips the stale slice, and after ecs_fini reports the tagged 4-byte
 * blocks still live. With FLECS_SANITIZE, flecs_ballocator_fini reports
 * "Leak detected! (size 16, remaining = 1)" and aborts in ecs_fini
 * (block_allocator.c 96-115); the handler prints FAIL. A control world,
 * run first, deletes Tag before the iterator is created: nothing leaks.
 *
 * Documented: flecs.h, FLECS_SANITIZE ("Enables expensive checks that can
 * detect issues early. Recommended for running tests"); Manual.md "Error
 * handling"; Queries.md "Iteration" and "Sorting". main returns 0 when no
 * tagged block leaks (and ecs_fini does not abort). */
#include "flecs.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <signal.h>

typedef struct { float x, y; } Position;
typedef struct { float x, y; } Velocity;

typedef struct Hdr {
    struct Hdr *next;
    size_t size;
    int freed;
    int tagged;
} Hdr;

static Hdr *blocks;
static int tagging;

static void* p_malloc(ecs_size_t size) {
    Hdr *h = malloc(sizeof(Hdr) + (size_t)size);
    if (!h) return NULL;
    h->size = (size_t)size;
    h->freed = 0;
    h->tagged = tagging;
    h->next = blocks;
    blocks = h;
    return h + 1;
}

static void* p_calloc(ecs_size_t size) {
    void *p = p_malloc(size);
    if (p) memset(p, 0, (size_t)size);
    return p;
}

static void p_free(void *ptr) {
    if (!ptr) return;
    Hdr *h = (Hdr*)ptr - 1;
    h->freed = 1;
    memset(ptr, 0xFF, h->size); /* kept, never reused */
}

static void* p_realloc(void *ptr, ecs_size_t size) {
    if (!ptr) return p_malloc(size);
    Hdr *h = (Hdr*)ptr - 1;
    void *n = p_malloc(size);
    if (!n) return NULL;
    memcpy(n, ptr, h->size < (size_t)size ? h->size : (size_t)size);
    ((Hdr*)n - 1)->tagged = h->tagged;
    p_free(ptr);
    return n;
}

/* tagged blocks still live, the number of 4-byte ones in *n4 */
static int live_tagged(int *n4) {
    int n = 0;
    *n4 = 0;
    for (Hdr *h = blocks; h; h = h->next) {
        if (h->tagged && !h->freed) {
            n ++;
            if (h->size == sizeof(int32_t)) (*n4) ++;
        }
    }
    return n;
}

static void untag_all(void) {
    for (Hdr *h = blocks; h; h = h->next) h->tagged = 0;
}

static int compare_x(ecs_entity_t e1, const void *p1, ecs_entity_t e2,
    const void *p2)
{
    (void)e1; (void)e2;
    const Position *a = p1, *b = p2;
    return (a->x > b->x) - (a->x < b->x);
}

static int stage; /* 0 control world, 1 the prediction, 2 its ecs_fini */

static void on_signal(int sig) {
    if (stage == 2 && sig == SIGABRT) {
        printf("FAIL: ecs_fini aborted (FLECS_SANITIZE leak check: a block "
            "was never freed)\n");
    } else {
        printf("INCONCLUSIVE: signal %d in stage %d\n", sig, stage);
    }
    fflush(stdout);
    _Exit(stage == 2 ? 1 : 2);
}

/* Returns the number of results of the second iteration; *skip_ok is set
 * when the iteration went as set up. */
static int run(int delete_during, int *skip_ok) {
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

    ecs_iter_t it0 = ecs_query_iter(world, q);
    while (ecs_query_next(&it0)) { }

    if (!delete_during) {
        ecs_delete(world, Tag);
    }

    int results = 0, saw_e2 = 0;
    ecs_iter_t it = ecs_query_iter(world, q);
    for (;;) {
        if (results == 1) tagging = 1; /* the call that skips the slice */
        bool more = ecs_query_next(&it);
        tagging = 0;
        if (!more) break;
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
        for (int i = 0; i < it.count; i ++) {
            if (it.entities[i] == e2) saw_e2 ++;
        }
        if (results > 10) break;
    }
    *skip_ok = !ecs_is_alive(world, e1) && saw_e2 == 1;

    ecs_entity_t ev = ecs_new_w_id(world, ecs_id(Velocity));
    (void)ev;
    ecs_query_fini(q);
    if (stage == 1) stage = 2;
    ecs_fini(world);
    if (stage == 2) stage = 1;
    return results;
}

int main(void) {
    const ecs_build_info_t *bi = ecs_get_build_info();
    int os_alloc = 0;
    for (const char **f = bi->flags; f && *f; f ++) {
        if (!strcmp(*f, "FLECS_USE_OS_ALLOC")) os_alloc = 1;
    }
    if (!os_alloc && !bi->sanitize) {
        printf("INCONCLUSIVE: build flecs.c with -DFLECS_USE_OS_ALLOC or "
            "-DFLECS_SANITIZE\n");
        return 2;
    }

    ecs_set_os_api_impl();
    if (os_alloc) {
        ecs_os_api.malloc_ = p_malloc;
        ecs_os_api.calloc_ = p_calloc;
        ecs_os_api.realloc_ = p_realloc;
        ecs_os_api.free_ = p_free;
    }
    signal(SIGABRT, on_signal);
    signal(SIGSEGV, on_signal);
    signal(SIGBUS, on_signal);

    int ok = 0, n4 = 0;
    stage = 0;
    int r = run(0, &ok);
    int live = live_tagged(&n4);
    printf("control (Tag deleted before the iterator): %d results; blocks "
        "allocated by the second ecs_query_next and live after ecs_fini: %d "
        "(4-byte: %d)\n", r, live, n4);
    /* the slices are rebuilt: [Position] rows 0..1, one result */
    if (r != 1 || !ok || (os_alloc && n4)) {
        printf("INCONCLUSIVE: the control did not behave\n");
        return 2;
    }
    untag_all();

    stage = 1;
    r = run(1, &ok);
    live = live_tagged(&n4);
    printf("prediction (Tag deleted after the first result): %d results; "
        "blocks allocated by the ecs_query_next that skipped the stale slice "
        "and live after ecs_fini: %d (4-byte: %d)\n", r, live, n4);
    if (!ok) {
        printf("INCONCLUSIVE: the iteration did not go as set up\n");
        return 2;
    }
    if (os_alloc && n4) {
        printf("FAIL: the 1-int dirty state the skip allocated for the "
            "zeroed table slot was never freed\n");
        return 1;
    }
    printf("no leak seen\n");
    return 0;
}
