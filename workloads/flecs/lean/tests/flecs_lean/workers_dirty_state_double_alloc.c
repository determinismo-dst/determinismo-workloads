/* Prediction F33 (needs threads: link with -lpthread): when a multi-threaded
 * system's query has change detection, every worker syncs the match monitor
 * of every table it passes (eval_iter.c 217-234: the chained query iterator
 * of ecs_worker_next, iter.c 1036-1095), and the sync allocates the table's
 * dirty state on first use (flecs_table_get_dirty_state, storage/table.c
 * 1432-1450: `if (!table->dirty_state) table->dirty_state = flecs_alloc_n(
 * &world->allocator, ...)`). Nothing synchronizes the workers there: two of
 * them can both see NULL, both allocate (from the world's allocator, which
 * is not thread-safe either), and both store; one allocation is lost. The
 * same holds for the match's monitor (change_detection.c 79-138). This is a
 * data race (C11 5.1.2.4: undefined behavior).
 *
 * The program makes the race window wide instead of waiting for it:
 * - table T has 599 four-byte components, so its dirty state is 2400 bytes;
 *   a block allocator with one chunk per block goes straight to the OS
 *   (block_allocator.c 150-158), so each allocation of T's dirty state is one
 *   ecs_os_malloc(2400);
 * - the OS API malloc is wrapped: during ecs_progress, a 2400-byte request
 *   waits (up to 2 seconds) until a second thread makes one. A correct
 *   program allocates T's dirty state once, so the first caller just times
 *   out. With the race both threads arrive, and T's dirty state is
 *   allocated twice; the first one leaks.
 *
 * Setup: the system's query gets change detection on the main thread first
 * (ecs_query_changed over an existing table, which creates monitors and sets
 * EcsQueryHasChangeDetection); T is created after that, so it has neither a
 * monitor nor a dirty state when the frame starts.
 *
 * Documented: Systems.md "Threading" (multi_threaded systems run on the
 * worker threads); Queries.md "Change Detection"; C11 data-race rule. */
#include "flecs.h"
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#define NCOMP 599
#define DIRTY_SIZE ((NCOMP + 1) * 4)

static ecs_os_api_malloc_t real_malloc;
static volatile int in_frame;
static int arrived;
static int dirty_allocs;

static void* malloc_rendezvous(ecs_size_t size) {
    if (in_frame && size == DIRTY_SIZE) {
        __atomic_add_fetch(&dirty_allocs, 1, __ATOMIC_SEQ_CST);
        __atomic_add_fetch(&arrived, 1, __ATOMIC_SEQ_CST);
        for (int i = 0; i < 2000; i ++) {
            if (__atomic_load_n(&arrived, __ATOMIC_SEQ_CST) >= 2) break;
            usleep(1000);
        }
    }
    return real_malloc(size);
}

static int runs;
static void Sys(ecs_iter_t *it) {
    (void)it;
    __atomic_add_fetch(&runs, 1, __ATOMIC_SEQ_CST);
}

int main(void) {
    ecs_set_os_api_impl();
    real_malloc = ecs_os_api.malloc_;
    ecs_os_api.malloc_ = malloc_rendezvous;

    ecs_world_t *world = ecs_init();

    static ecs_id_t ids[NCOMP];
    for (int i = 0; i < NCOMP; i ++) {
        ids[i] = ecs_component_init(world, &(ecs_component_desc_t){
            .type.size = 4, .type.alignment = 4 });
    }
    ecs_id_t c0 = ids[0];

    ecs_entity_t sys = ecs_entity(world, { .name = "Sys" });
    ecs_add_pair(world, sys, EcsDependsOn, EcsOnUpdate);
    ecs_system(world, {
        .entity = sys,
        .query.terms = {{ .id = c0, .inout = EcsIn }},
        .query.flags = EcsQueryDetectChanges,
        .callback = Sys,
        .multi_threaded = true
    });
    const ecs_system_t *s = ecs_system_get(world, sys);
    if (!s) { printf("INCONCLUSIVE: no system\n"); return 2; }
    ecs_query_t *q = s->query;

    /* a first table [c0]: ecs_query_changed creates its monitor and turns on
     * EcsQueryHasChangeDetection for the system's query */
    ecs_entity_t e0 = ecs_new(world);
    ecs_add_id(world, e0, c0);
    ecs_query_changed(q);

    /* T: created after, no monitor, no dirty state */
    ecs_table_t *t = ecs_table_find(world, ids, NCOMP);
    if (!t) { printf("INCONCLUSIVE: no table\n"); return 2; }
    ecs_new_w_table(world, t);

    ecs_set_threads(world, 2);

    in_frame = 1;
    ecs_progress(world, 0);
    in_frame = 0;

    int failed = 0;
    if (runs < 1) {
        printf("INCONCLUSIVE: the system did not run (%d)\n", runs);
        failed = 2;
    } else if (dirty_allocs == 0) {
        printf("INCONCLUSIVE: no dirty state was allocated during the frame\n");
        failed = 2;
    } else if (dirty_allocs > 1) {
        printf("FAIL: the dirty state of one table was allocated %d times by "
            "the worker threads of one system; all but one leak\n",
            dirty_allocs);
        failed = 1;
    }
    ecs_set_threads(world, 0);
    ecs_fini(world);
    return failed;
}
