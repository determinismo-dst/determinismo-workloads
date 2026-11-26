/* Prediction F47 (needs threads: link with -lpthread): every stage that runs
 * a multi-threaded system whose query has order_by sorts the system's
 * tables in place at the same time as the others, with no synchronization;
 * the stages also rebuild the query's slice vector and increment its
 * match_count at once.
 *
 * Each stage creates its own iterator over the system's query
 * (flecs_run_intern, addons/system/system.c 80-81; the main thread runs
 * stage 0 while the workers run the others, pipeline.c 627-645). Creating
 * it runs flecs_query_cache_iter_init (query/cache/cache_iter.c 11-37),
 * which for an order_by query calls flecs_query_cache_sort_tables
 * (order_by.c 228-321): a table whose match monitor is missing or out of
 * date is sorted in place (flecs_query_cache_sort_table, 12-45: a
 * quicksort whose swaps, flecs_table_swap, storage/table.c 2014-2090,
 * exchange entity ids, entity records and every column), then the slices
 * are rebuilt (215-225: ecs_vec_clear and ecs_vec_append_t with a NULL
 * allocator, an OS realloc) and cache->match_count is incremented (320).
 * The monitor is synced only when an iteration moves past the table
 * (eval_iter.c 217-234), so a stage that creates its iterator while another
 * is still sorting sees the table as changed and sorts it too.
 *
 * The program detects the overlap instead of waiting for corruption: the
 * order_by callback is the rendezvous. The first time a thread enters it
 * during the frame, it waits (up to 2 seconds) for a second thread to enter
 * too. A correct program sorts the table on one thread only, so the wait
 * times out; with the race both threads are inside the sort of the same
 * table at once. After the frame the table is checked: every entity once,
 * each with its own value.
 *
 * Documented: Systems.md "Threading" (multi_threaded systems run on all
 * worker threads; staging "makes it safe for multiple threads to iterate
 * the same world without taking locks"); Queries.md "Sorting"; C11
 * 5.1.2.4 (a data race is undefined behavior). A crash or an abort also
 * confirms the prediction (the handler prints FAIL and exits 1). main
 * returns 0 when no two threads sort at once and the table is intact. */
#include "flecs.h"
#include <stdio.h>
#include <stdlib.h>
#include <signal.h>
#include <unistd.h>

#define N 64

typedef struct { float x, y; } Position;

static volatile int in_frame;
static int arrived, inside, overlap, compares;
static __thread int waited;

static int compare_x(ecs_entity_t e1, const void *p1, ecs_entity_t e2,
    const void *p2)
{
    (void)e1; (void)e2;
    const Position *a = p1, *b = p2;
    if (in_frame) {
        __atomic_add_fetch(&compares, 1, __ATOMIC_SEQ_CST);
        if (__atomic_add_fetch(&inside, 1, __ATOMIC_SEQ_CST) > 1) {
            __atomic_store_n(&overlap, 1, __ATOMIC_SEQ_CST);
        }
        if (!waited) {
            waited = 1;
            __atomic_add_fetch(&arrived, 1, __ATOMIC_SEQ_CST);
            for (int i = 0; i < 2000; i ++) {
                if (__atomic_load_n(&arrived, __ATOMIC_SEQ_CST) >= 2) break;
                usleep(1000);
            }
            if (__atomic_load_n(&inside, __ATOMIC_SEQ_CST) > 1) {
                __atomic_store_n(&overlap, 1, __ATOMIC_SEQ_CST);
            }
        }
        __atomic_sub_fetch(&inside, 1, __ATOMIC_SEQ_CST);
    }
    return (a->x > b->x) - (a->x < b->x);
}

static void on_crash(int sig) {
    printf("FAIL: signal %d during the frame (the stages sorted one table "
        "at once)\n", sig);
    fflush(stdout);
    _Exit(1);
}

static int runs;
static void Sys(ecs_iter_t *it) {
    (void)it;
    __atomic_add_fetch(&runs, 1, __ATOMIC_SEQ_CST);
}

int main(void) {
    ecs_set_os_api_impl();
    ecs_world_t *world = ecs_init();
    ECS_COMPONENT(world, Position);

    ecs_entity_t sys = ecs_entity(world, { .name = "Sys" });
    ecs_add_pair(world, sys, EcsDependsOn, EcsOnUpdate);
    ecs_system(world, {
        .entity = sys,
        .query.terms = {{ .id = ecs_id(Position), .inout = EcsIn }},
        .query.order_by = ecs_id(Position),
        .query.order_by_callback = compare_x,
        .callback = Sys,
        .multi_threaded = true
    });

    /* one table, values in reverse order: the first frame sorts it */
    static ecs_entity_t ents[N];
    for (int i = 0; i < N; i ++) {
        ents[i] = ecs_insert(world, ecs_value(Position, {(float)(N - i), 0}));
    }

    ecs_set_threads(world, 2);
    signal(SIGABRT, on_crash);
    signal(SIGSEGV, on_crash);
    signal(SIGBUS, on_crash);
    in_frame = 1;
    ecs_progress(world, 0);
    in_frame = 0;

    /* the table: every entity once, each with its own value */
    int intact = 1;
    ecs_table_t *t = ecs_get_table(world, ents[0]);
    const ecs_entity_t *rows = ecs_table_entities(t);
    int count = ecs_table_count(t);
    if (count != N) intact = 0;
    for (int i = 0; i < N && intact; i ++) {
        int seen = 0;
        for (int r = 0; r < count; r ++) if (rows[r] == ents[i]) seen ++;
        const Position *p = ecs_get(world, ents[i], Position);
        if (seen != 1 || !p || p->x != (float)(N - i)) intact = 0;
    }

    printf("system runs: %d; compares during the frame: %d; two threads "
        "sorting at once: %d; table intact: %d\n", runs, compares, overlap,
        intact);
    int failed = 0;
    if (runs < 1 || compares == 0) {
        printf("INCONCLUSIVE: the system did not run or did not sort\n");
        failed = 2;
    } else if (overlap || !intact) {
        printf("FAIL: two threads sorted the system's table in place at "
            "once\n");
        failed = 1;
    }
    signal(SIGABRT, SIG_DFL);
    signal(SIGSEGV, SIG_DFL);
    signal(SIGBUS, SIG_DFL);
    ecs_set_threads(world, 0);
    ecs_fini(world);
    return failed;
}
