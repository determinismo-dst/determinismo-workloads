/* Prediction F53 (needs threads: link with -lpthread): ecs_iter_changed,
 * called from the callback of a multi_threaded system whose query has
 * change detection, aborts as soon as the world has worker threads; a
 * release build dereferences NULL instead. ecs_iter_skip in the same place
 * aborts too: iter_skip_multi_threaded_system.c includes this file with
 * FLECS_LEAN_SKIP set (a release build ignores the skip).
 *
 *   ecs_mini() + FlecsPipeline; Position; 4 entities
 *   system Sys (OnUpdate, multi_threaded, query { Position, in },
 *     .flags = EcsQueryDetectChanges); its callback calls
 *     ecs_iter_changed(it) (or ecs_iter_skip(it))
 *   ecs_progress              no threads: the call works (control)
 *   ecs_set_threads(world, 2); ecs_progress     abort
 *
 * With more than one stage, flecs_run_system gives a multi_threaded system's
 * callback a worker iterator (addons/system/system.c 97-100, ecs_worker_iter,
 * src/iter.c 1008-1034: next = ecs_worker_next). ecs_iter_changed starts
 * with ecs_check(it->next == ecs_query_next, ECS_UNSUPPORTED, NULL)
 * (query/cache/change_detection.c 680); ecs_iter_skip with
 * ecs_assert(it->next == ecs_query_next, ECS_INVALID_PARAMETER, NULL) (718).
 * In a release build ecs_iter_changed reads it->priv_.iter.query.elem (704):
 * the worker iterator's private data is its own, and that field was copied
 * from the query iterator when the worker iterator was made, before the
 * first result (iter.c 1020; ecs_worker_next copies only the part before
 * priv_, 1053-1054). ecs_iter_skip sets EcsIterSkip on the worker iterator,
 * whose flags ecs_worker_next overwrites from the query iterator.
 *
 * Documented: flecs.h ecs_iter_changed: "This operation must be used in
 * combination with a query that supports change detection (e.g., is
 * cached)" (no other condition); Queries.md "Change Detection" (enabled with
 * EcsQueryDetectChanges; "If no changes are made to the iterated table, the
 * skip function can be called to prevent marking the matched components as
 * dirty"); Systems.md "Threading" (multi_threaded systems). main returns 0
 * when the frame with threads completes. An abort or a crash confirms the
 * prediction: the handler prints FAIL and exits 1. */
#include "flecs.h"
#include <stdio.h>
#include <stdlib.h>
#include <signal.h>

typedef struct { float x, y; } Position;

static int calls, changed;

static void Sys(ecs_iter_t *it) {
#ifdef FLECS_LEAN_SKIP
    ecs_iter_skip(it);
    __atomic_add_fetch(&calls, 1, __ATOMIC_SEQ_CST);
#else
    if (ecs_iter_changed(it)) __atomic_add_fetch(&changed, 1, __ATOMIC_SEQ_CST);
    __atomic_add_fetch(&calls, 1, __ATOMIC_SEQ_CST);
#endif
}

static void on_crash(int sig) {
    printf("FAIL: signal %d in the frame with worker threads (the system's "
        "callback calls "
#ifdef FLECS_LEAN_SKIP
        "ecs_iter_skip"
#else
        "ecs_iter_changed"
#endif
        ")\n", sig);
    fflush(stdout);
    _Exit(1);
}

int main(void) {
    ecs_set_os_api_impl();
    ecs_world_t *world = ecs_mini();
    ECS_IMPORT(world, FlecsPipeline);
    ECS_COMPONENT(world, Position);

    ecs_entity_t sys = ecs_entity(world, { .name = "Sys" });
    ecs_add_pair(world, sys, EcsDependsOn, EcsOnUpdate);
    ecs_add_id(world, sys, EcsOnUpdate);
    ecs_system(world, {
        .entity = sys,
        .query.terms = {{ .id = ecs_id(Position), .inout = EcsIn }},
        .query.flags = EcsQueryDetectChanges,
        .callback = Sys,
        .multi_threaded = true
    });

    for (int i = 0; i < 4; i ++) {
        ecs_insert(world, ecs_value(Position, {(float)i, 0}));
    }

    ecs_progress(world, 0);
    int calls0 = calls, changed0 = changed;
    printf("frame without threads: callback calls %d, changed %d\n", calls0,
        changed0);
    fflush(stdout);
    if (calls0 < 1) {
        printf("INCONCLUSIVE: the system did not run\n");
        return 2;
    }

    ecs_set_threads(world, 2);
    signal(SIGABRT, on_crash);
    signal(SIGSEGV, on_crash);
    signal(SIGBUS, on_crash);
    ecs_progress(world, 0);
    signal(SIGABRT, SIG_DFL);
    signal(SIGSEGV, SIG_DFL);
    signal(SIGBUS, SIG_DFL);
    printf("frame with 2 threads: callback calls %d\n", calls - calls0);

    int failed = 0;
    if (calls - calls0 < 1) {
        printf("INCONCLUSIVE: the system did not run with threads\n");
        failed = 2;
    }
    ecs_set_threads(world, 0);
    ecs_fini(world);
    return failed;
}
