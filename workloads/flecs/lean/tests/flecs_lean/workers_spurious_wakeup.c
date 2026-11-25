/* Prediction F26 (needs threads: link with -lpthread): the worker
 * synchronization in addons/pipeline/worker.c does not re-check its
 * condition after a condition-variable wait. A spurious wakeup of the main
 * thread in flecs_wait_for_sync (worker.c 138-159: `if`, not `while`, around
 * ecs_os_cond_wait) trips worker.c 156-157,
 * ecs_assert(world->workers_waiting == (stage_count - 1), ECS_INTERNAL_ERROR)
 * while a worker is still running its systems; in a release build the main
 * thread merges the stages while the worker still writes to its stage. A
 * spurious wakeup of a worker in flecs_sync_worker (worker.c 13-31) makes it
 * run pipeline ops again while the main thread merges.
 *
 * ecs_os_cond_wait is pthread_cond_wait (posix_impl.inl 200-208) or
 * SleepConditionVariableCS (windows_impl.inl 127-132). Both may return
 * without a signal ("spurious wakeups ... may occur", POSIX). This program
 * makes one such wakeup happen on purpose: it installs an OS API cond_wait
 * that, once, releases and retakes the mutex and returns, which any
 * condition variable may do. A worker's system sleeps so that the main
 * thread reaches flecs_wait_for_sync first.
 *
 * Documented: Systems.md "Threading" (multithreaded systems run on all
 * worker threads, synchronized at sync points); Manual.md "Error handling"
 * (internal asserts are not reachable through valid use). */
#include "flecs.h"
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

typedef struct { float x, y; } Position;

static ecs_os_api_cond_wait_t real_cond_wait;
static ecs_os_thread_id_t main_thread;
static int spurious_left = 1;

static void cond_wait_spurious(ecs_os_cond_t cond, ecs_os_mutex_t mutex) {
    if (ecs_os_thread_self() == main_thread && spurious_left > 0) {
        spurious_left --;
        ecs_os_mutex_unlock(mutex);   /* a wakeup without a signal */
        ecs_os_mutex_lock(mutex);
        return;
    }
    real_cond_wait(cond, mutex);
}

static void on_abort(void) {
    printf("FAIL: aborted after a spurious wakeup in the worker synchronization\n");
    exit(1);
}

static void Slow(ecs_iter_t *it) {
    /* Round 4 correction: it->world is the world (stage id 0 on every
     * thread); the worker's stage is it->stage. */
    if (ecs_stage_get_id(it->stage) != 0) {
        usleep(200 * 1000); /* the main thread reaches the sync point first */
    }
}

int main(void) {
    /* Install the default (POSIX/Windows) OS API, then wrap its cond_wait.
     * ecs_set_os_api_impl marks the API initialized, so later
     * ecs_os_set_api calls are ignored: the global is edited instead. */
    ecs_set_os_api_impl();
    main_thread = ecs_os_thread_self();
    real_cond_wait = ecs_os_api.cond_wait_;
    ecs_os_api.cond_wait_ = cond_wait_spurious;
    ecs_os_api.abort_ = on_abort;

    ecs_world_t *world = ecs_init();
    ECS_COMPONENT(world, Position);

    ecs_entity_t sys = ecs_entity(world, { .name = "Slow" });
    ecs_add_pair(world, sys, EcsDependsOn, EcsOnUpdate);
    ecs_system(world, {
        .entity = sys,
        .query.terms = {{ .id = ecs_id(Position) }},
        .callback = Slow,
        .multi_threaded = true
    });

    for (int i = 0; i < 4; i ++) {
        ecs_insert(world, ecs_value(Position, {0, 0}));
    }

    ecs_set_threads(world, 2);

    ecs_progress(world, 0);

    ecs_fini(world);
    printf("OK\n");
    return 0;
}
