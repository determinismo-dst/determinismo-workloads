/* Prediction F54: the run callback of a single-threaded system whose query
 * has a trivial cache gets an iterator whose next is not ecs_query_next,
 * and ecs_iter_skip on it aborts.
 *
 *   ecs_mini() + FlecsPipeline; Position; 2 entities
 *   system Run (no phase, run callback, query { Position })
 *   ecs_run(world, Run, 0, NULL):
 *     in the run callback, it->next == ecs_query_next      false
 *     while (ecs_iter_next(it)) ecs_iter_skip(it);          abort
 *   control: the same system with .query.flags = EcsQueryDetectChanges:
 *     it->next == ecs_query_next is true, ecs_iter_skip works
 *
 * flecs_run_system (addons/system/system.c 22-161) creates the query
 * iterator (80-81). A system's query is cached (query/api.c 105-114: a
 * query with an entity), and a cache of one self term without order_by,
 * group_by or change detection is trivial (query/cache/cache.c 755-777),
 * so flecs_query_iter_constrain sets EcsIterTrivialCached (query/engine/
 * eval_iter.c 133-141). With a run callback, flecs_run_system then sets
 * it->next = flecs_query_trivial_cached_next (system.c 119-121) before
 * calling it. ecs_iter_skip asserts it->next == ecs_query_next
 * (query/cache/change_detection.c 718). With change detection the cache is
 * not trivial and next stays ecs_query_next.
 *
 * Documented: system.h, ecs_system_desc_t::run: "It should not be assumed
 * that the input iterator can always be iterated with ecs_query_next().
 * When a system is multithreaded and/or paged, the iterator can be either a
 * worker or a paged iterator ... An implementation can test whether the
 * iterator is a query iterator by testing whether the it->next value is
 * equal to ecs_query_next()" (this system is neither); Queries.md "Change
 * Detection": "If no changes are made to the iterated table, the skip
 * function can be called to prevent marking the matched components as
 * dirty". main returns 0 when the run callback gets ecs_query_next and the
 * skip works; an abort confirms the prediction (the handler prints FAIL and
 * exits 1). */
#include "flecs.h"
#include <stdio.h>
#include <stdlib.h>
#include <signal.h>

typedef struct { float x, y; } Position;
ECS_COMPONENT_DECLARE(Position);

static int is_query_next = -1, results, do_skip;

static void Run(ecs_iter_t *it) {
    is_query_next = it->next == ecs_query_next;
    while (ecs_iter_next(it)) {
        results ++;
        if (do_skip) ecs_iter_skip(it);
    }
}

static void on_abort(int sig) {
    (void)sig;
    printf("FAIL: ecs_iter_skip aborted in the run callback\n");
    fflush(stdout);
    _Exit(1);
}

static ecs_entity_t make_system(ecs_world_t *world, const char *name,
    ecs_flags32_t flags)
{
    ecs_entity_t e = ecs_entity(world, { .name = name });
    return ecs_system(world, {
        .entity = e,
        .query.terms = {{ .id = ecs_id(Position) }},
        .query.flags = flags,
        .run = Run
    });
}

int main(void) {
    ecs_world_t *world = ecs_mini();
    ECS_IMPORT(world, FlecsPipeline);
    ECS_COMPONENT_DEFINE(world, Position);
    ecs_insert(world, ecs_value(Position, {1, 0}));
    ecs_insert(world, ecs_value(Position, {2, 0}));

    ecs_entity_t ctl = make_system(world, "Control", EcsQueryDetectChanges);
    ecs_entity_t sys = make_system(world, "Run", 0);

    /* control, with the skip */
    do_skip = 1;
    ecs_run(world, ctl, 0, NULL);
    int ctl_next = is_query_next, ctl_results = results;
    printf("control (EcsQueryDetectChanges): it->next == ecs_query_next %d, "
        "results %d, skipped without abort\n", ctl_next, ctl_results);

    /* the system: first without the skip */
    do_skip = 0;
    results = 0;
    ecs_run(world, sys, 0, NULL);
    int next = is_query_next;
    printf("system: it->next == ecs_query_next %d, results %d\n", next,
        results);
    fflush(stdout);
    if (ctl_next != 1 || ctl_results < 1 || results < 1) {
        printf("INCONCLUSIVE: the control or the system did not run as set "
            "up\n");
        return 2;
    }

    do_skip = 1;
    results = 0;
    signal(SIGABRT, on_abort);
    ecs_run(world, sys, 0, NULL);
    signal(SIGABRT, SIG_DFL);
    printf("system with ecs_iter_skip: results %d, no abort\n", results);

    int failed = 0;
    if (next != 1) {
        printf("FAIL: the run callback of a single-threaded, unpaged system "
            "got an iterator whose next is not ecs_query_next\n");
        failed = 1;
    }
    ecs_fini(world);
    return failed;
}
