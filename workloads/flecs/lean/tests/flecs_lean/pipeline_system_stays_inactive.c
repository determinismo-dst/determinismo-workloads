/* Prediction F25: after ecs_run_aperiodic(world, EcsAperiodicEmptyQueries)
 * marks a system inactive, the system stays inactive when an entity enters a
 * table its query already matched, so ecs_progress does not run it. It stays
 * inactive even when a new table is matched later, as long as its cache
 * still holds another (empty) table: only a cache going from no tables to
 * one table reactivates it.
 *
 * flecs_process_empty_queries (world.c 1338-1354) adds EcsEmpty to every
 * query entity whose query has no results, including queries whose matched
 * tables are only empty. EcsEmpty is removed only in
 * flecs_query_cache_add_table (group.c 240-243), when a table joins a cache
 * that had none. An entity moving into a table the cache already holds adds
 * no table, so EcsEmpty stays. The pipeline schedules only systems without
 * EcsEmpty (pipeline.c 295-296).
 *
 * Documented: Systems.md "Pipelines" ("A pipeline is a list of systems that
 * is executed when the ecs_progress/world::progress function is invoked");
 * Systems.md "Sync points": a system is inactive when "it doesn't match any
 * entities". The system below matches e when ecs_progress is called. */
#include "flecs.h"
#include <stdio.h>

typedef struct { float x, y; } Position;

static int ran;
static void Sys(ecs_iter_t *it) { ran += it->count; }

int main(void) {
    ecs_world_t *world = ecs_init();
    ECS_COMPONENT(world, Position);

    /* ecs_entity_desc_t has no `add` field in v4.2: add the phase first */
    ecs_entity_t sys = ecs_entity(world, { .name = "Sys" });
    ecs_add_pair(world, sys, EcsDependsOn, EcsOnUpdate);
    ecs_system(world, {
        .entity = sys,
        .query.terms = {{ .id = ecs_id(Position) }},
        .callback = Sys
    });

    ecs_entity_t e = ecs_insert(world, ecs_value(Position, {1, 2}));
    ecs_progress(world, 0);
    if (ran != 1) {
        printf("INCONCLUSIVE: the system did not run before the scenario (%d)\n", ran);
        return 2;
    }

    ecs_remove(world, e, Position);    /* table [Position] is now empty */
    ecs_run_aperiodic(world, EcsAperiodicEmptyQueries); /* Sys gets EcsEmpty */
    ecs_add(world, e, Position);       /* e is back in [Position] */

    ran = 0;
    ecs_progress(world, 0);

    int failed = 0;
    if (ran != 1) {
        printf("FAIL: Sys matches e but ran for %d entities (EcsEmpty: %d)\n",
            ran, ecs_has_id(world, sys, EcsEmpty));
        failed = 1;
    }

    ecs_fini(world);
    if (!failed) printf("OK\n");
    return failed;
}
