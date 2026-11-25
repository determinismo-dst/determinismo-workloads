/* Prediction F15: a system whose query first tells the pipeline that it may
 * enqueue commands for a component ([out] Position(), or [out] !Position on
 * $this) and then, in the same query, reads that component ([in]
 * Position(), Position(Game), or Position matched on $this after the [out] !
 * term) makes ecs_progress abort while the pipeline builds its schedule:
 * pipeline.c 354, ecs_assert(needs_merge == false, ECS_INTERNAL_ERROR).
 *
 * flecs_pipeline_check_terms marks Position written by the first term, then
 * the second term sees a write and asks for a merge before the system; after
 * the merge the write state is reset and the same terms are checked again,
 * which asks for a merge again, and the assert fires.
 *
 * Documented: Systems.md "Sync points" ([out] X() marks a system that may
 * enqueue commands for X; [in] X() marks a system that reads X with get());
 * Manual.md "Error handling" (asserts are for invalid API use). */
#include "flecs.h"
#include <stdio.h>
#include <stdlib.h>

/* A system entity in the OnUpdate phase (ecs_entity_desc_t has no `add`
 * field in v4.2, so the DependsOn pair is added explicitly). */
static ecs_entity_t phase_entity(ecs_world_t *world, const char *name) {
    ecs_entity_t e = ecs_entity(world, { .name = name });
    ecs_add_pair(world, e, EcsDependsOn, EcsOnUpdate);
    return e;
}

typedef struct { float x, y; } Position;

static void on_abort(void) {
    printf("FAIL: ecs_progress aborted while building the pipeline schedule\n");
    exit(1);
}

static int runs;
static void ReadWrite(ecs_iter_t *it) { (void)it; runs ++; }

int main(void) {
    ecs_os_set_api_defaults();
    ecs_os_api_t os_api = ecs_os_get_api();
    os_api.abort_ = on_abort;
    ecs_os_set_api(&os_api);

    ecs_world_t *world = ecs_init();
    ECS_COMPONENT(world, Position);

    /* Reads Position with ecs_get and writes it back with ecs_set. */
    ecs_system(world, {
        .entity = phase_entity(world, "ReadWrite"),
        .query.terms = {
            { .id = ecs_id(Position), .src.id = EcsIsEntity, .inout = EcsOut },
            { .id = ecs_id(Position), .src.id = EcsIsEntity, .inout = EcsIn }
        },
        .callback = ReadWrite
    });

    ecs_progress(world, 0);

    int failed = 0;
    if (runs != 1) {
        printf("FAIL: system ran %d times\n", runs);
        failed = 1;
    }
    ecs_fini(world);
    return failed;
}
