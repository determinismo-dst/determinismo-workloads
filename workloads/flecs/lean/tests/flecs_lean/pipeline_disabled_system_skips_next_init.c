/* Prediction F17 in a world made by ecs_init() (round 4).
 *
 * ecs_init() creates ProgressTasks (addons/script/eval/async.c 1428-1433), an
 * immediate system without terms in EcsPreUpdate. Systems in EcsOnLoad run
 * before it (the builtin pipeline orders phases by their DependsOn depth,
 * pipeline.c 935-985). So when the first system of the frame is in OnLoad,
 * is immediate and disables itself, no system has run before it, and the
 * rebuild resumes from the stale position as in
 * pipeline_disabled_system_skips_next.c: Update, a regular OnLoad system
 * after it, is skipped, and ProgressTasks runs.
 *
 * Model: Pipeline.lean withBuiltin (ProgressTasks last); `flecs-search pipe
 * f17` prints "ran [0, 2]" (Init, ProgressTasks) for this program.
 *
 * Documented: Systems.md "Pipelines" ("A pipeline is a list of systems that
 * is executed when the ecs_progress/world::progress function is invoked");
 * Systems.md "Disabling systems". */
#include "flecs.h"
#include <stdio.h>
#include <stdlib.h>

static ecs_entity_t onload_entity(ecs_world_t *world, const char *name) {
    ecs_entity_t e = ecs_entity(world, { .name = name });
    ecs_add_pair(world, e, EcsDependsOn, EcsOnLoad);
    return e;
}

static int init_runs, update_runs;

static void Init(ecs_iter_t *it) {
    init_runs ++;
    ecs_enable(it->stage, it->system, false);
}

static void Update(ecs_iter_t *it) {
    (void)it;
    update_runs ++;
}

int main(void) {
    ecs_world_t *world = ecs_init();

    ecs_system(world, {
        .entity = onload_entity(world, "Init"),
        .callback = Init,
        .immediate = true
    });

    ecs_system(world, {
        .entity = onload_entity(world, "Update"),
        .callback = Update
    });

    ecs_progress(world, 0);

    int failed = 0;
    if (init_runs != 1 || update_runs != 1) {
        printf("FAIL: after one frame Init ran %d times, Update ran %d times "
            "(expected 1 and 1)\n", init_runs, update_runs);
        failed = 1;
    }
    ecs_fini(world);
    return failed;
}
