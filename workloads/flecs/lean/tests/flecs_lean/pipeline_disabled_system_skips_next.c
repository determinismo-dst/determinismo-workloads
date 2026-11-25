/* Prediction F17: when the only system that has run so far in a frame leaves
 * the pipeline at the sync point after it (it disables or deletes itself),
 * the pipeline is rebuilt and resumes from a stale position, skipping the
 * systems of the next operation for that frame.
 *
 * Here Init is an immediate system (so a sync point follows it) that disables
 * itself on its first run, a common one-shot pattern. Update is a regular
 * system after it. The first ecs_progress runs Init and never runs Update.
 *
 * flecs_pipeline_build (pipeline.c 450-458) repositions pq->cur_op/cur_i at
 * the last system in the new schedule whose last_frame is the current frame.
 * Init is no longer in the schedule and Update has not run, so cur_op/cur_i
 * keep their old values (op 0, system 0); flecs_pipeline_next_system then
 * moves past the new op 0, which now holds Update.
 *
 * Round 4 correction of this test (the model's code path is unchanged):
 * - Round 2's version used ecs_init(). ecs_init() imports FlecsScript, whose
 *   async addon creates ProgressTasks (addons/script/eval/async.c
 *   1428-1433): an immediate system without terms in EcsPreUpdate, always
 *   active. It runs before every OnUpdate system, so Init was not the only
 *   system that had run: the rebuild found ProgressTasks as the last system
 *   that ran and resumed correctly, and Update ran. The real flecs did
 *   exactly that. This version uses ecs_mini() with the pipeline module
 *   only, so Init is the first system of the frame (see also
 *   pipeline_disabled_system_skips_next_init.c for an ecs_init() world).
 * - The command goes through it->stage (Manual.md: "Pass an explicit stage
 *   to enqueue ECS operations"); it is flushed at the end of the immediate
 *   op (flecs_commands_end, pipeline.c 663), as before.
 *
 * Documented: Systems.md "Pipelines" ("A pipeline is a list of systems that
 * is executed when the ecs_progress/world::progress function is invoked");
 * Systems.md "Disabling systems" (ecs_enable on a system entity). */
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
    ecs_world_t *world = ecs_mini();
    ECS_IMPORT(world, FlecsPipeline);

    ecs_system(world, {
        .entity = phase_entity(world, "Init"),
        .callback = Init,
        .immediate = true
    });

    ecs_system(world, {
        .entity = phase_entity(world, "Update"),
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
