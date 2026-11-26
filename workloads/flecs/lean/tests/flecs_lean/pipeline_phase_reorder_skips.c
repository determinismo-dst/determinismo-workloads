/* Prediction F37: a system whose commands reorder the phases in the middle
 * of a frame makes the pipeline skip, in that frame, the systems that move
 * before it.
 *
 * Two custom phases, Pa and Pb, both depend on OnUpdate, so their systems
 * are in one cascade group and run by entity id: S1 (in Pa), then S2 (in Pb,
 * immediate, so there is a sync point before it). S1 enqueues
 * `Pa DependsOn Pb`. At the merge before S2 the command is applied; the
 * pipeline query's cascade term (`Phase(cascade(DependsOn))`, pipeline.c
 * 978-991) regroups S1's table one level deeper (the ancestry observer,
 * query/cache/cache.c 334-430; flecs_query_cache_move_table_to_group,
 * group.c 249-274), which bumps the cache's match count, and
 * flecs_pipeline_update rebuilds the schedule (pipeline.c 491-519 ->
 * 263-474). The new order is S2, S1. The rebuild resumes after the last
 * system in the new order that already ran this frame (450-458): S1, now the
 * last one. flecs_pipeline_next_system (475-489) steps past it and the frame
 * ends: S2 does not run in this frame.
 *
 * F17 skips systems through the same resume point when the system that ran
 * leaves the schedule; here every system stays in it and only the order
 * changes. In an ecs_init() world ProgressTasks runs first and S2 is still
 * skipped (the model's second case).
 *
 * World: ecs_mini() with the pipeline module, no builtin systems.
 * Documented: Systems.md "Pipelines" ("A pipeline is a list of systems that
 * is executed when the ecs_progress/world::progress function is invoked")
 * and "Builtin Pipeline" (systems are ordered by a topology sort on
 * DependsOn); S2 is enabled and active for the whole frame. main returns 0
 * when S2 runs once in the first frame. */
#include "flecs.h"
#include <stdio.h>
#include <stdlib.h>

static ecs_entity_t Pa, Pb;
static int s1_runs, s2_runs;

static void S1(ecs_iter_t *it) {
    s1_runs ++;
    if (s1_runs == 1) {
        ecs_add_pair(it->stage, Pa, EcsDependsOn, Pb);
    }
}

static void S2(ecs_iter_t *it) {
    (void)it;
    s2_runs ++;
}

static ecs_entity_t system_in(ecs_world_t *world, const char *name,
    ecs_entity_t phase)
{
    ecs_entity_t e = ecs_entity(world, { .name = name });
    ecs_add_pair(world, e, EcsDependsOn, phase);
    return e;
}

int main(void) {
    ecs_world_t *world = ecs_mini();
    ECS_IMPORT(world, FlecsPipeline);

    Pa = ecs_new_w_id(world, EcsPhase);
    ecs_add_pair(world, Pa, EcsDependsOn, EcsOnUpdate);
    Pb = ecs_new_w_id(world, EcsPhase);
    ecs_add_pair(world, Pb, EcsDependsOn, EcsOnUpdate);

    ecs_system(world, {
        .entity = system_in(world, "S1", Pa),
        .callback = S1
    });
    ecs_system(world, {
        .entity = system_in(world, "S2", Pb),
        .callback = S2,
        .immediate = true
    });

    ecs_progress(world, 0);
    int s1_first = s1_runs, s2_first = s2_runs;
    ecs_progress(world, 0);

    printf("frame 1: S1 %d, S2 %d; after frame 2: S1 %d, S2 %d\n",
        s1_first, s2_first, s1_runs, s2_runs);

    int failed = 0;
    if (s1_first != 1) {
        printf("INCONCLUSIVE: S1 did not run once in the first frame\n");
        failed = 2;
    } else if (s2_first != 1) {
        printf("FAIL: S2 ran %d times in the first frame (expected 1)\n",
            s2_first);
        failed = 1;
    }
    ecs_fini(world);
    return failed;
}
