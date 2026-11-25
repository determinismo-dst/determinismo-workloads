/* Prediction F31 (custom pipelines): a custom pipeline whose query has a
 * term that the query cache does not hold keeps its old schedule when that
 * term starts or stops matching.
 *
 * (a) pipeline `System, Running(Game)`: Game loses Running, and the system
 *     still runs every frame;
 * (b) pipeline `System, Foo` with Foo a DontFragment tag: the system loses
 *     Foo, and it still runs.
 *
 * Systems.md "Custom pipeline": "Applications can create their own pipelines
 * which fully customize which systems are matched"; "Pipelines": "A pipeline
 * is a list of systems that is executed when the ecs_progress/world::progress
 * function is invoked".
 *
 * flecs_pipeline_build (pipeline.c 263-274) rebuilds only when the match
 * count of the query cache changes (api.c 717-728). A fixed-source term and
 * a DontFragment term are not cacheable (validator.c 837-859), so they are
 * evaluated when the query is iterated: Game losing Running, or the system
 * losing a DontFragment tag (which does not move it to another table),
 * changes no table of the cache, and the schedule is not rebuilt. */
#include "flecs.h"
#include <stdio.h>
#include <stdlib.h>

static int runs;
static void Sys(ecs_iter_t *it) { (void)it; runs ++; }

static int variant(int dont_fragment) {
    ecs_world_t *world = ecs_mini();
    ECS_IMPORT(world, FlecsPipeline);
    ECS_TAG(world, Running);
    ECS_TAG(world, Foo);
    if (dont_fragment) {
        ecs_add_id(world, Foo, EcsDontFragment);
    }

    ecs_entity_t game = ecs_new(world);
    ecs_add(world, game, Running);

    ecs_entity_t pipeline;
    if (!dont_fragment) {
        pipeline = ecs_pipeline_init(world, &(ecs_pipeline_desc_t){
            .query.terms = {
                { .id = EcsSystem },
                { .id = Running, .src.id = game }
            }
        });
    } else {
        pipeline = ecs_pipeline_init(world, &(ecs_pipeline_desc_t){
            .query.terms = {
                { .id = EcsSystem },
                { .id = Foo }
            }
        });
    }
    if (!pipeline) {
        printf("INCONCLUSIVE: pipeline not created\n");
        ecs_fini(world);
        return 2;
    }
    ecs_set_pipeline(world, pipeline);

    ecs_entity_t s = ecs_entity(world, { .name = "Sys" });
    ecs_add(world, s, Foo);
    ecs_system(world, { .entity = s, .callback = Sys });

    runs = 0;
    ecs_progress(world, 0);
    if (runs != 1) {
        printf("INCONCLUSIVE: variant %d, first frame ran %d times\n",
            dont_fragment, runs);
        ecs_fini(world);
        return 2;
    }

    if (!dont_fragment) {
        ecs_remove(world, game, Running);
    } else {
        ecs_remove(world, s, Foo);
    }

    ecs_progress(world, 0);
    ecs_progress(world, 0);

    int failed = 0;
    if (runs != 1) {
        printf("FAIL: variant %d (%s): the system ran %d times; the pipeline "
            "query stopped matching it after the first frame\n",
            dont_fragment, dont_fragment ? "System, Foo (DontFragment)"
                : "System, Running(Game)", runs);
        failed = 1;
    }
    ecs_fini(world);
    return failed;
}

int main(void) {
    int a = variant(0);
    int b = variant(1);
    if (a == 1 || b == 1) return 1;
    if (a == 2 || b == 2) return 2;
    return 0;
}
