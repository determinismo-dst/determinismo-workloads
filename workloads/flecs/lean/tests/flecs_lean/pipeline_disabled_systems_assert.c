/* Prediction F17 (second symptom): three systems separated by sync points,
 * A (regular), B (immediate) and C (regular). A disables itself, and C
 * disables itself. After A's sync point the pipeline is rebuilt with a stale
 * position and runs C instead of B; after C's sync point it is rebuilt again,
 * the stale op pointer is past the end of the new schedule, and ecs_progress
 * aborts: pipeline.c 467-470, ecs_assert(pq->cur_op <=
 * ecs_vec_last_t(&pq->ops, ...), ECS_INTERNAL_ERROR). In a release build the
 * schedule reads past the end of its op array.
 *
 * Round 4 correction of this test:
 * - Round 2's A and C called ecs_enable(it->world, ...). In v4.2 it->world is
 *   the world itself and a world operation runs immediately (Manual.md:
 *   "Pass an explicit stage to enqueue ECS operations. Pass the world to
 *   execute operations immediately"); in a readonly system that creates a
 *   table in readonly mode, the assert of flecs_table_ensure
 *   (storage/table_graph.c 527). That is the abort the real flecs showed,
 *   not the predicted one. They now enqueue through it->stage.
 * - ecs_init()'s ProgressTasks (an always-active immediate system in
 *   EcsPreUpdate, addons/script/eval/async.c 1428-1433) runs before these
 *   OnUpdate systems and gives the rebuild a correct resume point. The world
 *   is ecs_mini() with the pipeline module only.
 *
 * Documented: Systems.md "Pipelines", "Disabling systems", "Immediate
 * systems"; Manual.md "Error handling". */
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

static void on_abort(void) {
    printf("FAIL: ecs_progress aborted (pipeline schedule position)\n");
    exit(1);
}

static int a_runs, b_runs, c_runs;

static void A(ecs_iter_t *it) { a_runs ++; ecs_enable(it->stage, it->system, false); }
static void B(ecs_iter_t *it) { (void)it; b_runs ++; }
static void C(ecs_iter_t *it) { c_runs ++; ecs_enable(it->stage, it->system, false); }

int main(void) {
    ecs_os_set_api_defaults();
    ecs_os_api_t os_api = ecs_os_get_api();
    os_api.abort_ = on_abort;
    ecs_os_set_api(&os_api);

    ecs_world_t *world = ecs_mini();
    ECS_IMPORT(world, FlecsPipeline);

    ecs_system(world, {
        .entity = phase_entity(world, "A"),
        .callback = A });
    ecs_system(world, {
        .entity = phase_entity(world, "B"),
        .callback = B, .immediate = true });
    ecs_system(world, {
        .entity = phase_entity(world, "C"),
        .callback = C });

    ecs_progress(world, 0);

    int failed = 0;
    if (a_runs != 1 || b_runs != 1 || c_runs != 1) {
        printf("FAIL: after one frame A, B, C ran %d, %d, %d times\n",
            a_runs, b_runs, c_runs);
        failed = 1;
    }
    ecs_fini(world);
    return failed;
}
