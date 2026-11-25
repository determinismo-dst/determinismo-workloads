/* Prediction F31 (builtin pipeline): a system that is a child of a module
 * through the Parent component (a Parent hierarchy) keeps running after the
 * module is disabled.
 *
 * Systems.md "Disabling systems": "When the parent of a system is disabled,
 * it will also be excluded from the builtin pipeline. This makes it possible
 * to disable all systems in a module with a single operation."
 * HierarchiesManual.md: ChildOf and Parent hierarchies behave the same for
 * relationship traversal ("Relationship traversal works for both
 * storages").
 *
 * flecs_pipeline_build (pipeline.c 263-274) rebuilds the schedule only when
 * the match count of the pipeline query's cache changed. When the module
 * gets Disabled, the cache's rematch observer for !Disabled(up(ChildOf))
 * revalidates the tables of the module's ChildOf children (match.c 356 bumps
 * the count), but returns early for a table with the Parent component and a
 * ChildOf term (cache.c 268-273): such tables are filtered per entity when
 * the query is iterated. The system's own table does not change. So the
 * count stays, the pipeline is not rebuilt, and the old schedule still runs
 * the system.
 *
 * The control, in a world of its own, is a ChildOf child, excluded as
 * documented. (In one world the control's rebuild would also re-evaluate
 * the Parent child and hide the prediction.) */
#include "flecs.h"
#include <stdio.h>
#include <stdlib.h>

static int runs;
static void Sys(ecs_iter_t *it) { (void)it; runs ++; }

/* returns the runs after the module was disabled, or -1 on a setup failure */
static int run(int childof) {
    ecs_world_t *world = ecs_mini();
    ECS_IMPORT(world, FlecsPipeline);

    ecs_entity_t module = ecs_new(world);
    ecs_entity_t s = childof
        ? ecs_new_w_pair(world, EcsChildOf, module)
        : ecs_new_w_parent(world, module, "Sys");
    ecs_add_pair(world, s, EcsDependsOn, EcsOnUpdate);
    ecs_system(world, { .entity = s, .callback = Sys });

    runs = 0;
    ecs_progress(world, 0);
    if (runs != 1) {
        ecs_fini(world);
        return -1;
    }

    ecs_enable(world, module, false);
    runs = 0;
    ecs_progress(world, 0);
    ecs_progress(world, 0);
    int r = runs;
    ecs_fini(world);
    return r;
}

int main(void) {
    int control = run(1);
    int parent = run(0);
    if (control != 0 || parent < 0) {
        printf("INCONCLUSIVE: control ran %d times after its module was "
            "disabled; Parent child setup %s\n", control,
            parent < 0 ? "failed" : "held");
        return 2;
    }
    if (parent != 0) {
        printf("FAIL: the system in the Parent hierarchy ran %d times in the "
            "two frames after its module was disabled\n", parent);
        return 1;
    }
    return 0;
}
