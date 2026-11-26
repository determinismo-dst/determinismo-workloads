#include "flecs.h"
#include <stdio.h>
typedef struct { float x, y; } Position;
typedef struct { float x, y; } Velocity;
static int ran;
static void Sys(ecs_iter_t *it) { ran += it->count; }
int main(void) {
    ecs_world_t *world = ecs_init();
    ECS_COMPONENT(world, Position);
    ECS_COMPONENT(world, Velocity);
    ecs_entity_t sys = ecs_entity(world, { .name = "Sys" });
    ecs_add_pair(world, sys, EcsDependsOn, EcsOnUpdate);
    ecs_system(world, { .entity = sys, .query.terms = {{ .id = ecs_id(Position) }}, .callback = Sys });
    ecs_entity_t e = ecs_insert(world, ecs_value(Position, {1, 2}));
    ecs_progress(world, 0);
    ecs_remove(world, e, Position);
    ecs_run_aperiodic(world, EcsAperiodicEmptyQueries);
    if (!ecs_has_id(world, sys, EcsEmpty)) { printf("INCONCLUSIVE\n"); return 2; }
    ecs_entity_t f = ecs_insert(world, ecs_value(Position, {1, 2}), ecs_value(Velocity, {0, 0}));  /* a new table */
    (void)f;
    ran = 0;
    ecs_progress(world, 0);
    if (ran != 1) { printf("FAIL: Sys ran for %d entities after a new matching table got an entity\n", ran); return 1; }
    ecs_delete(world, f);
    ecs_run_aperiodic(world, EcsAperiodicEmptyQueries);   /* deactivated again */
    ran = 0;
    ecs_progress(world, 0);
    if (ran != 0 || !ecs_has_id(world, sys, EcsEmpty)) { printf("FAIL: not deactivated again\n"); return 1; }
    ecs_fini(world);
    printf("OK\n");
    return 0;
}
