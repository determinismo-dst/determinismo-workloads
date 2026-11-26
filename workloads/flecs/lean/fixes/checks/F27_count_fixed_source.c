#include "flecs.h"
#include <stdio.h>
typedef struct { float x, y; } Position;
typedef struct { float x, y; } Velocity;
int main(void) {
    ecs_world_t *world = ecs_mini();
    ECS_COMPONENT(world, Position);
    ECS_COMPONENT(world, Velocity);
    ecs_entity_t game = ecs_insert(world, ecs_value(Velocity, {1, 1}));
    ecs_insert(world, ecs_value(Position, {0, 0}));
    ecs_query_t *q = ecs_query(world, {
        .terms = {{ ecs_id(Position), .inout = EcsIn },
                  { ecs_id(Velocity), .src.id = game, .inout = EcsIn }},
        .cache_kind = EcsQueryCacheAuto, .flags = EcsQueryDetectChanges });
    ecs_query_changed(q);
    ecs_iter_t it = ecs_query_iter(world, q);
    while (ecs_query_next(&it)) { }
    if (ecs_query_changed(q)) { printf("INCONCLUSIVE\n"); return 2; }
    ecs_set(world, game, Velocity, {2, 2});
    if (!ecs_query_changed(q)) { printf("INCONCLUSIVE: set not seen\n"); return 2; }
    ecs_query_count(q);
    if (!ecs_query_changed(q)) { printf("FAIL: after ecs_query_count, the fixed source's set is no longer reported\n"); return 1; }
    it = ecs_query_iter(world, q);
    while (ecs_query_next(&it)) { }
    if (ecs_query_changed(q)) { printf("FAIL: still changed after iterating\n"); return 1; }
    printf("OK\n");
    return 0;
}
