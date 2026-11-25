/* Prediction: inside a component's on_add hook, the entity does not have the
 * component yet from the API's point of view: ecs_has() is false and
 * ecs_get() is NULL.  flecs_table_move (table.c 1886-1904) runs on_add hooks
 * before flecs_move_entity (entity.c 188-191) points the record at the new
 * table.
 *
 * Documented: EntitiesComponents.md "Operations" lifecycle diagram
 * (img/component-lifecycle.svg): add -> table move -> ctor -> on_add hook ->
 * OnAdd observers; the hook runs after the table move.  OnAdd observers do
 * see the component. */
#include "flecs.h"
#include <stdio.h>

typedef struct { float x, y; } Position;
ECS_COMPONENT_DECLARE(Position);

static int hook_has = -1, hook_get = -1;

static void on_add_position(ecs_iter_t *it) {
    ecs_entity_t e = it->entities[0];
    hook_has = ecs_has(it->world, e, Position);
    hook_get = ecs_get(it->world, e, Position) != NULL;
}

int main(void) {
    ecs_world_t *world = ecs_mini();
    ECS_COMPONENT_DEFINE(world, Position);
    ecs_set_hooks(world, Position, { .on_add = on_add_position });

    ecs_entity_t e = ecs_new(world);
    ecs_add(world, e, Position);

    int failed = 0;
    if (hook_has != 1) { printf("FAIL: ecs_has false inside on_add hook\n"); failed = 1; }
    if (hook_get != 1) { printf("FAIL: ecs_get NULL inside on_add hook\n"); failed = 1; }
    ecs_fini(world);
    return failed;
}
