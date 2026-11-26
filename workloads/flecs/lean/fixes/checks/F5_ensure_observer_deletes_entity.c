/* Prediction: ecs_set on the world aborts with ECS_INTERNAL_ERROR
 * (entity.c 575, "r->table != NULL" in flecs_ensure) when an OnAdd observer
 * for the component deletes the entity through it->stage: flecs_ensure
 * flushes the observer's commands before it fetches the pointer.  ecs_add of
 * the same component, with the same observer, deletes the entity cleanly.
 *
 * Documented: Manual.md "Deferred operations" (structural changes from
 * observers go through it->stage; observer commands run before the next
 * command); EntitiesComponents.md "Operations" (set = ensure + modified).
 * Nothing documents that an observer may not delete its entity. */
#include "flecs.h"
#include <stdio.h>

typedef struct { float x, y; } Position;

static void delete_self(ecs_iter_t *it) {
    for (int i = 0; i < it->count; i ++) {
        ecs_delete(it->stage, it->entities[i]);
    }
}

int main(void) {
    ecs_world_t *world = ecs_mini();
    ECS_COMPONENT(world, Position);

    ecs_observer(world, {
        .query.terms = {{ ecs_id(Position) }},
        .events = { EcsOnAdd },
        .callback = delete_self
    });

    int failed = 0;
    ecs_entity_t a = ecs_new(world);
    ecs_add(world, a, Position);              /* control: works */
    if (ecs_is_alive(world, a)) { printf("FAIL: add: entity not deleted\n"); failed = 1; }

    ecs_entity_t e = ecs_new(world);
    Position *p = ecs_ensure(world, e, Position); printf("ensure returned %p\n", (void*)p);
    if (ecs_is_alive(world, e)) { printf("FAIL: set: entity not deleted\n"); failed = 1; }

    ecs_fini(world);
    return failed;
}
