/* Prediction: a queued ecs_set, alone in the queue for its entity, aborts
 * the merge with ECS_INTERNAL_ERROR (entity.c 575 in flecs_ensure, reached
 * from flecs_set_id_move, commands.c 1428-1434) when an OnAdd observer for
 * the component deletes the entity through it->stage.  With a second queued
 * command for the entity the batched path survives and the entity ends up
 * deleted.
 *
 * Documented: Manual.md "Deferred operations" (structural changes from
 * observers go through it->stage; observer commands run before the next
 * command; commands for deleted entities are discarded). */
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
    ecs_entity_t Tag = ecs_new(world);

    ecs_observer(world, {
        .query.terms = {{ ecs_id(Position) }},
        .events = { EcsOnAdd },
        .callback = delete_self
    });

    int failed = 0;
    ecs_world_t *stage = ecs_get_stage(world, 0);

    ecs_entity_t a = ecs_new(world);            /* control: batched */
    ecs_add_id(stage, a, Tag);
    ecs_set(stage, a, Position, {1, 2});
    ecs_merge(stage);
    if (ecs_is_alive(world, a)) { printf("FAIL: batched: entity not deleted\n"); failed = 1; }

    ecs_entity_t e = ecs_new(world);
    ecs_set(stage, e, Position, {1, 2});
    ecs_merge(stage);                           /* predicted: aborts */
    if (ecs_is_alive(world, e)) { printf("FAIL: entity not deleted\n"); failed = 1; }

    ecs_fini(world);
    return failed;
}
