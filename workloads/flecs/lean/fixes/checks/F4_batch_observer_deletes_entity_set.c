/* Prediction: an OnRemove observer that deletes its entity through it->stage
 * makes the merge abort (commands.c 1277, "r->table != NULL") when the remove
 * is batched with another command for the same entity.  On its own, the same
 * remove works and the entity is deleted.
 *
 * Documented: Manual.md "Deferred operations": operations that add, remove
 * or move entities in a locked table must go through it->stage; observer
 * commands run in nested queues that finish before the next command;
 * commands targeting an entity deleted before their execution are discarded. */
#include "flecs.h"
#include <stdio.h>

typedef struct { float x, y; } Position; typedef struct { float x, y; } Velocity;

static void delete_self(ecs_iter_t *it) {
    for (int i = 0; i < it->count; i ++) {
        ecs_delete(it->stage, it->entities[i]);
    }
}

int main(void) {
    ecs_world_t *world = ecs_mini();
    ECS_COMPONENT(world, Position); ECS_COMPONENT(world, Velocity);
    ecs_entity_t Tag = ecs_new(world);

    ecs_observer(world, {
        .query.terms = {{ ecs_id(Position) }},
        .events = { EcsOnRemove },
        .callback = delete_self
    });

    ecs_entity_t e = ecs_insert(world, ecs_value(Position, {1, 2}));

    ecs_world_t *stage = ecs_get_stage(world, 0);
    ecs_remove(stage, e, Position);
    ecs_set(stage, e, Velocity, {3, 4});
    ecs_merge(stage);   /* predicted: aborts here */

    int failed = 0;
    if (ecs_is_alive(world, e)) {
        printf("FAIL: entity alive after its OnRemove observer deleted it\n");
        failed = 1;
    }
    ecs_fini(world);
    return failed;
}
