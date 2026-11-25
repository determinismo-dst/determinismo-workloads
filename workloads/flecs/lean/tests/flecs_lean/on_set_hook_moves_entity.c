/* Prediction: when a component's on_set hook moves its entity to another table
 * through it->world (allowed: tables are not locked for on_set hooks, and
 * flecs' own test ComponentLifecycle_locked_storage_on_set does this), the
 * OnSet observers for that set run for the entity that took the old row: a
 * different entity, with that entity's value (component_actions.c 690-700
 * reuse the table and row captured before the hook).
 *
 * Documented: ObserversManual.md "OnSet Events" (an OnSet event is generated
 * each time set is called, for the entity it is called on) and "Hooks and
 * Events" (on_set hooks are invoked before OnSet events). */
#include "flecs.h"
#include <stdio.h>

typedef struct { float x, y; } Position;

static ecs_entity_t Tag;
static ecs_entity_t seen_entity;
static float seen_x;
static int seen_count;

static void on_set_position(ecs_iter_t *it) {
    Position *p = ecs_field(it, Position, 0);
    for (int i = 0; i < it->count; i ++) {
        if (p[i].x == 99) {
            ecs_add_id(it->world, it->entities[i], Tag);
        }
    }
}

static void observe_set(ecs_iter_t *it) {
    Position *p = ecs_field(it, Position, 0);
    seen_entity = it->entities[0];
    seen_x = p[0].x;
    seen_count ++;
}

int main(void) {
    ecs_world_t *world = ecs_mini();
    ECS_COMPONENT(world, Position);
    Tag = ecs_new(world);

    ecs_set_hooks(world, Position, { .on_set = on_set_position });
    ecs_observer(world, {
        .query.terms = {{ ecs_id(Position) }},
        .events = { EcsOnSet },
        .callback = observe_set
    });

    ecs_entity_t e = ecs_new(world);
    ecs_entity_t f = ecs_new(world);
    ecs_set(world, e, Position, {1, 1});
    ecs_set(world, f, Position, {2, 2});

    seen_entity = 0; seen_count = 0;
    ecs_set(world, e, Position, {99, 99});

    int failed = 0;
    if (seen_count != 1) { printf("FAIL: OnSet ran %d times\n", seen_count); failed = 1; }
    if (seen_entity != e) {
        printf("FAIL: OnSet observer got entity %llu (f=%llu), expected e=%llu\n",
            (unsigned long long)seen_entity, (unsigned long long)f,
            (unsigned long long)e);
        failed = 1;
    }
    if (seen_x != 99) { printf("FAIL: OnSet observer saw x=%f, expected 99\n", seen_x); failed = 1; }
    if (!ecs_has_id(world, e, Tag)) { printf("FAIL: hook did not add Tag\n"); failed = 1; }
    ecs_fini(world);
    return failed;
}
