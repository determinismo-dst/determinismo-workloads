/* Prediction: two queued sets of the same component on one entity are
 * batched: both values are copied into storage before either OnSet event
 * runs (commands.c 1179-1241), so the OnSet observer for the first set sees
 * the second value: e's OnSet calls see {3, 3} instead of {1, 3}.
 *
 * Documented: ObserversManual.md "OnSet order is maintained" ("The order in
 * which OnSet events are delivered is the same as in which they were
 * emitted ... makes it easier to write code that is agnostic to whether
 * operations are deferred or executed immediately"); executed immediately the
 * observer sees 1, then 3. */
#include "flecs.h"
#include <stdio.h>

typedef struct { float x, y; } Position;

static ecs_entity_t e_watch;
static float seen[8];
static int seen_count;

static void on_set(ecs_iter_t *it) {
    Position *p = ecs_field(it, Position, 0);
    for (int i = 0; i < it->count; i ++) {
        if (it->entities[i] == e_watch && seen_count < 8) seen[seen_count ++] = p[i].x;
    }
}

int main(void) {
    ecs_world_t *world = ecs_mini();
    ECS_COMPONENT(world, Position);
    ecs_observer(world, {
        .query.terms = {{ ecs_id(Position) }},
        .events = { EcsOnSet },
        .callback = on_set
    });

    ecs_entity_t e = ecs_new(world);
    ecs_entity_t other = ecs_new(world);
    e_watch = e;

    ecs_world_t *stage = ecs_get_stage(world, 0);
    ecs_set(stage, e, Position, {1, 1});
    ecs_set(stage, other, Position, {2, 2});
    ecs_set(stage, e, Position, {3, 3});
    ecs_merge(stage);

    int failed = 0;
    if (seen_count != 2) { printf("FAIL: %d OnSet calls for e\n", seen_count); failed = 1; }
    else if (seen[0] != 1 || seen[1] != 3) {
        printf("FAIL: OnSet calls for e saw x = %f then %f, expected 1 then 3\n", seen[0], seen[1]);
        failed = 1;
    }
    ecs_fini(world);
    return failed;
}
