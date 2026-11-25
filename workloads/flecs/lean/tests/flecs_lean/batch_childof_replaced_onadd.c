/* Prediction: (1) two queued adds of ChildOf for the same entity (ChildOf
 * is exclusive, so the second replaces the first) are batched into one move.
 * The merge then runs OnRemove and OnAdd observers for (ChildOf, p1) on an
 * entity that never has (ChildOf, p1) at that moment: the batch's diff lists
 * (ChildOf, p1) as removed and as added, and flecs_emit (observable.c
 * 1265-1274) skips ids the event's table does not have -- except ChildOf
 * pairs.  For other exclusive relationships the same batch emits nothing for
 * the replaced pair.
 *
 * (2) A queued add of (ChildOf, p) followed by a queued clear runs OnAdd
 * observers for (ChildOf, p) after the batch, on an entity left with no
 * components, and no OnRemove follows: an observer that tracks children
 * counts the entity as p's child forever.
 *
 * Documented: ObserversManual.md "OnAdd Events" ("An event only fires when
 * the component is actually added to the entity") and "OnRemove Events" ("An
 * event only fires when the component is actually removed").  Executed one at
 * a time, every event is for a pair the entity has at that moment. */
#include "flecs.h"
#include <stdio.h>

static ecs_entity_t p1;
static int bad_add, bad_remove, adds, removes;

static void on_add(ecs_iter_t *it) {
    for (int i = 0; i < it->count; i ++) {
        adds ++;
        if (!ecs_has_id(it->world, it->entities[i], it->event_id)) bad_add ++;
    }
}

static void on_remove(ecs_iter_t *it) {
    for (int i = 0; i < it->count; i ++) {
        removes ++;
        if (!ecs_has_id(it->world, it->entities[i], it->event_id)) bad_remove ++;
    }
}

int main(void) {
    ecs_world_t *world = ecs_mini();
    p1 = ecs_new(world);
    ecs_entity_t p2 = ecs_new(world);
    ecs_entity_t e = ecs_new(world);

    ecs_observer(world, {
        .query.terms = {{ ecs_pair(EcsChildOf, EcsWildcard) }},
        .events = { EcsOnAdd },
        .callback = on_add
    });
    ecs_observer(world, {
        .query.terms = {{ ecs_pair(EcsChildOf, EcsWildcard) }},
        .events = { EcsOnRemove },
        .callback = on_remove
    });

    ecs_world_t *stage = ecs_get_stage(world, 0);
    ecs_add_pair(stage, e, EcsChildOf, p1);
    ecs_add_pair(stage, e, EcsChildOf, p2);
    ecs_merge(stage);

    /* (2) add then clear */
    ecs_entity_t c = ecs_new(world);
    int adds_before = adds, removes_before = removes;
    ecs_add_pair(stage, c, EcsChildOf, p1);
    ecs_clear(stage, c);
    ecs_merge(stage);

    int failed = 0;
    if (adds - adds_before != removes - removes_before) {
        printf("FAIL: add+clear of (ChildOf, p1): %d OnAdd vs %d OnRemove calls\n",
            adds - adds_before, removes - removes_before);
        failed = 1;
    }
    if (!ecs_has_pair(world, e, EcsChildOf, p2)) { printf("FAIL: e not a child of p2\n"); failed = 1; }
    if (bad_add) { printf("FAIL: %d OnAdd observer call(s) for a ChildOf pair e does not have\n", bad_add); failed = 1; }
    if (bad_remove) { printf("FAIL: %d OnRemove observer call(s) for a ChildOf pair e does not have\n", bad_remove); failed = 1; }
    ecs_fini(world);
    return failed;
}
