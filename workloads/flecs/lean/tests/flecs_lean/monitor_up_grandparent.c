/* Prediction F20: a monitor observer on Position(up) reports OnAdd for an
 * entity that already matched its query, and OnRemove for an entity that
 * keeps matching, when an ancestor between the entity and the ancestor it
 * matched through gains or loses Position.
 *
 *   gp, p = child of gp, c = child of p, monitor on Position(up)
 *   add Position to gp    -> OnAdd p, OnAdd c        (both start matching)
 *   add Position to p     -> OnAdd c                 (c already matched)
 *   remove Position from p-> OnRemove c              (c still matches via gp)
 *
 * The event reaches c through propagation (observable.c 301-475), which
 * sets it->other_table to NULL (observable.c 328). The monitor tests whether
 * the "previous" table matched, and with no other table it uses the root
 * table (observer.c 694, 741-757), which never matches, so every
 * propagated OnAdd/OnRemove looks like a first match or a last unmatch.
 *
 * Documented: ObserversManual.md "Monitors" ("A monitor is an observer that
 * fires when an entity starts and stops matching a query"); flecs's own
 * Monitor_monitor_w_superset test expects no event for a second match. */
#include "flecs.h"
#include <stdio.h>

typedef struct { float x, y; } Position;

static int adds, removes;

static void Mon(ecs_iter_t *it) {
    if (it->event == EcsOnAdd) adds += it->count;
    else if (it->event == EcsOnRemove) removes += it->count;
}

int main(void) {
    ecs_world_t *world = ecs_mini();
    ECS_COMPONENT(world, Position);

    ecs_observer(world, {
        .query.terms = {{ ecs_id(Position), .src.id = EcsUp, .trav = EcsChildOf }},
        .events = { EcsMonitor },
        .callback = Mon
    });

    ecs_entity_t gp = ecs_new(world);
    ecs_entity_t p = ecs_new_w_pair(world, EcsChildOf, gp);
    ecs_entity_t c = ecs_new_w_pair(world, EcsChildOf, p);
    (void)c;

    ecs_add(world, gp, Position);
    int failed = 0;
    if (adds != 2 || removes != 0) {
        printf("INCONCLUSIVE: after the grandparent got Position: %d OnAdd, %d OnRemove\n",
            adds, removes);
        return 2;
    }

    ecs_add(world, p, Position);
    if (adds != 2) {
        printf("FAIL: OnAdd for an entity that already matched (%d OnAdd in total)\n", adds);
        failed = 1;
    }

    ecs_remove(world, p, Position);
    if (removes != 0) {
        printf("FAIL: OnRemove for an entity that still matches (%d OnRemove)\n", removes);
        failed = 1;
    }

    ecs_fini(world);
    return failed;
}
