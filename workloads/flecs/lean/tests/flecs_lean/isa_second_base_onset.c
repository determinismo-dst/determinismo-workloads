/* Prediction F43: OnSet events for an inherited component name a base that
 * is not the entity's source for it (the documented "primary source"), and
 * the event carries a value the entity does not have:
 *   1. adding a second base that also provides the component, when the
 *      first base keeps being the primary source;
 *   2. setting the component on that second base;
 *   3. adding a variant that has two bases providing the component: two
 *      OnSet events for one IsA add.
 * A table component with the (OnInstantiate, Inherit) trait throughout.
 *
 *   b1 < b2: prefabs, Position {1, 1} and {2, 2}
 *   inst: IsA b1; observer; then
 *   1. ecs_add_pair(inst, IsA, b2)   OnSet for inst, source b2
 *                                    (ecs_get(inst, Position) is {1, 1})
 *   2. ecs_set(b2, Position, {3, 3}) OnSet for inst, source b2
 *   3. v: prefab, IsA b1 and IsA b2; i3 = IsA v: two OnSet events (b1, b2)
 *   control: inst2: IsA b2, then IsA b1: one OnSet, source b1 (b1 becomes
 *   the primary source)
 *
 * Adding (IsA, b) forwards every id reachable through the pair
 * (flecs_emit_forward, observable.c 799-830) with the OnSet observers
 * (1196-1237); flecs_emit_forward_id (613-706) only asks whether the
 * entity's own table has the component (`owned`, 662-663, 697-700), not
 * whether another base already provides it. The reachable ids of (IsA, v)
 * list Position once per base of v that provides it, since v's table does
 * not have it (flecs_reachable_cache_ensure, 729-764). Setting a base
 * propagates the event to every table with (IsA, base) that does not own
 * the component (flecs_emit_propagate_id_for_range, 310-376). ecs_get
 * returns the first base in type order, depth first
 * (flecs_get_base_component, addons/prefab/instantiate.c 485-555).
 *
 * Documented: ObserversManual.md "Adding an IsA pair": "if a component from
 * a base entity is already provided by another base entity, and the new
 * base entity does not become the primary source for the component, no
 * OnSet event is generated. A base entity is the primary source for a
 * component if [...] It has the lowest entity id of all base entities that
 * provide the component"; "When an IsA pair is added to an entity, an OnSet
 * event is generated for each newly inherited component" (one event);
 * "Setting an Inherited Component". main returns 0 when no event names b2
 * for inst and i3 gets one event, from b1. */
#include "flecs.h"
#include <stdio.h>
#include <stdlib.h>

typedef struct { float x, y; } Position;

typedef struct {
    ecs_entity_t entity[32];
    ecs_entity_t source[32];
    int count;
} Log;

static void on_set(ecs_iter_t *it) {
    Log *log = it->ctx;
    for (int i = 0; i < it->count; i ++) {
        if (log->count < 32) {
            log->entity[log->count] = it->entities[i];
            log->source[log->count] = ecs_field_src(it, 0);
            log->count ++;
        }
    }
}

static int events_for(const Log *log, int from, ecs_entity_t e,
    ecs_entity_t src)
{
    int n = 0;
    for (int i = from; i < log->count; i ++) {
        if (log->entity[i] == e && (!src || log->source[i] == src)) n ++;
    }
    return n;
}

int main(void) {
    ecs_world_t *world = ecs_mini();
    ECS_COMPONENT(world, Position);
    ecs_add_pair(world, ecs_id(Position), EcsOnInstantiate, EcsInherit);

    ecs_entity_t b1 = ecs_new_w_id(world, EcsPrefab);
    ecs_entity_t b2 = ecs_new_w_id(world, EcsPrefab);
    if (b1 > b2) { ecs_entity_t t = b1; b1 = b2; b2 = t; }
    ecs_set(world, b1, Position, {1, 1});
    ecs_set(world, b2, Position, {2, 2});
    ecs_entity_t v = ecs_new_w_id(world, EcsPrefab);
    ecs_add_pair(world, v, EcsIsA, b1);
    ecs_add_pair(world, v, EcsIsA, b2);

    ecs_entity_t inst = ecs_new(world);
    ecs_add_pair(world, inst, EcsIsA, b1);
    ecs_entity_t inst2 = ecs_new(world);
    ecs_add_pair(world, inst2, EcsIsA, b2);

    Log log = {0};
    ecs_observer(world, { .query.terms = {{ ecs_id(Position) }},
        .events = { EcsOnSet }, .callback = on_set, .ctx = &log });

    /* 1 */
    int m0 = log.count;
    ecs_add_pair(world, inst, EcsIsA, b2);
    const Position *p = ecs_get(world, inst, Position);
    if (!p || p->x != 1) {
        printf("INCONCLUSIVE: inst does not see b1's Position\n");
        return 2;
    }
    int e1 = events_for(&log, m0, inst, 0);
    int e1b2 = events_for(&log, m0, inst, b2);

    /* 2 */
    int m1 = log.count;
    ecs_set(world, b2, Position, {3, 3});
    p = ecs_get(world, inst, Position);
    int e2 = events_for(&log, m1, inst, 0);

    /* 3 */
    int m2 = log.count;
    ecs_entity_t i3 = ecs_new_w_pair(world, EcsIsA, v);
    p = ecs_get(world, i3, Position);
    int e3 = events_for(&log, m2, i3, 0), e3b1 = events_for(&log, m2, i3, b1);

    /* control */
    int m3 = log.count;
    ecs_add_pair(world, inst2, EcsIsA, b1);
    int c = events_for(&log, m3, inst2, 0), cb1 = events_for(&log, m3, inst2, b1);

    printf("1. second base added: %d event(s) for inst, %d from b2\n", e1, e1b2);
    printf("2. second base set: %d event(s) for inst (its Position: %.0f)\n",
        e2, ecs_get(world, inst, Position)->x);
    printf("3. variant with two bases: %d event(s) for i3, %d from b1 "
        "(its Position: %.0f)\n", e3, e3b1, p ? p->x : -1);
    printf("control: b1 added after b2: %d event(s) for inst2, %d from b1\n",
        c, cb1);

    int failed = 0;
    if (c != 1 || cb1 != 1) {
        printf("INCONCLUSIVE: the control did not get one OnSet from b1\n");
        failed = 2;
    } else if (e1 != 0 || e2 != 0 || e3 != 1 || e3b1 != 1) {
        printf("FAIL: OnSet events name a base that is not the entity's "
            "source for Position\n");
        failed = 1;
    }
    ecs_fini(world);
    return failed;
}
