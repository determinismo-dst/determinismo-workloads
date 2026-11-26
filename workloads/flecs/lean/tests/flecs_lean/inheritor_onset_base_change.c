/* Prediction F51: when the inheritance of an entity changes in one of the
 * documented OnSet scenarios, its own inheritors, whose value of the
 * component changes with it, get no OnSet event. They do get the OnAdd or
 * OnRemove of the same change.
 *
 *   Position: table, Inherit
 *   (a) base = prefab {1, 2}; variant = prefab (no Position, no base yet)
 *       inst = IsA variant (no Position)
 *       ecs_add_pair(variant, EcsIsA, base)  inst now reads {1, 2}:
 *                                            OnAdd for inst, no OnSet
 *   (b) variant2 = prefab IsA base, owns {5, 5}; inst2 = IsA variant2
 *       (reads {5, 5})
 *       ecs_remove(variant2, Position)       inst2 now reads {1, 2}:
 *                                            OnRemove for inst2, no OnSet
 *   control: inst3 = IsA variant after (a): one OnSet (the documented
 *   "Adding an IsA pair" scenario).
 *
 * (a) Adding (IsA, base) forwards base's reachable ids (observable.c
 * 1196-1237; flecs_emit_forward, 799-888): to variant itself the OnAdd and,
 * because Position has a column, the OnSet observers (flecs_emit_forward_id,
 * 613-706); then, because variant is the target of an IsA pair, each element
 * is propagated down to variant's inheritors with the observers of the
 * emitted event only, OnAdd (`er`, 835-888). The OnSet observers (er_onset)
 * are not passed down. (b) Removing the override emits OnRemove for
 * variant2's table and propagates it (component_actions.c 333-367;
 * observable.c 571-611); the OnSet for the value now inherited is emitted
 * for variant2's table only (flecs_emit_on_set_for_override_on_remove,
 * 951-1002), without propagation.
 *
 * Documented: ObserversManual.md "OnSet and Inheritance": "To ensure that
 * OnSet events can be used reliably to detect component changes, events can
 * be produced by operations that change inheritance relationships or
 * operate on inherited from components"; "Adding an IsA pair": "an OnSet
 * event is generated for each newly inherited component"; "Removing an
 * Override": removing the override "reexposes the component from the base"
 * and "produces OnSet event". inst and inst2 inherit through the entity of
 * the scenario, and their values change with it. main returns 0 when inst
 * and inst2 each get one OnSet with base as the source. */
#include "flecs.h"
#include <stdio.h>
#include <stdlib.h>

typedef struct { float x, y; } Position;
ECS_COMPONENT_DECLARE(Position);

typedef struct {
    ecs_entity_t entity[32];
    ecs_entity_t source[32];
    int count;
} Log;

static void on_event(ecs_iter_t *it) {
    Log *log = it->ctx;
    for (int i = 0; i < it->count; i ++) {
        if (log->count < 32) {
            log->entity[log->count] = it->entities[i];
            log->source[log->count] = ecs_field_src(it, 0);
            log->count ++;
        }
    }
}

static int events_for(const Log *log, ecs_entity_t e, ecs_entity_t src) {
    int n = 0;
    for (int i = 0; i < log->count; i ++) {
        if (log->entity[i] == e && (!src || log->source[i] == src)) n ++;
    }
    return n;
}

static float x_of(ecs_world_t *world, ecs_entity_t e) {
    const Position *p = ecs_get(world, e, Position);
    return p ? p->x : -1;
}

int main(void) {
    ecs_world_t *world = ecs_mini();
    ECS_COMPONENT_DEFINE(world, Position);
    ecs_add_pair(world, ecs_id(Position), EcsOnInstantiate, EcsInherit);

    ecs_entity_t base = ecs_new_w_id(world, EcsPrefab);
    ecs_set(world, base, Position, {1, 2});
    ecs_entity_t variant = ecs_new_w_id(world, EcsPrefab);
    ecs_entity_t inst = ecs_new_w_pair(world, EcsIsA, variant);
    ecs_entity_t variant2 = ecs_new_w_id(world, EcsPrefab);
    ecs_add_pair(world, variant2, EcsIsA, base);
    ecs_set(world, variant2, Position, {5, 5});
    ecs_entity_t inst2 = ecs_new_w_pair(world, EcsIsA, variant2);
    float x0 = x_of(world, inst), x20 = x_of(world, inst2);

    Log set = {0}, add = {0}, rem = {0};
    ecs_observer(world, { .query.terms = {{ ecs_id(Position) }},
        .events = { EcsOnSet }, .callback = on_event, .ctx = &set });
    ecs_observer(world, { .query.terms = {{ ecs_id(Position) }},
        .events = { EcsOnAdd }, .callback = on_event, .ctx = &add });
    ecs_observer(world, { .query.terms = {{ ecs_id(Position) }},
        .events = { EcsOnRemove }, .callback = on_event, .ctx = &rem });

    /* (a) */
    ecs_add_pair(world, variant, EcsIsA, base);
    float x1 = x_of(world, inst);
    int a_set = events_for(&set, inst, 0), a_add = events_for(&add, inst, 0);

    /* (b) */
    ecs_remove(world, variant2, Position);
    float x21 = x_of(world, inst2);
    int b_set = events_for(&set, inst2, 0), b_rem = events_for(&rem, inst2, 0);

    /* control */
    ecs_entity_t inst3 = ecs_new_w_pair(world, EcsIsA, variant);
    int c_set = events_for(&set, inst3, base);

    printf("(a) inst reads x=%g, then x=%g: OnSet %d, OnAdd %d\n", x0, x1,
        a_set, a_add);
    printf("(b) inst2 reads x=%g, then x=%g: OnSet %d, OnRemove %d\n", x20,
        x21, b_set, b_rem);
    printf("control: inst3 = IsA variant: OnSet from base %d\n", c_set);

    int failed = 0;
    if (x0 != -1 || x1 != 1 || x20 != 5 || x21 != 1) {
        printf("INCONCLUSIVE: the values do not change as set up\n");
        failed = 2;
    } else if (c_set != 1) {
        printf("INCONCLUSIVE: the control got %d OnSet events\n", c_set);
        failed = 2;
    } else if (events_for(&set, inst, base) != 1 ||
        events_for(&set, inst2, base) != 1)
    {
        printf("FAIL: inst and inst2 got a new inherited value without an "
            "OnSet event\n");
        failed = 1;
    }
    ecs_fini(world);
    return failed;
}
