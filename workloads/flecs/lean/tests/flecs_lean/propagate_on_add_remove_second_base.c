/* Prediction F49: OnAdd and OnRemove events name a base that is not the one
 * up traversal finds, for an entity that already has the component from
 * its first base and keeps it.
 *
 *   Position: table, Inherit; b1 < b2 prefabs, b1 has Position {1, 1}
 *   OnAdd and OnRemove observers (default source self|up IsA)
 *   (a) propagation: inst = IsA b1, IsA b2 (b2 without Position)
 *       ecs_set(b2, Position, {2, 2})     OnAdd for inst, source b2
 *       ecs_remove(b2, Position)          OnRemove for inst, source b2
 *   (b) forwarding: b3 has Position {3, 3}; inst_f = IsA b1, then
 *       ecs_add_pair(inst_f, IsA, b3)     OnAdd for inst_f, source b3
 *       ecs_remove_pair(inst_f, IsA, b3)  OnRemove for inst_f, source b3
 *   (c) a diamond: v = IsA b4; d = IsA b4, IsA v (b4 without Position)
 *       ecs_set(b4, Position, {4, 4})     OnAdd for d twice, source b4
 *   ecs_get returns b1's value for inst and inst_f throughout.
 *
 * (a) The OnAdd and OnRemove of b2 are propagated to every entity of every
 * (IsA, b2) table that does not own Position (observable.c 310-376), with
 * no test of whether another base provides it first. (b) Adding or removing
 * (IsA, b3) forwards every element reachable through the pair
 * (flecs_emit_forward, 799-888; flecs_emit_forward_id, 613-706), again
 * without that test. (c) The propagation from b4 reaches d once through
 * (IsA, b4) and once more through v (flecs_emit_propagate_id_for_range
 * walks on below every entity of a table unless it is owned, 361-375). ecs_get takes the first
 * base in type order (flecs_get_base_component, addons/prefab/
 * instantiate.c 485-555). The same mechanism gave F43 its OnSet events.
 *
 * Documented: ObserversManual.md "OnAdd Events" ("An event only fires when
 * the component is actually added to the entity"), "OnRemove Events",
 * "Event Propagation" and "Event Forwarding" ("Only reachable components
 * are forwarded ... this ensures consistency with the behavior of up
 * traversal in queries"); "Adding an IsA pair" names b1, "the lowest entity
 * id of all base entities that provide the component", the primary source.
 * Control: an entity whose only base gains Position gets one OnAdd. main
 * returns 0 when inst, inst_f and d get no such event and d gets one OnAdd. */
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
        if (log->entity[i] == e && log->source[i] == src) n ++;
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

    ecs_entity_t b1 = ecs_new_w_id(world, EcsPrefab);
    ecs_entity_t b2 = ecs_new_w_id(world, EcsPrefab);
    ecs_entity_t b3 = ecs_new_w_id(world, EcsPrefab);
    ecs_entity_t b4 = ecs_new_w_id(world, EcsPrefab);
    ecs_entity_t b5 = ecs_new_w_id(world, EcsPrefab);
    ecs_set(world, b1, Position, {1, 1});
    ecs_set(world, b3, Position, {3, 3});
    if (!(b1 < b2 && b1 < b3)) {
        printf("INCONCLUSIVE: ids not in creation order\n");
        return 2;
    }

    ecs_entity_t inst = ecs_new_w_pair(world, EcsIsA, b1);
    ecs_add_pair(world, inst, EcsIsA, b2);
    ecs_entity_t inst_f = ecs_new_w_pair(world, EcsIsA, b1);
    ecs_entity_t v = ecs_new_w_pair(world, EcsIsA, b4);
    ecs_entity_t d = ecs_new_w_pair(world, EcsIsA, b4);
    ecs_add_pair(world, d, EcsIsA, v);
    ecs_entity_t ctl = ecs_new_w_pair(world, EcsIsA, b5);

    Log add = {0}, rem = {0};
    ecs_observer(world, { .query.terms = {{ ecs_id(Position) }},
        .events = { EcsOnAdd }, .callback = on_event, .ctx = &add });
    ecs_observer(world, { .query.terms = {{ ecs_id(Position) }},
        .events = { EcsOnRemove }, .callback = on_event, .ctx = &rem });

    /* (a) */
    ecs_set(world, b2, Position, {2, 2});
    float xa1 = x_of(world, inst);
    ecs_remove(world, b2, Position);
    float xa2 = x_of(world, inst);
    int a_add = events_for(&add, inst, b2), a_rem = events_for(&rem, inst, b2);

    /* (b) */
    ecs_add_pair(world, inst_f, EcsIsA, b3);
    float xb1 = x_of(world, inst_f);
    ecs_remove_pair(world, inst_f, EcsIsA, b3);
    float xb2 = x_of(world, inst_f);
    int b_add = events_for(&add, inst_f, b3);
    int b_rem = events_for(&rem, inst_f, b3);

    /* (c) and the control */
    ecs_set(world, b4, Position, {4, 4});
    int c_add = events_for(&add, d, b4);
    ecs_set(world, b5, Position, {5, 5});
    int ctl_add = events_for(&add, ctl, b5);

    printf("(a) inst sees x=%g, then x=%g; OnAdd from b2 %d, OnRemove from "
        "b2 %d\n", xa1, xa2, a_add, a_rem);
    printf("(b) inst_f sees x=%g, then x=%g; OnAdd from b3 %d, OnRemove "
        "from b3 %d\n", xb1, xb2, b_add, b_rem);
    printf("(c) d: OnAdd from b4 %d (expected 1); control: OnAdd from b5 "
        "%d (expected 1)\n", c_add, ctl_add);

    int failed = 0;
    if (xa1 != 1 || xa2 != 1 || xb1 != 1 || xb2 != 1) {
        printf("INCONCLUSIVE: ecs_get does not return b1's value\n");
        failed = 2;
    } else if (ctl_add != 1) {
        printf("INCONCLUSIVE: the control got %d OnAdd events\n", ctl_add);
        failed = 2;
    } else if (a_add || a_rem || b_add || b_rem || c_add != 1) {
        printf("FAIL: OnAdd/OnRemove events name a base that is not the "
            "entity's source (or come twice)\n");
        failed = 1;
    }
    ecs_fini(world);
    return failed;
}
