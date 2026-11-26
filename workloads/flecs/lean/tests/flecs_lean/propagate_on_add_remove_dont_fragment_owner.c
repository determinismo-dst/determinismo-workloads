/* Prediction F48: adding a DontFragment component to a base, or removing it,
 * gives an OnAdd or OnRemove event to an instance that owns the component
 * itself, with the base as the source, and to that instance's own
 * inheritors. Table and Sparse components give the owner no event (and
 * stop the propagation there).
 *
 *   Defense: DontFragment, Inherit; Position: table, Inherit;
 *   Health: Sparse, Inherit
 *   base = prefab (none of the three); inst = IsA base; inst sets all three
 *   inst2 = IsA inst (sees inst's values)
 *   OnAdd and OnRemove observers (default source self|up IsA), then
 *   ecs_set(base, Defense, {60})   OnAdd for inst and inst2, source base
 *   ecs_remove(base, Defense)       OnRemove for inst and inst2, source base
 * (b) the ChildOf example of ObserversManual.md "Event Propagation", with
 *   Mass: DontFragment (Velocity: table, the control)
 *   parent; child = ChildOf parent, owns Mass and Velocity; grandchild =
 *   ChildOf child; OnSet observers with .src.id = EcsSelf|EcsUp (ChildOf)
 *   ecs_set(parent, Mass, {1})      OnSet for child and grandchild, source
 *                                   parent
 *
 * ecs_set on base adds the component: flecs_actions_on_add_intern
 * (component_actions.c 286-331; for a DontFragment component
 * flecs_sparse_on_add reports the new element) emits OnAdd for base's table,
 * and flecs_emit propagates it down (observable.c 1312-1317:
 * flecs_propagate_entities, 571-611; flecs_emit_propagate, 440-475;
 * flecs_emit_propagate_id, 378-438). For every table with (IsA, base),
 * flecs_emit_propagate_id_for_range invokes the self|up observers unless the
 * table owns the component (324: owned = flecs_component_get_table(cr,
 * table) != NULL; 347-350), and walks on below the table's entities unless it
 * is owned (361). A DontFragment component is in no table type: inst's
 * table never "owns" Defense, so inst gets the event, and so does inst2,
 * whose Defense is inst's. The OnRemove of ecs_remove(base, Defense) takes
 * the same path (component_actions.c 333-367). The same mechanism gave F42
 * its OnSet. The walk is the same for every traversable relationship
 * (flecs_emit_propagate follows each (R, base) record, 461-472), so (b) takes
 * it along ChildOf.
 *
 * Documented: ObserversManual.md "OnAdd Events" ("An event only fires when
 * the component is actually added to the entity"), "OnRemove Events", and
 * "Event Propagation": "Events propagate until a leaf entity is found, or
 * an entity with the propagated component is found ... This ensures that
 * the results are consistent with up traversal"; its example: "if an event
 * for Position is propagated from a parent to a child with Position, that
 * event will not be propagated to the child's children". inst owns Defense
 * before and after both calls; child owns Mass. main returns 0 when neither
 * inst nor inst2 gets an event and grandchild gets no OnSet from parent. */
#include "flecs.h"
#include <stdio.h>
#include <stdlib.h>

typedef struct { float x, y; } Position;
typedef struct { int value; } Health;
typedef struct { int value; } Defense;
typedef struct { float value; } Mass;
typedef struct { float x, y; } Velocity;

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

static void observe(ecs_world_t *world, ecs_id_t id, Log *add, Log *rem) {
    ecs_observer(world, { .query.terms = {{ id }}, .events = { EcsOnAdd },
        .callback = on_event, .ctx = add });
    ecs_observer(world, { .query.terms = {{ id }}, .events = { EcsOnRemove },
        .callback = on_event, .ctx = rem });
}

int main(void) {
    ecs_world_t *world = ecs_mini();
    ECS_COMPONENT(world, Position);
    ECS_COMPONENT(world, Health);
    ECS_COMPONENT(world, Defense);
    ecs_add_pair(world, ecs_id(Position), EcsOnInstantiate, EcsInherit);
    ecs_add_id(world, ecs_id(Health), EcsSparse);
    ecs_add_pair(world, ecs_id(Health), EcsOnInstantiate, EcsInherit);
    ecs_add_id(world, ecs_id(Defense), EcsDontFragment);
    ecs_add_pair(world, ecs_id(Defense), EcsOnInstantiate, EcsInherit);

    ecs_entity_t base = ecs_new_w_id(world, EcsPrefab);
    ecs_entity_t inst = ecs_new_w_pair(world, EcsIsA, base);
    ecs_set(world, inst, Position, {5, 5});
    ecs_set(world, inst, Health, {5});
    ecs_set(world, inst, Defense, {7});
    ecs_entity_t inst2 = ecs_new_w_pair(world, EcsIsA, inst);
    if (!ecs_owns(world, inst, Defense) || !ecs_owns(world, inst, Position) ||
        !ecs_owns(world, inst, Health) || ecs_owns(world, inst2, Defense))
    {
        printf("INCONCLUSIVE: the setup does not hold\n");
        return 2;
    }

    Log ap = {0}, rp = {0}, ah = {0}, rh = {0}, ad = {0}, rd = {0};
    observe(world, ecs_id(Position), &ap, &rp);
    observe(world, ecs_id(Health), &ah, &rh);
    observe(world, ecs_id(Defense), &ad, &rd);

    ecs_set(world, base, Position, {1, 2});
    ecs_set(world, base, Health, {10});
    ecs_set(world, base, Defense, {60});
    const Defense *d = ecs_get(world, inst, Defense);
    const Defense *d2 = ecs_get(world, inst2, Defense);
    int add_ok = d && d->value == 7 && d2 && d2->value == 7;

    ecs_remove(world, base, Position);
    ecs_remove(world, base, Health);
    ecs_remove(world, base, Defense);
    d = ecs_get(world, inst, Defense);
    d2 = ecs_get(world, inst2, Defense);
    int rem_ok = d && d->value == 7 && d2 && d2->value == 7 &&
        ecs_owns(world, inst, Defense);

    int controls = events_for(&ap, inst, base) + events_for(&rp, inst, base) +
        events_for(&ah, inst, base) + events_for(&rh, inst, base) +
        events_for(&ap, inst2, base) + events_for(&rp, inst2, base) +
        events_for(&ah, inst2, base) + events_for(&rh, inst2, base);
    int a1 = events_for(&ad, inst, base), r1 = events_for(&rd, inst, base);
    int a2 = events_for(&ad, inst2, base), r2 = events_for(&rd, inst2, base);
    printf("events with source base: Position and Health (inst, inst2) %d; "
        "Defense OnAdd inst %d, inst2 %d; Defense OnRemove inst %d, "
        "inst2 %d\n", controls, a1, a2, r1, r2);

    /* (b) ChildOf */
    ECS_COMPONENT(world, Mass);
    ECS_COMPONENT(world, Velocity);
    ecs_add_id(world, ecs_id(Mass), EcsDontFragment);
    ecs_entity_t parent = ecs_new(world);
    ecs_entity_t child = ecs_new_w_pair(world, EcsChildOf, parent);
    ecs_set(world, child, Mass, {7});
    ecs_set(world, child, Velocity, {7, 7});
    ecs_entity_t grandchild = ecs_new_w_pair(world, EcsChildOf, child);
    Log sm = {0}, sv = {0};
    ecs_entity_t om = ecs_observer(world, { .query.terms = {{ ecs_id(Mass),
        .src.id = EcsSelf|EcsUp }}, .events = { EcsOnSet },
        .callback = on_event, .ctx = &sm });
    ecs_entity_t ov = ecs_observer(world, { .query.terms = {{
        ecs_id(Velocity), .src.id = EcsSelf|EcsUp }}, .events = { EcsOnSet },
        .callback = on_event, .ctx = &sv });
    ecs_set(world, parent, Mass, {1});
    ecs_set(world, parent, Velocity, {1, 1});
    const Mass *gm = ecs_get(world, grandchild, Mass);
    int b_ok = om && ov && !gm;
    int vc = events_for(&sv, child, parent) + events_for(&sv, grandchild, parent);
    int mc = events_for(&sm, child, parent);
    int mg = events_for(&sm, grandchild, parent);
    printf("(b) OnSet from parent: Velocity (child, grandchild) %d; Mass "
        "child %d, grandchild %d\n", vc, mc, mg);

    int failed = 0;
    if (!add_ok || !rem_ok || !b_ok) {
        printf("INCONCLUSIVE: the setup does not hold (Defense values, or "
            "the ChildOf observers)\n");
        failed = 2;
    } else if (controls != 0 || vc != 0) {
        printf("INCONCLUSIVE: a control (table or Sparse) got an event\n");
        failed = 2;
    } else {
        if (a1 || r1 || a2 || r2) {
            printf("FAIL: inst owns Defense (7) throughout, yet it%s got "
                "OnAdd and OnRemove events from base\n",
                (a2 || r2) ? " and inst2" : "");
            failed = 1;
        }
        if (mg) {
            printf("FAIL: the OnSet of parent's Mass reached grandchild "
                "through child, which owns Mass\n");
            failed = 1;
        }
    }
    ecs_fini(world);
    return failed;
}
