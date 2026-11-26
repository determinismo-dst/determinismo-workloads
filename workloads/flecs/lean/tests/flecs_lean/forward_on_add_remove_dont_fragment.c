/* Prediction F50: adding an IsA pair to a base with an inherited
 * DontFragment component gives no OnAdd event for it, and removing the pair
 * gives no OnRemove event, while the entity gains and loses the component.
 * Table and Sparse components get both events.
 *
 *   Defense: DontFragment, Inherit; Position: table, Inherit;
 *   Health: Sparse, Inherit
 *   base = prefab with all three
 *   OnAdd and OnRemove observers (default source self|up IsA)
 *   inst = ecs_new(world)
 *   ecs_add_pair(inst, EcsIsA, base)     OnAdd for Position and Health only
 *   ecs_remove_pair(inst, EcsIsA, base)  OnRemove for Position and Health only
 * (b) the ChildOf example of ObserversManual.md "Event Forwarding", with
 *   Mass: DontFragment (Velocity: table, the control)
 *   parent with Mass and Velocity; OnAdd observers with .src.id = EcsUp
 *   (ChildOf); child = ecs_new_w_pair(world, EcsChildOf, parent)
 *                                        OnAdd for Velocity only
 *
 * flecs_emit forwards the ids reachable through the pair (observable.c
 * 1196-1237; flecs_emit_forward, 799-888): flecs_reachable_cache_ensure
 * (708-780) lists the Inherit ids of base's table type, and a DontFragment
 * component is in no table type, so Defense is never listed and no event is
 * forwarded for it, OnAdd or OnRemove. Instantiation does not add it either:
 * flecs_instantiate_dont_fragment skips Inherit components of a base the
 * instance has an IsA pair to (addons/prefab/instantiate.c 313-316). The
 * same mechanism gave F41 its missing OnSet. For (b) the reachable ids of
 * (ChildOf, parent) are all ids of parent's table type (no Inherit filter,
 * 736-738), which again never holds Mass.
 *
 * Documented: ObserversManual.md "Event Forwarding": "if a (ChildOf,
 * my_parent) pair is added to an entity, and my_parent has components
 * Position and Velocity, an OnAdd event is produced for each component and
 * emitted for the child ... adding a pair results in forwarded OnAdd
 * events, and removing a pair results in forwarded OnRemove events";
 * ComponentTraits.md "DontFragment trait" lists ECS operations among what
 * works (its limitations name monitors, not observers). ecs_has(inst,
 * Defense) is true after the add and false after the remove. main returns 0 when Defense gets one OnAdd and
 * one OnRemove for inst, and Mass one OnAdd for child. */
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
    int count;
} Log;

static void on_event(ecs_iter_t *it) {
    Log *log = it->ctx;
    for (int i = 0; i < it->count; i ++) {
        if (log->count < 32) log->entity[log->count ++] = it->entities[i];
    }
}

static int events_for(const Log *log, ecs_entity_t e) {
    int n = 0;
    for (int i = 0; i < log->count; i ++) if (log->entity[i] == e) n ++;
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
    ecs_set(world, base, Position, {1, 2});
    ecs_set(world, base, Health, {10});
    ecs_set(world, base, Defense, {50});

    Log ap = {0}, rp = {0}, ah = {0}, rh = {0}, ad = {0}, rd = {0};
    observe(world, ecs_id(Position), &ap, &rp);
    observe(world, ecs_id(Health), &ah, &rh);
    observe(world, ecs_id(Defense), &ad, &rd);

    ecs_entity_t inst = ecs_new(world);
    ecs_add_pair(world, inst, EcsIsA, base);
    int has_after_add = ecs_has(world, inst, Defense) &&
        !ecs_owns(world, inst, Defense);
    ecs_remove_pair(world, inst, EcsIsA, base);
    int has_after_remove = ecs_has(world, inst, Defense);

    int pa = events_for(&ap, inst), pr = events_for(&rp, inst);
    int ha = events_for(&ah, inst), hr = events_for(&rh, inst);
    int da = events_for(&ad, inst), dr = events_for(&rd, inst);
    printf("inst: Position OnAdd %d OnRemove %d; Health OnAdd %d OnRemove "
        "%d; Defense OnAdd %d OnRemove %d\n", pa, pr, ha, hr, da, dr);

    /* (b) ChildOf */
    ECS_COMPONENT(world, Mass);
    ECS_COMPONENT(world, Velocity);
    ecs_add_id(world, ecs_id(Mass), EcsDontFragment);
    ecs_entity_t parent = ecs_new(world);
    ecs_set(world, parent, Mass, {1});
    ecs_set(world, parent, Velocity, {1, 1});
    Log am = {0}, av = {0};
    ecs_entity_t om = ecs_observer(world, { .query.terms = {{ ecs_id(Mass),
        .src.id = EcsUp }}, .events = { EcsOnAdd }, .callback = on_event,
        .ctx = &am });
    ecs_entity_t ov = ecs_observer(world, { .query.terms = {{
        ecs_id(Velocity), .src.id = EcsUp }}, .events = { EcsOnAdd },
        .callback = on_event, .ctx = &av });
    ecs_entity_t child = ecs_new_w_pair(world, EcsChildOf, parent);
    int b_ok = om && ov && ecs_get_target_for_id(world, child, EcsChildOf,
        ecs_id(Velocity)) == parent;
    int ma = events_for(&am, child), va = events_for(&av, child);
    printf("(b) child = ChildOf parent: Velocity(up) OnAdd %d; Mass(up) "
        "OnAdd %d\n", va, ma);

    int failed = 0;
    if (!has_after_add || has_after_remove || !b_ok) {
        printf("INCONCLUSIVE: inst does not inherit Defense through the "
            "pair, or the ChildOf observers were not created\n");
        failed = 2;
    } else if (pa != 1 || pr != 1 || ha != 1 || hr != 1 || va != 1) {
        printf("INCONCLUSIVE: a control (table or Sparse) did not get its "
            "events\n");
        failed = 2;
    } else {
        if (da != 1 || dr != 1) {
            printf("FAIL: inst gained and lost the inherited Defense without "
                "an OnAdd and an OnRemove\n");
            failed = 1;
        }
        if (ma != 1) {
            printf("FAIL: child gained Mass through ChildOf (the documented "
                "example) without an OnAdd\n");
            failed = 1;
        }
    }
    ecs_fini(world);
    return failed;
}
