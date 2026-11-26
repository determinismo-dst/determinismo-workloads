/* Prediction F42: setting a DontFragment component on a base produces an
 * OnSet event for an instance that overrides the component: the event
 * names the base as the source and carries the base's new value, while the
 * instance's own value is unchanged. Table and Sparse components get no
 * event for the overriding instance.
 *
 *   Defense: DontFragment, Inherit; Position: table, Inherit;
 *   Health: Sparse, Inherit
 *   base: prefab with all three; inst = IsA base, then inst overrides all
 *   three (ecs_set on inst)
 *   OnSet observers (default source self|up IsA), then
 *   ecs_set(base, Defense, {60})   OnSet for inst, source base, value 60;
 *                                  ecs_get(inst, Defense) is still 7
 *
 * ecs_set on base emits OnSet for base's table and propagates it down
 * (observable.c 1316: flecs_propagate_entities, 571-611; flecs_emit_propagate
 * 440-465; flecs_emit_propagate_id 378-438): for every table with (IsA,
 * base), flecs_emit_propagate_id_for_range invokes the up and self|up
 * observers unless the table owns the component (324: `owned =
 * flecs_component_get_table(cr, table) != NULL`; 337-354). A DontFragment
 * component is in no table type, so no table "owns" it, and inst, which
 * holds its own value in the sparse storage, gets the base's event. For a
 * table or Sparse component the override is in inst's table type.
 *
 * Documented: ObserversManual.md "Setting an Inherited Component": "When an
 * inherited component is modified, an OnSet event is propagated to all
 * entities that inherit the component" (inst does not: it owns Defense);
 * "OnSet and Inheritance": "If the base entity has a component that the
 * entity already had no event is generated"; PrefabsManual.md "Component
 * Overriding". main returns 0 when no OnSet reaches inst. */
#include "flecs.h"
#include <stdio.h>
#include <stdlib.h>

typedef struct { float x, y; } Position;
typedef struct { int value; } Health;
typedef struct { int value; } Defense;
ECS_COMPONENT_DECLARE(Defense);

typedef struct {
    ecs_entity_t entity[16];
    ecs_entity_t source[16];
    int value[16];
    int count;
} Log;

static void on_set_defense(ecs_iter_t *it) {
    Log *log = it->ctx;
    ecs_entity_t src = ecs_field_src(it, 0);
    for (int i = 0; i < it->count; i ++) {
        if (log->count < 16) {
            /* the value the event reports: the source's (an up field) */
            const Defense *d = ecs_get(it->world,
                src ? src : it->entities[i], Defense);
            log->entity[log->count] = it->entities[i];
            log->source[log->count] = src;
            log->value[log->count] = d ? d->value : -1;
            log->count ++;
        }
    }
}

static void on_set(ecs_iter_t *it) {
    Log *log = it->ctx;
    for (int i = 0; i < it->count; i ++) {
        if (log->count < 16) {
            log->entity[log->count] = it->entities[i];
            log->source[log->count] = ecs_field_src(it, 0);
            log->count ++;
        }
    }
}

static int events_for(const Log *log, ecs_entity_t e) {
    int n = 0;
    for (int i = 0; i < log->count; i ++) {
        if (log->entity[i] == e) n ++;
    }
    return n;
}

int main(void) {
    ecs_world_t *world = ecs_mini();
    ECS_COMPONENT(world, Position);
    ECS_COMPONENT(world, Health);
    ECS_COMPONENT_DEFINE(world, Defense);
    ecs_add_pair(world, ecs_id(Position), EcsOnInstantiate, EcsInherit);
    ecs_add_id(world, ecs_id(Health), EcsSparse);
    ecs_add_pair(world, ecs_id(Health), EcsOnInstantiate, EcsInherit);
    ecs_add_id(world, ecs_id(Defense), EcsDontFragment);
    ecs_add_pair(world, ecs_id(Defense), EcsOnInstantiate, EcsInherit);

    ecs_entity_t base = ecs_new_w_id(world, EcsPrefab);
    ecs_set(world, base, Position, {1, 2});
    ecs_set(world, base, Health, {10});
    ecs_set(world, base, Defense, {50});

    ecs_entity_t inst = ecs_new_w_pair(world, EcsIsA, base);
    ecs_set(world, inst, Position, {5, 5});
    ecs_set(world, inst, Health, {5});
    ecs_set(world, inst, Defense, {7});
    if (!ecs_owns(world, inst, Position) || !ecs_owns(world, inst, Health) ||
        !ecs_owns(world, inst, Defense))
    {
        printf("INCONCLUSIVE: inst does not own its overrides\n");
        return 2;
    }

    Log lp = {0}, lh = {0}, ld = {0};
    ecs_observer(world, { .query.terms = {{ ecs_id(Position) }},
        .events = { EcsOnSet }, .callback = on_set, .ctx = &lp });
    ecs_observer(world, { .query.terms = {{ ecs_id(Health) }},
        .events = { EcsOnSet }, .callback = on_set, .ctx = &lh });
    ecs_observer(world, { .query.terms = {{ ecs_id(Defense) }},
        .events = { EcsOnSet }, .callback = on_set_defense, .ctx = &ld });

    ecs_set(world, base, Position, {3, 4});
    ecs_set(world, base, Health, {20});
    ecs_set(world, base, Defense, {60});

    const Defense *d = ecs_get(world, inst, Defense);
    int np = events_for(&lp, inst), nh = events_for(&lh, inst);
    int nd = events_for(&ld, inst);
    printf("OnSet events for inst after setting base: Position %d, Health %d, "
        "Defense %d; ecs_get(inst, Defense) = %d\n", np, nh, nd,
        d ? d->value : -1);
    for (int i = 0; i < ld.count; i ++) {
        if (ld.entity[i] == inst) {
            printf("  Defense event for inst: source %s, value %d\n",
                ld.source[i] == base ? "base" : "other", ld.value[i]);
        }
    }

    int failed = 0;
    if (!d || d->value != 7) {
        printf("INCONCLUSIVE: inst's own Defense changed\n");
        failed = 2;
    } else if (np != 0 || nh != 0) {
        printf("INCONCLUSIVE: a control (table or Sparse) got an event\n");
        failed = 2;
    } else if (nd != 0) {
        printf("FAIL: inst owns Defense (7) but got an OnSet for the base's "
            "value\n");
        failed = 1;
    }
    ecs_fini(world);
    return failed;
}
