/* Prediction F41: adding an IsA pair produces no OnSet event for an inherited
 * Sparse or DontFragment component with the (OnInstantiate, Inherit) trait,
 * at one or two IsA levels. A table component gets the event.
 *
 *   Position: table, Inherit; Health: Sparse, Inherit;
 *   Defense: DontFragment, Inherit
 *   base: prefab with all three; variant: prefab, IsA base
 *   OnSet observers (default source self|up IsA), then
 *   i1 = IsA base     (one level)   OnSet for Position only
 *   i2 = IsA variant  (two levels)  OnSet for Position only
 *
 * flecs_emit forwards the ids reachable through the new (IsA, b) pair with
 * the OnSet observers (observable.c 1196-1237, flecs_emit_forward 799-890).
 * The reachable ids are the Inherit ids of b's table type, and through b's
 * own IsA pairs those of its bases (flecs_reachable_cache_ensure, 708-780):
 * a DontFragment component is never in a table type, so it is never listed.
 * For a listed id, flecs_emit_forward_id invokes the OnSet observers only
 * when the id has a column in the source's table (685: `if (storage_i !=
 * -1)`); ecs_table_type_to_column_index is -1 for a Sparse component, which
 * has no column (storage/table.c 162-165). Instantiation emits nothing
 * either: flecs_instantiate_dont_fragment skips Inherit components of a
 * base the instance has an IsA pair to (addons/prefab/instantiate.c
 * 313-316).
 *
 * Documented: ObserversManual.md "OnSet and Inheritance": OnSet events for
 * inheritance are "enabled by default for components with the
 * (OnInstantiate, Inherit) trait"; "Adding an IsA pair": "When an IsA pair
 * is added to an entity, an OnSet event is generated for each newly
 * inherited component". ComponentTraits.md "Sparse trait": "ECS operations
 * and queries work as expected with sparse components"; "DontFragment
 * trait" (built on the Sparse storage). main returns 0 when each of i1 and
 * i2 gets one OnSet per component, with base as the source. */
#include "flecs.h"
#include <stdio.h>
#include <stdlib.h>

typedef struct { float x, y; } Position;
typedef struct { int value; } Health;
typedef struct { int value; } Defense;

typedef struct {
    ecs_entity_t entity[16];
    ecs_entity_t source[16];
    int count;
} Log;

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

static int events_for(const Log *log, ecs_entity_t e, ecs_entity_t src) {
    int n = 0;
    for (int i = 0; i < log->count; i ++) {
        if (log->entity[i] == e && log->source[i] == src) n ++;
    }
    return n;
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
    ecs_entity_t variant = ecs_new_w_id(world, EcsPrefab);
    ecs_add_pair(world, variant, EcsIsA, base);

    Log lp = {0}, lh = {0}, ld = {0};
    ecs_observer(world, { .query.terms = {{ ecs_id(Position) }},
        .events = { EcsOnSet }, .callback = on_set, .ctx = &lp });
    ecs_observer(world, { .query.terms = {{ ecs_id(Health) }},
        .events = { EcsOnSet }, .callback = on_set, .ctx = &lh });
    ecs_observer(world, { .query.terms = {{ ecs_id(Defense) }},
        .events = { EcsOnSet }, .callback = on_set, .ctx = &ld });

    ecs_entity_t i1 = ecs_new_w_pair(world, EcsIsA, base);
    ecs_entity_t i2 = ecs_new_w_pair(world, EcsIsA, variant);

    const Health *h = ecs_get(world, i2, Health);
    const Defense *d = ecs_get(world, i2, Defense);
    if (!h || h->value != 10 || !d || d->value != 50 ||
        ecs_owns(world, i1, Health) || ecs_owns(world, i1, Defense))
    {
        printf("INCONCLUSIVE: the instances do not inherit the components\n");
        return 2;
    }

    int p1 = events_for(&lp, i1, base), p2 = events_for(&lp, i2, base);
    int h1 = events_for(&lh, i1, base), h2 = events_for(&lh, i2, base);
    int d1 = events_for(&ld, i1, base), d2 = events_for(&ld, i2, base);
    printf("OnSet events (one level, two levels): Position %d %d, "
        "Health (Sparse) %d %d, Defense (DontFragment) %d %d\n",
        p1, p2, h1, h2, d1, d2);

    int failed = 0;
    if (p1 != 1 || p2 != 1) {
        printf("INCONCLUSIVE: the table component control did not get one "
            "OnSet per IsA add\n");
        failed = 2;
    } else if (h1 != 1 || h2 != 1 || d1 != 1 || d2 != 1) {
        printf("FAIL: an IsA add produced no OnSet for an inherited Sparse or "
            "DontFragment component\n");
        failed = 1;
    }
    ecs_fini(world);
    return failed;
}
