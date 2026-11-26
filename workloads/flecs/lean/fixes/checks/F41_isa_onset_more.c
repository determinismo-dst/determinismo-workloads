/* Check for F41, beyond the finding's test. Health: Sparse, Inherit;
 * Defense: DontFragment, Inherit; Armor: DontFragment, default
 * (OnInstantiate, Override). OnSet observers with self|up (default) and with
 * up only.
 *   1. o owns Health and Defense, then gets IsA base: no self|up event (owned
 *      takes precedence), one up event each, source base;
 *   2. inst IsA b1 (without the components), then IsA b2 (with them): one
 *      self|up event each, source b2;
 *   3. i IsA base: Armor is copied at instantiation (an owned value): one
 *      self|up event, no source, as on v4.2.0.
 * main returns 0 when every count matches. */
#include "flecs.h"
#include <stdio.h>

typedef struct { int value; } Health;
typedef struct { int value; } Defense;
typedef struct { int value; } Armor;

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

static int events(const Log *log, int from, ecs_entity_t e, ecs_entity_t src) {
    int n = 0;
    for (int i = from; i < log->count; i ++) {
        if (log->entity[i] == e && log->source[i] == src) n ++;
    }
    return n;
}

int main(void) {
    ecs_world_t *world = ecs_mini();
    ECS_COMPONENT(world, Health);
    ECS_COMPONENT(world, Defense);
    ECS_COMPONENT(world, Armor);
    ecs_add_id(world, ecs_id(Health), EcsSparse);
    ecs_add_pair(world, ecs_id(Health), EcsOnInstantiate, EcsInherit);
    ecs_add_id(world, ecs_id(Defense), EcsDontFragment);
    ecs_add_pair(world, ecs_id(Defense), EcsOnInstantiate, EcsInherit);
    ecs_add_id(world, ecs_id(Armor), EcsDontFragment);

    ecs_entity_t base = ecs_new_w_id(world, EcsPrefab);
    ecs_set(world, base, Health, {10});
    ecs_set(world, base, Defense, {50});
    ecs_set(world, base, Armor, {5});
    ecs_entity_t b1 = ecs_new_w_id(world, EcsPrefab);

    Log h = {0}, d = {0}, hu = {0}, du = {0}, a = {0};
    ecs_observer(world, { .query.terms = {{ ecs_id(Health) }},
        .events = { EcsOnSet }, .callback = on_set, .ctx = &h });
    ecs_observer(world, { .query.terms = {{ ecs_id(Defense) }},
        .events = { EcsOnSet }, .callback = on_set, .ctx = &d });
    ecs_observer(world, { .query.terms = {{ ecs_id(Health), .src.id = EcsUp, .trav = EcsIsA }},
        .events = { EcsOnSet }, .callback = on_set, .ctx = &hu });
    ecs_observer(world, { .query.terms = {{ ecs_id(Defense), .src.id = EcsUp, .trav = EcsIsA }},
        .events = { EcsOnSet }, .callback = on_set, .ctx = &du });
    ecs_observer(world, { .query.terms = {{ ecs_id(Armor) }},
        .events = { EcsOnSet }, .callback = on_set, .ctx = &a });

    int failed = 0;

    /* 1 */
    ecs_entity_t o = ecs_new(world);
    ecs_set(world, o, Health, {1});
    ecs_set(world, o, Defense, {2});
    int mh = h.count, md = d.count, mhu = hu.count, mdu = du.count;
    ecs_add_pair(world, o, EcsIsA, base);
    int n1[4] = { events(&h, mh, o, base), events(&d, md, o, base),
        events(&hu, mhu, o, base), events(&du, mdu, o, base) };
    printf("1. owner gets IsA base: self|up Health %d, Defense %d; up Health "
        "%d, Defense %d\n", n1[0], n1[1], n1[2], n1[3]);
    if (n1[0] || n1[1] || n1[2] != 1 || n1[3] != 1) failed = 1;

    /* 2 */
    ecs_entity_t inst = ecs_new(world);
    ecs_add_pair(world, inst, EcsIsA, b1);
    mh = h.count; md = d.count;
    ecs_add_pair(world, inst, EcsIsA, base);
    int n2[2] = { events(&h, mh, inst, base), events(&d, md, inst, base) };
    printf("2. IsA b1 (nothing), then IsA base: Health %d, Defense %d\n",
        n2[0], n2[1]);
    if (n2[0] != 1 || n2[1] != 1) failed = 1;

    /* 3 */
    int ma = a.count;
    ecs_entity_t i = ecs_new_w_pair(world, EcsIsA, base);
    const Armor *ar = ecs_get(world, i, Armor);
    int n3 = events(&a, ma, i, 0), n3b = events(&a, ma, i, base);
    printf("3. Armor (Override) copied: %d owned event(s), %d from base; "
        "owns %d value %d\n", n3, n3b, ecs_owns(world, i, Armor),
        ar ? ar->value : -1);
    if (n3 != 1 || n3b != 0) failed = 1;

    printf(failed ? "FAIL\n" : "OK\n");
    ecs_fini(world);
    return failed;
}
