/* F50 check: forwarded OnAdd and OnRemove of inherited DontFragment
 * components, beyond the finding's test.
 *   Defense: DontFragment, Inherit; Mass: DontFragment
 *   (a) inst has an inheritor j (j IsA inst): (IsA, base) added to inst gives
 *       j one OnAdd Defense from base too; removed, one OnRemove
 *   (b) own owns Defense: (IsA, base) added: no self|up event for own, one
 *       for an up-only observer
 *   (c) grandparent gp has Mass; p ChildOf gp; ch = new ChildOf p: one
 *       OnAdd Mass(up) for ch, from gp
 *   (d) Armor: DontFragment, DontInherit, on base: no event (not inherited,
 *       not copied)
 *   (e) deleting inst2 (IsA base): one OnRemove Defense */
#include "flecs.h"
#include <stdio.h>

typedef struct { int v; } Defense;
typedef struct { int v; } Armor;
typedef struct { float v; } Mass;

typedef struct { ecs_entity_t e[64], src[64]; int n; } Log;

static void on_event(ecs_iter_t *it) {
    Log *l = it->ctx;
    for (int i = 0; i < it->count && l->n < 64; i ++) {
        l->e[l->n] = it->entities[i]; l->src[l->n] = ecs_field_src(it, 0);
        l->n ++;
    }
}

static int count(const Log *l, ecs_entity_t e, ecs_entity_t src) {
    int n = 0;
    for (int i = 0; i < l->n; i ++) {
        if (l->e[i] == e && (!src || l->src[i] == src)) n ++;
    }
    return n;
}

int main(void) {
    ecs_world_t *world = ecs_mini();
    ECS_COMPONENT(world, Defense);
    ECS_COMPONENT(world, Armor);
    ECS_COMPONENT(world, Mass);
    ecs_add_id(world, ecs_id(Defense), EcsDontFragment);
    ecs_add_pair(world, ecs_id(Defense), EcsOnInstantiate, EcsInherit);
    ecs_add_id(world, ecs_id(Armor), EcsDontFragment);
    ecs_add_pair(world, ecs_id(Armor), EcsOnInstantiate, EcsDontInherit);
    ecs_add_id(world, ecs_id(Mass), EcsDontFragment);

    ecs_entity_t base = ecs_new_w_id(world, EcsPrefab);
    ecs_set(world, base, Defense, {50});
    ecs_set(world, base, Armor, {5});
    ecs_entity_t inst = ecs_new(world);
    ecs_entity_t j = ecs_new_w_pair(world, EcsIsA, inst);
    ecs_entity_t own = ecs_new(world);
    ecs_set(world, own, Defense, {7});
    ecs_entity_t inst2 = ecs_new_w_pair(world, EcsIsA, base);
    ecs_entity_t gp = ecs_new(world);
    ecs_set(world, gp, Mass, {1});
    ecs_entity_t p = ecs_new_w_pair(world, EcsChildOf, gp);

    Log add = {0}, rem = {0}, add_up = {0}, add_m = {0}, add_a = {0};
    ecs_observer(world, { .query.terms = {{ ecs_id(Defense) }},
        .events = { EcsOnAdd }, .callback = on_event, .ctx = &add });
    ecs_observer(world, { .query.terms = {{ ecs_id(Defense) }},
        .events = { EcsOnRemove }, .callback = on_event, .ctx = &rem });
    ecs_observer(world, { .query.terms = {{ ecs_id(Defense), .src.id = EcsUp,
        .trav = EcsIsA }}, .events = { EcsOnAdd }, .callback = on_event,
        .ctx = &add_up });
    ecs_observer(world, { .query.terms = {{ ecs_id(Mass), .src.id = EcsUp }},
        .events = { EcsOnAdd }, .callback = on_event, .ctx = &add_m });
    ecs_observer(world, { .query.terms = {{ ecs_id(Armor) }},
        .events = { EcsOnAdd }, .callback = on_event, .ctx = &add_a });

    ecs_add_pair(world, inst, EcsIsA, base);
    int a_add = count(&add, inst, base), a_add_j = count(&add, j, base);
    ecs_remove_pair(world, inst, EcsIsA, base);
    int a_rem = count(&rem, inst, base), a_rem_j = count(&rem, j, base);

    ecs_add_pair(world, own, EcsIsA, base);
    int b_self = count(&add, own, 0), b_up = count(&add_up, own, base);

    ecs_entity_t ch = ecs_new_w_pair(world, EcsChildOf, p);
    int c_m = count(&add_m, ch, gp);

    int d_a = count(&add_a, inst, 0) + count(&add_a, own, 0);

    ecs_delete(world, inst2);
    int e_rem = count(&rem, inst2, base);

    printf("(a) inst OnAdd %d OnRemove %d, j OnAdd %d OnRemove %d; (b) own "
        "self|up %d, up-only %d; (c) ch Mass(up) from gp %d; (d) Armor "
        "forwarded %d; (e) deleted inst2 OnRemove %d\n", a_add, a_rem,
        a_add_j, a_rem_j, b_self, b_up, c_m, d_a, e_rem);
    int ok = a_add == 1 && a_rem == 1 && a_add_j == 1 && a_rem_j == 1 &&
        b_self == 0 && b_up == 1 && c_m == 1 && d_a == 0 && e_rem == 1;
    printf(ok ? "OK\n" : "FAIL\n");
    ecs_fini(world);
    return ok ? 0 : 1;
}
