/* F49 check: OnAdd and OnRemove through IsA name the entities' source, once,
 * for table, Sparse and DontFragment storage.
 *   (a) inst IsA b1, IsA b2 (b1 provides C first), c IsA inst:
 *       C set on and removed from b2: no event for inst or c
 *   (b) diamond d IsA b4, IsA v; v IsA b4: C removed from b4: one OnRemove
 *       for d, from b4
 *   (c) inst_f IsA b1; k ChildOf inst_f: (IsA, b3) added to and removed from
 *       inst_f (b3 provides C, after b1): no OnAdd or OnRemove C(up ChildOf)
 *       for k from b3
 *   (d) control: e IsA b5 alone, c5 IsA e: C set on b5: one OnAdd for e and
 *       one for c5, from b5
 *   (e) up-only (IsA) observers get an event for every base that provides
 *       C, once (flecs's Observer_propagate_isa_add_to_second_base): in (a)
 *       one OnAdd and one OnRemove for inst from b2, in (b) one OnRemove for
 *       d from b4 */
#include "flecs.h"
#include <stdio.h>

typedef struct { int v; } C;

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

static int run(int storage) {
    ecs_world_t *world = ecs_mini();
    ECS_COMPONENT(world, C);
    if (storage == 1) ecs_add_id(world, ecs_id(C), EcsSparse);
    if (storage == 2) ecs_add_id(world, ecs_id(C), EcsDontFragment);
    ecs_add_pair(world, ecs_id(C), EcsOnInstantiate, EcsInherit);

    ecs_entity_t b1 = ecs_new_w_id(world, EcsPrefab);
    ecs_entity_t b2 = ecs_new_w_id(world, EcsPrefab);
    ecs_entity_t b3 = ecs_new_w_id(world, EcsPrefab);
    ecs_entity_t b4 = ecs_new_w_id(world, EcsPrefab);
    ecs_entity_t b5 = ecs_new_w_id(world, EcsPrefab);
    ecs_set(world, b1, C, {1});
    ecs_set(world, b3, C, {3});
    ecs_set(world, b4, C, {4});

    ecs_entity_t inst = ecs_new_w_pair(world, EcsIsA, b1);
    ecs_add_pair(world, inst, EcsIsA, b2);
    ecs_entity_t c = ecs_new_w_pair(world, EcsIsA, inst);
    ecs_entity_t v = ecs_new_w_pair(world, EcsIsA, b4);
    ecs_entity_t d = ecs_new_w_pair(world, EcsIsA, b4);
    ecs_add_pair(world, d, EcsIsA, v);
    ecs_entity_t inst_f = ecs_new_w_pair(world, EcsIsA, b1);
    ecs_entity_t k = ecs_new_w_pair(world, EcsChildOf, inst_f);
    ecs_entity_t e = ecs_new_w_pair(world, EcsIsA, b5);
    ecs_entity_t c5 = ecs_new_w_pair(world, EcsIsA, e);

    Log add = {0}, rem = {0}, add_up = {0}, rem_up = {0}, up = {0};
    ecs_observer(world, { .query.terms = {{ ecs_id(C), .src.id = EcsUp,
        .trav = EcsIsA }}, .events = { EcsOnAdd, EcsOnRemove },
        .callback = on_event, .ctx = &up });
    ecs_observer(world, { .query.terms = {{ ecs_id(C) }},
        .events = { EcsOnAdd }, .callback = on_event, .ctx = &add });
    ecs_observer(world, { .query.terms = {{ ecs_id(C) }},
        .events = { EcsOnRemove }, .callback = on_event, .ctx = &rem });
    ecs_observer(world, { .query.terms = {{ ecs_id(C), .src.id = EcsUp,
        .trav = EcsChildOf }}, .events = { EcsOnAdd }, .callback = on_event,
        .ctx = &add_up });
    ecs_observer(world, { .query.terms = {{ ecs_id(C), .src.id = EcsUp,
        .trav = EcsChildOf }}, .events = { EcsOnRemove },
        .callback = on_event, .ctx = &rem_up });

    ecs_set(world, b2, C, {2});
    ecs_remove(world, b2, C);
    int a = count(&add, inst, 0) + count(&rem, inst, 0) +
        count(&add, c, 0) + count(&rem, c, 0);
    int ea = count(&up, inst, b2);

    ecs_remove(world, b4, C);
    int bd = count(&rem, d, b4);
    int ed = count(&up, d, b4);

    ecs_add_pair(world, inst_f, EcsIsA, b3);
    ecs_remove_pair(world, inst_f, EcsIsA, b3);
    int ck = count(&add_up, k, b3) + count(&rem_up, k, b3);

    ecs_set(world, b5, C, {5});
    int de = count(&add, e, b5), dc5 = count(&add, c5, b5);

    printf("storage %d: (a) events for inst and c %d; (b) OnRemove for d "
        "%d; (c) C(up) events for k from b3 %d; (d) control e %d c5 %d; "
        "(e) up-only: inst from b2 %d, d from b4 %d\n",
        storage, a, bd, ck, de, dc5, ea, ed);
    ecs_fini(world);
    if (de != 1 || dc5 != 1) return 2;
    return (a == 0 && bd == 1 && ck == 0 && ea == 2 && ed == 1) ? 0 : 1;
}

int main(void) {
    int rc = 0;
    for (int s = 0; s < 3; s ++) {
        int r = run(s);
        if (r == 2) { printf("INCONCLUSIVE: the control failed\n"); return 2; }
        rc |= r;
    }
    printf(rc ? "FAIL\n" : "OK\n");
    return rc;
}
