/* F51 check: the OnSet of an inheritance change reaches the inheritors at
 * every depth and through ChildOf, once, with the base as source. The
 * inheritors that get the component from another base first (other, other2)
 * get no OnSet only with F43's patch too (an OnSet through a base that isn't
 * the source is F43's finding); the check prints their count.
 *   Position: table, Inherit
 *   (a) variant (no base yet): inst IsA variant, deep IsA inst,
 *       other IsA b0 (b0 provides {9, 9}), IsA variant; kid ChildOf variant
 *       ecs_add_pair(variant, IsA, base): one OnSet from base for inst, deep
 *       and kid (Position(up ChildOf)); none for other
 *   (b) variant2 IsA base, owns {5, 5}: inst2 IsA variant2, deep2 IsA inst2,
 *       other2 IsA b0, IsA variant2
 *       ecs_remove(variant2, Position): one OnSet from base for inst2 and
 *       deep2; none for other2 */
#include "flecs.h"
#include <stdio.h>

typedef struct { float x, y; } Position;

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
    ECS_COMPONENT(world, Position);
    ecs_add_pair(world, ecs_id(Position), EcsOnInstantiate, EcsInherit);

    ecs_entity_t b0 = ecs_new_w_id(world, EcsPrefab);
    ecs_set(world, b0, Position, {9, 9});
    ecs_entity_t base = ecs_new_w_id(world, EcsPrefab);
    ecs_set(world, base, Position, {1, 2});

    ecs_entity_t variant = ecs_new(world); /* not a prefab: kid isn't one */
    ecs_entity_t inst = ecs_new_w_pair(world, EcsIsA, variant);
    ecs_entity_t deep = ecs_new_w_pair(world, EcsIsA, inst);
    ecs_entity_t other = ecs_new_w_pair(world, EcsIsA, b0);
    ecs_add_pair(world, other, EcsIsA, variant);
    ecs_entity_t kid = ecs_new_w_pair(world, EcsChildOf, variant);

    ecs_entity_t variant2 = ecs_new_w_id(world, EcsPrefab);
    ecs_add_pair(world, variant2, EcsIsA, base);
    ecs_set(world, variant2, Position, {5, 5});
    ecs_entity_t inst2 = ecs_new_w_pair(world, EcsIsA, variant2);
    ecs_entity_t deep2 = ecs_new_w_pair(world, EcsIsA, inst2);
    ecs_entity_t other2 = ecs_new_w_pair(world, EcsIsA, b0);
    ecs_add_pair(world, other2, EcsIsA, variant2);

    Log set = {0}, set_up = {0};
    ecs_observer(world, { .query.terms = {{ ecs_id(Position) }},
        .events = { EcsOnSet }, .callback = on_event, .ctx = &set });
    ecs_observer(world, { .query.terms = {{ ecs_id(Position),
        .src.id = EcsUp, .trav = EcsChildOf }}, .events = { EcsOnSet },
        .callback = on_event, .ctx = &set_up });

    ecs_add_pair(world, variant, EcsIsA, base);
    int a_inst = count(&set, inst, base), a_deep = count(&set, deep, base);
    int a_kid = count(&set_up, kid, 0), a_other = count(&set, other, 0);

    ecs_remove(world, variant2, Position);
    int b_inst = count(&set, inst2, base), b_deep = count(&set, deep2, base);
    int b_other = count(&set, other2, 0);

    const Position *pd = ecs_get(world, deep2, Position);
    const Position *po = ecs_get(world, other2, Position);
    printf("(a) OnSet from base: inst %d, deep %d; kid (up ChildOf) %d; "
        "other %d\n(b) OnSet from base: inst2 %d, deep2 %d; other2 %d "
        "(deep2 reads %g, other2 reads %g)\n", a_inst, a_deep, a_kid,
        a_other, b_inst, b_deep, b_other, pd ? pd->x : -1, po ? po->x : -1);
    int ok = a_inst == 1 && a_deep == 1 && a_kid == 1 &&
        b_inst == 1 && b_deep == 1;
    if (a_other || b_other) {
        printf("note: other and other2 got an OnSet through a base that "
            "isn't their source (F43)\n");
    }
    printf(ok ? "OK\n" : "FAIL\n");
    ecs_fini(world);
    return ok ? 0 : 1;
}
