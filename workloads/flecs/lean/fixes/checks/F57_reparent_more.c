/* F57 check: re-parenting a Parent-storage child.
 *   (a) deferred: ecs_set(stage, e, EcsParent, {p2}) in readonly mode, merged:
 *       one OnRemove Tag(up) for e, source p1, and one OnRemove (ChildOf, p1)
 *   (b) both parents have Tag: OnRemove Tag(up) from p1, then OnAdd from p3,
 *       the order of a ChildOf re-parent (control: the same with ChildOf)
 *   (c) setting the parent the child already has: no OnRemove (v4.2.0 emits
 *       the OnSet as an OnAdd of (ChildOf, p3) again; the check prints it)
 *   (d) a parent at another depth: the events of (b), and the child's depth
 *       follows (ecs_get_parent chain) */
#include "flecs.h"
#include <stdio.h>

typedef struct { int n; ecs_entity_t e[32], src[32]; ecs_entity_t ev[32]; } Log;

static void on_event(ecs_iter_t *it) {
    Log *l = it->ctx;
    for (int i = 0; i < it->count && l->n < 32; i ++) {
        l->e[l->n] = it->entities[i]; l->src[l->n] = ecs_field_src(it, 0);
        l->ev[l->n] = it->event; l->n ++;
    }
}

int main(void) {
    ecs_world_t *world = ecs_mini();
    ECS_TAG(world, Tag);
    ecs_entity_t p1 = ecs_new_w_id(world, Tag);
    ecs_entity_t p2 = ecs_new(world);
    ecs_entity_t p3 = ecs_new_w_id(world, Tag);
    ecs_entity_t deep = ecs_new_w_parent(world, ecs_new_w_parent(world,
        ecs_new_w_id(world, Tag), NULL), NULL);
    ecs_add(world, deep, Tag);

    Log tl = {0}, pl = {0};
    ecs_observer(world, { .query.terms = {{ Tag, .src.id = EcsUp }},
        .events = { EcsOnAdd, EcsOnRemove }, .callback = on_event,
        .ctx = &tl });
    ecs_observer(world, { .query.terms = {{ ecs_pair(EcsChildOf,
        EcsWildcard) }}, .events = { EcsOnRemove }, .callback = on_event,
        .ctx = &pl });

    /* (a) */
    ecs_entity_t e = ecs_new_w_parent(world, p1, NULL);
    tl.n = pl.n = 0;
    ecs_world_t *stage = ecs_get_stage(world, 0);
    ecs_readonly_begin(world, false);
    ecs_set(stage, e, EcsParent, {p2});
    ecs_readonly_end(world);
    int a_ok = tl.n == 1 && tl.ev[0] == EcsOnRemove && tl.src[0] == p1 &&
        pl.n == 1 && ecs_get_parent(world, e) == p2;

    /* (b) */
    ecs_entity_t f = ecs_new_w_parent(world, p1, NULL);
    tl.n = pl.n = 0;
    ecs_set(world, f, EcsParent, {p3});
    int b_ok = tl.n == 2 && tl.ev[0] == EcsOnRemove && tl.src[0] == p1 &&
        tl.ev[1] == EcsOnAdd && tl.src[1] == p3 && pl.n == 1;
    ecs_entity_t g = ecs_new_w_pair(world, EcsChildOf, p1);
    tl.n = pl.n = 0;
    ecs_add_pair(world, g, EcsChildOf, p3);
    int b_ctl = tl.n == 2 && tl.ev[0] == EcsOnRemove && tl.ev[1] == EcsOnAdd;

    /* (c) */
    tl.n = pl.n = 0;
    ecs_set(world, f, EcsParent, {p3});
    int c_rem = 0;
    for (int i = 0; i < tl.n; i ++) c_rem += tl.ev[i] == EcsOnRemove;
    int c_ok = c_rem == 0 && pl.n == 0;
    printf("(c) same parent: %d OnAdd Tag(up) events\n", tl.n - c_rem);

    /* (d) */
    tl.n = pl.n = 0;
    ecs_set(world, f, EcsParent, {deep});
    int d_ok = tl.n == 2 && tl.ev[0] == EcsOnRemove && tl.src[0] == p3 &&
        tl.ev[1] == EcsOnAdd && tl.src[1] == deep && pl.n == 1 &&
        ecs_get_parent(world, f) == deep;

    printf("(a) deferred %d; (b) remove then add %d (ChildOf control %d); "
        "(c) same parent %d; (d) other depth %d\n", a_ok, b_ok, b_ctl, c_ok,
        d_ok);
    ecs_fini(world);
    if (!b_ctl) { printf("INCONCLUSIVE: control\n"); return 2; }
    int ok = a_ok && b_ok && c_ok && d_ok;
    printf(ok ? "OK\n" : "FAIL\n");
    return ok ? 0 : 1;
}
