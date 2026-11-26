/* Prediction F57: re-parenting a child with Parent storage (ecs_set of
 * EcsParent to another parent) delivers no OnRemove: not for the
 * (ChildOf, old parent) pair, and not for the old parent's components that
 * the child (and its own children) no longer reach through up traversal.
 * The same re-parenting with ChildOf storage delivers both (flecs's own
 * Observer_propagate_reparent_from_owned_to_empty_parent).
 *
 *   Tag; p1 has Tag, p2 has nothing (both roots, same depth)
 *   observers: Tag(up) for OnAdd and OnRemove; (ChildOf, *) for OnRemove
 *   control: c = ecs_new_w_pair(EcsChildOf, p1);
 *            ecs_add_pair(world, c, EcsChildOf, p2)
 *            -> OnRemove Tag (c, source p1); OnRemove (ChildOf, p1) for c
 *   control: d = ecs_new_w_parent(p1); ecs_remove(world, d, EcsParent)
 *            -> OnRemove Tag (d, source p1); OnRemove (ChildOf, p1) for d
 *   prediction: e = ecs_new_w_parent(p1); g = ecs_new_w_parent(e);
 *            ecs_set(world, e, EcsParent, {p2})
 *            -> nothing: e and g lose Tag(up) without OnRemove
 *
 * The Parent component's OnSet is re-emitted as the OnAdd of
 * (ChildOf, parent) (observable.c 1160-1183: pdesc.event = event ==
 * EcsOnSet ? EcsOnAdd : event), and its OnRemove as the OnRemove of
 * (ChildOf, parent); the forward of that pair delivers the parent's
 * components (flecs_emit_forward, 799-888). Setting the component again to
 * another parent runs the on_replace hook (flecs_on_replace_parent,
 * storage/non_fragmenting_childof.c 113-197: the old parent's ordered
 * children, the name index, the depth) and then the OnSet: the OnAdd of
 * (ChildOf, p2) and its forward (p2 has no Tag: nothing). No code path
 * emits the OnRemove of (ChildOf, p1) or forwards p1's Tag as removed.
 *
 * Documented: ObserversManual.md "OnRemove Events", "Event Forwarding"
 * ("adding a pair results in forwarded OnAdd events, and removing a pair
 * results in forwarded OnRemove events"); HierarchiesManual.md
 * ("Relationship traversal works for both storages (Position(up) ...)",
 * "Queries with ChildOf terms work with both storages"). flecs's own
 * Observer_on_add_childof_wildcard_w_parent_component expects the OnAdd of
 * (ChildOf, p2) after such a re-parent. main returns 0 when the prediction
 * gets the OnRemove events. */
#include "flecs.h"
#include <stdio.h>
#include <stdlib.h>

typedef struct {
    int count;
    ecs_entity_t event[16], entity[16], source[16];
} Log;

static void log_up(ecs_iter_t *it) {
    Log *l = it->ctx;
    for (int i = 0; i < it->count && l->count < 16; i ++) {
        l->event[l->count] = it->event;
        l->entity[l->count] = it->entities[i];
        l->source[l->count] = ecs_field_src(it, 0);
        l->count ++;
    }
}

static void log_pair(ecs_iter_t *it) {
    Log *l = it->ctx;
    for (int i = 0; i < it->count && l->count < 16; i ++) {
        l->event[l->count] = it->event;
        l->entity[l->count] = it->entities[i];
        l->source[l->count] = ecs_pair_second(it->world, ecs_field_id(it, 0));
        l->count ++;
    }
}

static int has(const Log *l, ecs_entity_t ev, ecs_entity_t e, ecs_entity_t s) {
    for (int i = 0; i < l->count; i ++) {
        if (l->event[i] == ev && l->entity[i] == e && l->source[i] == s) {
            return 1;
        }
    }
    return 0;
}

int main(void) {
    ecs_world_t *world = ecs_mini();
    ECS_TAG(world, Tag);

    ecs_entity_t p1 = ecs_new(world);
    ecs_add(world, p1, Tag);
    ecs_entity_t p2 = ecs_new(world);

    ecs_entity_t c = ecs_new_w_pair(world, EcsChildOf, p1);
    ecs_entity_t d = ecs_new_w_parent(world, p1, NULL);
    ecs_entity_t e = ecs_new_w_parent(world, p1, NULL);
    ecs_entity_t g = ecs_new_w_parent(world, e, NULL);

    Log up = {0}, pair = {0};
    ecs_observer(world, {
        .query.terms = {{ Tag, .src.id = EcsUp }},
        .events = { EcsOnAdd, EcsOnRemove },
        .callback = log_up,
        .ctx = &up
    });
    ecs_observer(world, {
        .query.terms = {{ ecs_pair(EcsChildOf, EcsWildcard) }},
        .events = { EcsOnRemove },
        .callback = log_pair,
        .ctx = &pair
    });

    /* control: ChildOf storage */
    ecs_add_pair(world, c, EcsChildOf, p2);
    int c_up = has(&up, EcsOnRemove, c, p1);
    int c_pair = has(&pair, EcsOnRemove, c, p1);

    /* control: Parent storage, the component removed */
    ecs_remove(world, d, EcsParent);
    int d_up = has(&up, EcsOnRemove, d, p1);
    int d_pair = has(&pair, EcsOnRemove, d, p1);

    printf("controls: ChildOf re-parent: OnRemove Tag(up) %d, OnRemove "
        "(ChildOf, p1) %d; Parent removed: OnRemove Tag(up) %d, OnRemove "
        "(ChildOf, p1) %d\n", c_up, c_pair, d_up, d_pair);
    if (!d_up) {
        printf("NOTE: removing the Parent component did not deliver the "
            "OnRemove either (the model predicts it does)\n");
    }
    if (!c_up) {
        printf("INCONCLUSIVE: the ChildOf control did not get its OnRemove\n");
        ecs_fini(world);
        return 2;
    }

    up.count = 0;
    pair.count = 0;
    ecs_set(world, e, EcsParent, {p2});
    int ok_parent = ecs_get_parent(world, e) == p2;
    int e_up = has(&up, EcsOnRemove, e, p1);
    int g_up = has(&up, EcsOnRemove, g, p1);
    int e_pair = has(&pair, EcsOnRemove, e, p1);
    printf("prediction: e re-parented to p2: %d; OnRemove Tag(up) for e %d, "
        "for its child g %d; OnRemove (ChildOf, p1) for e %d; events seen "
        "%d\n", ok_parent, e_up, g_up, e_pair, up.count + pair.count);
    int failed = 0;
    if (!ok_parent) {
        printf("INCONCLUSIVE: the parent did not change\n");
        failed = 2;
    } else if (!e_up || !g_up) {
        printf("FAIL: e%s lost Tag(up) from p1 without an OnRemove\n",
            !g_up ? " and its child g" : "");
        failed = 1;
    } else if (c_pair && !e_pair) {
        printf("FAIL: no OnRemove for (ChildOf, p1), which the ChildOf "
            "storage delivers\n");
        failed = 1;
    }
    ecs_fini(world);
    return failed;
}
