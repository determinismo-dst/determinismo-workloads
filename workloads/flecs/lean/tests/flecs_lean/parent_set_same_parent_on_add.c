/* Prediction F62: setting the Parent component of a child to the parent it
 * already has (or calling ecs_modified on it) delivers the OnAdd of
 * (ChildOf, parent) again, and forwards the parent's components as OnAdd
 * again, to the child and to its own children.
 *
 *   Tag; p has Tag; e = ecs_new_w_parent(p); g = ecs_new_w_parent(e)
 *   observers: (ChildOf, *) OnAdd; Tag(up) OnAdd
 *   prediction: ecs_set(world, e, EcsParent, {p})
 *     -> OnAdd (ChildOf, p) for e, OnAdd Tag for e and for g (source p)
 *   prediction: ecs_modified(world, e, EcsParent) -> the same
 *   control: c = ecs_new_w_pair(EcsChildOf, p);
 *            ecs_add_pair(world, c, EcsChildOf, p) -> nothing
 *
 * Code path (flecs v4.2.0): ecs_set_id (entity.c 1986-2031) calls
 * flecs_copy_id (810-834): the on_replace hook flecs_on_replace_parent
 * (storage/non_fragmenting_childof.c 113-197) returns for an unchanged
 * parent (138-144: "Setting the parent a child already has is a no-op"),
 * then flecs_notify_on_set emits OnSet (838-839; the table has OnSet
 * observers for EcsParent because a (ChildOf, *) OnAdd observer counts as
 * one, observer.c 151-157). flecs_emit re-emits the Parent component's
 * OnSet as the OnAdd of (ChildOf, parent) (observable.c 1160-1183), whose
 * forward delivers the parent's components (799-888).
 *
 * Documented: ObserversManual.md "OnAdd Events": "An event only fires when
 * the component is actually added to the entity, so not on each add
 * operation"; HierarchiesManual.md: "Relationship traversal works for both
 * storages". main returns 0 when no OnAdd is delivered. */
#include "flecs.h"
#include <stdio.h>
#include <stdlib.h>

typedef struct {
    int count;
    ecs_entity_t entity[32], source[32];
} Log;

static void log_up(ecs_iter_t *it) {
    Log *l = it->ctx;
    for (int i = 0; i < it->count && l->count < 32; i ++) {
        l->entity[l->count] = it->entities[i];
        l->source[l->count] = ecs_field_src(it, 0);
        l->count ++;
    }
}

static void log_pair(ecs_iter_t *it) {
    Log *l = it->ctx;
    for (int i = 0; i < it->count && l->count < 32; i ++) {
        l->entity[l->count] = it->entities[i];
        l->source[l->count] = ecs_pair_second(it->world, ecs_field_id(it, 0));
        l->count ++;
    }
}

int main(void) {
    ecs_world_t *world = ecs_mini();
    ECS_TAG(world, Tag);

    ecs_entity_t p = ecs_new(world);
    ecs_add(world, p, Tag);
    ecs_entity_t c = ecs_new_w_pair(world, EcsChildOf, p);
    ecs_entity_t e = ecs_new_w_parent(world, p, NULL);
    ecs_entity_t g = ecs_new_w_parent(world, e, NULL);

    Log up = {0}, pair = {0};
    ecs_observer(world, {
        .query.terms = {{ Tag, .src.id = EcsUp }},
        .events = { EcsOnAdd },
        .callback = log_up,
        .ctx = &up
    });
    ecs_observer(world, {
        .query.terms = {{ ecs_pair(EcsChildOf, EcsWildcard) }},
        .events = { EcsOnAdd },
        .callback = log_pair,
        .ctx = &pair
    });

    /* control: ChildOf storage, the pair added again */
    ecs_add_pair(world, c, EcsChildOf, p);
    printf("control: ecs_add_pair(c, ChildOf, p) again: %d OnAdd Tag(up), "
        "%d OnAdd (ChildOf, *)\n", up.count, pair.count);
    if (up.count || pair.count) {
        printf("INCONCLUSIVE: the ChildOf control delivered OnAdd\n");
        ecs_fini(world);
        return 2;
    }

    int failed = 0;

    ecs_set(world, e, EcsParent, {p});
    printf("prediction: ecs_set(e, EcsParent, {p}) again (parent %s): %d "
        "OnAdd Tag(up), %d OnAdd (ChildOf, *)\n",
        ecs_get_parent(world, e) == p ? "unchanged" : "CHANGED",
        up.count, pair.count);
    for (int i = 0; i < up.count; i ++) {
        printf("  OnAdd Tag(up): entity %s, source %s\n",
            up.entity[i] == e ? "e" : up.entity[i] == g ? "g" : "other",
            up.source[i] == p ? "p" : "other");
    }
    for (int i = 0; i < pair.count; i ++) {
        printf("  OnAdd (ChildOf, *): entity %s, parent %s\n",
            pair.entity[i] == e ? "e" : "other",
            pair.source[i] == p ? "p" : "other");
    }
    if (up.count || pair.count) {
        printf("FAIL: OnAdd for a parent and a component the entity "
            "already had\n");
        failed = 1;
    }

    up.count = 0;
    pair.count = 0;
    ecs_modified(world, e, EcsParent);
    printf("prediction: ecs_modified(e, EcsParent): %d OnAdd Tag(up), %d "
        "OnAdd (ChildOf, *)\n", up.count, pair.count);
    if (up.count || pair.count) {
        printf("FAIL: ecs_modified delivered OnAdd\n");
        failed = 1;
    }

    ecs_fini(world);
    return failed;
}
