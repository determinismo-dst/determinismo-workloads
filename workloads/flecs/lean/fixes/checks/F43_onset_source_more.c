/* Check for F43 (and F41/F42 where the storage is Sparse or DontFragment),
 * beyond the finding's test. For each storage (table, Sparse, DontFragment),
 * all with (OnInstantiate, Inherit), and an OnSet observer (self|up):
 *   1. diamond: e1 IsA e0; e2 IsA e0 and IsA e1; set e0: one event for e2,
 *      source e0 (also with e1 created before e0, so (IsA, e1) comes first
 *      in e2's type);
 *   2. inst IsA b1, then IsA b2 (b1 < b2): setting b2 gives inst no event,
 *      setting b1 gives one, source b1;
 *   3. a chain: c IsA inst (from 2): setting b1 gives c one event, setting
 *      b2 none.
 * Bases and instances are not prefabs (observers skip prefabs).
 * The expected counts are those of ObserversManual.md "Adding an IsA pair"
 * (primary source) and "Setting an Inherited Component". main returns 0 when
 * every count matches. */
#include "flecs.h"
#include <stdio.h>

typedef struct { int value; } C;

typedef struct {
    ecs_entity_t entity[64];
    ecs_entity_t source[64];
    int count;
} Log;

static void on_set(ecs_iter_t *it) {
    Log *log = it->ctx;
    for (int i = 0; i < it->count; i ++) {
        if (log->count < 64) {
            log->entity[log->count] = it->entities[i];
            log->source[log->count] = ecs_field_src(it, 0);
            log->count ++;
        }
    }
}

static int events(const Log *log, int from, ecs_entity_t e, ecs_entity_t src) {
    int n = 0;
    for (int i = from; i < log->count; i ++) {
        if (log->entity[i] == e && (!src || log->source[i] == src)) n ++;
    }
    return n;
}

static const char *names[] = { "table", "Sparse", "DontFragment" };

static int run(int storage, int reversed) {
    ecs_world_t *world = ecs_mini();
    ECS_COMPONENT(world, C);
    if (storage == 1) ecs_add_id(world, ecs_id(C), EcsSparse);
    if (storage == 2) ecs_add_id(world, ecs_id(C), EcsDontFragment);
    ecs_add_pair(world, ecs_id(C), EcsOnInstantiate, EcsInherit);

    Log log = {0};
    ecs_observer(world, { .query.terms = {{ ecs_id(C) }},
        .events = { EcsOnSet }, .callback = on_set, .ctx = &log });

    int failed = 0, m;

    /* 1 */
    ecs_entity_t first = ecs_new(world);
    ecs_entity_t second = ecs_new(world);
    ecs_entity_t e0 = reversed ? second : first, e1 = reversed ? first : second;
    ecs_set(world, e0, C, {1});
    ecs_add_pair(world, e1, EcsIsA, e0);
    ecs_entity_t e2 = ecs_new(world);
    ecs_add_pair(world, e2, EcsIsA, e0);
    ecs_add_pair(world, e2, EcsIsA, e1);
    m = log.count;
    ecs_set(world, e0, C, {2});
    int d = events(&log, m, e2, 0), ds = events(&log, m, e2, e0);
    printf("%s%s 1. diamond: %d event(s) for e2, %d from e0\n", names[storage],
        reversed ? " (e1 < e0)" : "", d, ds);
    if (d != 1 || ds != 1) failed = 1;

    /* 2 */
    ecs_entity_t b1 = ecs_new_w_id(world, EcsPrefab);
    ecs_entity_t b2 = ecs_new_w_id(world, EcsPrefab);
    ecs_set(world, b1, C, {10});
    ecs_set(world, b2, C, {20});
    ecs_entity_t inst = ecs_new(world);
    ecs_add_pair(world, inst, EcsIsA, b1);
    ecs_add_pair(world, inst, EcsIsA, b2);
    ecs_entity_t c = ecs_new_w_pair(world, EcsIsA, inst);
    m = log.count;
    ecs_set(world, b2, C, {21});
    int s2 = events(&log, m, inst, 0), c2 = events(&log, m, c, 0);
    m = log.count;
    ecs_set(world, b1, C, {11});
    int s1 = events(&log, m, inst, b1), c1 = events(&log, m, c, b1);
    const C *v = ecs_get(world, c, C);
    printf("%s%s 2. set b2: %d for inst, %d for c; set b1: %d for inst, %d "
        "for c (c's value %d)\n", names[storage], reversed ? " (e1 < e0)" : "",
        s2, c2, s1, c1, v ? v->value : -1);
    if (s2 != 0 || c2 != 0 || s1 != 1 || c1 != 1 || !v || v->value != 11) {
        failed = 1;
    }

    ecs_fini(world);
    return failed;
}

int main(void) {
    int failed = 0;
    for (int s = 0; s < 3; s ++) {
        for (int r = 0; r < 2; r ++) {
            failed |= run(s, r);
        }
    }
    printf(failed ? "FAIL\n" : "OK\n");
    return failed;
}
