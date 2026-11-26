/* F53 check: ecs_iter_changed and ecs_iter_skip on the worker iterators of
 * multithreaded systems give the single-threaded results, frame by frame.
 *
 *   4 worker threads; every table has 40 entities, so every worker gets rows
 *   S1 [in] Position, 3 tables: skips unchanged results
 *   S2 [in] Velocity, 1 table: skips every result in frames 1-2, then only
 *      unchanged ones (its table must stay changed while it skips)
 *   S3 [inout] Mass, 1 table: writes its rows when changed (its own writes
 *      must not be reported as changes)
 *   frame 1: everything new; frame 2: nothing written;
 *   before frame 3: one Position of table B set; frame 4: nothing written.
 * Expected per frame, as (worker, table) results reported changed:
 *   S1: 12, 0, 4, 0;  S2: 4, 4, 4, 0;  S3: 4, 0, 0, 0.
 * The same counts divided by 4 hold with no threads (the control). */
#include "flecs.h"
#include <stdio.h>
#include <stdlib.h>

typedef struct { float x, y; } Position;
typedef struct { float x, y; } Velocity;
typedef struct { float value; } Mass;

static int s1, s2, s3, s2_skip_all;

static void S1(ecs_iter_t *it) {
    if (!ecs_iter_changed(it)) { ecs_iter_skip(it); return; }
    __atomic_add_fetch(&s1, 1, __ATOMIC_SEQ_CST);
}

static void S2(ecs_iter_t *it) {
    if (ecs_iter_changed(it)) {
        __atomic_add_fetch(&s2, 1, __ATOMIC_SEQ_CST);
        if (s2_skip_all) ecs_iter_skip(it);
    } else {
        ecs_iter_skip(it);
    }
}

static void S3(ecs_iter_t *it) {
    if (!ecs_iter_changed(it)) { ecs_iter_skip(it); return; }
    __atomic_add_fetch(&s3, 1, __ATOMIC_SEQ_CST);
    Mass *m = ecs_field(it, Mass, 0);
    for (int i = 0; i < it->count; i ++) m[i].value += 1;
}

static ecs_entity_t sys_entity(ecs_world_t *world, const char *name) {
    ecs_entity_t e = ecs_entity(world, { .name = name });
    ecs_add_pair(world, e, EcsDependsOn, EcsOnUpdate);
    return e;
}

static int run(int threads, int out[3][4]) {
    ecs_world_t *world = ecs_mini();
    ECS_IMPORT(world, FlecsPipeline);
    ECS_COMPONENT(world, Position);
    ECS_COMPONENT(world, Velocity);
    ECS_COMPONENT(world, Mass);
    ECS_TAG(world, TagB);
    ECS_TAG(world, TagC);

    ecs_system(world, { .entity = sys_entity(world, "S1"),
        .query.terms = {{ ecs_id(Position), .inout = EcsIn }},
        .query.flags = EcsQueryDetectChanges, .callback = S1,
        .multi_threaded = true });
    ecs_system(world, { .entity = sys_entity(world, "S2"),
        .query.terms = {{ ecs_id(Velocity), .inout = EcsIn }},
        .query.flags = EcsQueryDetectChanges, .callback = S2,
        .multi_threaded = true });
    ecs_system(world, { .entity = sys_entity(world, "S3"),
        .query.terms = {{ ecs_id(Mass), .inout = EcsInOut }},
        .query.flags = EcsQueryDetectChanges, .callback = S3,
        .multi_threaded = true });

    ecs_entity_t in_b = 0;
    for (int i = 0; i < 40; i ++) {
        ecs_insert(world, ecs_value(Position, {1, 1}));
        ecs_entity_t b = ecs_insert(world, ecs_value(Position, {1, 1}));
        ecs_add(world, b, TagB);
        if (!in_b) in_b = b;
        ecs_entity_t c = ecs_insert(world, ecs_value(Position, {1, 1}));
        ecs_add(world, c, TagC);
        ecs_insert(world, ecs_value(Velocity, {1, 1}));
        ecs_insert(world, ecs_value(Mass, {1}));
    }

    if (threads) ecs_set_threads(world, threads);
    s2_skip_all = 1;
    for (int f = 0; f < 4; f ++) {
        s1 = s2 = s3 = 0;
        if (f == 2) {
            s2_skip_all = 0;
            ecs_set(world, in_b, Position, {2, 2});
        }
        ecs_progress(world, 0);
        out[0][f] = s1; out[1][f] = s2; out[2][f] = s3;
    }
    if (threads) ecs_set_threads(world, 0);
    ecs_fini(world);
    return 0;
}

int main(void) {
    ecs_set_os_api_impl();
    static const int expect[3][4] = {{3, 0, 1, 0}, {1, 1, 1, 0}, {1, 0, 0, 0}};
    int st[3][4], mt[3][4], failed = 0;
    run(0, st);
    run(4, mt);
    for (int s = 0; s < 3; s ++) {
        printf("S%d: no threads %d %d %d %d; 4 threads %d %d %d %d\n", s + 1,
            st[s][0], st[s][1], st[s][2], st[s][3],
            mt[s][0], mt[s][1], mt[s][2], mt[s][3]);
        for (int f = 0; f < 4; f ++) {
            if (st[s][f] != expect[s][f]) {
                printf("INCONCLUSIVE: the control differs (S%d frame %d)\n",
                    s + 1, f + 1);
                return 2;
            }
            if (mt[s][f] != 4 * expect[s][f]) failed = 1;
        }
    }
    if (failed) {
        printf("FAIL: the worker iterators report other changes than the "
            "single-threaded run\n");
        return 1;
    }
    printf("OK\n");
    return 0;
}
