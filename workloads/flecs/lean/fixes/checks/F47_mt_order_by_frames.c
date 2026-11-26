/* Check for F47: a multithreaded order_by system over several frames, with 4
 * threads. Between frames the main thread gives every entity a new value and
 * moves some entities to another table (a tag added or removed), so every
 * frame needs a new sort. In every frame each worker must see its rows in
 * ascending order (each worker gets a part of each sorted slice), and every
 * entity must be seen once. A single-threaded order_by system in the same
 * pipeline is the control. main returns 0 when every frame holds. */
#include "flecs.h"
#include <stdio.h>
#include <stdlib.h>

#define N 300
#define FRAMES 20
#define THREADS 4

typedef struct { float x, y; } Position;

static int compare_x(ecs_entity_t e1, const void *p1, ecs_entity_t e2,
    const void *p2)
{
    (void)e1; (void)e2;
    const Position *a = p1, *b = p2;
    return (a->x > b->x) - (a->x < b->x);
}

static ecs_entity_t ents[N];
static int seen[THREADS][N];
static float last[THREADS];
static int unordered[THREADS];
static int st_seen[N];
static float st_last;
static int st_unordered;

static int index_of(ecs_entity_t e) {
    for (int i = 0; i < N; i ++) if (ents[i] == e) return i;
    return -1;
}

static void MtSys(ecs_iter_t *it) {
    int w = ecs_stage_get_id(it->stage);
    const Position *p = ecs_field(it, Position, 0);
    for (int i = 0; i < it->count; i ++) {
        if (p[i].x < last[w]) unordered[w] ++;
        last[w] = p[i].x;
        int k = index_of(it->entities[i]);
        if (k >= 0) seen[w][k] ++;
    }
}

static void StSys(ecs_iter_t *it) {
    const Position *p = ecs_field(it, Position, 0);
    for (int i = 0; i < it->count; i ++) {
        if (p[i].x < st_last) st_unordered ++;
        st_last = p[i].x;
        int k = index_of(it->entities[i]);
        if (k >= 0) st_seen[k] ++;
    }
}

int main(void) {
    ecs_world_t *world = ecs_init();
    ECS_COMPONENT(world, Position);
    ECS_TAG(world, TagA);
    ECS_TAG(world, TagB);

    ecs_entity_t mt = ecs_entity(world, { .name = "MtSys" });
    ecs_add_pair(world, mt, EcsDependsOn, EcsOnUpdate);
    ecs_entity_t st = ecs_entity(world, { .name = "StSys" });
    ecs_add_pair(world, st, EcsDependsOn, EcsPostUpdate);
    ecs_system(world, {
        .entity = mt,
        .query.terms = {{ .id = ecs_id(Position), .inout = EcsIn }},
        .query.order_by = ecs_id(Position),
        .query.order_by_callback = compare_x,
        .callback = MtSys,
        .multi_threaded = true
    });
    ecs_system(world, {
        .entity = st,
        .query.terms = {{ .id = ecs_id(Position), .inout = EcsIn }},
        .query.order_by = ecs_id(Position),
        .query.order_by_callback = compare_x,
        .callback = StSys
    });

    srand(1);
    for (int i = 0; i < N; i ++) {
        ents[i] = ecs_insert(world, ecs_value(Position, {(float)(rand() % 1000), 0}));
        if (i % 3 == 1) ecs_add(world, ents[i], TagA);
        if (i % 3 == 2) ecs_add(world, ents[i], TagB);
    }

    ecs_set_threads(world, THREADS);
    int failed = 0;
    for (int f = 0; f < FRAMES; f ++) {
        for (int w = 0; w < THREADS; w ++) {
            last[w] = -1;
            unordered[w] = 0;
            for (int i = 0; i < N; i ++) seen[w][i] = 0;
        }
        st_last = -1; st_unordered = 0;
        for (int i = 0; i < N; i ++) st_seen[i] = 0;

        ecs_progress(world, 0);

        int once = 1, st_once = 1, unord = 0;
        for (int i = 0; i < N; i ++) {
            int n = 0;
            for (int w = 0; w < THREADS; w ++) n += seen[w][i];
            if (n != 1) once = 0;
            if (st_seen[i] != 1) st_once = 0;
        }
        for (int w = 0; w < THREADS; w ++) unord += unordered[w];
        if (!once || unord || !st_once || st_unordered) {
            printf("frame %d: every entity once %d, out of order %d; control: "
                "once %d, out of order %d\n", f, once, unord, st_once,
                st_unordered);
            failed = 1;
        }

        /* new values; move some entities to another table */
        for (int i = 0; i < N; i ++) {
            ecs_set(world, ents[i], Position, {(float)(rand() % 1000), 0});
            if (rand() % 10 == 0) {
                if (ecs_has(world, ents[i], TagA)) ecs_remove(world, ents[i], TagA);
                else ecs_add(world, ents[i], TagA);
            }
        }
    }

    printf("%d frames with %d threads: %s\n", FRAMES, THREADS,
        failed ? "FAIL" : "OK");
    ecs_set_threads(world, 0);
    ecs_fini(world);
    return failed;
}
