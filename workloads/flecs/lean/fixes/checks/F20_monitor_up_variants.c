#include "flecs.h"
#include <stdio.h>
typedef struct { float x, y; } Position;
static int adds, removes;
static void Mon(ecs_iter_t *it) {
    if (it->event == EcsOnAdd) adds += it->count;
    else if (it->event == EcsOnRemove) removes += it->count;
}
static int run(int parent_storage, ecs_flags64_t src) {
    ecs_world_t *world = ecs_mini();
    ECS_COMPONENT(world, Position);
    adds = removes = 0;
    ecs_observer(world, {
        .query.terms = {{ ecs_id(Position), .src.id = src, .trav = EcsChildOf }},
        .events = { EcsMonitor }, .callback = Mon });
    ecs_entity_t gp = ecs_new(world), p, c;
    if (parent_storage) {
        p = ecs_new_w_parent(world, gp, NULL); c = ecs_new_w_parent(world, p, NULL);
    } else {
        p = ecs_new_w_pair(world, EcsChildOf, gp); c = ecs_new_w_pair(world, EcsChildOf, p);
    }
    (void)c;
    int f = 0;
    ecs_add(world, gp, Position);     /* p, c start matching */
    int su = (src != EcsUp); /* self|up: gp itself matches too */
    if (adds != 2 + su) { printf("  gp add: %d OnAdd\n", adds); f = 1; }
    ecs_add(world, p, Position);      /* nothing changes for c (self|up: p now owns, it matched before) */
    ecs_remove(world, p, Position);   /* nothing changes */
    if (adds != 2 + su || removes != 0) { printf("  p add/remove: %d OnAdd %d OnRemove\n", adds, removes); f = 1; }
    ecs_remove(world, gp, Position);  /* p, c stop matching */
    if (removes != 2 + su) { printf("  gp remove: %d OnRemove\n", removes); f = 1; }
    ecs_add(world, p, Position);      /* c starts matching (and p for self|up) */
    int exp = su ? 5 : 3;
    if (adds != exp) { printf("  p add again: %d OnAdd, expected %d\n", adds, exp); f = 1; }
    ecs_fini(world);
    return f;
}
int main(void) {
    int f = 0;
    for (int ps = 0; ps < 2; ps ++) {
        for (int s = 0; s < 2; s ++) {
            ecs_flags64_t src = s ? (EcsSelf|EcsUp) : EcsUp;
            int r = run(ps, src);
            printf("%s, %s: %s\n", ps ? "Parent" : "ChildOf", s ? "self|up" : "up", r ? "FAIL" : "ok");
            f |= r;
        }
    }
    return f;
}
