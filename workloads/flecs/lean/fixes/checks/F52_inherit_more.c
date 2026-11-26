/* F52 check: Parent-storage prefab children with Inherit components that
 * have an on_set hook or are Sparse, instantiated for an instance at depth 2
 * (the spawner's transposed tables) and twice (the cached spawner).
 * Velocity: Inherit + on_set hook; Health: Sparse + Inherit; Mass: owned
 * (no trait) + on_set hook, the control: its hook runs for every instance
 * child. Every instance child must read the prefab child's Velocity and
 * Health without owning them; Velocity's hook must not run for them. (On
 * v4.2.0 the Parent path calls Mass's hook twice per instance child, the
 * ChildOf path once; the check only prints that count.) */
#include "flecs.h"
#include <stdio.h>
#include <signal.h>
#include <stdlib.h>

typedef struct { float x, y; } Velocity;
typedef struct { int v; } Health;
typedef struct { float v; } Mass;

static int vel_hook, mass_hook;
static void vel_on_set(ecs_iter_t *it) { vel_hook += it->count; }
static void mass_on_set(ecs_iter_t *it) { mass_hook += it->count; }

static void on_abort(int sig) {
    (void)sig; printf("FAIL: abort\n"); fflush(stdout); _Exit(1);
}

static ecs_entity_t first_child(ecs_world_t *world, ecs_entity_t e) {
    ecs_iter_t it = ecs_children(world, e);
    ecs_entity_t r = 0;
    while (ecs_children_next(&it)) if (it.count && !r) r = it.entities[0];
    return r;
}

int main(void) {
    ecs_world_t *world = ecs_mini();
    ECS_COMPONENT(world, Velocity);
    ECS_COMPONENT(world, Health);
    ECS_COMPONENT(world, Mass);
    ecs_set_hooks(world, Velocity, { .on_set = vel_on_set });
    ecs_set_hooks(world, Mass, { .on_set = mass_on_set });
    ecs_add_pair(world, ecs_id(Velocity), EcsOnInstantiate, EcsInherit);
    ecs_add_id(world, ecs_id(Health), EcsSparse);
    ecs_add_pair(world, ecs_id(Health), EcsOnInstantiate, EcsInherit);

    ecs_entity_t p = ecs_new_w_id(world, EcsPrefab);
    ecs_entity_t c = ecs_new_w_parent(world, p, NULL);
    ecs_set(world, c, Velocity, {3, 4});
    ecs_set(world, c, Health, {10});
    ecs_set(world, c, Mass, {2});
    int vel0 = vel_hook, mass0 = mass_hook;

    signal(SIGABRT, on_abort);
    ecs_entity_t root = ecs_new(world);
    ecs_entity_t mid = ecs_new_w_parent(world, root, NULL);
    ecs_entity_t insts[3];
    insts[0] = ecs_new_w_pair(world, EcsIsA, p);
    insts[1] = ecs_new_w_parent(world, mid, NULL);
    ecs_add_pair(world, insts[1], EcsIsA, p);
    insts[2] = ecs_new_w_pair(world, EcsIsA, p);
    signal(SIGABRT, SIG_DFL);

    int ok = 1;
    for (int i = 0; i < 3; i ++) {
        ecs_entity_t ch = first_child(world, insts[i]);
        const Velocity *v = ch ? ecs_get(world, ch, Velocity) : NULL;
        const Health *h = ch ? ecs_get(world, ch, Health) : NULL;
        const Mass *m = ch ? ecs_get(world, ch, Mass) : NULL;
        int inherits = ch && !ecs_owns(world, ch, Velocity) &&
            !ecs_owns(world, ch, Health) && ecs_owns(world, ch, Mass);
        printf("instance %d: child reads Velocity %g, Health %d, Mass %g; "
            "inherits Velocity and Health %d\n", i, v ? v->x : -1,
            h ? h->v : -1, m ? m->v : -1, inherits);
        ok &= v && v->x == 3 && h && h->v == 10 && m && m->v == 2 &&
            inherits;
    }
    printf("on_set hook calls during instantiation: Velocity %d, Mass %d\n",
        vel_hook - vel0, mass_hook - mass0);
    ok &= (vel_hook == vel0) && (mass_hook - mass0 >= 3);
    printf(ok ? "OK\n" : "FAIL\n");
    ecs_fini(world);
    return ok ? 0 : 1;
}
