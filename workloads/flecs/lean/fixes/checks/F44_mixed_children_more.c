/* Check for F44, beyond the finding's test:
 *   1. a prefab whose first child has the Parent component and whose second
 *      child has a ChildOf pair, instantiated twice (the second instance uses
 *      the cached tree spawner); ecs_get_target(inst, prefab_child) of the
 *      Parent child keeps finding its instance child;
 *   2. three levels: Parent child q1, its ChildOf child q2, and q2's Parent
 *      child q3 (each with Position {level, 0});
 *   3. a ChildOf child below a ChildOf child below a Parent child.
 * main returns 0 when every instance has a copy of every prefab child, with
 * its value, at the right place. */
#include "flecs.h"
#include <stdio.h>

typedef struct { float x, y; } Position;
ECS_COMPONENT_DECLARE(Position);

static int count_children(ecs_world_t *world, ecs_entity_t parent,
    ecs_entity_t *first, float x)
{
    int n = 0;
    ecs_iter_t it = ecs_children(world, parent);
    while (ecs_children_next(&it)) {
        for (int i = 0; i < it.count; i ++) {
            const Position *p = ecs_get(world, it.entities[i], Position);
            if (p && p->x == x) {
                if (first) *first = it.entities[i];
                n ++;
            }
        }
    }
    return n;
}

int main(void) {
    ecs_world_t *world = ecs_mini();
    ECS_COMPONENT_DEFINE(world, Position);
    int failed = 0;

    /* 1 */
    ecs_entity_t P = ecs_new_w_id(world, EcsPrefab);
    ecs_entity_t b = ecs_new_w_parent(world, P, NULL);
    ecs_set(world, b, Position, {2, 0});
    ecs_entity_t a = ecs_new_w_pair(world, EcsChildOf, P);
    ecs_set(world, a, Position, {1, 0});
    for (int k = 0; k < 2; k ++) {
        ecs_entity_t inst = ecs_new_w_pair(world, EcsIsA, P);
        ecs_entity_t ib = 0;
        int na = count_children(world, inst, NULL, 1);
        int nb = count_children(world, inst, &ib, 2);
        ecs_entity_t tb = ecs_get_target(world, inst, b, 0);
        printf("1. instance %d: copy of a %d, copy of b %d, "
            "get_target(b) is b's copy %d\n", k + 1, na, nb, tb == ib && ib);
        if (na != 1 || nb != 1 || tb != ib) failed = 1;
    }
    (void)a;

    /* 2 */
    ecs_entity_t Q = ecs_new_w_id(world, EcsPrefab);
    ecs_entity_t q1 = ecs_new_w_parent(world, Q, NULL);
    ecs_set(world, q1, Position, {1, 0});
    ecs_entity_t q2 = ecs_new_w_pair(world, EcsChildOf, q1);
    ecs_set(world, q2, Position, {2, 0});
    ecs_entity_t q3 = ecs_new_w_parent(world, q2, NULL);
    ecs_set(world, q3, Position, {3, 0});
    for (int k = 0; k < 2; k ++) {
        ecs_entity_t inst = ecs_new_w_pair(world, EcsIsA, Q);
        ecs_entity_t c1 = 0, c2 = 0;
        int n1 = count_children(world, inst, &c1, 1);
        int n2 = c1 ? count_children(world, c1, &c2, 2) : 0;
        int n3 = c2 ? count_children(world, c2, NULL, 3) : 0;
        printf("2. instance %d: levels %d %d %d\n", k + 1, n1, n2, n3);
        if (n1 != 1 || n2 != 1 || n3 != 1) failed = 1;
    }

    /* 3 */
    ecs_entity_t S = ecs_new_w_id(world, EcsPrefab);
    ecs_entity_t s1 = ecs_new_w_parent(world, S, NULL);
    ecs_set(world, s1, Position, {1, 0});
    ecs_entity_t s2 = ecs_new_w_pair(world, EcsChildOf, s1);
    ecs_set(world, s2, Position, {2, 0});
    ecs_entity_t s3 = ecs_new_w_pair(world, EcsChildOf, s2);
    ecs_set(world, s3, Position, {3, 0});
    {
        ecs_entity_t inst = ecs_new_w_pair(world, EcsIsA, S);
        ecs_entity_t c1 = 0, c2 = 0;
        int n1 = count_children(world, inst, &c1, 1);
        int n2 = c1 ? count_children(world, c1, &c2, 2) : 0;
        int n3 = c2 ? count_children(world, c2, NULL, 3) : 0;
        printf("3. levels %d %d %d\n", n1, n2, n3);
        if (n1 != 1 || n2 != 1 || n3 != 1) failed = 1;
    }

    printf(failed ? "FAIL\n" : "OK\n");
    ecs_fini(world);
    return failed;
}
