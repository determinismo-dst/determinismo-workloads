/* Prediction F44: when a prefab has children in both hierarchy storages (a
 * ChildOf child and a Parent child), its instances get no copy of the
 * ChildOf child. The same holds below a Parent child: its ChildOf children
 * are not instantiated.
 *
 *   P: prefab; a = ChildOf P, Position {1, 2}; b = Parent P, Velocity {3, 4}
 *   inst = IsA P             inst has one child (b's), none for a
 *   controls: a prefab with two ChildOf children, one with two Parent
 *   children: two instance children each
 *   nested: Q: prefab; q1 = Parent Q; q2 = ChildOf q1
 *   inst_q = IsA Q           inst_q's child has no child for q2
 *
 * flecs_instantiate (addons/prefab/instantiate.c 393-480): when (ChildOf,
 * P) has ordered children and at least one Parent child
 * (flecs_component_has_non_fragmenting_childof, storage/non_fragmenting_
 * childof.h 46-51), the instance is built by P's TreeSpawner and the
 * function returns (424-440). The Parent child turned on the ordered
 * children of (ChildOf, P) (non_fragmenting_childof.c 43-45), whose list
 * then holds the ChildOf children too (ordered_children.c 21-44, 151-171),
 * but the spawner's walk keeps only children whose table has Parent
 * (tree_spawner.c 79-81) and descends only into the ordered children of a
 * kept child (104-113). Without a Parent child, each ChildOf child is
 * instantiated by flecs_instantiate_children (135-299).
 *
 * Documented: HierarchiesManual.md "Hierarchy storage": "A single parent
 * can contain children that use both ChildOf and Parent hierarchies" ("OK:
 * single parent with children using mixed storages"); "Prefab
 * instantiation works with both storages"; PrefabsManual.md "Prefab
 * Hierarchies" (an instance gets the prefab's children). main returns 0
 * when every instance has one child per prefab child. */
#include "flecs.h"
#include <stdio.h>
#include <stdlib.h>

typedef struct { float x, y; } Position;
ECS_COMPONENT_DECLARE(Position);
typedef struct { float x, y; } Velocity;

static int child_count(ecs_world_t *world, ecs_entity_t parent) {
    int n = 0;
    ecs_iter_t it = ecs_children(world, parent);
    while (ecs_children_next(&it)) n += it.count;
    return n;
}

/* the instance's child that copies a (a ChildOf child copies Position) */
static int has_copy_of_a(ecs_world_t *world, ecs_entity_t parent) {
    int found = 0;
    ecs_iter_t it = ecs_children(world, parent);
    while (ecs_children_next(&it)) {
        for (int i = 0; i < it.count; i ++) {
            const Position *p = ecs_get(world, it.entities[i], Position);
            if (p && p->x == 1 && p->y == 2) found = 1;
        }
    }
    return found;
}

int main(void) {
    ecs_world_t *world = ecs_mini();
    ECS_COMPONENT_DEFINE(world, Position);
    ECS_COMPONENT(world, Velocity);

    /* mixed */
    ecs_entity_t P = ecs_new_w_id(world, EcsPrefab);
    ecs_entity_t a = ecs_new_w_pair(world, EcsChildOf, P);
    ecs_set(world, a, Position, {1, 2});
    ecs_entity_t b = ecs_new_w_parent(world, P, NULL);
    ecs_set(world, b, Velocity, {3, 4});
    if (child_count(world, P) != 2) {
        printf("INCONCLUSIVE: P has %d children\n", child_count(world, P));
        return 2;
    }

    /* controls */
    ecs_entity_t C = ecs_new_w_id(world, EcsPrefab);
    ecs_set(world, ecs_new_w_pair(world, EcsChildOf, C), Position, {1, 2});
    ecs_set(world, ecs_new_w_pair(world, EcsChildOf, C), Velocity, {3, 4});
    ecs_entity_t R = ecs_new_w_id(world, EcsPrefab);
    ecs_set(world, ecs_new_w_parent(world, R, NULL), Position, {1, 2});
    ecs_set(world, ecs_new_w_parent(world, R, NULL), Velocity, {3, 4});

    /* nested: a ChildOf child below a Parent child */
    ecs_entity_t Q = ecs_new_w_id(world, EcsPrefab);
    ecs_entity_t q1 = ecs_new_w_parent(world, Q, NULL);
    ecs_entity_t q2 = ecs_new_w_pair(world, EcsChildOf, q1);
    ecs_set(world, q2, Position, {1, 2});

    ecs_entity_t inst = ecs_new_w_pair(world, EcsIsA, P);
    ecs_entity_t inst_c = ecs_new_w_pair(world, EcsIsA, C);
    ecs_entity_t inst_r = ecs_new_w_pair(world, EcsIsA, R);
    ecs_entity_t inst_q = ecs_new_w_pair(world, EcsIsA, Q);

    int n = child_count(world, inst), nc = child_count(world, inst_c);
    int nr = child_count(world, inst_r), nq = child_count(world, inst_q);
    int nq1 = 0;
    {
        ecs_iter_t it = ecs_children(world, inst_q);
        while (ecs_children_next(&it)) {
            for (int i = 0; i < it.count; i ++) {
                nq1 += child_count(world, it.entities[i]);
            }
        }
    }
    printf("children: mixed %d (copy of the ChildOf child: %d), two ChildOf "
        "%d, two Parent %d; nested: %d child with %d grandchild\n",
        n, has_copy_of_a(world, inst), nc, nr, nq, nq1);

    int failed = 0;
    if (nc != 2 || nr != 2 || nq != 1) {
        printf("INCONCLUSIVE: a control instance does not have its children\n");
        failed = 2;
    } else if (n != 2 || !has_copy_of_a(world, inst) || nq1 != 1) {
        printf("FAIL: the instance has no child for a ChildOf prefab child "
            "next to or below a Parent child\n");
        failed = 1;
    }
    (void)b;
    ecs_fini(world);
    return failed;
}
