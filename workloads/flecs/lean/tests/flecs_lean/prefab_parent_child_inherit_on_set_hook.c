/* Prediction F52 (first form): instantiating a prefab whose Parent-storage
 * child has an (OnInstantiate, Inherit) component with an on_set hook
 * aborts. The second form, an Inherit Sparse component, is
 * prefab_parent_child_inherit_sparse.c, which includes this file with
 * FLECS_LEAN_SPARSE set.
 *
 *   Velocity: (OnInstantiate, Inherit), on_set hook (first form);
 *             Sparse, (OnInstantiate, Inherit), no hook (second form)
 *   controls: the same prefab with a ChildOf child (instance child owns
 *   Velocity); a Parent child with Velocity auto-overridden (owns it)
 *   p = prefab; c = ecs_new_w_parent(p) {Position, Velocity}
 *   ecs_new_w_pair(world, EcsIsA, p)        abort
 *
 * A prefab with Parent children is instantiated by its TreeSpawner
 * (addons/prefab/instantiate.c 424-440). The instance child's table leaves
 * out every id whose record has the Inherit or DontInherit trait
 * (flecs_prefab_spawner_build_type, tree_spawner.c 27-31): the instance
 * child inherits Velocity through (IsA, c) instead (57). After appending
 * the instance child, flecs_spawner_instantiate calls
 * flecs_instantiate_sparse(..., emit_non_sparse = true) (tree_spawner.c
 * 335-338), which walks c's whole table type and skips only DontInherit ids
 * (instantiate.c 73-133):
 *   - for a Sparse id it copies the value into the instance child's sparse
 *     storage after ecs_assert(dst_ptr != NULL) (119-124), which fails: the
 *     instance child has no Velocity of its own;
 *   - for every id it calls flecs_notify_on_set_w_cr(..., invoke_hook =
 *     true) (129-130), which for a component with an on_set hook looks the
 *     instance child's table up in the component's table cache and asserts
 *     it is there (component_actions.c 672-681: ecs_assert(elem != NULL), 679).
 * The ChildOf path copies Inherit components to the instance child
 * (instantiate.c 171-184), so they are in its table. flecs's own
 * NonFragmentingChildOf_instantiate_w_inherit has no hook and no Sparse
 * storage.
 *
 * Documented: ComponentTraits.md "OnInstantiate trait" ("Inherit");
 * HierarchiesManual.md "Prefab instantiation works with both storages",
 * "When instantiating a prefab with a Parent hierarchy, instance children
 * will inherit from the prefab children"; ComponentTraits.md "Sparse trait"
 * ("ECS operations and queries work as expected with sparse components");
 * Manual.md "Error handling". An abort confirms the prediction: the handler
 * prints FAIL and exits 1. main returns 0 when the instance child inherits
 * Velocity from c. */
#include "flecs.h"
#include <stdio.h>
#include <stdlib.h>
#include <signal.h>

typedef struct { float x, y; } Position;
typedef struct { float x, y; } Velocity;

static int hook_calls;
static void velocity_on_set(ecs_iter_t *it) { hook_calls += it->count; }

static void on_abort(int sig) {
    (void)sig;
    printf("FAIL: instantiating the prefab with a Parent child aborted\n");
    fflush(stdout);
    _Exit(1);
}

static ecs_entity_t child_of_instance(ecs_world_t *world, ecs_entity_t i) {
    ecs_iter_t it = ecs_children(world, i);
    ecs_entity_t result = 0;
    while (ecs_children_next(&it)) {
        if (it.count && !result) result = it.entities[0];
    }
    return result;
}

int main(void) {
    ecs_world_t *world = ecs_mini();
    ECS_COMPONENT(world, Position);
    ECS_COMPONENT(world, Velocity);
#ifdef FLECS_LEAN_SPARSE
    ecs_add_id(world, ecs_id(Velocity), EcsSparse);
#else
    ecs_set_hooks(world, Velocity, { .on_set = velocity_on_set });
#endif
    ecs_add_pair(world, ecs_id(Velocity), EcsOnInstantiate, EcsInherit);

    /* control: ChildOf child */
    ecs_entity_t pc = ecs_new_w_id(world, EcsPrefab);
    ecs_entity_t cc = ecs_new_w_pair(world, EcsChildOf, pc);
    ecs_set(world, cc, Position, {1, 2});
    ecs_set(world, cc, Velocity, {3, 4});
    ecs_entity_t ic = ecs_new_w_pair(world, EcsIsA, pc);
    ecs_entity_t icc = child_of_instance(world, ic);
    const Velocity *vc = icc ? ecs_get(world, icc, Velocity) : NULL;

    /* control: Parent child, Velocity auto-overridden */
    ecs_entity_t pa = ecs_new_w_id(world, EcsPrefab);
    ecs_entity_t ca = ecs_new_w_parent(world, pa, NULL);
    ecs_set(world, ca, Position, {1, 2});
    ecs_set(world, ca, Velocity, {3, 4});
    ecs_auto_override(world, ca, Velocity);
    ecs_entity_t ia = ecs_new_w_pair(world, EcsIsA, pa);
    ecs_entity_t iac = child_of_instance(world, ia);
    const Velocity *va = iac ? ecs_get(world, iac, Velocity) : NULL;
    printf("controls: ChildOf child's Velocity %s (owned %d); auto-overridden"
        " Parent child's Velocity %s (owned %d)\n",
        vc && vc->x == 3 ? "{3, 4}" : "wrong", icc && ecs_owns(world, icc,
        Velocity), va && va->x == 3 ? "{3, 4}" : "wrong", iac &&
        ecs_owns(world, iac, Velocity));
    fflush(stdout);
    if (!vc || vc->x != 3 || !va || va->x != 3) {
        printf("INCONCLUSIVE: a control failed\n");
        return 2;
    }

    /* the prediction: Parent child, Velocity inherited */
    ecs_entity_t p = ecs_new_w_id(world, EcsPrefab);
    ecs_entity_t c = ecs_new_w_parent(world, p, NULL);
    ecs_set(world, c, Position, {1, 2});
    ecs_set(world, c, Velocity, {3, 4});

    signal(SIGABRT, on_abort);
    ecs_entity_t i = ecs_new_w_pair(world, EcsIsA, p);
    signal(SIGABRT, SIG_DFL);

    ecs_entity_t ichild = child_of_instance(world, i);
    const Velocity *v = ichild ? ecs_get(world, ichild, Velocity) : NULL;
    printf("instance child: inherits Velocity from c %d, value %s; on_set "
        "hook calls %d\n", ichild && ecs_has_pair(world, ichild, EcsIsA, c) &&
        !ecs_owns(world, ichild, Velocity), v && v->x == 3 ? "{3, 4}" :
        "wrong", hook_calls);
    int failed = 0;
    if (!v || v->x != 3) {
        printf("FAIL: the instance child does not read c's Velocity\n");
        failed = 1;
    }
    ecs_fini(world);
    return failed;
}
