/* Round 8: the Parent-storage forms of F48 (b) and F50 (b), whose ChildOf
 * forms the real flecs confirmed in round 7. Same mechanisms, the other
 * hierarchy storage.
 *
 *   Mass: DontFragment; Position: table (the control)
 *   (a) F50, Parent form: parent has Mass and Position; observers
 *       Mass(up) and Position(up) for OnAdd;
 *       child = ecs_new_w_parent(world, parent, NULL)
 *       -> OnAdd Position for child (source parent); no OnAdd Mass
 *   (b) F48, Parent form: child2 = ecs_new_w_parent(parent2) owns Mass and
 *       Position; grandchild = ecs_new_w_parent(child2); observers
 *       Mass(self|up) and Position(self|up) for OnAdd;
 *       ecs_set Mass and Position on parent2
 *       -> Position: OnAdd for parent2 only (child2 owns it, grandchild
 *          sees child2's); Mass: OnAdd also for child2 and grandchild,
 *          source parent2
 *
 * (a) The Parent component's OnSet is re-emitted as the OnAdd of
 * (ChildOf, parent) (observable.c 1160-1183), whose forward lists the ids
 * of the parent's table type (flecs_reachable_cache_ensure, 708-780): a
 * DontFragment component is never in it.
 * (b) The propagation from parent2 walks its ordered children one row
 * each (flecs_emit_propagate_id, 389-418) and decides ownership by the
 * child's table (flecs_emit_propagate_id_for_range, 324): a DontFragment
 * component is in no table, so child2 is not an owner and the walk goes on
 * to the grandchild.
 *
 * Documented: ObserversManual.md "Event Forwarding" ("if a (ChildOf,
 * my_parent) pair is added to an entity, and my_parent has components
 * Position and Velocity, an OnAdd event is produced for each component and
 * emitted for the child"), "Event Propagation" ("if an event for Position
 * is propagated from a parent to a child with Position, that event will not
 * be propagated to the child's children"); HierarchiesManual.md
 * ("Relationship traversal works for both storages"); ComponentTraits.md
 * "DontFragment trait". main returns 0 when Mass behaves like Position. */
#include "flecs.h"
#include <stdio.h>

typedef struct { float value; } Mass;
typedef struct { float x, y; } Position;

typedef struct {
    int count;
    ecs_entity_t entity[16], source[16];
} Log;

static void log_add(ecs_iter_t *it) {
    Log *l = it->ctx;
    for (int i = 0; i < it->count && l->count < 16; i ++) {
        l->entity[l->count] = it->entities[i];
        l->source[l->count] = ecs_field_src(it, 0);
        l->count ++;
    }
}

static int has(const Log *l, ecs_entity_t e, ecs_entity_t s) {
    for (int i = 0; i < l->count; i ++) {
        if (l->entity[i] == e && l->source[i] == s) return 1;
    }
    return 0;
}

int main(void) {
    ecs_world_t *world = ecs_mini();
    ECS_COMPONENT(world, Mass);
    ECS_COMPONENT(world, Position);
    ecs_add_id(world, ecs_id(Mass), EcsDontFragment);

    /* (a) */
    ecs_entity_t parent = ecs_new(world);
    ecs_set(world, parent, Mass, {1});
    ecs_set(world, parent, Position, {1, 2});
    Log ma = {0}, pa = {0};
    ecs_observer(world, {
        .query.terms = {{ ecs_id(Mass), .src.id = EcsUp }},
        .events = { EcsOnAdd }, .callback = log_add, .ctx = &ma });
    ecs_observer(world, {
        .query.terms = {{ ecs_id(Position), .src.id = EcsUp }},
        .events = { EcsOnAdd }, .callback = log_add, .ctx = &pa });
    ecs_entity_t child = ecs_new_w_parent(world, parent, NULL);
    int a_pos = has(&pa, child, parent), a_mass = has(&ma, child, parent);
    printf("(a) ecs_new_w_parent: OnAdd Position(up) for the child %d; "
        "OnAdd Mass(up) %d\n", a_pos, a_mass);

    /* (b) */
    ecs_entity_t parent2 = ecs_new(world);
    ecs_entity_t child2 = ecs_new_w_parent(world, parent2, NULL);
    ecs_set(world, child2, Mass, {2});
    ecs_set(world, child2, Position, {3, 4});
    ecs_entity_t grandchild = ecs_new_w_parent(world, child2, NULL);
    Log mb = {0}, pb = {0};
    ecs_observer(world, {
        .query.terms = {{ ecs_id(Mass), .src.id = EcsSelf | EcsUp,
            .trav = EcsChildOf }},
        .events = { EcsOnAdd }, .callback = log_add, .ctx = &mb });
    ecs_observer(world, {
        .query.terms = {{ ecs_id(Position), .src.id = EcsSelf | EcsUp,
            .trav = EcsChildOf }},
        .events = { EcsOnAdd }, .callback = log_add, .ctx = &pb });
    ecs_set(world, parent2, Mass, {5});
    ecs_set(world, parent2, Position, {5, 5});
    printf("(b) ecs_set on parent2: Position OnAdd events %d (child2 %d, "
        "grandchild %d); Mass OnAdd events %d (child2 from parent2 %d, "
        "grandchild from parent2 %d)\n", pb.count, has(&pb, child2, parent2),
        has(&pb, grandchild, parent2), mb.count, has(&mb, child2, parent2),
        has(&mb, grandchild, parent2));

    int failed = 0;
    if (!a_pos || pb.count != 1) {
        printf("INCONCLUSIVE: a Position control did not behave\n");
        failed = 2;
    } else {
        if (!a_mass) {
            printf("FAIL (F50, Parent form): no OnAdd Mass(up) for the new "
                "child of a parent with Mass\n");
            failed = 1;
        }
        if (has(&mb, child2, parent2) || has(&mb, grandchild, parent2)) {
            printf("FAIL (F48, Parent form): OnAdd Mass for an owner of Mass "
                "or below it, with source parent2\n");
            failed = 1;
        }
    }
    ecs_fini(world);
    return failed;
}
