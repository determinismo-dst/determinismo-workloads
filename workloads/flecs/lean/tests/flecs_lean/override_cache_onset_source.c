/* Prediction F24 (OnSet from a base without the component): removing an
 * override emits OnSet with a base that no longer has the component as the
 * source. An observer that reads the field then reads through a NULL table
 * record (flecs_field_shared, iter.c 206-245: the base's table has no column
 * for Position, and it->trs[0] is NULL), a crash in practice.
 *
 * flecs_emit_on_set_for_override_on_remove (observable.c 946-1001) takes the
 * base from the table's override ref (flecs_table_get_override, table.c
 * 2310-2340) and looks up the base's table record, which is NULL (978-980).
 * The ref was computed while base had Position; base then lost it, but the
 * refresh check (table.c 483) compares against a generation that did not
 * move, because base's reachable cache was already invalid (observable.c
 * 504-510).
 *
 * Documented: ObserversManual.md "OnSet and Inheritance": OnSet is produced
 * when removing an override re-exposes an inherited component. Here base has
 * no Position, so nothing is re-exposed and no OnSet is due. This program
 * checks the source before reading the field, so it fails instead of
 * crashing. */
#include "flecs.h"
#include <stdio.h>

typedef struct { float x, y; } Position;
ECS_COMPONENT_DECLARE(Position);

static int bad_onset;

static void OnSet(ecs_iter_t *it) {
    ecs_entity_t src = ecs_field_src(it, 0);
    if (src && !ecs_owns(it->world, src, Position)) {
        printf("FAIL: OnSet for entity %u with source %u, which has no Position\n",
            (uint32_t)it->entities[0], (uint32_t)src);
        bad_onset ++;
        return; /* ecs_field(it, Position, 0) would read a NULL table record */
    }
    const Position *p = ecs_field(it, Position, 0);
    (void)p;
}

int main(void) {
    ecs_world_t *world = ecs_mini();
    ECS_COMPONENT_DEFINE(world, Position);
    ecs_add_pair(world, ecs_id(Position), EcsOnInstantiate, EcsInherit);

    ecs_observer(world, {
        .query.terms = {{ .id = ecs_id(Position), .src.id = EcsSelf|EcsUp, .trav = EcsIsA }},
        .events = { EcsOnSet },
        .callback = OnSet
    });

    ecs_entity_t base = ecs_new_w_id(world, EcsPrefab);
    ecs_entity_t inst = ecs_new_w_pair(world, EcsIsA, base); /* validates the
                                                              * reachable cache */
    ecs_set(world, base, Position, {50, 50}); /* valid -> invalid: generation + 1 */
    ecs_add(world, inst, Position);         /* override: refs refreshed, ref ->
                                             * base */
    ecs_remove(world, base, Position);      /* already invalid: no increment */
    ecs_remove(world, inst, Position);      /* predicted: OnSet with source base */

    int failed = bad_onset != 0;
    if (ecs_has(world, inst, Position)) {
        printf("INCONCLUSIVE: inst still has Position\n");
        failed = failed ? 1 : 2;
    }

    ecs_fini(world);
    if (!failed) printf("OK\n");
    return failed;
}
