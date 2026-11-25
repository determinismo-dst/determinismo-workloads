/* Prediction F24 (missing OnSet): removing an override does not produce the
 * documented OnSet for the re-exposed base value, because the table's
 * override cache still says the base has no Position.
 *
 * flecs_emit_on_set_for_override_on_remove (observable.c 946-1001) asks the
 * entity's table for the override ref (flecs_table_get_override, table.c
 * 2310-2340). The ref was computed when base had no Position, and the
 * refresh check (table.c 483) compares against a generation that did not
 * move when base got Position, because base's reachable cache was already
 * invalid (observable.c 504-510). With no ref, no OnSet is emitted.
 *
 * Documented: ObserversManual.md "OnSet and Inheritance", "Removing an
 * Override": "When an overridden component is removed, the inherited
 * component is reexposed ... An OnSet event will be produced for the
 * inherited component" (components with the (OnInstantiate, Inherit) trait,
 * observers with the default self|up source). */
#include "flecs.h"
#include <stdio.h>

typedef struct { float x, y; } Position;

static ecs_entity_t inst_watched;
static int onset_for_inst;

static void OnSet(ecs_iter_t *it) {
    for (int i = 0; i < it->count; i ++) {
        if (it->entities[i] == inst_watched) onset_for_inst ++;
    }
}

int main(void) {
    ecs_world_t *world = ecs_mini();
    ECS_COMPONENT(world, Position);
    ECS_TAG(world, Tag);
    ecs_add_pair(world, ecs_id(Position), EcsOnInstantiate, EcsInherit);

    ecs_observer(world, {
        .query.terms = {{ .id = ecs_id(Position), .src.id = EcsSelf|EcsUp, .trav = EcsIsA }},
        .events = { EcsOnSet },
        .callback = OnSet
    });

    ecs_entity_t base = ecs_new_w_id(world, EcsPrefab);
    ecs_entity_t inst = ecs_new_w_pair(world, EcsIsA, base); /* validates the
                                                              * reachable cache */
    ecs_add(world, base, Tag);              /* valid -> invalid: generation + 1 */
    ecs_add(world, inst, Position);         /* override; refs refreshed: base
                                             * has no Position yet */
    ecs_set(world, base, Position, {50, 50}); /* already invalid: no increment */

    inst_watched = inst;
    onset_for_inst = 0;
    ecs_remove(world, inst, Position);      /* re-exposes base's {50, 50} */

    int failed = 0;
    const Position *p = ecs_get(world, inst, Position);
    if (!p || p->x != 50) {
        printf("INCONCLUSIVE: inst does not inherit {50, 50} from base\n");
        ecs_fini(world);
        return 2;
    }
    if (onset_for_inst == 0) {
        printf("FAIL: removing the override re-exposed {50, 50} but no OnSet was emitted for inst\n");
        failed = 1;
    }

    ecs_fini(world);
    if (!failed) printf("OK\n");
    return failed;
}
