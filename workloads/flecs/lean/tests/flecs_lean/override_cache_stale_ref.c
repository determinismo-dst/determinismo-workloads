/* Prediction F24 (assert): a table's override cache keeps a ref to a base
 * that no longer has the component, and the next entity that gets the
 * component in that table aborts at storage/table.c 979,
 * ecs_assert(base_ptr != NULL, ECS_INTERNAL_ERROR) (a NULL copy source in a
 * release build).
 *
 * A table with an (IsA, base) pair caches, per column, a ref to the base the
 * column's value is copied from when an entity gets the component there
 * (flecs_table_update_overrides, table.c 471-508; flecs_table_invoke_ctor,
 * 963-993). The cache is refreshed when the generation of the (IsA, base)
 * record's reachable cache changed (table.c 483). That generation is only
 * incremented when the reachable cache goes from valid to invalid
 * (flecs_emit_propagate_invalidate_tables, observable.c 504-510: "Subtree is
 * already marked invalid"); it becomes valid again only when an (IsA, base)
 * pair is added or removed (flecs_emit_forward, observable.c 811-812). So once
 * the base changed after the last IsA add, later changes of the base leave the
 * generation alone, and the override cache keeps refs computed for an older
 * state of the base.
 *
 * Documented: ComponentTraits.md "OnInstantiate trait" (Copy, the default:
 * the base's components are copied to the instance); PrefabsManual.md
 * "Component Overriding" (adding a component the base has initializes it with
 * the base's value); when the base does not have the component, adding it is
 * a plain add. Manual.md "Error handling": internal asserts are not
 * reachable through valid API use. */
#include "flecs.h"
#include <stdio.h>
#include <stdlib.h>

typedef struct { float x, y; } Position;

static void on_abort(void) {
    printf("FAIL: aborted while constructing Position from a stale override ref\n");
    exit(1);
}

int main(void) {
    ecs_os_set_api_defaults();
    ecs_os_api_t os_api = ecs_os_get_api();
    os_api.abort_ = on_abort;
    ecs_os_set_api(&os_api);

    ecs_world_t *world = ecs_mini();
    ECS_COMPONENT(world, Position);
    ECS_TAG(world, Tag);

    ecs_entity_t base = ecs_new(world);
    ecs_set(world, base, Position, {1, 2});

    /* inst gets a copy; adding (IsA, base) makes base's reachable cache
     * valid */
    ecs_entity_t inst = ecs_new_w_pair(world, EcsIsA, base);

    ecs_add(world, base, Tag);          /* valid -> invalid: generation + 1 */

    ecs_remove(world, inst, Position);
    ecs_add(world, inst, Position);     /* table [Position, (IsA, base)]
                                         * refreshes its refs: base */

    ecs_remove(world, base, Position);  /* already invalid: no increment */

    ecs_remove(world, inst, Position);
    ecs_add(world, inst, Position);     /* predicted: abort at table.c 979 */

    int failed = 0;
    if (!ecs_has(world, inst, Position)) {
        printf("FAIL: inst does not have Position after ecs_add\n");
        failed = 1;
    }

    ecs_fini(world);
    if (!failed) printf("OK\n");
    return failed;
}
