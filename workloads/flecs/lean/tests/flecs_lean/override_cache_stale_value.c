/* Prediction F24 (wrong value): after the sequence below, every new instance
 * of `base` gets a default-constructed Position instead of a copy of base's
 * Position, until base changes again.
 *
 * The table [Position, (IsA, base)] refreshes its override refs while base
 * has no Position (the ref is empty). base then gets Position back, but the
 * generation the cache is keyed on does not move, because base's reachable
 * cache was already invalid (observable.c 504-510; table.c 471-508, 483). New
 * instances land in that table and are constructed from the empty ref
 * (flecs_table_invoke_ctor, table.c 963-993): the ctor runs instead of the
 * copy.
 *
 * Documented: ComponentTraits.md "OnInstantiate trait": "By default, when an
 * entity is instantiated, the components from the base entity (the IsA
 * target) are copied to the instance." */
#include "flecs.h"
#include <stdio.h>

typedef struct { float x, y; } Position;

static void Position_ctor(void *ptr, int32_t count, const ecs_type_info_t *ti) {
    (void)ti;
    Position *p = ptr;
    for (int32_t i = 0; i < count; i ++) { p[i].x = -1; p[i].y = -1; }
}

int main(void) {
    ecs_world_t *world = ecs_mini();
    ECS_COMPONENT(world, Position);
    ecs_set_hooks(world, Position, { .ctor = Position_ctor });

    ecs_entity_t base = ecs_new(world);
    ecs_set(world, base, Position, {1, 1});

    ecs_entity_t inst = ecs_new_w_pair(world, EcsIsA, base); /* {1, 1} */

    ecs_remove(world, base, Position);  /* valid -> invalid: generation + 1 */

    ecs_remove(world, inst, Position);
    ecs_add(world, inst, Position);     /* refs refreshed: base has none, so
                                         * inst gets the ctor value (right) */

    ecs_set(world, base, Position, {99, 99}); /* already invalid: no increment */

    ecs_entity_t inst2 = ecs_new_w_pair(world, EcsIsA, base);
    ecs_entity_t inst3 = ecs_new_w_pair(world, EcsIsA, base);

    int failed = 0;
    const Position *p2 = ecs_get(world, inst2, Position);
    const Position *p3 = ecs_get(world, inst3, Position);
    if (!p2 || !p3) {
        printf("FAIL: an instance has no Position\n");
        failed = 1;
    } else {
        if (p2->x != 99 || p2->y != 99) {
            printf("FAIL: inst2 Position is {%g, %g}, base has {99, 99}\n", p2->x, p2->y);
            failed = 1;
        }
        if (p3->x != 99 || p3->y != 99) {
            printf("FAIL: inst3 Position is {%g, %g}, base has {99, 99}\n", p3->x, p3->y);
            failed = 1;
        }
    }

    ecs_fini(world);
    if (!failed) printf("OK\n");
    return failed;
}
