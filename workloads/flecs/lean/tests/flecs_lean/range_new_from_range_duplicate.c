/* Prediction: ecs_new_from_range returns an entity that is already alive
 * when the id it recycles was made alive again with ecs_make_alive while it
 * sat in the (inactive) range's recycled list: entity_ranges.c 249-252 pops
 * the id and flecs_entity_index_ensure finds it alive, then
 * flecs_add_to_root_table asserts (entity.c 660, "r->table == NULL").
 * Same root cause as range_make_alive_recycled.c.
 *
 * Documented: entity_ranges.h ecs_new_from_range ("creates a new entity with
 * an id from the specified range ... If the range has recycled ids, a
 * recycled id is returned"); EntitiesComponents.md "Manual Ids" (make_alive
 * may be used on an id that is not in use). */
#include "flecs.h"
#include <stdio.h>

int main(void) {
    ecs_world_t *world = ecs_mini();
    const ecs_entity_range_t *r = ecs_entity_range_new(world, 5000, 6000);

    ecs_entity_t e = ecs_new_from_range(world, r);   /* 5000, r not active */
    ecs_delete(world, e);                            /* 5000v1 -> r's recycled list */
    ecs_entity_t e1 = e | (1ull << 32);               /* the recycled handle */
    ecs_make_alive(world, e1);

    int failed = 0;
    if (!ecs_is_alive(world, e1)) { printf("FAIL: make_alive did not make e1 alive\n"); failed = 1; }

    ecs_entity_t n = ecs_new_from_range(world, r);   /* predicted: aborts */
    if (n == e1 || (uint32_t)n == (uint32_t)e1) {
        printf("FAIL: new_from_range returned the alive entity %llu\n", (unsigned long long)n);
        failed = 1;
    }
    ecs_fini(world);
    return failed;
}
