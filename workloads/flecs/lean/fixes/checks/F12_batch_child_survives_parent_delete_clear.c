/* Prediction: queued [add (ChildOf, p) to c; delete p; remove (ChildOf, p)
 * from c] leaves c alive.  The merge batches c's two commands at the
 * position of the first (commands.c 1351-1369, 968-1134): c's add and
 * remove cancel before p's delete runs, so c is not a child of p when p is
 * deleted.  Run in queue order, c is p's child when p is deleted and is
 * deleted with it (the later remove is discarded).
 *
 * Documented: Manual.md "Deferred operations" (queued commands run at merge;
 * commands targeting an entity deleted before their execution are
 * discarded); HierarchiesManual.md / Relationships.md "Cleanup properties"
 * (deleting a parent deletes its children); ObserversManual.md "Event order
 * is undefined between entities" allows batching to reorder events, not to
 * change which entities survive. */
#include "flecs.h"
#include <stdio.h>

int main(void) {
    ecs_world_t *world = ecs_mini();
    ecs_entity_t p = ecs_new(world);
    ecs_entity_t c = ecs_new(world);

    ecs_world_t *stage = ecs_get_stage(world, 0);
    ecs_add_pair(stage, c, EcsChildOf, p);
    ecs_delete(stage, p);
    ecs_clear(stage, c);
    ecs_merge(stage);

    int failed = 0;
    if (ecs_is_alive(world, p)) { printf("FAIL: parent alive\n"); failed = 1; }
    if (ecs_is_alive(world, c)) {
        printf("FAIL: child survived the deletion of its parent\n");
        failed = 1;
    }
    ecs_fini(world);
    return failed;
}
