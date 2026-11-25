/* Prediction: deleting the target of a (OnDeleteTarget, Panic) relationship
 * does not panic when the same entity is also a child of that target: the
 * ChildOf pair's Delete policy wins (on_delete.c 130-133, "Delete takes
 * precedence"), the entity is deleted and the Panic pair is never checked.
 *
 * Documented: ComponentTraits.md "OnDeleteTarget trait": Panic throws an
 * error when the target of the relationship is deleted. */
#include "flecs.h"
#include <stdio.h>
#include <stdlib.h>

static void on_abort(void) {
    if (ecs_log_last_error() == ECS_CONSTRAINT_VIOLATED) {
        exit(0);   /* documented: the delete panics */
    }
    printf("FAIL: unexpected abort (error %d)\n", ecs_log_last_error());
    exit(2);
}

int main(void) {
    ecs_os_set_api_defaults();
    ecs_os_api_t os_api = ecs_os_get_api();
    os_api.abort_ = on_abort;
    ecs_os_set_api(&os_api);
    ecs_log_set_level(-5);

    ecs_world_t *world = ecs_mini();
    ecs_entity_t RPanic = ecs_new(world);
    ecs_add_pair(world, RPanic, EcsOnDeleteTarget, EcsPanic);

    ecs_entity_t t = ecs_new(world);
    ecs_entity_t e = ecs_new(world);
    ecs_add_pair(world, e, RPanic, t);
    ecs_add_pair(world, e, EcsChildOf, t);

    ecs_delete(world, t);   /* documented: panics */

    printf("FAIL: deleting the target of a Panic relationship did not panic "
        "(e alive: %d)\n", ecs_is_alive(world, e));
    return 1;
}
