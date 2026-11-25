/* Prediction: deleting the target of a (OnDeleteTarget, Panic) relationship
 * does not panic when the same entity also has a pair with the same target
 * for a relationship created later (default Remove policy):
 * flecs_get_delete_action (on_delete.c 111-152) keeps the policy of the last
 * matching pair unless one is Delete, so Panic is overwritten by Remove.  With
 * the relationships created in the other order, the same delete panics.
 *
 * Documented: ComponentTraits.md "OnDeleteTarget trait": Panic throws an
 * error when the target of a relationship is deleted. */
#include "flecs.h"
#include <stdio.h>
#include <stdlib.h>

static void on_abort(void) {
    /* documented behaviour: the delete panics with CONSTRAINT_VIOLATED */
    if (ecs_log_last_error() == ECS_CONSTRAINT_VIOLATED) {
        exit(0);
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
    ecs_entity_t RPlain = ecs_new(world);   /* created after: larger id */

    ecs_entity_t t = ecs_new(world);
    ecs_entity_t e = ecs_new(world);
    ecs_add_pair(world, e, RPanic, t);
    ecs_add_pair(world, e, RPlain, t);

    ecs_delete(world, t);   /* documented: panics */

    printf("FAIL: deleting the target of a Panic relationship did not panic "
        "(e alive: %d, has (RPanic, t): %d)\n", ecs_is_alive(world, e),
        ecs_is_alive(world, e) ? ecs_has_pair(world, e, RPanic, t) : -1);
    return 1;
}
