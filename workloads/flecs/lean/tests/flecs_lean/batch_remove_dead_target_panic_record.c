/* F2, corrected. Round 1's batch_remove_dead_target_panic.c did not panic on
 * the real flecs: flecs_remove_invalid (commands.c 893-942) reads the policy
 * from the (Rel, *) component record and, when that record does not exist,
 * drops the command. Adding (OnDeleteTarget, Panic) to Rel does not create
 * (Rel, *) (flecs_register_flag_for_trait, bootstrap.c 207-218, only updates
 * existing records); the first (Rel, x) pair does, and the record then lives
 * until Rel is deleted. Round 1's model created (Rel, *) with the trait.
 *
 * Prediction (corrected model): once Rel has been used in any pair, the same
 * program panics in the merge: a queued remove of (Rel, tgt), batched with
 * another command for the entity, after tgt was deleted earlier in the same
 * merge (commands.c 917-920 -> on_delete.c 770-784). Nobody had (Rel, tgt),
 * so deleting tgt was legal, and removing a pair the entity does not have does
 * nothing.
 *
 * Documented: ComponentTraits.md "OnDeleteTarget" (Panic throws when a target
 * in use is deleted); EntitiesComponents.md "Operations" (remove of an absent
 * component does nothing). */
#include "flecs.h"
#include <stdio.h>
#include <stdlib.h>

static void on_abort(void) {
    printf("FAIL: merge panicked on the remove of a pair nobody had\n");
    exit(1);
}

int main(void) {
    ecs_os_set_api_defaults();
    ecs_os_api_t os_api = ecs_os_get_api();
    os_api.abort_ = on_abort;
    ecs_os_set_api(&os_api);

    ecs_world_t *world = ecs_mini();
    ecs_entity_t Rel = ecs_new(world);
    ecs_add_pair(world, Rel, EcsOnDeleteTarget, EcsPanic);
    ecs_entity_t Tag = ecs_new(world);
    ecs_entity_t tgt = ecs_new(world);
    ecs_entity_t e = ecs_new(world);

    /* Rel used in a pair once: creates the (Rel, *) record */
    ecs_entity_t other = ecs_new(world);
    ecs_entity_t holder = ecs_new(world);
    ecs_add_pair(world, holder, Rel, other);

    ecs_world_t *stage = ecs_get_stage(world, 0);
    ecs_delete(stage, tgt);          /* legal: nobody has (Rel, tgt) */
    ecs_add_id(stage, e, Tag);
    ecs_remove_pair(stage, e, Rel, tgt);
    ecs_merge(stage);

    int failed = 0;
    if (!ecs_is_alive(world, e) || !ecs_has_id(world, e, Tag)) {
        printf("FAIL: entity state after merge is wrong\n");
        failed = 1;
    }
    ecs_fini(world);
    return failed;
}
