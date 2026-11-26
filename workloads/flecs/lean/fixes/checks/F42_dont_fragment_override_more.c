/* Check for F42, beyond the finding's test. Defense: DontFragment, Inherit.
 * i1 and i2 IsA base, in one table; i1 overrides Defense; j IsA i1; k IsA i2.
 * Setting base's Defense: one self|up OnSet for i2 and one for k (source
 * base), none for i1 or j (their value is i1's); an up-only observer gets
 * the event for every instance of base (i1 and i2), as it does for a table
 * component. main returns 0 when every count matches. */
#include "flecs.h"
#include <stdio.h>

typedef struct { int value; } Defense;

typedef struct {
    ecs_entity_t entity[32];
    ecs_entity_t source[32];
    int count;
} Log;

static void on_set(ecs_iter_t *it) {
    Log *log = it->ctx;
    for (int i = 0; i < it->count; i ++) {
        if (log->count < 32) {
            log->entity[log->count] = it->entities[i];
            log->source[log->count] = ecs_field_src(it, 0);
            log->count ++;
        }
    }
}

static int events(const Log *log, ecs_entity_t e) {
    int n = 0;
    for (int i = 0; i < log->count; i ++) {
        if (log->entity[i] == e) n ++;
    }
    return n;
}

int main(void) {
    ecs_world_t *world = ecs_mini();
    ECS_COMPONENT(world, Defense);
    ecs_add_id(world, ecs_id(Defense), EcsDontFragment);
    ecs_add_pair(world, ecs_id(Defense), EcsOnInstantiate, EcsInherit);

    ecs_entity_t base = ecs_new_w_id(world, EcsPrefab);
    ecs_set(world, base, Defense, {50});
    ecs_entity_t i1 = ecs_new_w_pair(world, EcsIsA, base);
    ecs_entity_t i2 = ecs_new_w_pair(world, EcsIsA, base);
    ecs_set(world, i1, Defense, {7});
    ecs_entity_t j = ecs_new_w_pair(world, EcsIsA, i1);
    ecs_entity_t k = ecs_new_w_pair(world, EcsIsA, i2);
    if (ecs_get_table(world, i1) != ecs_get_table(world, i2)) {
        printf("INCONCLUSIVE: i1 and i2 are in different tables\n");
        return 2;
    }

    Log l = {0}, lu = {0};
    ecs_observer(world, { .query.terms = {{ ecs_id(Defense) }},
        .events = { EcsOnSet }, .callback = on_set, .ctx = &l });
    ecs_observer(world, { .query.terms = {{ ecs_id(Defense), .src.id = EcsUp, .trav = EcsIsA }},
        .events = { EcsOnSet }, .callback = on_set, .ctx = &lu });

    ecs_set(world, base, Defense, {60});
    const Defense *dj = ecs_get(world, j, Defense);
    const Defense *dk = ecs_get(world, k, Defense);
    printf("self|up: i1 %d, i2 %d, j %d, k %d; up: i1 %d, i2 %d; values j %d, "
        "k %d\n", events(&l, i1), events(&l, i2), events(&l, j), events(&l, k),
        events(&lu, i1), events(&lu, i2), dj ? dj->value : -1,
        dk ? dk->value : -1);
    int failed = events(&l, i1) || events(&l, i2) != 1 || events(&l, j) ||
        events(&l, k) != 1 || events(&lu, i1) != 1 || events(&lu, i2) != 1;
    printf(failed ? "FAIL\n" : "OK\n");
    ecs_fini(world);
    return failed;
}
