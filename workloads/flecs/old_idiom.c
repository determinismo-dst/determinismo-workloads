// SPDX-License-Identifier: MIT
// The old idiom, natively (README, "Found: master's old-idiom hazard"): a system deletes through
// it->world while it iterates. v4.2.0 with FLECS_SANITIZE: e5 and e6 keep 2 and 3 (1 and 2 right).
//   cc -std=gnu11 -DFLECS_SANITIZE -I <flecs>/distr old_idiom.c <flecs>/distr/flecs.c -o old_idiom
#include "flecs.h"
#include <stdio.h>
typedef struct { int value; } Health;
ECS_COMPONENT_DECLARE(Health);
static void Decay(ecs_iter_t *it) {
  Health *h = ecs_field(it, Health, 0);
  for (int i = 0; i < it->count; i++) {
    h[i].value -= 1;
    if (h[i].value <= 0) ecs_delete(it->world, it->entities[i]);  /* the old idiom */
  }
}
int main(void) {
  ecs_world_t *world = ecs_init();
  ECS_COMPONENT_DEFINE(world, Health);
  ECS_SYSTEM(world, Decay, EcsOnUpdate, Health);
  int start[6] = {1, 2, 3, 1, 2, 3};
  ecs_entity_t e[6];
  for (int i = 0; i < 6; i++) { e[i] = ecs_new(world); ecs_set(world, e[i], Health, {start[i]}); }
  ecs_progress(world, 0);
  for (int i = 0; i < 6; i++) {
    const Health *h = ecs_is_alive(world, e[i]) ? ecs_get(world, e[i], Health) : NULL;
    printf("e%d: %s %d (expected %s %d)\n", i + 1, ecs_is_alive(world, e[i]) ? "alive" : "deleted", h ? h->value : -1,
           start[i] - 1 > 0 ? "alive" : "deleted", start[i] - 1);
  }
  return ecs_fini(world);
}
