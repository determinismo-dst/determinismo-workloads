/* F54 check: the run callback of a system with a trivially cached query
 * iterates the same results with ecs_query_next, ecs_iter_next and a worker
 * iterator over it, and skipping a result with ecs_iter_skip leaves the
 * results unchanged. */
#include "flecs.h"
#include <stdio.h>

typedef struct { float x, y; } Position;
ECS_COMPONENT_DECLARE(Position);
static int mode, rows, is_query_next;

static void Run(ecs_iter_t *it) {
    is_query_next = it->next == ecs_query_next;
    if (mode == 0) {
        while (ecs_query_next(it)) rows += it->count;
    } else if (mode == 1) {
        while (ecs_iter_next(it)) { rows += it->count; ecs_iter_skip(it); }
    } else {
        ecs_iter_t wit = ecs_worker_iter(it, 0, 1);
        while (ecs_worker_next(&wit)) rows += wit.count;
    }
}

int main(void) {
    ecs_world_t *world = ecs_mini();
    ECS_IMPORT(world, FlecsPipeline);
    ECS_COMPONENT_DEFINE(world, Position);
    ECS_TAG(world, Tag);
    for (int i = 0; i < 5; i ++) ecs_insert(world, ecs_value(Position, {1, 1}));
    for (int i = 0; i < 3; i ++) {
        ecs_entity_t e = ecs_insert(world, ecs_value(Position, {1, 1}));
        ecs_add(world, e, Tag);
    }
    ecs_entity_t sys = ecs_system(world, {
        .entity = ecs_entity(world, { .name = "Sys" }),
        .query.terms = {{ .id = ecs_id(Position) }}, .run = Run });
    int counts[3], nexts[3];
    for (mode = 0; mode < 3; mode ++) {
        rows = 0;
        ecs_run(world, sys, 0, NULL);
        counts[mode] = rows; nexts[mode] = is_query_next;
    }
    printf("rows: ecs_query_next %d, ecs_iter_next + skip %d, worker %d; "
        "it->next == ecs_query_next %d %d %d\n", counts[0], counts[1],
        counts[2], nexts[0], nexts[1], nexts[2]);
    int ok = counts[0] == 8 && counts[1] == 8 && counts[2] == 8 &&
        nexts[0] && nexts[1] && nexts[2];
    printf(ok ? "OK\n" : "FAIL\n");
    ecs_fini(world);
    return ok ? 0 : 1;
}
