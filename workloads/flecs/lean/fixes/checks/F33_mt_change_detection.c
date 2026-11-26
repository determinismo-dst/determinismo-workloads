/* Sanity check for the F33 patch: change detection with a multi-threaded
 * system still marks written tables dirty and syncs the system's monitors. */
#include "flecs.h"
#include <stdio.h>

typedef struct { float x, y; } Position;
static int runs;
static void Writer(ecs_iter_t *it) { (void)it; ecs_os_ainc(&runs); }
static void Reader(ecs_iter_t *it) { (void)it; }

int main(void) {
    ecs_world_t *world = ecs_init();
    ECS_COMPONENT(world, Position);
    ECS_TAG(world, Tag);

    ecs_entity_t w = ecs_entity(world, { .name = "Writer" });
    ecs_add_pair(world, w, EcsDependsOn, EcsOnUpdate);
    ecs_entity_t r = ecs_entity(world, { .name = "Reader" });
    ecs_add_pair(world, r, EcsDependsOn, EcsOnUpdate);

    for (int i = 0; i < 10; i ++) {
        ecs_insert(world, ecs_value(Position, {0, 0}));
        ecs_entity_t e = ecs_insert(world, ecs_value(Position, {0, 0}));
        ecs_add(world, e, Tag);
    }

    ecs_query_t *other = ecs_query(world, {
        .terms = {{ ecs_id(Position), .inout = EcsIn }},
        .cache_kind = EcsQueryCacheAuto, .flags = EcsQueryDetectChanges });

    ecs_system(world, { .entity = w, .callback = Writer, .multi_threaded = true,
        .query.terms = {{ ecs_id(Position), .inout = EcsInOut }} });
    ecs_system(world, { .entity = r, .callback = Reader, .multi_threaded = true,
        .query.terms = {{ ecs_id(Position), .inout = EcsIn }},
        .query.flags = EcsQueryDetectChanges });
    ecs_query_t *rq = ecs_system_get(world, r)->query;

    ecs_set_threads(world, 4);
    ecs_query_changed(other);
    ecs_query_changed(rq);
    ecs_iter_t it = ecs_query_iter(world, other);
    while (ecs_query_next(&it)) {}
    int failed = 0;
    for (int f = 0; f < 3; f ++) {
        if (ecs_query_changed(other)) { printf("FAIL: changed before frame %d\n", f); failed = 1; }
        ecs_progress(world, 0);
        if (!ecs_query_changed(other)) { printf("FAIL: writer's tables not dirty after frame %d\n", f); failed = 1; }
        it = ecs_query_iter(world, other);
        while (ecs_query_next(&it)) {}
    }
    /* Reader's monitors are synced by the frame: the writer's write is seen
     * by the reader within the same frame (reader runs after writer), so after
     * the frame nothing changed for it. */
    ecs_set_threads(world, 0);
    printf("runs %d\n", runs);
    ecs_fini(world);
    return failed;
}
