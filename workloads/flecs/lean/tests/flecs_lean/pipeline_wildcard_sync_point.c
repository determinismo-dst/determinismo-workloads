/* Prediction F16: the pipeline inserts no sync point between a system
 * annotated as writing a pair and a later system that reads an overlapping
 * pair, when one of the two uses a wildcard on the other side or uses Any:
 *   (a) [out] (Likes, *)()   then a system matching (*, Bob)
 *   (b) [out] (Likes, Bob)() then a system matching (Likes, _)
 * The reader runs before the writer's commands are merged and misses the
 * entity the writer gave (Likes, Bob).
 *
 * flecs_pipeline_get_write_state (pipeline.c 61-105) compares a read with
 * ecs_id_match(written, read) and ecs_id_match(read, written_wildcard).
 * ecs_id_match (id.c 12-84) treats only Wildcard as a wildcard and only on the
 * pattern side: (*, Bob) does not match (Likes, *), (Likes, *) does not match
 * (*, Bob), and (Likes, Bob) does not match (Likes, _).
 *
 * Documented: Systems.md "Sync points" ("When a pipeline sees a read for a
 * component for which commands could have been inserted, a sync point is
 * inserted before the system that reads"); Queries.md "Wildcards" (_ matches
 * any target, at most once). */
#include "flecs.h"
#include <stdio.h>
#include <stdlib.h>

/* A system entity in the OnUpdate phase (ecs_entity_desc_t has no `add`
 * field in v4.2, so the DependsOn pair is added explicitly). */
static ecs_entity_t phase_entity(ecs_world_t *world, const char *name) {
    ecs_entity_t e = ecs_entity(world, { .name = name });
    ecs_add_pair(world, e, EcsDependsOn, EcsOnUpdate);
    return e;
}

static ecs_entity_t Likes, Hates, Bob, Alice, e_new;
static int seen;

/* Round 4 correction: v4.2's it->world is the world itself, and a world
 * operation runs immediately (Manual.md: "Pass an explicit stage to enqueue
 * ECS operations. Pass the world to execute operations immediately ...
 * Observer and system iterators expose it->stage for queued operations").
 * In a readonly system that trips the readonly assert of flecs_table_ensure
 * (storage/table_graph.c 527) instead of queueing the command.  The
 * command is queued on it->stage, as the prediction assumes. */
static void Writer(ecs_iter_t *it) {
    ecs_add_pair(it->stage, e_new, Likes, Bob);
}

static void Reader(ecs_iter_t *it) {
    seen += it->count;
}

static int run(int variant) {
    ecs_world_t *world = ecs_init();
    Likes = ecs_new(world);
    Hates = ecs_new(world);
    Bob = ecs_new(world);
    Alice = ecs_new(world);
    e_new = ecs_new(world);
    seen = 0;

    ecs_id_t written, read;
    ecs_entity_t e0 = ecs_new(world);
    if (variant == 0) {
        written = ecs_pair(Likes, EcsWildcard);
        read = ecs_pair(EcsWildcard, Bob);
        ecs_add_pair(world, e0, Hates, Bob);    /* reader matches e0 already */
    } else {
        written = ecs_pair(Likes, Bob);
        read = ecs_pair(Likes, EcsAny);
        ecs_add_pair(world, e0, Likes, Alice);  /* reader matches e0 already */
    }

    ecs_system(world, {
        .entity = phase_entity(world, "Writer"),
        .query.terms = {
            { .id = written, .src.id = EcsIsEntity, .inout = EcsOut }
        },
        .callback = Writer
    });

    ecs_system(world, {
        .entity = phase_entity(world, "Reader"),
        .query.terms = {{ .id = read }},
        .callback = Reader
    });

    ecs_progress(world, 0);

    int failed = 0;
    if (seen != 2) {
        printf("FAIL (variant %c): reader saw %d entities in the first frame, "
            "expected 2 (no sync point after the writer)\n", 'a' + variant, seen);
        failed = 1;
    }
    ecs_fini(world);
    return failed;
}

int main(void) {
    int failed = run(0);
    failed |= run(1);
    return failed;
}
