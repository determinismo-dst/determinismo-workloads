/* Prediction F59 (form d): in an uncached query Position || Velocity(up),
 * a result of the up term that follows a duplicate carries the duplicate
 * check's Position id and table record: ecs_field_id says Position for an
 * entity that has no Position, and ecs_field reads Position from the
 * parent, which does not have it (a NULL table record).
 *
 *   x [Velocity {7,8}]; D = child of x with Position {1,2}; D2 = child of x
 *   with Tag (tables with (ChildOf, x) created in the order D's, D2's)
 *   query (uncached): Position || Velocity(up ChildOf)
 *   expected: D (Position, self); D2 (Velocity from x, {7,8})
 *   predicted: D2 comes with ecs_field_id = Position and source x; ecs_field
 *             crashes in a debug and a release build
 *
 * Code path (flecs v4.2.0): the up select (flecs_query_up_select,
 * eval_up.c 124-283) writes it->ids once per selected table (the select of
 * Velocity on x's table, flecs_query_select_w_id, eval.c 52-133) and yields
 * the down cache's tables (D's, then D2's) without writing it again
 * (264-280). For D's table select_or's duplicate check runs the Position
 * term (flecs_query_with, eval.c 150-249: flecs_query_set_match writes
 * it->ids, it->trs and it->columns), finds a duplicate and skips the
 * result without restoring anything (eval.c 1473-1477, 1488-1490). D2's result then
 * saves those values as its own and restores them after its duplicate
 * check (1454-1456, 1492-1495). flecs_field_shared (iter.c 206-246) reads
 * the source x's table: tr is D's record, Position is not in x's table,
 * flecs_component_get_table returns NULL (242-244).
 *
 * Documented: Queries.md "Or Operator" ("a single term can return results
 * of multiple types ... an application has to make sure that it is working
 * with the expected type": ecs_field_id is how it does); flecs.h
 * ecs_field_id. The control runs the up term alone (Velocity(up)).
 *
 * Build: the default debug build, and also -DNDEBUG. A crash confirms (the
 * handler prints FAIL and exits 1), and so does the wrong id. */
#include "flecs.h"
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct { float x, y; } Position;
typedef struct { float x, y; } Velocity;

static const char *where = "setup";

static void on_signal(int sig) {
    if (!strncmp(where, "control", 7)) {
        printf("INCONCLUSIVE: signal %d (%s)\n", sig, where);
        fflush(stdout);
        _Exit(2);
    }
    printf("FAIL: signal %d (%s)\n", sig, where);
    fflush(stdout);
    _Exit(1);
}

static int run(int control) {
    ecs_world_t *world = ecs_mini();
    ECS_COMPONENT(world, Position);
    ECS_COMPONENT(world, Velocity);
    ECS_TAG(world, Tag);

    ecs_entity_t x = ecs_insert(world, ecs_value(Velocity, {7, 8}));
    ecs_entity_t d = ecs_new_w_pair(world, EcsChildOf, x);
    ecs_set(world, d, Position, {1, 2});
    ecs_entity_t d2 = ecs_new_w_pair(world, EcsChildOf, x);
    ecs_add(world, d2, Tag);

    ecs_query_t *q;
    if (control) {
        q = ecs_query(world, {
            .terms = {{ ecs_id(Velocity), .src.id = EcsUp, .trav = EcsChildOf }},
            .cache_kind = EcsQueryCacheNone
        });
    } else {
        q = ecs_query(world, {
            .terms = {
                { ecs_id(Position), .oper = EcsOr },
                { ecs_id(Velocity), .src.id = EcsUp, .trav = EcsChildOf }
            },
            .cache_kind = EcsQueryCacheNone
        });
    }

    const char *name = control ? "control" : "prediction";
    int bad = 0, seen_d2 = 0;
    ecs_iter_t it = ecs_query_iter(world, q);
    while (ecs_query_next(&it)) {
        ecs_id_t id = ecs_field_id(&it, 0);
        ecs_entity_t src = ecs_field_src(&it, 0);
        for (int i = 0; i < it.count; i ++) {
            ecs_entity_t e = it.entities[i];
            const char *who = e == d ? "D" : e == d2 ? "D2" : "other";
            printf("  %s: %s, ecs_field_id %s, ecs_field_src %s\n", name, who,
                id == ecs_id(Position) ? "Position" :
                id == ecs_id(Velocity) ? "Velocity" : "other",
                src == x ? "x" : src == 0 ? "0" : "other");
            if (e == d2) {
                seen_d2 ++;
                if (id != ecs_id(Velocity) || src != x) {
                    bad ++;
                }
            }
        }
        if (it.entities[0] == d2) {
            where = control ? "control: ecs_field on D2" : "ecs_field on D2";
            fflush(stdout);
            const Velocity *v = ecs_field(&it, Velocity, 0);
            printf("    ecs_field: {%g, %g} (expected {7, 8})\n", v->x, v->y);
            if (v->x != 7 || v->y != 8) {
                bad ++;
            }
            where = name;
        }
    }
    if (seen_d2 != 1) {
        printf("  %s: D2 returned %d times\n", name, seen_d2);
        bad ++;
    }
    ecs_query_fini(q);
    ecs_fini(world);
    return bad;
}

int main(void) {
    signal(SIGSEGV, on_signal);
    signal(SIGBUS, on_signal);
    signal(SIGABRT, on_signal);

    where = "control";
    if (run(1)) {
        printf("INCONCLUSIVE: the control differs\n");
        return 2;
    }
    where = "prediction";
    if (run(0)) {
        printf("FAIL: D2's result names Position, or reads the wrong value\n");
        return 1;
    }
    return 0;
}
