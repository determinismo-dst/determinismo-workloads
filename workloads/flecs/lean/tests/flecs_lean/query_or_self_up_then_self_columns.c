/* Prediction F59 (form c): in an uncached query Position(self|up) ||
 * Velocity, a result of the Velocity term after a result that Position
 * reached through up traversal aborts a debug build in ecs_query_next
 * (flecs_iter_assert_columns: "it->columns[0]=-1 does not match expected
 * 0"); a release build returns columns[0] = -1 with source 0, and
 * ecs_field reads entity 0's record.
 *
 *   p [Position {1,2}], c ChildOf p, e [Velocity {3,4}]
 *   query (uncached): Position(self|up ChildOf) || Velocity
 *   expected: p (Position, self), c (Position from p), e (Velocity, self,
 *             columns[0] = 0)
 *
 * Code path (flecs v4.2.0): the self|up select (flecs_query_up_select,
 * eval_up.c 124-283) yields p's table with the field's up_fields bit reset,
 * then c's table with the bit set (280). It is exhausted with the bit set.
 * The Velocity term's select computes the column with the bit set: -1
 * (flecs_query_it_set_tr, eval_utils.c 359-369). select_or saves ids, trs
 * and columns (eval.c 1454-1456) and runs the duplicate check, whose
 * flecs_query_self_up_with resets the bit before failing (eval_up.c
 * 557); then it restores the saved column -1 (1492-1495). The bit is
 * now clear, the source 0 and tr set, so flecs_iter_assert_columns
 * (eval_iter.c 253-273) expects tr->column.
 *
 * Documented: Queries.md "Or Operator"; flecs.h ecs_field_column ("Fields
 * matched on other tables will return -1", so a $this match has a column).
 * The control (Velocity || Position(self|up)) runs first.
 *
 * Build: the default debug build (an abort confirms), and also -DNDEBUG (a
 * crash in ecs_field confirms, or columns[0] = -1 for e). The handler
 * prints FAIL and exits 1. */
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

static int run(int self_first) {
    ecs_world_t *world = ecs_mini();
    ECS_COMPONENT(world, Position);
    ECS_COMPONENT(world, Velocity);
    ecs_entity_t p = ecs_insert(world, ecs_value(Position, {1, 2}));
    ecs_new_w_pair(world, EcsChildOf, p);
    ecs_entity_t e = ecs_insert(world, ecs_value(Velocity, {3, 4}));

    ecs_query_t *q;
    if (self_first) {
        q = ecs_query(world, {
            .terms = {
                { ecs_id(Velocity), .oper = EcsOr },
                { ecs_id(Position), .src.id = EcsSelf|EcsUp, .trav = EcsChildOf }
            },
            .cache_kind = EcsQueryCacheNone
        });
    } else {
        q = ecs_query(world, {
            .terms = {
                { ecs_id(Position), .src.id = EcsSelf|EcsUp, .trav = EcsChildOf,
                  .oper = EcsOr },
                { ecs_id(Velocity) }
            },
            .cache_kind = EcsQueryCacheNone
        });
    }

    int bad = 0;
    ecs_iter_t it = ecs_query_iter(world, q);
    where = self_first ? "control: ecs_query_next" : "ecs_query_next";
    while (ecs_query_next(&it)) {
        int is_v = ecs_field_id(&it, 0) == ecs_id(Velocity);
        printf("  %s: entity %u, field %s, ecs_field_src %u, columns[0] %d, "
            "up flag %d\n", self_first ? "control" : "prediction",
            (unsigned)it.entities[0], is_v ? "Velocity" : "Position",
            (unsigned)ecs_field_src(&it, 0), it.columns[0],
            (int)(it.up_fields & 1));
        if (is_v) {
            if (it.columns[0] < 0) {
                bad ++;
            }
            where = "ecs_field(Velocity)";
            fflush(stdout);
            const Velocity *v = ecs_field(&it, Velocity, 0);
            printf("    ecs_field: {%g, %g}\n", v->x, v->y);
            if (it.entities[0] != e || v->x != 3) {
                bad ++;
            }
            where = "ecs_query_next";
        }
        fflush(stdout);
    }
    ecs_query_fini(q);
    ecs_fini(world);
    return bad;
}

int main(void) {
    signal(SIGSEGV, on_signal);
    signal(SIGBUS, on_signal);
    signal(SIGABRT, on_signal);

    if (run(1)) {
        printf("INCONCLUSIVE: the control differs\n");
        return 2;
    }

    if (run(0)) {
        printf("FAIL: the Velocity result has no column\n");
        return 1;
    }
    return 0;
}
