/* Prediction F59 (forms b and a): in an uncached query whose Or chain has an
 * up term before a self term, the self term's results keep field state
 * that the up term wrote: a wrong ecs_field_src and a value read from
 * another entity, or a read of entity 0.
 *
 *   query (uncached): Position(up ChildOf) || Velocity
 *   form b: p [Position, Velocity {100,200}], c ChildOf p [Velocity],
 *           e [Velocity {3,4}]; tables with Velocity created in the order
 *           c's, e's, p's
 *     expected: c (Position from p), e (Velocity, source 0, {3,4}),
 *               p (Velocity, source 0, {100,200})
 *     predicted: e and p come with ecs_field_src = p, columns[0] = -1 and
 *               the up flag set; ecs_field(Velocity) for e reads p's
 *               {100,200}
 *   form a: p [Position], c ChildOf p, e [Velocity {3,4}]
 *     predicted: e comes with source 0, columns[0] = -1, the up flag set;
 *               ecs_field(Velocity) takes the shared path with source 0:
 *               a debug build asserts "entity 0 does not exist", a release
 *               build reads a NULL table.
 *
 * Code path (flecs v4.2.0): flecs_query_select_or (query/engine/eval.c
 * 1390-1508) yields a later term's result after checking the earlier terms
 * against it, and then restores only it->ids, it->trs and it->columns of
 * the field (1492-1495). The up term's select (flecs_query_up_select,
 * eval_up.c 124-283) sets it->sources to the traversable entity (96-99) and
 * the field's up_fields bit (flecs_set_source_set_flag, 280); when it is
 * exhausted the source is reset (205-207) but the bit stays. The self
 * term's select computes its column with that bit (flecs_query_it_set_tr,
 * eval_utils.c 359-369: -1 when the bit or a source is set). In form b,
 * the duplicate check of c's table runs the up term, whose success writes
 * the source p (flecs_query_up_set_fields, eval_up.c 285-301); the result
 * is skipped without restoring anything (eval.c 1473-1477, 1488-1490), and e and p
 * then come with source p. ecs_field (iter.c 112-160) goes to
 * flecs_field_shared (206-246), which reads the source's table.
 *
 * Documented: Queries.md "Source": ecs_field_src "Returns 0, meaning entity
 * is stored in it.entities" for a $this match; flecs.h ecs_field_src: "the
 * entity on which the field was matched"; Queries.md "Or Operator": "We can
 * only use ecs_field if the field type is the same for all results"
 * (Position and Velocity are both {float x, y} here). Two controls run
 * first: the self term first (Velocity || Position(up)), and form a's world
 * without the child (the up term returns nothing).
 *
 * Build: the default debug build, and also -DNDEBUG. A crash or an abort in
 * form a confirms (the handler prints FAIL and exits 1). main returns 0
 * when every result is as documented. */
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

static ecs_query_t* make_query(ecs_world_t *world, int self_first) {
    ecs_entity_t P = ecs_lookup(world, "Position");
    ecs_entity_t V = ecs_lookup(world, "Velocity");
    if (self_first) {
        return ecs_query(world, {
            .terms = {
                { V, .oper = EcsOr },
                { P, .src.id = EcsUp, .trav = EcsChildOf }
            },
            .cache_kind = EcsQueryCacheNone
        });
    }
    return ecs_query(world, {
        .terms = {
            { P, .src.id = EcsUp, .trav = EcsChildOf, .oper = EcsOr },
            { V }
        },
        .cache_kind = EcsQueryCacheNone
    });
}

/* Prints every result; returns the number of results that differ from the
 * documented ones. expect_src(e) gives the expected source of entity e. */
static int iterate(ecs_world_t *world, ecs_query_t *q, const char *name,
    ecs_entity_t p, int read_fields)
{
    ecs_entity_t V = ecs_lookup(world, "Velocity");
    int bad = 0;
    ecs_iter_t it = ecs_query_iter(world, q);
    while (ecs_query_next(&it)) {
        ecs_id_t id = ecs_field_id(&it, 0);
        ecs_entity_t src = ecs_field_src(&it, 0);
        for (int i = 0; i < it.count; i ++) {
            ecs_entity_t e = it.entities[i];
            int is_v = id == V;
            ecs_entity_t want = is_v ? 0 : p;
            printf("  %s: entity %u, field %s, ecs_field_src %u (expected %u),"
                " columns[0] %d, up flag %d\n", name, (unsigned)e,
                is_v ? "Velocity" : "Position", (unsigned)src,
                (unsigned)want, it.columns[0], (int)(it.up_fields & 1));
            if (src != want) {
                bad ++;
            }
            if (is_v && read_fields) {
                where = "ecs_field(Velocity) on a self result";
                fflush(stdout);
                const Velocity *v = ecs_field(&it, Velocity, 0);
                const Velocity *own = ecs_get_id(world, e, V);
                const Velocity *got = ecs_field_is_self(&it, 0) ? &v[i] : v;
                printf("    ecs_field: {%g, %g}; the entity's own Velocity "
                    "{%g, %g}\n", got->x, got->y, own->x, own->y);
                if (got->x != own->x || got->y != own->y) {
                    bad ++;
                }
                where = name;
            }
        }
    }
    return bad;
}

int main(void) {
    signal(SIGSEGV, on_signal);
    signal(SIGBUS, on_signal);
    signal(SIGABRT, on_signal);

    /* controls, in form a's world */
    {
        ecs_world_t *world = ecs_mini();
        ECS_COMPONENT(world, Position);
        ECS_COMPONENT(world, Velocity);
        ecs_entity_t p = ecs_insert(world, ecs_value(Position, {1, 2}));
        ecs_new_w_pair(world, EcsChildOf, p);
        ecs_insert(world, ecs_value(Velocity, {3, 4}));

        where = "control: Velocity || Position(up)";
        ecs_query_t *q = make_query(world, 1);
        int bad = iterate(world, q, "control self first", p, 1);
        ecs_query_fini(q);
        ecs_fini(world);
        if (bad) {
            printf("INCONCLUSIVE: the self-first control differs\n");
            return 2;
        }
    }
    {
        ecs_world_t *world = ecs_mini();
        ECS_COMPONENT(world, Position);
        ECS_COMPONENT(world, Velocity);
        ecs_entity_t p = ecs_insert(world, ecs_value(Position, {1, 2}));
        ecs_insert(world, ecs_value(Velocity, {3, 4}));
        where = "control: Position(up) || Velocity, no child";
        ecs_query_t *q = make_query(world, 0);
        int bad = iterate(world, q, "control no child", p, 1);
        ecs_query_fini(q);
        ecs_fini(world);
        if (bad) {
            printf("INCONCLUSIVE: the no-child control differs\n");
            return 2;
        }
    }

    int failed = 0;

    /* form b: the duplicate check writes the source */
    {
        ecs_world_t *world = ecs_mini();
        ECS_COMPONENT(world, Position);
        ECS_COMPONENT(world, Velocity);
        ecs_entity_t p = ecs_insert(world, ecs_value(Position, {1, 2}));
        ecs_entity_t c = ecs_new_w_pair(world, EcsChildOf, p);
        ecs_set(world, c, Velocity, {10, 20});
        ecs_entity_t e = ecs_insert(world, ecs_value(Velocity, {3, 4}));
        ecs_set(world, p, Velocity, {100, 200});
        printf("form b: p %u, c %u, e %u\n", (unsigned)p, (unsigned)c,
            (unsigned)e);

        where = "form b";
        ecs_query_t *q = make_query(world, 0);
        int bad = iterate(world, q, "form b", p, 1);
        ecs_query_fini(q);
        ecs_fini(world);
        if (bad) {
            printf("FAIL: form b: %d result(s) name the wrong source or "
                "read another entity's Velocity\n", bad);
            failed = 1;
        }
    }

    /* form a: the up flag stays set; the read goes to entity 0 */
    {
        ecs_world_t *world = ecs_mini();
        ECS_COMPONENT(world, Position);
        ECS_COMPONENT(world, Velocity);
        ecs_entity_t p = ecs_insert(world, ecs_value(Position, {1, 2}));
        ecs_entity_t c = ecs_new_w_pair(world, EcsChildOf, p);
        ecs_entity_t e = ecs_insert(world, ecs_value(Velocity, {3, 4}));
        printf("form a: p %u, c %u, e %u\n", (unsigned)p, (unsigned)c,
            (unsigned)e);

        where = "form a";
        ecs_query_t *q = make_query(world, 0);
        int bad = iterate(world, q, "form a", p, 1);
        ecs_query_fini(q);
        ecs_fini(world);
        if (bad) {
            printf("FAIL: form a: %d result(s) differ\n", bad);
            failed = 1;
        }
    }

    return failed;
}
