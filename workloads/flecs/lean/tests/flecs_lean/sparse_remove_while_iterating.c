/* Prediction F60: removing a DontFragment tag while iterating a query on it
 * skips or repeats entities, depending on the iterator.
 *
 *   part A (the trivial sparse search): 2100 entities with the DontFragment
 *     tag Df; query "Df" (uncached); the loop removes Df from every entity
 *     of each result.
 *     expected: 2100 entities returned, none left with Df
 *     predicted: 1076 returned; 1024 entities (the last ones created) keep
 *       Df and are never returned
 *     control: the same loop over "Df, !Unused" (not trivial: the VM's
 *       sparse select) returns all 2100.
 *   part B (the VM's sparse select): a0, a1 in [Position], b0, b1 in
 *     [Position, Tag]; Df added to a0, b0, a1, b1 in that order; query
 *     "Df, Position" (uncached); after the first result the loop removes Df
 *     from a0, which has not been returned.
 *     expected: b1, a1, b0 once each, a0 never
 *     predicted: b1 twice (the last result is the range b0, b1)
 *
 * Code path (flecs v4.2.0): a DontFragment id keeps its entities in a
 * sparse set; a removal swaps the removed id with the last one
 * (flecs_sparse_remove, datastructures/sparse.c 398-...;
 * flecs_sparse_swap_dense, 177-191) and moves no entity between tables.
 * The trivial sparse search (flecs_query_trivial_sparse_search,
 * query/engine/eval_sparse.c 506-618; chosen for an all-DontFragment self
 * query, validator.c 1902-1942) walks the dense array forward in batches of
 * FLECS_QUERY_SPARSE_BATCH_SIZE (1024, query/types.h 373), so the ids
 * swapped into the slots it passed are never visited. The VM's sparse
 * select (flecs_query_sparse_select_id, eval_sparse.c 121-182) walks
 * backward, which keeps the remove-the-current-result loop correct, but an
 * id removed from an unvisited slot takes the last id, already returned.
 *
 * Documented: flecs's own DontFragment_add_to_self_while_iterate changes
 * the DontFragment ids of the current result while iterating, without
 * deferring (a DontFragment change moves no entity); Systems.md "Immediate
 * systems": operations through the iterator's world execute immediately,
 * only "operations on the iterated over entity must still be deferred";
 * Queries.md "Iteration": table locking exists so that changes do not
 * cause "iterating an entity twice, or missing an entity".
 *
 * Build: the default debug build. main returns 0 when every entity is
 * returned once. */
#include "flecs.h"
#include <stdio.h>
#include <stdlib.h>

#define N 2100

typedef struct { float x, y; } Position;

static int part_a(int use_vm, int *left) {
    ecs_world_t *world = ecs_mini();
    ecs_entity_t Df = ecs_new(world);
    ecs_add_id(world, Df, EcsDontFragment);
    ecs_entity_t Unused = ecs_new(world);

    static ecs_entity_t ents[N];
    for (int i = 0; i < N; i ++) {
        ents[i] = ecs_new(world);
        ecs_add_id(world, ents[i], Df);
    }

    ecs_query_t *q;
    if (use_vm) {
        q = ecs_query(world, {
            .terms = {{ Df }, { Unused, .oper = EcsNot }},
            .cache_kind = EcsQueryCacheNone
        });
    } else {
        q = ecs_query(world, {
            .terms = {{ Df }},
            .cache_kind = EcsQueryCacheNone
        });
    }

    int visits = 0;
    ecs_iter_t it = ecs_query_iter(world, q);
    while (ecs_query_next(&it)) {
        for (int i = 0; i < it.count; i ++) {
            visits ++;
            ecs_remove_id(world, it.entities[i], Df);
        }
    }

    *left = 0;
    for (int i = 0; i < N; i ++) {
        *left += ecs_has_id(world, ents[i], Df);
    }

    ecs_query_fini(q);
    ecs_fini(world);
    return visits;
}

int main(void) {
    int left = 0;
    int v_vm = part_a(1, &left);
    printf("control (Df, !Unused: the VM's select): %d returned, %d left "
        "with Df\n", v_vm, left);
    if (v_vm != N || left) {
        printf("INCONCLUSIVE: the control did not return every entity\n");
        return 2;
    }

    int failed = 0;
    int v = part_a(0, &left);
    printf("part A (Df: the trivial sparse search): %d returned, %d left "
        "with Df (expected %d, 0)\n", v, left, N);
    if (v != N || left) {
        printf("FAIL: the trivial sparse search skipped %d entities\n",
            N - v);
        failed = 1;
    }

    {
        ecs_world_t *world = ecs_mini();
        ECS_COMPONENT(world, Position);
        ECS_TAG(world, Tag);
        ecs_entity_t Df = ecs_new(world);
        ecs_add_id(world, Df, EcsDontFragment);

        ecs_entity_t a0 = ecs_new_w(world, Position);
        ecs_entity_t b0 = ecs_new_w(world, Position);
        ecs_add(world, b0, Tag);
        ecs_entity_t a1 = ecs_new_w(world, Position);
        ecs_entity_t b1 = ecs_new_w(world, Position);
        ecs_add(world, b1, Tag);
        ecs_add_id(world, a0, Df);
        ecs_add_id(world, b0, Df);
        ecs_add_id(world, a1, Df);
        ecs_add_id(world, b1, Df);

        ecs_query_t *q = ecs_query(world, {
            .terms = {{ Df }, { ecs_id(Position) }},
            .cache_kind = EcsQueryCacheNone
        });

        ecs_entity_t ent[4] = { a0, b0, a1, b1 };
        int seen[4] = {0}, results = 0;
        ecs_iter_t it = ecs_query_iter(world, q);
        while (ecs_query_next(&it)) {
            printf("part B result %d:", results);
            for (int i = 0; i < it.count; i ++) {
                printf(" %u", (unsigned)it.entities[i]);
                for (int j = 0; j < 4; j ++) {
                    if (ent[j] == it.entities[i]) seen[j] ++;
                }
            }
            printf("\n");
            if (results == 0) {
                ecs_remove_id(world, a0, Df);
            }
            results ++;
        }
        printf("part B: a0 %d, b0 %d, a1 %d, b1 %d (expected 0 or 1 for a0, "
            "1 for the others)\n", seen[0], seen[1], seen[2], seen[3]);
        if (seen[1] != 1 || seen[2] != 1 || seen[3] != 1 || seen[0] > 1) {
            printf("FAIL: the VM's sparse select returned an entity twice "
                "or missed one\n");
            failed = 1;
        }
        ecs_query_fini(q);
        ecs_fini(world);
    }

    return failed;
}
