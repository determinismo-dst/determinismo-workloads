/* F58 check: instances at depths 6, 7 (twice) and 12 of a prefab with
 * Parent children, deleted, then the prefab deleted: the number of tables
 * left after ecs_delete_empty_tables must be what instances at depths 1, 2
 * (twice) and 3 leave in another world (the control), and every instance
 * child must have had the prefab child's component. */
#include "flecs.h"
#include <stdio.h>
#include <signal.h>
#include <stdlib.h>

static void on_abort(int sig) {
    (void)sig;
    printf("FAIL: abort deleting the prefab\n");
    fflush(stdout);
    _Exit(1);
}

static int table_count(ecs_world_t *world) {
    ecs_delete_empty_tables(world, &(ecs_delete_empty_tables_desc_t){
        .delete_generation = 0, .time_budget_seconds = 0 });
    const ecs_world_info_t *info = ecs_get_world_info(world);
    return info->table_count;
}

static ecs_entity_t chain(ecs_world_t *world, int n) {
    ecs_entity_t p = ecs_new(world);
    for (int i = 1; i < n; i ++) p = ecs_new_w_parent(world, p, NULL);
    return p;
}

static int run(const int *depths, int *children_ok_out) {
    ecs_world_t *world = ecs_mini();
    ECS_TAG(world, Foo);
    ecs_entity_t base = ecs_new_w_id(world, EcsPrefab);
    ecs_entity_t c = ecs_new_w_parent(world, base, NULL);
    ecs_add(world, c, Foo);
    ecs_entity_t parents[4], inst[4];
    for (int i = 0; i < 4; i ++) parents[i] = chain(world, depths[i]);
    int before = table_count(world);
    int children_ok = 1;
    for (int i = 0; i < 4; i ++) {
        inst[i] = ecs_new_w_parent(world, parents[i], NULL);
        ecs_add_pair(world, inst[i], EcsIsA, base);
        ecs_iter_t it = ecs_children(world, inst[i]);
        int n = 0;
        while (ecs_children_next(&it)) {
            for (int j = 0; j < it.count; j ++) {
                n += ecs_has(world, it.entities[j], Foo);
            }
        }
        children_ok &= n == 1;
    }
    for (int i = 0; i < 4; i ++) ecs_delete(world, inst[i]);
    signal(SIGABRT, on_abort);
    ecs_delete(world, base);
    signal(SIGABRT, SIG_DFL);
    int after = table_count(world);
    ecs_fini(world);
    *children_ok_out = children_ok;
    return after - before;
}

int main(void) {
    static const int shallow[] = {1, 2, 2, 3}, deep[] = {6, 7, 7, 12};
    int ok_s = 0, ok_d = 0;
    int ds = run(shallow, &ok_s);
    int dd = run(deep, &ok_d);
    printf("tables left: depths 1-3 %d, depths 6-12 %d; instance children "
        "with Foo %d %d\n", ds, dd, ok_s, ok_d);
    if (!ok_s) { printf("INCONCLUSIVE: control\n"); return 2; }
    int ok = ok_d && dd == ds;
    printf(ok ? "OK\n" : "FAIL\n");
    return ok ? 0 : 1;
}
