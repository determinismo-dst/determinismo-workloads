/* Prediction F45, Parent hierarchy: the program of
 * prefab_child_auto_override_dont_fragment.c with the prefab child created
 * by ecs_new_w_parent. The TreeSpawner's first build turns the child's
 * `ECS_AUTO_OVERRIDE | Defense` into Defense in the cached table type
 * (flecs_prefab_spawner_build_type, addons/prefab/tree_spawner.c 33-42) and
 * flecs_table_find_or_create (tree_spawner.c 93) reaches the assert of
 * flecs_table_init (storage/table.c 249-259). An abort confirms the
 * prediction. */
#define FLECS_LEAN_PARENT_CHILD 1
#include "prefab_child_auto_override_dont_fragment.c"
