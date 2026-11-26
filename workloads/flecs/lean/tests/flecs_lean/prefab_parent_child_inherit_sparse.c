/* Prediction F52 (second form): instantiating a prefab whose Parent-storage
 * child has a Sparse component with the (OnInstantiate, Inherit) trait
 * aborts at flecs_instantiate_sparse's ecs_assert(dst_ptr != NULL)
 * (addons/prefab/instantiate.c 119-124). See
 * prefab_parent_child_inherit_on_set_hook.c for the code path and the
 * documentation; this file builds that program with Velocity Sparse and no
 * hook. An abort confirms the prediction (the handler prints FAIL and exits
 * 1). */
#define FLECS_LEAN_SPARSE
#include "prefab_parent_child_inherit_on_set_hook.c"
