/* Prediction F53 (second form, needs threads: link with -lpthread):
 * ecs_iter_skip, called from the callback of a multi_threaded system,
 * aborts as soon as the world has worker threads
 * (query/cache/change_detection.c 718: ecs_assert(it->next ==
 * ecs_query_next, ECS_INVALID_PARAMETER)); a release build sets the skip
 * flag on the worker iterator, whose flags ecs_worker_next overwrites, so
 * the skip is lost. The program is iter_changed_multi_threaded_system.c
 * with the callback calling ecs_iter_skip; see that file for the code path
 * and the documentation. An abort confirms the prediction. */
#define FLECS_LEAN_SKIP
#include "iter_changed_multi_threaded_system.c"
