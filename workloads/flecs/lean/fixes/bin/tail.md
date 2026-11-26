
## Findings without a fix

Each of these has its section above, with the code path and what a fix would need.

- **F9** (a queued set written in place is lost when the component goes away before the merge). The in-place write is intended: flecs's own tests assert it, for example `Commands.defer_set` ("set will not be deferred if the component exists").
  - Always queueing the value turns the finding's tests green, but breaks 10 of flecs's tests.
  - Keeping the in-place write and fixing the loss needs a new command state, handled in both the batched and the unbatched merge.
  - It is a design decision, or a documentation change: Manual.md says queued changes become visible at the merge.
- **F13** (the generation wraps after 2^16 recycles). The 16-bit generation is part of the public id layout, and any width wraps. The documentation should say that a stale handle can test alive again after 65,536 recycles of its id.
- **F14** (`on_add` hooks don't see the component on the entity). Hooks run inside `flecs_table_move`, before the entity's record points at the new table.
  - Making the entity visible to the hook needs a two-pass move: data first, then hooks, after the record is updated. `on_remove` hooks must keep seeing the old state.
  - The documentation says nothing in words. It could say that the hook must use its iterator.
- **F28** (instance children outside the active entity range). flecs's own test `World.range_prefab_spawn_deferred_after_range_switch` requires instance children next to their instance, outside the active range. The change the finding's test asks for breaks it, so the documentation of ranges should change instead.
- **F30** (a table leaving the cache during an iteration makes the iterator skip another one). The cache iterator walks vectors by index and holds pointers that calls made during the iteration move or free. There is no small fix. A fix needs one of:
  - cache changes deferred while a cached query is iterated;
  - iterators that resynchronize, with order-preserving removals;
  - a documented rule that such calls must be deferred during a C iteration.
- **F35** (cascade regrouping during an iteration returns a table twice, or frees the group being iterated). The same design question as F30, for groups.
- **F37** (a system whose commands reorder the phases makes the pipeline skip systems in that frame).
  - The tried fix resumed at the first system that had not run yet. It broke 9 of flecs's Pipeline tests, which require a system that joins the schedule mid-frame behind the current position to wait for the next frame.
  - Telling the two cases apart needs per-system pending state carried across rebuilds, readable by the worker threads.
  - It is a redesign of the resume protocol and a decision for flecs.
