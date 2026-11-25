# A Lean replica of flecs

flecs (SanderMertens/flecs, the C entity component system, MIT) at its latest release, v4.2.0,
replicated in Lean 4 function by function from its source, blind (from the code, its docs and its
own tests only), and searched for departures from what its docs promise, under every order of API
calls and every interleaving of worker threads within bounds.

## Round 1

[REPORT.md](REPORT.md): 14 predictions, F1-F14, each with a minimal API program, the property and
its source in flecs's docs, the code path at v4.2.0, the search's story and tape, and a C test.
Storage (the entity index, tables, the table graph), deferred commands and stages, hooks and
observers, relationships and their cleanup policies are replicated; queries, systems and the
pipeline, and prefabs aren't yet.

The C tests ([tests/flecs_lean/](tests/flecs_lean/)) each return 0 when flecs behaves as
documented, built with `distr/flecs.c` and asserts on: a failure confirms its prediction. None
has run on the real flecs yet.

## On the real flecs

Round 1's 20 C tests on flecs v4.2.0 (the latest release), through determinismo-ci, flecs compiled
with coverage, 3 timelines each, every verdict the same in all 3
([validation/round-1-evidence.txt](validation/round-1-evidence.txt)):
- 13 of the 14 predictions behave as predicted (19 of 20 tests):
  - F1, F6, F7, F9, F10, F11, F12, F13 and F14 with the wrong values or callbacks their tests check
    for;
  - F4, F5 and F8 by flecs's own internal-error asserts (`ECS_INTERNAL_ERROR`: its invariants, not
    a misuse check);
  - F3 aborts the merge as predicted, at another assert than the one predicted:
    `ecs_make_alive_id`'s `!ecs_exists(world, t)` (`ECS_INVALID_PARAMETER`), not "second element
    of pair is not alive".
- F2 (the batched remove with a Panic relationship) passes: flecs behaves as documented there.
- F13 is the 16-bit generation wrapping by design, a defect only against the docs' "a deleted
  handle is not alive"; F14 the report marks lower confidence (the docs show the order only in a
  diagram). The behaviors are confirmed either way.
- Not yet searched against flecs's issues.

## Building and running

    lake update && lake build flecs-search FlecsLean
    .lake/build/bin/flecs-search cases                    # each C test's program in the model
    .lake/build/bin/flecs-search explore SEED N ENTS LEN  # random API programs

The replica's own fixes, when a round adds any, are switches off by default: the replica is flecs
as written.

## License

MIT, as flecs (copyright Sander Mertens; portions copyright Meta Platforms, Inc. and affiliates).
