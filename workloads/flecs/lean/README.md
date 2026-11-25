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

## Building and running

    lake update && lake build flecs-search FlecsLean
    .lake/build/bin/flecs-search cases                    # each C test's program in the model
    .lake/build/bin/flecs-search explore SEED N ENTS LEN  # random API programs

The replica's own fixes, when a round adds any, are switches off by default: the replica is flecs
as written.

## License

MIT, as flecs (copyright Sander Mertens; portions copyright Meta Platforms, Inc. and affiliates).
