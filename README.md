# determinismo-workloads

Test programs for real systems, run with [determinismo](https://github.com/determinismo-dst/determinismo).
Each directory under `workloads/` is one system's test program (its nodes, scenarios and
properties), with what it found in its README.

| Workload | System | Scenarios |
|---|---|---|
| [datalevin](workloads/datalevin/README.md) | Datalevin 1.2.10, high availability (three servers) | `append` |

## Build

With Zig 0.17.0, the platform a pinned dependency (`build.zig.zon`):

```sh
zig build datalevin-test
```

The program lands in `zig-out/bin/`.

## Run

On a determinismo host (bare-metal x86-64 Linux with KVM), from this directory (the workloads
name their Dockerfiles from here):

```sh
determinismo explore --program zig-out/bin/datalevin-test --scenario append --branches 8
```

Or through serve, as a hunt:

```sh
curl -X POST localhost:7878/runs -d '{"program": "zig-out/bin/datalevin-test", "scenario": "append",
  "time_budget": "2h", "timeline": "600s", "memory_mib": 10240, "branching": "tree"}'
```

## CI

- `.github/workflows/build.yml`: builds every workload on each push and pull request.
- `.github/workflows/hunt.yml`: Datalevin's hunt on a determinismo host, started or resumed on a
  schedule; the host decides whether it has room (a host busy with other runs skips it), and the
  job's log holds counts only. It needs the repository's secrets (the host, a key limited to the
  hunt's one command), so it never runs for pull requests.

## License

MIT (LICENSE). Each system under test keeps its own license; its workload names it.
