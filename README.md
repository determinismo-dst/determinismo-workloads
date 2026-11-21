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

The program lands in `zig-out/bin/`. Workloads are found by their layout, nothing to list:
`workloads/<name>/workload/` is a Clojure program (the platform's `determinismo.workload`), and
`workloads/<name>/<name>_test.zig` a Zig one (the platform's modules: `determinismo`, `tcp`,
`resp`, `nrepl`, `pg`); either builds as `<name>-test`.

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
- `.github/workflows/probe.yml`: what GitHub's hosted runners offer determinismo's hypervisor (run
  by hand).
- `.github/workflows/hunt.yml` with `host/hunt.sh`: an example of a continuous hunt on your own
  determinismo host. Each tick (every 15 minutes) asks the host, over SSH with a key limited to
  that one command (`restrict,command="…/hunt.sh"` in its `authorized_keys`), to keep Datalevin's
  hunt going: its run resumed, a new run when the last finished or the deployed build changed, or
  stopped when the host is busy with other runs. Off unless the repository variable `HUNT` is
  `on` and the secrets `HUNT_HOST`, `HUNT_USER`, `HUNT_SSH_KEY` and `HUNT_KNOWN_HOSTS` are set;
  never on pull requests; its log holds counts only.

## License

MIT (LICENSE). Each system under test keeps its own license; its workload names it.
