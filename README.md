# determinismo-workloads

Test programs for real systems, run with [determinismo](https://github.com/determinismo-dst/determinismo).
Each directory under `workloads/` is one system's test program (its nodes, scenarios and
properties), with what it found in its README.

| Workload | System | Scenarios |
|---|---|---|
| [datalevin](workloads/datalevin/README.md) | Datalevin 1.2.10, high availability (three servers) | `append` |
| [duckdb](workloads/duckdb/README.md) | DuckDB 2.0.0, embedded (Jepsen's local node) and over Quack, its client-server protocol | `append`, `fkey_register`, `trigger`, `variant` |
| [flecs](workloads/flecs/README.md) | Flecs v4.2.0, an in-memory entity component system, under a stress harness checked against a model | `stress` |
| [jank-interop](workloads/jank-interop/README.md) | jank's compiler and C++ interop (jank with coverage), Hegel generating the cases; the test program in jank | `interop`, `language`, `programs`, `collections`, `semantics`, `mixed` |

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
- Campaigns, `host/campaigns-here.sh` with `host/campaign.sh` and `campaigns.json`: each listed
  workload's campaign on a host of ours, against a serve of its own (its cores, memory limit and
  data), every two hours (a systemd timer) one campaign after another, 35 minutes each with all
  the serve's cores: one long run per campaign (a workload's
  scenario at a platform commit and a version of its files), each stretch resuming it where the
  last stopped. Each stretch's report at the reports' site (`runs/campaign-<workload>/`).
  GitHub's hosted runners cannot run them: within minutes of our VMs starting, the counters'
  interrupts, virtualized twice, took every runner down (Azure's and AWS-hosted alike).
- `.github/workflows/aws-hunt.yml` with `host/metal-hunt.sh`: a workload's hunt (DuckDB's by default) on an AWS
  bare-metal machine rented for it (a spot m5zn.metal, about a dollar an hour), from GitHub's
  hosted runner: launched from your determinismo base AMI through an OIDC role (no keys stored),
  set up by the platform's `infra/host/setup.sh`, the hunt run for the asked minutes, its counts
  in the log. A machine set up for a platform commit is saved as that commit's image, so later
  launches skip the setup; and it waits 15 minutes (`keep_minutes`) for the next run, which takes
  it as it is; untaken, it powers itself off, as it does past its deadline should a job die.
  While it runs, serve's own page live and read only for anyone (a tunnel to serve's
  `--public-listen` address; the link in the job's log and the reports' index). Each run's report:
  on its run page (the job summary), and whole, read only, at
  [determinismo-dst.github.io/determinismo-workloads](https://determinismo-dst.github.io/determinismo-workloads/)
  (one page a run). What to set up once is at the top of the workflow. Run by hand.

## License

MIT (LICENSE). Each system under test keeps its own license; its workload names it.
