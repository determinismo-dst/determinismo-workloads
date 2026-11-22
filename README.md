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
  data), one campaign after another, each with all the serve's cores for the stretch's minutes
  (by hand, or every two hours by a timer on that host; none scheduled now): one long run per
  campaign (a workload's
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

## Hunts on your own AWS account

`aws-hunt.yml` runs a workload's hunt on a bare-metal machine it rents for the run (spot: about
$1 an hour for `c5.metal`'s 48 cores or `m5zn.metal`'s 24; determinismo runs its own KVM on the
hardware, so no virtual machine will do). Once, in a fork or copy of this repository:

1. The stack (`aws/hunt-setup.yaml`): GitHub's OIDC provider, a role only your repository's
   main branch may take (no access keys), and the security group `determinismo-ci`.
   ```
   aws cloudformation deploy --region us-east-1 --stack-name determinismo-ci \
     --template-file aws/hunt-setup.yaml --capabilities CAPABILITY_IAM \
     --parameter-overrides GitHubOwner=<you> GitHubRepository=<this repository>
   ```
   (`CreateOidcProvider=false` if your account has GitHub's provider already.)
2. The repository's secrets and variable:
   ```
   gh secret set AWS_ROLE_ARN --body "$(aws cloudformation describe-stacks --region us-east-1 \
     --stack-name determinismo-ci --query 'Stacks[0].Outputs[0].OutputValue' --output text)"
   ssh-keygen -t ed25519 -N '' -f ci-key && gh secret set CI_SSH_KEY < ci-key && rm ci-key ci-key.pub
   gh variable set BASE_AMI --body ami-02e6a531699846d74
   ```
   `BASE_AMI` is determinismo's public base image in us-east-1 (Debian with determinismo's KVM
   and tooling; each machine is then set up for the platform's commit by its own setup.sh).
3. Spot in your account: `aws iam create-service-linked-role --aws-service-name spot.amazonaws.com`
   if it never used spot before (an error saying the role exists is fine: the stack's role may not
   create it), and a spot vCPU quota of the machine's vCPUs (Service Quotas, "All Standard (A, C, D, H, I, M,
   R, T, Z) Spot Instance Requests": 96 for `c5.metal`, 48 for `m5zn.metal`); new accounts start
   lower.

Then, in Actions, aws-hunt, Run workflow (or `gh workflow run aws-hunt.yml -f workload=duckdb
-f machine=c5.metal -f minutes=60`): the machine's setup (about half an hour, skipped by later runs
at the same platform commit), the hunt, its counts in the job's log, and its report on this
repository's Pages. A machine is one workload's; it powers itself off after the run.

## License

MIT (LICENSE). Each system under test keeps its own license; its workload names it.
