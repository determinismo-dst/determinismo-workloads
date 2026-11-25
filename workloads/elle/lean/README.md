# A Lean replica of Elle

Elle (jepsen-io/elle, Jepsen's transactional consistency checker, which determinismo's checks run
through its service, the platform's [checkers/elle](https://github.com/determinismo-dst/determinismo/tree/next/checkers/elle)) replicated in Lean 4 from its source, function by function, at
main 4e359e5 (one commit after v0.2.8, which the service runs: the same code). Each of its
verdicts is compared with an independent specification: Adya's dependency graphs over every
interpretation of a history (every version order, every outcome of an indeterminate operation),
built from the definitions rather than from Elle's code. It was written blind, from Elle's code,
its documentation and the papers it implements, and searched with determinismo's Lean library
(`sdk/lean`, pinned in `lakefile.toml`).

## Rounds

- **Round 1**: history handling, list-append, rw-register (initial states, `:wfr-keys?`),
  closed-predicate, the graph machinery (Bifurcan's Tarjan, BFS), anomaly classification and the
  consistency-model lattice. 12 disagreements, D1–D13 (D13 a TODO in Elle's code).
  [REPORT.md](REPORT.md).
- **Round 2**: rw-register's `:linearizable-keys?`, `:sequential-keys?` and `:transaction-order`,
  the cycle search's time limit, every fold's chunking, `:not`/`:also-not`, and the platform's
  Elle service as it was (`service/`, from `fetch-sources.sh`); complete fixes for D3, D10 and D13.
  9 more disagreements, D14–D22, four of them in the service (D16–D19).
  [REPORT-2.md](REPORT-2.md).

## What the real Elle said

Every disagreement was reproduced by running Elle on its minimal history
(`results/*.cases.edn`, Elle's answers in `results/*.elle.edn`). Within Elle's documented scope
(no failed or indeterminate transactions, every append read) none turned up, over about 325,000
histories. The findings, each with what it changes: [UNREPORTED.md](UNREPORTED.md). The service
([checkers/elle](https://github.com/determinismo-dst/determinismo/tree/next/checkers/elle)) runs Elle with the fixes for D3, D9, D10 (and D11) and D13, and its own for D16, D17
and D19; each has a test in its `test/`. D18: its strict-serializable-per-key keeps the stricter reading, described as such.

The reports' `scratch/...` paths (the cases, Elle's and the service's answers, the patched
namespaces as checked, the suite logs) are under [evidence/scratch/](evidence/scratch/).

## Elle as written, our deployed Elle, and proposed fixes

The replica is Elle as written: every switch in `Opts` (Elle/Txn.lean) defaults to `false`, and a
search compares that with a run where some are on. The switches stand for three different things:

- **Elle as written (Elle 0.2.8 / main 4e359e5):** every switch off. This is what the searches
  call "Elle".
- **Our deployed service** (determinismo's checkers/elle: patched namespaces loaded ahead of
  Elle's jar, running in every determinismo check): `fixD3`, `fixD13`, `cpFixed` (D9, D10, D11)
  and `perKeyFixed` (D19), together `Service.check (deployed := true)`.
- **Proposed, deployed nowhere:** round 3's `fixD1`, `fixD2`, `fixD4`, `fixD5`, `fixD6`, `fixD7`,
  `fixD8`, `fixD12`, `fixD20`, `fixD21`, `fixD22`. Each is checked here and as a patch of the
  deployed namespaces (REPORT-3.md says which are safe); none is in Elle or in our service yet.

When a proposal is deployed, this section moves it to the second list.

## Building and running

With [elan](https://github.com/leanprover/elan) installed (it takes the Lean version from
`lean-toolchain`; Lake fetches determinismo's Lean library at the commit `lakefile.toml` pins):

```sh
lake build Elle elle-search
lake exe elle-search explore la read=cuts txns=5 mops=3 keys=2 threads=3 seeds=5000
runner/batch.sh runner/batch1.txt   # round 1's searches, one per line, into results/
```

`./fetch-sources.sh` puts Elle at 4e359e5 in `upstream/` (git-ignored), compiles its Java
classes and writes its classpath to `deps/` (it needs a JDK and Leiningen). Then real Elle on a
cases file:

```sh
runner/elle.sh results/closed-predicate.cases.edn /tmp/closed-predicate.elle.edn
```

The runner scripts run each job directly; with `LEAN_JOB` set, through that command instead
(`$LEAN_JOB <seconds> <command>`: a machine's job slots).

## License

A translation of Elle's code, so under Elle's license, the Eclipse Public License 2.0
([LICENSE](LICENSE)). Elle is copyright 2019–2020 Jepsen, LLC and Peter Alvaro.
