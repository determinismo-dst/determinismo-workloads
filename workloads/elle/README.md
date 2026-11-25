# Elle

Not a workload: Elle (jepsen-io/elle, Jepsen's transactional consistency checker) is how
determinismo judges transaction histories, through its service in the platform's
[checkers/elle](https://github.com/determinismo-dst/determinismo/tree/next/checkers/elle). This
directory holds its Lean replica, [lean/](lean/README.md): Elle written function by function in
Lean 4 and checked against an independent specification. Its findings are in
[lean/UNREPORTED.md](lean/UNREPORTED.md); the fixes determinismo applies are in checkers/elle.
