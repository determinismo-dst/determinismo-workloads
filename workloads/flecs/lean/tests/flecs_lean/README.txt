C tests for the predictions in ../../REPORT.md, against flecs v4.2.0.

Each file is one program.  main() returns 0 when flecs behaves as its
documentation says; a non-zero return or an abort confirms the prediction.
Build each with the single-file distribution, debug build (asserts on):

    cc -std=c99 -I ../../upstream/distr <test>.c ../../upstream/distr/flecs.c -o t && ./t; echo $?

Tests that expect flecs to panic install an abort handler that exits 0
(documented panic) and return 1 when no panic happens.
