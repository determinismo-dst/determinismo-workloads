// CE19: a run adopted across a serve restart ends "passed" when its explorer exited 3 for an
// assertion no timeline reached (the catalog's verdict).
// Where: src/serve.zig, beside recorded_status (after line 5918).
// Fails at 3939448: runs_reap's adopted branch (serve.zig:5983) and runs_adopt's
// (5821) take the record's last summary (recorded_status), whose property lines are each
// aggregate's failing() (report.zig:830): an assertion unreached in the scenario is judged across
// scenarios, failing:false there. The explorer's `exit` file (main.zig:1166-1175), written for
// these very runs, is not read.

test "an adopted run's status is its explorer's, a catalog's failure included" {
    // One scenario; "test command started: check" declared in every timeline (commands_declare)
    // and reached in none (a finally skipped in each, its timelines all interrupted): explore
    // exits 3 (report.zig Catalog.judge, main.zig:1162) and writes "3 exited with status 3".
    const record =
        \\{"start":{"scenario":"s"}}
        \\{"summary":{"branches":8,"failing_branches":0,"properties":[{"kind":"reachable","message":"test command started: check","failing":false,"branches_hit":0,"branches_true":0,"branches_failing":0,"example_branch":null,"location":null}]}}
        \\
    ;
    try std.testing.expectEqual(@as(u32, 3), recorded_status(record));
}

// The same on the platform (e2e): a program whose scenario is
//     s.parallel_driver("work", work);      // each start raises SIGKILL on itself once
//     s.finally("check", check);            // never runs: every timeline interrupted
// with --timeline 30s --branches 8, through serve (POST /runs). Restart serve while the run goes
// (it adopts the run: runs_discover, pid file). When the run ends:
//     GET /runs/<id>          -> "state": "passed"      (expected "failed")
//     cat runs/<id>/exit      -> "3 exited with status 3"
// A serve that never restarted shows "failed" for the same run.
