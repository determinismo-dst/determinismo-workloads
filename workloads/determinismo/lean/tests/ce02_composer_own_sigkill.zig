// CE2 (still there at 3939448 for SIGKILL): with --min-drive 0, a start that died of SIGKILL on
// its own before the ending is reaped by kill_all and reported killed: never judged.
// Where: a scenario in tests/selftest/selftest.zig, beside ending_signal_scenario; the code:
// guest/runtime/composer.zig:853-856 (min_drive returns at once for 0: nothing reaped),
// 401-407 (kill_all reaps every child with killed = true), 335-340 (by_kill: SIGKILL is all it
// asks), 1324-1328 (report_exit: killed, no judgment). Not unit-testable (processes).

/// One start in two of `oom` dies of SIGKILL at once (the OOM killer's signal, or a kill from
/// outside the composer); the eventually ending kills the rest.
fn own_sigkill_scenario(s: *System.Scenario) void {
    s.parallel_driver("oom", oom_driver);
    s.eventually("after", own_sigkill_eventually);
}

fn oom_driver(_: *System.Context) !void {
    if (sdk.random_below(2) == 0) {
        sdk.event("killed_self", .{});
        _ = linux.kill(linux.getpid(), .KILL);
    }
    const long = linux.timespec{ .sec = 30, .nsec = 0 };
    _ = linux.nanosleep(&long, null);
}

fn own_sigkill_eventually(_: *System.Context) !void {}

// Run:
//   determinismo explore --program selftest --scenario own_sigkill --no-swarm --min-drive 0 \
//     --drive-max none --branches 16 --events-dir E
// Expect in every timeline with a `killed_self` event: a `command_exit` of `oom` with
// "status": 137 and "test commands exit successfully" false (as without --min-drive 0, where
// min_drive's wait_until reaps it first). At 3939448 the `command_exit` says "killed": true and
// the property is never false for it.
