// CE5 (still there at 3939448, its other path): a driver starts past half the timeline's limit
// after waiting for a parallelism slot.
// Where: the scenario in tests/selftest/selftest.zig (beside ending_signal_scenario, which the
// round-1 fixes added); the code: guest/runtime/composer.zig:795-805, run_drivers' loop checks
// the stop before driver_start, and driver_start (849-851, driver_start_by 854-874) waits for a
// slot with no deadline (wait_below(parallelism, maxInt): reaped with hang) before it starts.
// Not unit-testable (processes): the scenario, its assertion and its explore command.

/// Drivers that each hold the only slot past half the timeline's limit (parallelism 1).
fn slot_wait_scenario(s: *System.Scenario) void {
    s.parallel_driver("holding", holding_driver);
    s.parallel_driver("next", next_driver);
}

/// Holds the slot 400 s of virtual time (a slow system's step under faults).
fn holding_driver(_: *System.Context) !void {
    const long = linux.timespec{ .sec = 400, .nsec = 0 };
    _ = linux.nanosleep(&long, null);
}

/// Marks its start: none may come past half the limit (300 s with --timeline-limit 600s).
fn next_driver(_: *System.Context) !void {
    var now: linux.timespec = undefined;
    _ = linux.clock_gettime(.MONOTONIC, &now);
    const started_s: u64 = @intCast(now.sec);
    // The composer's drive start is within a second of the guest's boot plus the setup: read it
    // from its event in the check below rather than here; this driver only says when it began.
    sdk.event("next_started", .{ .monotonic_s = started_s });
}

// Run:
//   determinismo explore --program selftest --scenario slot_wait --no-swarm \
//     --drive-max none --timeline-limit 600s --branches 16 --events-dir E \
//     --decide composer.parallelism_log2=0
// Check (each timeline): the first `command_start` of "next" after a start of "holding" lies
// before composer_start + 300 s:
//   determinismo query E 'event=command_start details.name=next' --until-vtime ...
// Expected: none past 300 s of the driver phase. At 3939448 a timeline whose first start is
// "holding" starts "next" at about 400 s, then logs drivers_stopped: the start came after the stop
// it was meant to respect (a hang at the limit for a slow command, Redpanda's run 177's case).
