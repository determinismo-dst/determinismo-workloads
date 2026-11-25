// CE27: a test suite that hangs in some of its shard's timelines (a deadlock its schedules
// reach: the race CI on determinismo is for) makes determinismo-ci say "error", its shard line
// "failing in 0 of 3 timelines", and exit 1 (with --flaky-passes too). With `junit`, a runner
// that dies before its report in one timeline does the same through tests_judge's
// `unreported`. docs/CI.md knows fail, flaky and pass: "failing in every timeline, fail; in
// some, flaky"; `run`: "exit status 0 when they pass"; "Exit status 0 when every shard passes, 1
// when one fails, 2 when one is flaky (`--flaky-passes` counts flaky as passing)".
// Where: src/products/ci.zig. Fails at 3939448: shard_sql (273-275) counts the timelines that
// stated the shard property; a hung one states nothing (the script's det-assert after the run
// command, 250); 286: `if (row.timelines < config.timelines) "error"`; 288-291 print
// `row.failing` (0); tests_judge (440-485) 470 and 475: "error" for any unreported timeline.

// Unit test, beside "a shard's verdict line read" (ci.zig, after 524), on the verdict made a
// function of the row and the shard's timelines, as 286 computes it inline:
//     fn shard_verdict(row: ShardRow, timelines: u32) []const u8
test "a shard whose tests hang in one timeline of three is flaky, failing in that one" {
    // Two timelines stated the property (true), the third hung: the row shard_sql returns.
    const row: ShardRow = .{ .shard = 1, .failing = 0, .timelines = 2 };
    try std.testing.expectEqualStrings("flaky", shard_verdict(row, 3));
}

// e2e: examples/ci-demo with a fourth test whose two threads take two locks in opposite order
// (a deadlock some schedules reach under thread_pause and interleave), `junit` given, 3
// timelines. Assert the job's log says the shard is "flaky" (or "fail" when every timeline
// hangs) and "failing in k of 3 timelines" with k the hung timelines, and the exit status is 2
// (0 with --flaky-passes). At 3939448: "error ... failing in 0 of 3 timelines", exit 1.
