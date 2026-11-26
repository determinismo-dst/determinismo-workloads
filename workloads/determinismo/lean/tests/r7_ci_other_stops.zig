// Round 7, round 6's list: xargs's other stops, and a run line ending in `&`. Appended to copies
// of ci.zig (62e06e3's, a7fe05d's, df8f08b's), reusing their shard_report_count (20,000 names of
// 80 bytes, one shard; macOS's xargs makes batches of 5,000).
// xargs stops at a command killed by a signal (GNU: "If any invocation of the command is
// terminated by a signal, xargs stops immediately"; BSD alike). A runner `exec`'d by the run line
// and killed (the OOM killer, a crash) was xargs's command itself at 62e06e3: the later batches
// never ran. Since a7fe05d the run line runs in a subshell: the shell xargs ran exits with the
// subshell's status (128 + the signal), and xargs goes on. The test: red on 62e06e3, green on
// a7fe05d and df8f08b.

fn r7_runner_exec_killed(arena: std.mem.Allocator, report: []const u8) ![]const u8 {
    // The first batch's runner writes its report, then is killed by SIGKILL; the others pass.
    return std.fmt.allocPrint(arena, "for t in {{tests}}; do printf '<testcase classname=\"c\" name=\"%s\"/>\\n' \"$t\"; done > {s}; if [ \"$1\" = suite.module.000000.a_test_name_long_enough_to_take_eighty_bytes_of_the_line ]; then exec sh -c 'kill -9 $$'; fi", .{report});
}

test "round 7: an exec'd runner killed by a signal leaves every test of the shard judged" {
    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    try std.testing.expectEqual(@as(usize, 20_000), try shard_report_count(arena_state.allocator(), std.testing.io, r7_runner_exec_killed));
}

fn r7_runner_backgrounded(arena: std.mem.Allocator, report: []const u8) ![]const u8 {
    // A run line ending in `&`: its runner (a second to start) in the background.
    return std.fmt.allocPrint(arena, "(sleep 1; for t in {{tests}}; do printf '<testcase classname=\"c\" name=\"%s\"/>\\n' \"$t\"; done > {s}) &", .{report});
}

test "round 7: a run line ending in & (what the report holds once the command ended)" {
    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const judged = try shard_report_count(arena_state.allocator(), std.testing.io, r7_runner_backgrounded);
    std.debug.print("\na run line ending in &: {d} of 20,000 names in the report once the command ended\n", .{judged});
    try std.testing.expectEqual(@as(usize, 20_000), judged);
}
