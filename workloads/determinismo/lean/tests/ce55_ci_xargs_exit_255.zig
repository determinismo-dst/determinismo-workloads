// CE55: CE40's fix (ci.zig:537-552) moves each xargs run's report aside whatever the run line
// does with its shell, and the shell exits with the run's status (`exit $s`). xargs stops at a
// command that exits 255 (GNU and BSD xargs: "exits immediately ... if an invocation exits with
// a value of 255", findutils' CHILD_EXIT_PLEASE_STOP_IMMEDIATELY): a runner exiting 255 in one
// run (mocha, whose status is its failure count capped at 255; a JVM's System.exit(-1); go's
// os.Exit(-1); `exit -1`) leaves every later batch of the shard's names never run, never
// reported, never judged; nothing says so but the shard's failure. The subshell keeps the 255:
// at 62e06e3 and 3939448 too.
// Property: docs/CI.md (`junit`): "each test gets its own verdict across its shard's
// timelines"; ci.zig:529-533 (a7fe05d): "every test of the shard gets its verdict, not only the
// last run's ..., whatever the run line does with its shell (CE40)".
// Where: src/products/ci.zig, beside "a run line ending in a comment still has every xargs run's
// report judged" (after line 714), reusing its shard_report_count. Needs /bin/sh and xargs.
// Fails at a7fe05d: compiled and run against a copy of ci.zig (scratch/zig6/ci): 5,000 of 20,000
// judged on macOS's xargs (its batches of 5,000 names), the first run's runner exiting 255.

fn runner_exits_255(arena: std.mem.Allocator, report: []const u8) ![]const u8 {
    // The first run's runner reports its tests, then exits 255 (255 failing tests under mocha).
    return std.fmt.allocPrint(arena, "for t in {{tests}}; do printf '<testcase classname=\"c\" name=\"%s\"/>\\n' \"$t\"; done > {s}; if [ \"$1\" = suite.module.000000.a_test_name_long_enough_to_take_eighty_bytes_of_the_line ]; then exit 255; fi", .{report});
}

test "a runner exiting 255 in one xargs run still has every test of the shard judged" {
    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    try std.testing.expectEqual(@as(usize, 20_000), try shard_report_count(arena_state.allocator(), std.testing.io, runner_exits_255));
}
