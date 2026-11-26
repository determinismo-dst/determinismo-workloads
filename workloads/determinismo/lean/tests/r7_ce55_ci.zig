// Round 7: CE55 against both versions. Round 6's test (tests/ce55_ci_xargs_exit_255.zig), renamed
// so it sits beside df8f08b's own. Appended to copies of a7fe05d's and df8f08b's
// src/products/ci.zig. Red on a7fe05d's (xargs stops at the 255: 5,000 of 20,000 judged on
// macOS's xargs), green on df8f08b's (a 255 passed on as 254).

fn r7_runner_exits_255(arena: std.mem.Allocator, report: []const u8) ![]const u8 {
    // The first run's runner reports its tests, then exits 255 (255 failing tests under mocha).
    return std.fmt.allocPrint(arena, "for t in {{tests}}; do printf '<testcase classname=\"c\" name=\"%s\"/>\\n' \"$t\"; done > {s}; if [ \"$1\" = suite.module.000000.a_test_name_long_enough_to_take_eighty_bytes_of_the_line ]; then exit 255; fi", .{report});
}

test "round 7, CE55: a runner exiting 255 in one xargs run still has every test of the shard judged" {
    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    try std.testing.expectEqual(@as(usize, 20_000), try shard_report_count(arena_state.allocator(), std.testing.io, r7_runner_exits_255));
}
