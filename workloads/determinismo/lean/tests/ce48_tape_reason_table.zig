// CE48: CE20's other table. A replay still refuses a tape with more than 1,024 decisions carrying
// a reason (reason_count_max, tape.zig:120, 639), and the recorder writes them all (tape_override
// counts overrides alone, vm.zig:3684-3699). The guest's egress proxy asks its channel at each
// connection (guest/runtime/egress.zig:42-58: sdk.egress_channel, a decision the VM answers with
// `egress_channel_reason`, vm.zig:3756-3761), so a timeline whose system opens 1,025 outside
// connections has a tape no replay can read: every replay of it, every node made by a replay of
// it, and every child's chain through it fail at the parse (TapeTooLong).
// Where: src/core/tape.zig, beside "a session's 70,560 taped answers parse: a replay reads every
// tape its recorder wrote" (after line 937). Needs only std.
// Fails at 62e06e3 (TapeTooLong): compiled and run against a copy of tape.zig (scratch/zig5/tape).

test "a timeline's 1,025 egress connections parse: each its channel's decision and reason" {
    const allocator = std.testing.allocator;
    const overrides = try Overrides.create(allocator);
    defer overrides.destroy();
    const scratch = try allocator.alloc(u8, 16 * 1024);
    defer allocator.free(scratch);
    var source: std.ArrayList(u8) = .empty;
    defer source.deinit(allocator);
    try source.appendSlice(allocator, "{\"tape\":2,\"inputs\":\"00000000000000aa\",\"exploration_seed\":\"0000000000000007\"," ++
        "\"branch\":0,\"branch_seed\":\"00000000000000ff\"}\n");
    // vm.zig:3514's reason, as tape.write_override writes it (one line a connection).
    const reason = "how the machine's egress goes: 0 the host's relay, 1 egress decisions";
    for (0..1_025) |connection| {
        try source.print(allocator, "{{\"pull\":{d},\"hex\":\"0100000000000000\",\"reason\":\"{s}\"}}\n", .{ 100 + 7 * connection, reason });
    }
    _ = try parse(source.items, scratch, overrides);
    try std.testing.expectEqual(@as(u32, 1_025), overrides.count);
}
