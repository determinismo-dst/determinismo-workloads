// CE20: a timeline with more than 65,536 overrides is recorded whole and never replays: an idle
// listening session's 14 virtual minutes of ingress polls, egress or serve replies past 4 MiB.
// Where: src/core/tape.zig, beside "a relayed session's polls, thousands of ingress answers,
// parse: their reason is their kind" (after line 844).
// Fails at 3939448: override_parse refuses the 65,537th entry (tape.zig:554-556,
// override_count_max = 1 << 16, line 8), error.TapeTooLong; the recording side writes every
// answer (vm.zig:3730, 3766, 3803) with no bound.

test "a session's tape of fourteen virtual minutes of ingress polls replays" {
    const allocator = std.testing.allocator;
    const overrides = try allocator.create(Overrides);
    defer allocator.destroy(overrides);
    const scratch = try allocator.alloc(u8, 16 * 1024);
    defer allocator.free(scratch);
    var source: std.ArrayList(u8) = .empty;
    defer source.deinit(allocator);
    try source.appendSlice(allocator, "{\"tape\":2,\"inputs\":\"00000000000000aa\",\"exploration_seed\":\"0000000000000007\"," ++
        "\"branch\":0,\"branch_seed\":\"00000000000000ff\"}\n");
    // 84 polls a virtual second (tape.zig:100-102), each answer on the tape: 14 minutes.
    const polls = 84 * 14 * 60;
    for (0..polls) |poll| {
        try source.print(allocator, "{{\"pull\":{d},\"hex\":\"0100000000000000\",\"reason\":\"{s}\"}}\n", .{ 700 + poll, ingress_reason });
    }
    _ = try parse(source.items, scratch, overrides);
    try std.testing.expectEqual(@as(u32, polls), overrides.count);
}
