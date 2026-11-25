// CE18: a `sometimes` never true passes when its message is reached under another kind.
// Where: src/report.zig, beside "one message with two kinds is two properties, whichever
// timeline came first" (after line 894).
// Fails at 3939448: Catalog entries are keyed by identity alone (report.zig:128-136) and
// `made_true` (140-145) answers for whatever kind reached the message.

test "a sometimes never true is not made true by its message under another kind" {
    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const multiverse = try std.testing.allocator.create(Multiverse);
    defer std.testing.allocator.destroy(multiverse);
    multiverse.* = .{};
    // Timeline 1: sometimes(false, "m"); timeline 2: always(true, "m"). Two properties
    // (Property.same), the sometimes never true.
    var sometimes = Events.Property{ .kind = .sometimes, .message = undefined, .message_size = 1, .hits = 1, .trues = 0 };
    sometimes.message[0] = 'm';
    var always = Events.Property{ .kind = .always, .message = undefined, .message_size = 1, .hits = 1, .trues = 1 };
    always.message[0] = 'm';
    try multiverse.merge(&sometimes, 1);
    try multiverse.merge(&always, 2);
    try std.testing.expectEqual(@as(u32, 0), multiverse.failing_violations());
    var catalog = Catalog{ .arena = arena };
    try multiverse.catalog_reached(&catalog);
    const unmet = try multiverse.sometimes_unmet(arena);
    try std.testing.expectEqual(@as(usize, 1), unmet.len);
    // main.zig:1150-1155 fails the run unless the catalog says the sometimes was made true.
    try std.testing.expect(!catalog.made_true(unmet[0]));
}
