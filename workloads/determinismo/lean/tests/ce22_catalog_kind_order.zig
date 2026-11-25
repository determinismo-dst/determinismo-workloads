// CE22: a message declared with two kinds in two timelines is judged by whichever kind the
// catalog noted first: the exploration's verdict depends on the order its timelines ended.
// Where: src/report.zig, beside "test Catalog" (after line 189).
// Fails at 3939448: Catalog.note keeps the first kind of an identity (report.zig:128-136) and
// judge (148-170) decides "must be reached" by it; catalog_reached notes the aggregates in the
// order they were merged (report.zig:752-765), the order timelines ended.

test "the catalog's verdict does not depend on the order its kinds were noted" {
    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    var failing: [2]u32 = undefined;
    for ([_]bool{ false, true }, 0..) |reachable_first, at| {
        var catalog = Catalog{ .arena = arena_state.allocator() };
        // Timeline A declared `reachable "m"`, timeline B `always_or_unreachable "m"`; neither
        // reached it. Ended A then B, or B then A.
        if (reachable_first) try catalog.note(.reachable, "m", false);
        try catalog.note(.always_or_unreachable, "m", false);
        if (!reachable_first) try catalog.note(.reachable, "m", false);
        failing[at] = catalog.judge(true);
    }
    // The reachable never reached fails either way (each kind its own property, as
    // Property.same says).
    try std.testing.expectEqual(@as(u32, 1), failing[0]);
    try std.testing.expectEqual(@as(u32, 1), failing[1]);
}
