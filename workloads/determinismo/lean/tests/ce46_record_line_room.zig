// CE46: a timeline's record line keeps its properties while their estimated size fits 40 KiB
// (report.zig:42-45, 513-531: `name.len + 128` bytes each, in the timeline's table order, the
// rest left out and `properties_all` false). A resume merges what the line kept
// (main.zig:2030-2036, 2170-2176) and says how many lines were partial, "their verdicts not
// counted" (2207-2208): a property past the room, a failing `always` among them, is judged in no
// timeline it was recorded in. A table past the room is 320 properties of 192-byte messages, or
// about 230 of 50 bytes: a CI job's shard (`det-assert junit`: one "test passes: ..." property a
// test), a workload's property a key or a node.
// Property: main.zig:2023-2025 ("counted in the resumed run's verdict as its own timelines' are"),
// 2828 ("A resumed run's recorded timelines count in its verdict as its own do (CE29)").
// Where: src/report.zig, beside `pub fn recorded_merge` (after line 608): a record line made by
// `Multiverse.add`'s writer for a timeline of 400 properties, the 400th failing, read back as
// resume_read reads it and merged.
// Fails at 62e06e3 (the Lean replica: runs5/resume.txt; theorem ce46_failure_past_the_room): the
// failing property is past the room; the resumed multiverse has no failing property.

test "a recorded timeline's failing property counts on resume, however many it evaluated" {
    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var events: Events = .{};
    // 400 properties of 100-byte messages, each evaluated once; the last one false.
    for (0..400) |index| {
        var message: [100]u8 = @splat('p');
        _ = std.fmt.bufPrint(&message, "test passes: suite::case_{d:0>4}", .{index}) catch unreachable;
        try events.assertion_note(.always, &message, index != 399);
    }
    const line = try record_line_of(arena, &events); // The branch line report.zig:513-560 writes.
    const parsed = try std.json.parseFromSliceLeaky(struct { branch: struct { properties: []const Recorded, properties_all: bool } }, arena, line, .{ .ignore_unknown_fields = true });
    var multiverse: Multiverse = .{};
    for (parsed.branch.properties) |*property| try multiverse.recorded_merge(property, 0);
    // The timeline failed: its resumed verdict says so.
    try std.testing.expectEqual(@as(u32, 1), multiverse.failing_properties());
}
