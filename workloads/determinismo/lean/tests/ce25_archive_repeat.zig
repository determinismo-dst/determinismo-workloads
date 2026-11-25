// CE25: the archive returns to a repeat: a timeline whose whole trace equals an earlier one's
// becomes another place of the cells it reached, and a return goes there.
// ARCHITECTURE.md §9: "Repeats: a timeline whose whole trace equals an earlier one's is never
// returned to". Where: src/main.zig. Fails at 3939448: tree_judge_begin runs archive_add for
// every judged timeline (6366) before it skips repeats (6400: `if ((try
// state.traces.getOrPut(arena, summary.trace_hash)).found_existing) continue;`), and
// archive_add (6989-7040) adds a place for a behavior another timeline reached (7016-7026);
// Cell.place (5826-5829) returns to each place in turn.

// Unit test, beside "the archive returns first to a cell whose returns paid" (main.zig, after
// 5880): timeline 1 is timeline 0 again (one trace); its behavior is no place of the cell.
test "a repeat is no archive cell's place" {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var state: TreeState = .{
        .base = 1, .total = 64, .size = 16, .children = 4, .pipeline = 1, .jobs = 1,
        .holding = false, .registry = undefined, .change = null, .hunks_reached = &.{},
        .candidates = &.{}, .tape_buffer = undefined, .io = undefined, .archive = true,
        .prefer_sometimes = true, .setup = undefined,
    };
    const setup: *const Snapshot = @ptrFromInt(@alignOf(Snapshot));
    const plan = [_]Planned{
        .{ .index = 0, .seed = 1, .snapshot = setup },
        .{ .index = 1, .seed = 2, .snapshot = setup },
    };
    var summaries: [2]*Summary = undefined;
    for (&summaries, 0..) |*summary, index| {
        summary.* = try arena.create(Summary);
        summary.*.* = .{
            .index = @intCast(index), .start_ns = 0, .end_ns = 10 * std.time.ns_per_s,
            .behavior_count = 1, .behaviors = undefined, .holder_count = 0, .holders = undefined,
            .trace_hash = 0x7ace, .last_pull_ns = 9 * std.time.ns_per_s, .cut = false,
        };
        summary.*.behaviors[0] = .{ .hash = 0xbe, .vtime_ns = std.time.ns_per_s };
    }
    // Timeline 0 judged (its trace known), then timeline 1, the same trace.
    try archive_add(arena, &state, &plan, summaries[0]);
    try state.traces.put(arena, summaries[0].trace_hash, {});
    try archive_add(arena, &state, &plan, summaries[1]);
    const cell = state.cells.get(0xbe).?;
    for (cell.places[0..cell.place_count]) |place| try std.testing.expect(place.branch != 1);
}
