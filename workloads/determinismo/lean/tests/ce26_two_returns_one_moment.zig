// CE26: a generation returns twice to one moment: its frontier's return just after a behavior
// is not counted as a return to that behavior's archive cell, and the archive, filling half the
// moments, picks the same cell (new cells rank first: their timelines' count is 0 when the
// archive ranks them, `state.visits` updated only after, 6431-6435). Two nodes at one moment
// (the second a replay from the parent's start: a holder serves one return), 2 x children
// timelines from it, one moment fewer in the generation. docs/AGENTS.md: "A generation of 16 is
// 4 fresh starts and 3 moments with 4 branches each"; archive_returns' comment (7077-7080):
// "seldom returned to ...; each return counts". docs/PLUGINS.md (returns): the explorer's fill
// goes to "other timelines than those chosen", but archive_returns (7081-7123) skips only a
// cell a strategy return took (7106), not its timeline.
// Where: src/main.zig tree_returns 7323-7339 (a frontier return has no `cell`), archive_returns
// 7081-7123. In the replica's runs: 8.6% of judgments (129 of 1500) with the default shape.

// Unit test, beside "a plugin's returns are kept whole and the archive fills around them"
// (main.zig, after 5917).
test "a generation never returns twice to one moment" {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var state: TreeState = .{
        .base = 1, .total = 64, .size = 16, .children = 4, .pipeline = 1, .jobs = 1,
        .holding = false, .registry = undefined, .change = null, .hunks_reached = &.{},
        .candidates = &.{}, .tape_buffer = undefined, .io = undefined, .archive = true,
        .prefer_sometimes = true, .setup = undefined,
    };
    // Timeline 0 alone reached `sometimes "leader elected": true` at 1 s (this generation's new
    // cell, its one place just after it); its frontier is the same moment.
    const at = std.time.ns_per_s + return_after_ns;
    var cell: Cell = .{ .places = undefined, .label = "sometimes \"leader elected\": true", .sought = true };
    cell.places[0] = .{ .branch = 0, .vtime_ns = at };
    try state.cells.put(arena, 0x5e, cell);
    const frontier = [_]TreeReturn{.{ .branch = 0, .vtime_ns = at, .why = "Returned to #0 just after it first reached it: its frontier." }};
    var random: std.Random.DefaultPrng = .init(1);
    const returns = try archive_returns(arena, &state, state.size, &frontier, &random);
    for (returns, 0..) |a, i| for (returns[i + 1 ..]) |b| {
        try std.testing.expect(!(a.branch == b.branch and a.vtime_ns == b.vtime_ns));
    };
}
