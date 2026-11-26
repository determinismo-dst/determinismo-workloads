// CE53: CE20's fix stops a timeline's recorder at override_count_max (1,048,576) overrides with a
// `tape_full` line at the next pull (vm.zig:3684-3699), and a replay stops there (TapeFull,
// tape.zig:310-320). The explorer never reads it (main.zig has no reference to tape_full):
// `archive_add` (7096-7140) and the judgment's frontier take a judged timeline's moments up to its
// last randomness pull (`last_pull_ns`), past the marker too. A node made from a holder there is
// the real state, so its children run and are recorded, failures included; each child's tape
// chains through the parent to that moment, and a replay of it alone (a failure's replay, a
// session on it, serve's analyses) stops at the parent's marker. A node made by replay stops
// there itself, its return lost.
// Property: README_AI.md ("every timeline replays bit-identically"); docs/ANTITHESIS.md
// (Branching: "every timeline's path in its record and tape (it replays alone)"); vm.zig:
// 3684-3687 (a7fe05d: "a replay stops at that pull ... instead of a tape no replay can read").
// Where: src/main.zig, beside "the archive returns first to a cell whose returns paid, among
// equally rare ones, mostly" (main.zig:5918). Needs the platform's tree. `tape_full_ns` names the
// moment the fix keeps in a Summary (the `tape_full` event's), returns kept before it as before
// last_pull_ns.
// Fails at a7fe05d: the field does not exist (by the model: Replica/Tape6.lean, theorem
// ce53_child_of_a_full_tape_never_replays).

test "no return is planned past where a judged timeline's tape stopped (tape_full)" {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var state: TreeState = .{
        .base = 1,
        .total = 64,
        .size = 16,
        .children = 4,
        .pipeline = 1,
        .jobs = 1,
        .holding = true,
        .registry = undefined,
        .change = null,
        .hunks_reached = &.{},
        .candidates = &.{},
        .tape_buffer = undefined,
        .io = undefined,
        .archive = true,
        .prefer_sometimes = true,
        .setup = undefined,
    };
    const summary = try arena.create(Summary);
    summary.* = .{
        .index = 0,
        .start_ns = 0,
        .end_ns = 10 * std.time.ns_per_s,
        .behavior_count = 2,
        .behaviors = undefined,
        .holder_count = 0,
        .holders = undefined,
        .trace_hash = 1,
        .last_pull_ns = 9 * std.time.ns_per_s,
        .cut = false,
        // Its recorder stopped taping at 2 s (override_count_max reached there).
        .tape_full_ns = 2 * std.time.ns_per_s,
    };
    summary.behaviors[0] = .{ .hash = 11, .vtime_ns = 1 * std.time.ns_per_s };
    summary.behaviors[1] = .{ .hash = 22, .vtime_ns = 5 * std.time.ns_per_s };
    const plan = [_]Planned{.{ .index = 0, .seed = 7, .snapshot = undefined }};
    try archive_add(arena, &state, &plan, summary);
    try std.testing.expect(state.cells.get(11) != null);
    // The behavior reached at 5 s is past the marker: no place a child could replay from.
    try std.testing.expect(state.cells.get(22) == null);
}
