// Round 7: CE53 against both versions, through the archive itself. A judged timeline whose tape
// was full at 2 s (override_count_max reached: vm.zig's tape_override writes the marker, and a
// replay of any chain through it stops there, TapeFull), its last pull at 9 s, behaviors new to
// the tree at 1 s and 5 s. A return to 5 s makes children whose chain stops at the marker: they
// never replay alone, nor do their failures.
// Property: README_AI.md ("every timeline replays bit-identically"); docs/ANTITHESIS.md
// (Branching: "every timeline's path in its record and tape (it replays alone)"); df8f08b's
// main.zig:6552-6555 ("Past a full tape's marker a child's chain stops there and never replays").
// The first test: red on a7fe05d (the summary's last_pull_ns ignores the tape), green on
// df8f08b (returns_before_ns). The second, CE58 (round 7, what CE53's fix leaves): the same timeline cut at
// its horizon (`--horizon`: a cut branch's moments are open to its end, archive_add's `open =
// summary.cut or ...`): red on both.

fn r7_summary_last_pull(vm: anytype, summary: *Summary) void {
    R7_SUMMARY_STATEMENT
}

fn r7_archive_after(cut: bool) !struct { early: bool, late: bool } {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var state: TreeState = .{};
    var summary: Summary = .{ .index = 0, .start_ns = 0, .end_ns = 10 * std.time.ns_per_s, .cut = cut, .behavior_count = 2 };
    summary.behaviors[0] = .{ .hash = 11, .vtime_ns = 1 * std.time.ns_per_s };
    summary.behaviors[1] = .{ .hash = 22, .vtime_ns = 5 * std.time.ns_per_s };
    const vm: R7Vm = .{ .last_pull_ns = 9 * std.time.ns_per_s, .tape_full_ns = 2 * std.time.ns_per_s };
    r7_summary_last_pull(&vm, &summary);
    const plan = [_]Planned{.{ .index = 0, .seed = 7 }};
    if (@typeInfo(@TypeOf(archive_add)).@"fn".param_types.len == 5) {
        try archive_add(arena, &state, &plan, &summary, false);
    } else {
        try archive_add(arena, &state, &plan, &summary);
    }
    return .{ .early = state.cells.get(11) != null, .late = state.cells.get(22) != null };
}

test "round 7, CE53: the archive keeps no place past where a timeline's tape was full" {
    const cells = try r7_archive_after(false);
    try std.testing.expect(cells.early);
    try std.testing.expect(!cells.late);
}

test "round 7, CE58: nor in a timeline cut at its horizon" {
    const cells = try r7_archive_after(true);
    try std.testing.expect(cells.early);
    try std.testing.expect(!cells.late);
}
