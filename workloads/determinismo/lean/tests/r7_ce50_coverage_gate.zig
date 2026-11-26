// Round 7: CE50 against both versions, through serve's coverage_gate itself. A run started from
// a machine's checkpoint (`checkpoint`: POST /machines/<id>/checkpoint, a sandbox, explore-here)
// or a session fork's snapshot (`from_snapshot`): its setup ran in the machine, its own
// events/setup.jsonl is empty, and its first four timelines, repeating what the machine ran,
// report no coverage. Property: docs/SDKS.md (the gate is for a run without coverage); the
// stop's reason ("its system runs without its language's instrumentation").
// Red on a7fe05d's gate (stopped), green on df8f08b's (serve.zig:779-783: such a run returns
// before the stop). The control: an ordinary run without coverage is stopped by both.
// The third test is CE56 (round 7, what CE50's fix leaves): at the run's end the same gate writes its
// `uncovered` file, "no coverage in its N timelines: its system runs without its language's
// instrumentation ... build its workload with it", for the same run (serve.zig:762-772, before
// the exemptions): red on both versions.

fn r7_gate(request: []const u8, going: bool) !struct { stopped: bool, uncovered: bool } {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    var root_buffer: [4096]u8 = undefined;
    const root = root_buffer[0..try tmp.dir.realPathFile(io, ".", &root_buffer)];
    try tmp.dir.createDirPath(io, "events");
    try tmp.dir.writeFile(io, .{ .sub_path = "events/setup.jsonl", .data = "" });
    var shared: Shared = .{ .going = going, .request = request, .directory = root, .covered = 0, .explored = 4 };
    var server: Server = .{ .shared = &shared, .arena = arena, .io = io };
    var connection: duckdb.Connection = .{ .shared = &shared };
    coverage_gate(&server, 1, &connection);
    const uncovered = if (tmp.dir.access(io, "uncovered", .{})) |_| true else |_| false;
    return .{ .stopped = shared.run.stopped, .uncovered = uncovered };
}

test "round 7, CE50: a run from a machine's checkpoint or a fork's snapshot is not stopped as uninstrumented" {
    try std.testing.expect(!(try r7_gate("{\"checkpoint\":\"/data/machines/3/checkpoints/here-1\",\"branching\":\"flat\"}", true)).stopped);
    try std.testing.expect(!(try r7_gate("{\"from_snapshot\":\"/data/sessions/2/fork-15000000000\",\"from_run\":7}", true)).stopped);
}

test "round 7, CE50's control: a run of its own without coverage is stopped" {
    try std.testing.expect((try r7_gate("{\"program\":\"/data/artifacts/p\"}", true)).stopped);
}

test "round 7, CE56: a run from a checkpoint that ended is not said to run uninstrumented" {
    try std.testing.expect(!(try r7_gate("{\"checkpoint\":\"/data/machines/3/checkpoints/here-1\",\"branching\":\"flat\"}", false)).uncovered);
}

test "round 7, CE56's control: a run of its own that ended without coverage is said uncovered" {
    try std.testing.expect((try r7_gate("{\"program\":\"/data/artifacts/p\"}", false)).uncovered);
}
