// CE28: a session opened on a CI job's run (docs/CI.md: "Each failing timeline is on serve's run
// page ..., a REPL there") changes the job's shard verdicts: shard_sql reads `timeline_events`,
// sessions' timelines included. A failing shard (false in its 3 timelines) with a session whose
// run passes (a fix tried at its REPL) reads "flaky": exit 2, and 0 with --flaky-passes: the job
// passes. A passing shard with a session that failed reads flaky. store.zig:676-679: "What the
// run explored: its timelines but those that extend one (a person's sessions ...). What a run
// found is judged over these"; its view `explored_timeline_events` (684-686) is that.
// Where: src/products/ci.zig:273-275 (`FROM timeline_events`), 286.

// Unit test, in src/store.zig beside "a timeline that extends another (a session's) is queried
// as any, and never among what the run found" (after 1990), with ci.zig's shard_sql (made pub).
test "a CI shard's verdict counts the run's timelines, never a session's" {
    const io = testing.io;
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var tmp = testing.tmpDir(.{});
    defer tmp.cleanup();
    const directory = try std.fmt.allocPrint(arena, ".zig-cache/tmp/{s}/events", .{&tmp.sub_path});
    const cwd = std.Io.Dir.cwd();
    try cwd.createDirPath(io, directory);
    const failed =
        \\{"assert":{"type":"always","message":"the CI shard's tests pass","condition":false,"details":{"shard":1,"status":1}}}
    ;
    const passed =
        \\{"assert":{"type":"always","message":"the CI shard's tests pass","condition":true,"details":{"shard":1,"status":0}}}
    ;
    const files = comptime [_]struct { []const u8, []const u8 }{
        .{ "setup.jsonl", line(1, 100, "{\"event\":\"node_start\",\"details\":{\"node\":\"app\"}}") },
        .{ "branch-0.jsonl", line(2, 900, failed) },
        .{ "branch-1.jsonl", line(3, 900, failed) },
        .{ "branch-2.jsonl", line(4, 900, failed) },
        // Timeline 3: a session on timeline 0 from 500, its run passing after a fix at its REPL.
        .{ "branch-3.jsonl", line(5, 950, passed) },
        .{ "timelines.jsonl", timeline_line(0, 1000, "[]") ++ timeline_line(1, 1000, "[]") ++ timeline_line(2, 1000, "[]") ++
            "{\"index\":3,\"outcome\":\"command_done\",\"vtime_ns\":1000,\"wall_ns\":10," ++
            "\"path\":[{\"branch\":0,\"seed\":7,\"vtime_ns\":500}],\"extends\":{\"branch\":0,\"vtime_ns\":500}}\n" },
    };
    inline for (files) |file| {
        try cwd.writeFile(io, .{ .sub_path = try std.fs.path.join(arena, &.{ directory, file[0] }), .data = file[1] });
        if (event_files.index_of(file[0])) |index| try event_files.compress(directory, index);
    }
    var failure: duckdb.Failure = .{};
    var database = try duckdb.Database.open(":memory:", .{ .threads = 2 }, &failure);
    defer database.close();
    const store = try Store.attach(&database, arena, directory, "run_1", &failure);
    var attached = try store.connect(&database, arena, &failure);
    defer attached.close();
    _ = try ingest(&attached, arena, io, directory);
    const Row = struct { shard: u32, failing: u64, timelines: u64 };
    const rows = try attached.rows(Row, arena, @import("products/ci.zig").shard_sql, .{});
    try testing.expectEqual(1, rows.len);
    // The shard failed in every one of its 3 timelines: "fail" (ci.zig:291).
    try testing.expectEqual(Row{ .shard = 1, .failing = 3, .timelines = 3 }, rows[0]);
}
