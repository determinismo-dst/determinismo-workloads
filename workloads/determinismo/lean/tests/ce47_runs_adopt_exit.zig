// CE47: CE19's fix reads the explorer's `exit` for discovered and adopted runs (ended_status,
// serve.zig:5903-5909; 5756, 6017), but runs_adopt (5795-5822), for a run resumed from a command
// line (the resume's adopt note, main.zig:1287-1294), deletes `exit` with the run's other end
// notes (5806-5810) and, when the resumed explorer has ended already, takes the record's summary
// alone (5815: `recorded_status(record)`). The note is written as the resume starts and read at
// the watcher's next look (a second), so a resume that ends sooner has its own `exit` deleted:
// every complete resume (CE29's path, main.zig:2212-2229, ends in milliseconds) and any short
// one. The record's last summary is then the interrupted run's (or none: "interrupted"), or the
// resume's own, which has no catalog (report.zig `record_summary`): a run failing on a
// `reachable` never reached shows "passed", CE19's case again.
// Property: serve.zig:5898-5902 (ended_status: "How a run's explorer ended: its `exit` ..."),
// 5912 ("A failing property fails the run, as explore exits").
// Where: src/serve.zig, beside `test "a run's end is its explorer's exit, then its record's
// summary"` (after line 5937): runs_adopt over a data directory whose run has an adopt note, an
// `exit` the resumed explorer wrote ("3 exited with status 3") and no pid.
// Fails at 62e06e3: the run's status is 0 (its record's summary), `exit` gone.

test "a command-line resume that ended before serve looked keeps its explorer's exit" {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const data = try std.fmt.allocPrint(arena, ".zig-cache/tmp/{s}", .{&tmp.sub_path});
    const cwd = std.Io.Dir.cwd();
    const run = try std.fs.path.join(arena, &.{ data, "runs", "1" });
    try cwd.createDirPath(io, run);
    // Every timeline passed (the resume's summary: no catalog in it); the resumed explorer
    // exited 3 for a catalog's reachable no timeline reached, and is gone (no pid).
    try cwd.writeFile(io, .{ .sub_path = try std.fs.path.join(arena, &.{ run, "record.jsonl" }), .data = "{\"summary\":{\"branches\":2,\"failing_branches\":0}}\n" });
    try cwd.writeFile(io, .{ .sub_path = try std.fs.path.join(arena, &.{ run, "exit" }), .data = "3 exited with status 3\n" });
    try host_runs.adopt_note(arena, data, 1);
    var shared: Shared = .{};
    shared.runs[0] = .{ .id = 1, .pid = 0, .status = status_interrupted, .stopped = true };
    shared.run_count = 1;
    var server: Server = .{
        .shared = &shared,
        .options = .{ .listen = "", .data_directory = data, .machine = &.{}, .self = "" },
        .io = io,
        .arena = arena,
    };
    runs_adopt(&server);
    try std.testing.expectEqual(@as(?u32, 3), shared.runs[0].status);
}
