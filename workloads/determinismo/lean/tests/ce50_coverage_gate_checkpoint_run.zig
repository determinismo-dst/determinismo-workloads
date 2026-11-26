// CE50: CE30's fix (serve.zig:703-727 `setup_covered`, 750) reads the run's own
// events/setup.jsonl for a coverage event. A run that starts from a snapshot its setup ran in
// elsewhere has none there: a machine's checkpoint (`checkpoint`, POST /machines/<id>/checkpoint:
// a fast VM's explore-here, a sandbox, a developer's REPL), a session's fork's futures
// (`from_snapshot`). main.zig:2690-2703 opens setup.jsonl and writes nothing to it (the events
// go to fork.jsonl or nowhere). Its timelines start with the setup's coverage bits in the
// snapshot, so the lines the setup ran are reported by no timeline: four timelines that reach no
// new line stop an instrumented run as "its system runs without its language's instrumentation"
// (CE30's case, by another way in). Only a CI job is exempt (765-769, CE38's fix).
// Property: docs/SDKS.md:101-105 ("a run whose first 4 ended timelines report none is stopped":
// a run without coverage); the stop's reason (serve.zig:758-759); serve.zig:703-706 (CE30's
// fix: "the coverage bits are in the setup's snapshot, so timelines repeating the setup's paths
// report none, and the gate stopped instrumented runs as uninstrumented").
// Where: src/serve.zig, beside "an instrumented run whose first timelines repeat its setup's
// code is not stopped as uncovered" (after line 6007). Needs the platform's tree (duckdb). The
// machine's own events (<data>/machines/<machine>/events.jsonl, serve.zig:3424) hold the
// coverage its setup reported: what a fix can read.
// Fails at a7fe05d (by the model: Replica/Serve3.lean's gate, theorem ce50_snapshot_run_stopped).

test "an instrumented run from a machine's checkpoint whose first timelines repeat its setup's code is not stopped" {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const data = try std.fmt.allocPrint(arena, ".zig-cache/tmp/{s}", .{&tmp.sub_path});
    const cwd = std.Io.Dir.cwd();
    const events = try std.fs.path.join(arena, &.{ data, "runs", "1", "events" });
    try cwd.createDirPath(io, events);
    // A checkpoint run: the setup ran in machine m1, which reported its coverage.
    try cwd.writeFile(io, .{ .sub_path = try std.fs.path.join(arena, &.{ data, "runs", "1", "request.json" }), .data = "{\"checkpoint\":\"m1/here-1\"}" });
    try cwd.writeFile(io, .{ .sub_path = try std.fs.path.join(arena, &.{ events, "setup.jsonl" }), .data = "" });
    const machine = try std.fs.path.join(arena, &.{ data, "machines", "m1" });
    try cwd.createDirPath(io, machine);
    const covered = "{\"seq\":1,\"vtime_ns\":10,\"event\":{\"event\":\"coverage\",\"details\":{\"name\":\"line /src/server.zig:42\"}}}\n";
    try cwd.writeFile(io, .{ .sub_path = try std.fs.path.join(arena, &.{ machine, "events.jsonl" }), .data = covered });
    var failure: duckdb.Failure = .{};
    const shared = try std.testing.allocator.create(Shared);
    defer std.testing.allocator.destroy(shared);
    const options: Options = .{ .listen = "", .data_directory = data, .machine = &.{}, .self = "" };
    shared.* = .{ .options = options, .io = io, .database = try duckdb.Database.open(":memory:", .{ .threads = 1 }, &failure) };
    defer shared.database.close();
    var connection = try shared.database.connect(&failure);
    defer connection.close();
    try connection.exec("CREATE TABLE events (name VARCHAR); CREATE TABLE timelines (branch INTEGER, extends INTEGER); " ++
        "CREATE VIEW explored AS SELECT * FROM timelines WHERE extends IS NULL; " ++
        "INSERT INTO timelines VALUES (0, NULL), (1, NULL), (2, NULL), (3, NULL)");
    var explorer = try std.process.spawn(io, .{ .argv = &.{ "sleep", "60" }, .stdout = .ignore, .stderr = .ignore });
    defer explorer.kill(io);
    shared.runs[0] = .{ .id = 1, .pid = explorer.id.? };
    shared.run_count = 1;
    var server: Server = .{ .shared = shared, .options = options, .io = io, .arena = arena };
    coverage_gate(&server, 1, &connection);
    try std.testing.expect(!shared.runs[0].stopped);
}
