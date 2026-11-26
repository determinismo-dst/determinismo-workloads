// CE51: a7fe05d records `--clock-start-max` in a command-line run's request (main.zig:1400-1406)
// so serve's analyses boot its guest's command line; the other flags its machine's inputs
// depend on (main.zig:8676-8705 inputs_hash: the command line, the timers, the epoch, the
// initramfs) are still left out of request.json and machine.json (run_request_write,
// 1374-1487): `--timeline-limit` (det.timeline_limit_ms=, on every guest line, an hour by
// default), `--no-swarm` (det.swarm=0; `swarm` written at its default, true), `--epoch`,
// `--timer-slack-us`, `--timer-landing-permille` (machine.json keeps none), `--injector` (the
// initramfs; no `injectors`). An analysis (replay_argv, serve.zig:2865-2880: run_machine, then
// system_arguments 5565-5600) boots other inputs and refuses every tape (TapeInputsDiffer,
// main.zig:2615-2621): causality, explain, a session, a replay. A run recorded before a7fe05d
// with `--clock-start-max` stays refused (no request of before has it).
// Property: main.zig:1402-1405 (a7fe05d: "In the guest's command line too: left out, serve's
// analyses of a run started with --clock-start-max 0 booted another guest line, and its tapes
// were refused"), 1395, 1408, 1411 ("In the guest's command line: replays need it"); the test
// "a run's request keeps what its guest's command line needs: the wall clock's start".
// Where: src/main.zig, beside that test (after line 1369). Needs the platform's tree (serve.zig).
// Fails at a7fe05d (by the model: Replica/Request6.lean, theorem ce51_analysis_boots_other_inputs).

test "a run's request and machine keep every flag its machine's inputs depend on" {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const directory = try std.fmt.allocPrint(arena, ".zig-cache/tmp/{s}", .{&tmp.sub_path});
    const cwd = std.Io.Dir.cwd();
    const kernel = try std.fs.path.joinZ(arena, &.{ directory, "vmlinuz" });
    try cwd.writeFile(io, .{ .sub_path = kernel, .data = "a kernel" });
    const program = try std.fs.path.joinZ(arena, &.{ directory, "workload" });
    try cwd.writeFile(io, .{ .sub_path = program, .data = "a program" });
    var arguments = try parse_arguments(arena, &.{
        "determinismo",           "explore", "--kernel",                kernel, "--program", program,
        "--timeline-limit",       "30s",     "--no-swarm",              "--epoch", "2030-01-01",
        "--timer-slack-us",       "50",      "--timer-landing-permille", "500",
    });
    try run_request_write(arena, io, directory, directory, &arguments);
    const request = try cwd.readFileAlloc(io, try std.fs.path.join(arena, &.{ directory, "request.json" }), arena, .limited(1 << 20));
    const machine = try cwd.readFileAlloc(io, try std.fs.path.join(arena, &.{ directory, "machine.json" }), arena, .limited(1 << 20));
    const asked = try std.json.parseFromSliceLeaky(serve.RunRequest, arena, request, .{ .ignore_unknown_fields = true });
    // What serve's analyses boot: the run's machine.json, then its request (replay_argv).
    var argv: std.ArrayList([]const u8) = .empty;
    try argv.appendSlice(arena, &.{ "determinismo", "explore" });
    try argv.appendSlice(arena, try std.json.parseFromSliceLeaky([]const []const u8, arena, machine, .{}));
    try serve.system_arguments(arena, &argv, &asked);
    var argv_z: std.ArrayList([:0]const u8) = .empty;
    for (argv.items) |word| try argv_z.append(arena, try arena.dupeZ(u8, word));
    const analysis = try parse_arguments(arena, argv_z.items);
    try std.testing.expectEqualStrings(
        try cmdline_build(arena, "console=ttyS0", &arguments, null),
        try cmdline_build(arena, "console=ttyS0", &analysis, null),
    );
    try std.testing.expectEqual(arguments.epoch_seconds, analysis.epoch_seconds);
    try std.testing.expectEqual(arguments.timer_slack_us, analysis.timer_slack_us);
    try std.testing.expectEqual(arguments.timer_delay_permille, analysis.timer_delay_permille);
}
