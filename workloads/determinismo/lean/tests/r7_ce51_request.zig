// Round 7: CE51 against both versions, through run_request_write (main.zig) and serve's
// system_arguments, as an analysis builds its explorer's argv (serve.zig replay_argv: the run's
// machine.json, then system_arguments over its request.json). A command-line run given
// `--timeline-limit 30s --no-swarm --epoch 1767225600 --timer-slack-us 250
// --timer-landing-permille 50 --injector <path>`: each is in its guest's command line, its
// initramfs or its machine (inputs_hash), so the analysis must be given each again, with its
// value; else every tape is refused (TapeInputsDiffer).
// Property: main.zig (a7fe05d 1402-1405, df8f08b 1441-1446): "In the guest's command line too:
// left out, serve's analyses of a run started with --clock-start-max 0 booted another guest
// line, and its tapes were refused"; the request's "In the guest's command line: replays need it".
// The first test, the five flags in the guest's command line and machine: red on a7fe05d,
// green on df8f08b. The control: --clock-start-max, which a7fe05d already kept.
// The second test, CE60 (round 7: what CE51's fix leaves), `--injector`: the injector goes on the
// system disk under its file's name (prepare.zig:1464-1471 `/det/injectors/<basename>`), and the
// disk's name is a hash of its contents, each injector's basename included (prepare.zig:195-199;
// main.zig:8967-8969 inputs_hash: each disk's basename). run_request_write keeps it by content
// (runs.zig:217-219: `<hash>-<basename>`) for the request alone; the run itself booted the file
// as given. The analysis's `--injector` is the kept copy: another name on another system disk,
// another inputs hash: every tape refused (TapeInputsDiffer), as before the fix. Red on both.
// The harness's runs.zig names a kept copy as runs.zig:212-232 does.

fn r7_analysis_argv(arena: std.mem.Allocator, arguments: *Arguments) ![]const []const u8 {
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    var root_buffer: [4096]u8 = undefined;
    const root = try arena.dupe(u8, root_buffer[0..try tmp.dir.realPathFile(io, ".", &root_buffer)]);
    // The files the run was given, as they are on the host.
    var files: std.ArrayList([]const u8) = .empty;
    try files.appendSlice(arena, &.{ arguments.kernel_path, arguments.program_path.?, r7_files ++ "/explorer" });
    try files.appendSlice(arena, arguments.injectors);
    for (files.items) |given| {
        try std.Io.Dir.cwd().createDirPath(io, std.fs.path.dirname(given).?);
        try std.Io.Dir.cwd().writeFile(io, .{ .sub_path = given, .data = std.fs.path.basename(given) });
    }
    try run_request_write(arena, io, root, root, arguments);
    const request = try tmp.dir.readFileAlloc(io, "request.json", arena, .limited(1 << 20));
    const machine = try tmp.dir.readFileAlloc(io, "machine.json", arena, .limited(1 << 20));
    const asked = try std.json.parseFromSliceLeaky(serve.RunRequest, arena, request, .{ .ignore_unknown_fields = true });
    var argv: std.ArrayList([]const u8) = .empty;
    try argv.appendSlice(arena, try std.json.parseFromSliceLeaky([]const []const u8, arena, machine, .{}));
    try serve.system_arguments(arena, &argv, &asked);
    return argv.items;
}

fn r7_has(argv: []const []const u8, flag: []const u8, value: ?[]const u8) bool {
    for (argv, 0..) |word, index| {
        if (!std.mem.eql(u8, word, flag)) continue;
        const given = value orelse return true;
        if (index + 1 < argv.len and std.mem.eql(u8, argv[index + 1], given)) return true;
    }
    return false;
}

/// The run's files, under the test's own directory (round 7's scratch, removed after).
const r7_files = "scratch/zig7/tmp/ce51";

test "round 7, CE51: a command-line run's analyses are given every input flag of its command line and machine" {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var arguments: Arguments = .{
        .kernel_path = r7_files ++ "/kernels/vmlinuz",
        .program_path = r7_files ++ "/workloads/bank",
        .timeline_limit_ns = 30 * std.time.ns_per_s,
        .timeline_limit_text = "30s",
        .swarm = false,
        .epoch_seconds = 1767225600,
        .timer_slack_us = 250,
        .timer_delay_permille = 50,
    };
    const argv = try r7_analysis_argv(arena, &arguments);
    try std.testing.expect(r7_has(argv, "--timeline-limit", "30s"));
    try std.testing.expect(r7_has(argv, "--no-swarm", null));
    try std.testing.expect(r7_has(argv, "--epoch", "1767225600"));
    try std.testing.expect(r7_has(argv, "--timer-slack-us", "250"));
    try std.testing.expect(r7_has(argv, "--timer-landing-permille", "50"));
}

test "round 7, CE60: an injector reaches the analysis under the name the run's system disk has" {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var arguments: Arguments = .{
        .kernel_path = r7_files ++ "/kernels/vmlinuz",
        .program_path = r7_files ++ "/workloads/bank",
        .injectors = &.{r7_files ++ "/injectors/chaos"},
    };
    const argv = try r7_analysis_argv(arena, &arguments);
    var given: ?[]const u8 = null;
    for (argv, 0..) |word, index| {
        if (std.mem.eql(u8, word, "--injector") and index + 1 < argv.len) given = argv[index + 1];
    }
    try std.testing.expect(given != null);
    std.debug.print("\nthe run's injector: chaos; the analysis's: {s}\n", .{std.fs.path.basename(given.?)});
    try std.testing.expectEqualStrings("chaos", std.fs.path.basename(given.?));
}

test "round 7, CE51's control: --clock-start-max is given again (a7fe05d's own fix)" {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var arguments: Arguments = .{ .kernel_path = r7_files ++ "/kernels/vmlinuz", .program_path = r7_files ++ "/workloads/bank", .clock_start_max_text = "0" };
    const argv = try r7_analysis_argv(arena, &arguments);
    try std.testing.expect(r7_has(argv, "--clock-start-max", "0"));
}
