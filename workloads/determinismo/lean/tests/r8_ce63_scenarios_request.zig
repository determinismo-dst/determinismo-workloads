
// Round 8, CE63: a run of several scenarios (`--scenario all`) is a run per scenario, the first
// keeping the run already claimed, "its request now naming the scenario" (main.zig:1328-1359
// `run_scenario`, the same at df8f08b and c4f246e): run_request_write writes that run's
// request.json again, from the explorer's own arguments. serve started the run with the request
// it was posted (serve.zig:2163-2175, run_start: `asked` written whole). After the rewrite:
// - its `scenario` is the first scenario's name: serve's resume (run_resume -> explore_arguments,
//   serve.zig:2249 `--scenario <asked.scenario>`) explores that scenario alone; interrupted in
//   it, the run's other scenarios are never explored (no run of theirs was claimed yet), and its
//   catalog is judged over one scenario (main.zig:1166-1170: every_scenario false, nothing fails);
// - what only serve records is gone: here `return_branches` (serve.zig:2228-2230 gives it to the
//   explorer; resume_read, main.zig:2295-2299, refuses a tree whose record says another
//   return_branches: "the record of another run") and `ci` (the coverage gate's exemption for a
//   CI job, serve.zig:784).
// Property: serve.zig:5684-5687 (run_resume: "Continues a run that ended before its end ...: its
// explorer again, as it was asked"); README_AI.md's request (a run's request.json is what serve
// replays and continues it with: main.zig:1196-1200).
// The test: serve's request for `--scenario all`, a tree with return_branches 2, a CI job's;
// run_scenario for the first scenario, verbatim; the request read back as serve reads it.
// Red on both versions.

test "round 8, CE63: a run of several scenarios keeps the request it was asked" {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    var root_buffer: [4096]u8 = undefined;
    const root = try arena.dupe(u8, root_buffer[0..try tmp.dir.realPathFile(io, ".", &root_buffer)]);
    const files = "scratch/zig8/tmp/ce63";
    for ([_][]const u8{ files ++ "/kernels/vmlinuz", files ++ "/workloads/bank", files ++ "/explorer" }) |given| {
        try std.Io.Dir.cwd().createDirPath(io, std.fs.path.dirname(given).?);
        try std.Io.Dir.cwd().writeFile(io, .{ .sub_path = given, .data = std.fs.path.basename(given) });
    }
    // As serve's run_start writes it (the request posted, the run's own fields beside it).
    const posted: serve.RunRequest = .{
        .program = files ++ "/workloads/bank",
        .scenario = "all",
        .branching = "tree",
        .return_branches = 2,
        .ci = .{ .repository = "bank", .branch = "main", .commit = "c0ffee" },
        .seed = 7,
    };
    try tmp.dir.writeFile(io, .{ .sub_path = "request.json", .data = try std.fmt.allocPrint(arena, "{f}", .{std.json.fmt(posted, .{})}) });
    // The explorer serve started: `--run-directory <root> --scenario all --return-branches 2 ...`.
    var arguments: Arguments = .{
        .kernel_path = files ++ "/kernels/vmlinuz",
        .program_path = files ++ "/workloads/bank",
        .scenario = "all",
        .seed = 7,
        .run_directory = root,
        .data_directory = root,
    };
    // main.zig:1115-1121: the first of its scenarios ("transfer", "audit").
    try run_scenario(arena, io, &arguments, "transfer", true);
    const text = try tmp.dir.readFileAlloc(io, "request.json", arena, .limited(1 << 20));
    const asked = try std.json.parseFromSliceLeaky(serve.RunRequest, arena, text, .{ .ignore_unknown_fields = true });
    std.debug.print("\nthe request asked: scenario all, return_branches 2, a CI job's; after the first scenario began: scenario {?s}, return_branches {?d}, ci {s}\n", .{
        asked.scenario, asked.return_branches, if (asked.ci != null) "kept" else "gone",
    });
    try std.testing.expectEqualStrings("all", asked.scenario.?);
    try std.testing.expectEqual(@as(?u32, 2), asked.return_branches);
    try std.testing.expect(asked.ci != null);
}
