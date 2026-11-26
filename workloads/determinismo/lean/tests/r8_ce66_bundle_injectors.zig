
// Round 8, CE66 (an area no round covered: bundles): `determinismo bundle` (bundle.zig) gathers a
// timeline's inputs "with everything it replays on" (bundle.zig:2-9: "how someone else replays a
// finding's timeline exactly"; README.txt: "the rest is what they were recorded on (a tape
// refuses other inputs)"): the kernel and initramfs (machine.json), the program and the
// explorer (request.json, 111-133), the pinned system's images, the tapes. A run's injectors are
// inputs too (on its system disk: prepare.zig:196-200 hashes each one's name and content, and
// docs/PLUGINS.md:149-151 "part of the run's inputs"), and its request names them by the
// recording host's paths (CE60's kept copies: <data>/artifacts/<hash>/<name>); the bundle
// leaves them there. Its replay (`explore --run . --branch <n>`: verify.run_arguments ->
// serve.system_arguments, `--injector <path>`) reads the recording host's file: on any other
// host there is none, and with a store (`--store`, `bundle fetch`) nothing brings it either.
// The test: a run with an injector, bundled with a store; every path the bundle's request names
// for its inputs (program, injectors) is the bundle's or listed in STORED. Red on c4f246e.
// Its control: the program alone, green.
fn r8_bundle(with_injector: bool) !bool {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const io = std.testing.io;
    const cwd = std.Io.Dir.cwd();
    const root = "scratch/zig8/tmp/ce66";
    cwd.deleteTree(io, root) catch {};
    const data = root ++ "/data";
    const run_directory = data ++ "/runs/5";
    for ([_][]const u8{ data ++ "/artifacts/1111111111111111-vmlinuz", data ++ "/artifacts/2222222222222222-bank", data ++ "/artifacts/3333333333333333/chaos", run_directory ++ "/cpuid.txt" }) |path| {
        try cwd.createDirPath(io, std.fs.path.dirname(path).?);
        try cwd.writeFile(io, .{ .sub_path = path, .data = std.fs.path.basename(path) });
    }
    try cwd.createDirPath(io, run_directory ++ "/events");
    try cwd.createDirPath(io, run_directory ++ "/tapes");
    try cwd.writeFile(io, .{ .sub_path = run_directory ++ "/machine.json", .data = "[\"--kernel\",\"" ++ data ++ "/artifacts/1111111111111111-vmlinuz\",\"--cpuid\",\"" ++ run_directory ++ "/cpuid.txt\"]" });
    const request = if (with_injector)
        "{\"program\":\"" ++ data ++ "/artifacts/2222222222222222-bank\",\"injectors\":[\"" ++ data ++ "/artifacts/3333333333333333/chaos\"],\"seed\":7}"
    else
        "{\"program\":\"" ++ data ++ "/artifacts/2222222222222222-bank\",\"seed\":7}";
    try cwd.writeFile(io, .{ .sub_path = run_directory ++ "/request.json", .data = request });
    try cwd.writeFile(io, .{ .sub_path = run_directory ++ "/events/system.pin.json", .data = "{}" });
    try cwd.writeFile(io, .{ .sub_path = run_directory ++ "/tapes/branch-0.jsonl", .data = "{\"tape\":2,\"branch\":0}\n" });
    const out = root ++ "/bundle";
    const store = root ++ "/store";
    try std.testing.expectEqual(@as(u8, 0), try run(arena, io, &.{ run_directory, "0", out, "--store", store }));
    // What its replay reads (verify.run_arguments: request.json through system_arguments).
    const Asked = struct { program: ?[]const u8 = null, injectors: ?[]const []const u8 = null };
    const asked = try std.json.parseFromSliceLeaky(Asked, arena, try read(arena, io, out, "request.json"), .{ .ignore_unknown_fields = true });
    const stored = try read(arena, io, out, "STORED");
    var inputs: std.ArrayList([]const u8) = .empty;
    try inputs.append(arena, asked.program.?);
    if (asked.injectors) |list| try inputs.appendSlice(arena, list);
    var carried = true;
    for (inputs.items) |path| {
        const inside = !std.fs.path.isAbsolute(path) and std.mem.indexOf(u8, stored, path) != null;
        std.debug.print("\nthe bundle's request names {s}: {s}", .{ path, if (inside) "the bundle's (STORED)" else "the recording host's, not in the bundle" });
        carried = carried and inside;
    }
    std.debug.print("\n", .{});
    return carried;
}

test "round 8, CE66: a bundle carries every input its request names, its injectors too" {
    try std.testing.expect(try r8_bundle(true));
}

test "round 8, CE66's control: a run without an injector" {
    try std.testing.expect(try r8_bundle(false));
}
