// CE40: a run line that leaves its shell (`exit`, `exec`, a trailing `#` comment, `set -e` with a
// failing runner) never reaches the move shard_command appends after it, so xargs's runs write
// their JUnit reports over each other again: only the last run's tests are judged (CE21's fix
// undone), and under `set -e` the failing run's tests are the ones lost.
// Where: src/products/ci.zig, beside "every test of a shard is in its JUnit report, however many
// runs xargs splits the list into" (after line 658). Needs only std, /bin/sh, awk, tr, xargs.
// Fails at 62e06e3: shard_command (ci.zig:533-554) appends `; s=$?; if [ -f <junit> ]; then mv
// ...; fi; exit $s` after the run line as written. examples/ci-demo/ci-capped.json:6 is the first
// form (`...; exit $status`).
// Compiled and run against a copy of 62e06e3's ci.zig and serve_client.zig (scratch/zig5/ci):
// both tests fail there (20,000 names: two xargs runs on macOS's xargs, more on GNU's).

fn shard_report_count(arena: std.mem.Allocator, io: std.Io, runner_of: fn (std.mem.Allocator, []const u8) anyerror![]const u8) !usize {
    var directory = std.testing.tmpDir(.{});
    defer directory.cleanup();
    var root_buffer: [4096]u8 = undefined;
    const root = root_buffer[0..try directory.dir.realPathFile(io, ".", &root_buffer)];
    const list = try std.fs.path.join(arena, &.{ root, "tests" });
    const report = try std.fs.path.join(arena, &.{ root, "junit.xml" });
    var names: std.ArrayList(u8) = .empty;
    for (0..20_000) |i| try names.print(arena, "suite.module.{d:0>6}.a_test_name_long_enough_to_take_eighty_bytes_of_the_line\n", .{i});
    try directory.dir.writeFile(io, .{ .sub_path = "tests", .data = names.items });
    const command = try shard_command(arena, try runner_of(arena, report), list, 1, "0", report);
    _ = try std.process.run(arena, io, .{ .argv = &.{ "/bin/sh", "-c", command } });
    const text = directory.dir.readFileAlloc(io, "junit.xml", arena, .limited(1 << 26)) catch return 0;
    return std.mem.count(u8, text, "<testcase");
}

fn runner_exits(arena: std.mem.Allocator, report: []const u8) ![]const u8 {
    // examples/ci-demo/ci-capped.json's shape: the runner, then something, then `exit $status`.
    return std.fmt.allocPrint(arena, "for t in {{tests}}; do printf '<testcase classname=\"c\" name=\"%s\"/>\\n' \"$t\"; done > {s}; status=$?; echo done; exit $status", .{report});
}

fn runner_set_e(arena: std.mem.Allocator, report: []const u8) ![]const u8 {
    // `set -e`; the first run's runner fails after its report (a failing test), the others pass.
    return std.fmt.allocPrint(arena, "set -e; for t in {{tests}}; do printf '<testcase classname=\"c\" name=\"%s\"/>\\n' \"$t\"; done > {s}; test \"$1\" != suite.module.000000.a_test_name_long_enough_to_take_eighty_bytes_of_the_line", .{report});
}

test "a run line ending in exit still has every xargs run's report judged" {
    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    try std.testing.expectEqual(@as(usize, 20_000), try shard_report_count(arena_state.allocator(), std.testing.io, runner_exits));
}

test "under set -e a failing xargs run's tests are judged" {
    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    try std.testing.expectEqual(@as(usize, 20_000), try shard_report_count(arena_state.allocator(), std.testing.io, runner_set_e));
}
