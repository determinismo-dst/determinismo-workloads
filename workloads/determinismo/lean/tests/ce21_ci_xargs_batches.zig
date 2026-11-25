// CE21: with `{tests}`, a shard whose names pass xargs's buffer runs its runner several times,
// each run writing the JUnit report anew: only the last run's tests are judged.
// Where: src/products/ci.zig, beside "a shard's verdict line read" (after line 524); run where
// the shards run (Linux, sh, awk, tr and GNU xargs, as a node's image has them).
// Fails at 3939448: the shard's command (ci.zig:226-233) is
//   awk -v n=N -v i=I '(NR - 1) % n == i' <list> | tr '\n' '\000' | xargs -0 sh -c '<run "$@">' sh
// and GNU xargs splits its arguments past its command buffer (131,072 bytes by default).

test "a shard's tests all reach one run of its runner" {
    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const io = std.testing.io;
    var directory = std.testing.tmpDir(.{});
    defer directory.cleanup();
    const root = try directory.dir.realpathAlloc(arena, ".");
    // 3,000 tests of 80 bytes, one shard: the list as the setup wrote it (tests_path).
    var list: std.ArrayList(u8) = .empty;
    for (0..3000) |index| try list.print(arena, "tests/test_module_{d:0>5}.py::TestCase::test_case_with_a_long_name_{d:0>6}\n", .{ index, index });
    const list_path = try std.fs.path.join(arena, &.{ root, "tests" });
    try std.Io.Dir.cwd().writeFile(io, .{ .sub_path = list_path, .data = list.items });
    // The runner: each run writes its report (here: its argument count) anew, as --junitxml does.
    const report = try std.fs.path.join(arena, &.{ root, "report" });
    const run = try std.fmt.allocPrint(arena, "echo \"$#\" > {s}", .{report});
    // ci.zig:226-233's command for shard 0 of 1, its awk program's {timeline%1} already 0.
    var line: std.ArrayList(u8) = .empty;
    try line.print(arena, "awk -v n=1 -v i=0 '(NR - 1) % n == i' {s} | tr '\\n' '\\000' | xargs -0 sh -c ", .{list_path});
    try shell_quote(arena, &line, run); // ci.zig replaces `{tests}` by "$@"; this runner counts them.
    try line.appendSlice(arena, " sh");
    const result = try std.process.run(arena, io, .{ .argv = &.{ "/bin/sh", "-c", line.items } });
    try std.testing.expect(result.term.success());
    // The report det-assert junit reads names every test of the shard.
    const reported = try std.Io.Dir.cwd().readFileAlloc(io, report, arena, .limited(64));
    try std.testing.expectEqualStrings("3000\n", reported);
}
