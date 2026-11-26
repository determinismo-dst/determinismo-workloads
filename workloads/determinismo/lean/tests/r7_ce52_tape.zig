// Round 7: CE52 against both versions. Round 6's three tests (tests/ce52_tape_long_session_step.zig),
// renamed so they sit beside df8f08b's own. Appended to copies of a7fe05d's and df8f08b's
// src/core/tape.zig (write_all calling libc's write so they run on macOS). Red on a7fe05d's
// (write_step's 128 KiB buffer, the 64 KiB parse scratch), green on df8f08b's (write_step
// streams, step_line_parse decodes into the step table).

fn r7_tape_with_step(allocator: std.mem.Allocator, step: []const u8, tmp: *std.testing.TmpDir) ![]u8 {
    const io = std.testing.io;
    const file = try tmp.dir.createFile(io, "branch-0.jsonl", .{ .truncate = true });
    const header = "{\"tape\":2,\"inputs\":\"00000000000000aa\",\"exploration_seed\":\"0000000000000007\"," ++
        "\"branch\":0,\"branch_seed\":\"00000000000000ff\",\"from_branch\":0,\"from_vtime_ns\":15000000000}\n";
    write_all(file.handle, header);
    write_step(file.handle, step, 15_000_019_720);
    write_override(file.handle, 606, &.{1}, "");
    write_step(file.handle, "det:over", 15_227_000_000);
    file.close(io);
    return tmp.dir.readFileAlloc(io, "branch-0.jsonl", allocator, .limited(1 << 24));
}

test "round 7, CE52: a session's REPL message of 96 KiB (a det:ask step of 131,072 bytes) is read back from its tape" {
    const allocator = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const step = try allocator.alloc(u8, "det:ask /run/det/nrepl-in 7 ".len + 131_072);
    defer allocator.free(step);
    @memcpy(step[0.."det:ask /run/det/nrepl-in 7 ".len], "det:ask /run/det/nrepl-in 7 ");
    @memset(step["det:ask /run/det/nrepl-in 7 ".len..], 'Q'); // Base64: nothing to escape.
    const source = try r7_tape_with_step(allocator, step, &tmp);
    defer allocator.free(source);
    const overrides = try Overrides.create(allocator);
    defer overrides.destroy();
    const scratch = try allocator.alloc(u8, 64 * 1024); // As main.zig:2612 and node.zig:60 give.
    defer allocator.free(scratch);
    _ = try parse(source, scratch, overrides);
    const steps = overrides.steps_taped();
    try std.testing.expectEqual(@as(usize, 2), steps.len);
    try std.testing.expectEqualStrings(step, overrides.step_of(steps[0]));
    try std.testing.expectEqual(@as(u32, 1), overrides.count);
}

test "round 7, CE52: a session's shell step of 40,000 quoted words is read back from its tape" {
    const allocator = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    var step: std.ArrayList(u8) = .empty;
    defer step.deinit(allocator);
    try step.appendSlice(allocator, "det-nodes exec app sh -c 'printf \"%s\\n\"");
    for (0..20_000) |_| try step.appendSlice(allocator, " \"a\""); // 80,000 bytes, 40,000 escapes.
    try step.appendSlice(allocator, "'");
    const source = try r7_tape_with_step(allocator, step.items, &tmp);
    defer allocator.free(source);
    const overrides = try Overrides.create(allocator);
    defer overrides.destroy();
    const scratch = try allocator.alloc(u8, 64 * 1024);
    defer allocator.free(scratch);
    _ = try parse(source, scratch, overrides);
    try std.testing.expectEqualStrings(step.items, overrides.step_of(overrides.steps_taped()[0]));
}

test "round 7, CE52: a session's REPL message of 33 KiB (a det:ask step of 45,000 bytes) is read back from its tape" {
    // Written whole (under the 128 KiB buffer), refused by the parse: 42,235 bytes is the longest
    // step a 64 KiB scratch reads (std.json's Value copies each string), measured on Zig 0.17.
    const allocator = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const step = try allocator.alloc(u8, 45_000);
    defer allocator.free(step);
    @memcpy(step[0.."det:ask /run/det/nrepl-in 7 ".len], "det:ask /run/det/nrepl-in 7 ");
    @memset(step["det:ask /run/det/nrepl-in 7 ".len..], 'Q');
    const source = try r7_tape_with_step(allocator, step, &tmp);
    defer allocator.free(source);
    try std.testing.expect(std.mem.endsWith(u8, source, "\"det:over\"}\n")); // Every line whole.
    const overrides = try Overrides.create(allocator);
    defer overrides.destroy();
    const scratch = try allocator.alloc(u8, 64 * 1024);
    defer allocator.free(scratch);
    _ = try parse(source, scratch, overrides);
    try std.testing.expectEqualStrings(step, overrides.step_of(overrides.steps_taped()[0]));
}
