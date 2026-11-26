// CE52: a session's step longer than write_step's buffer leaves its tape line unfinished.
// write_step (tape.zig:500-511) writes the line's head `{"vtime":<ns>,"step":` at once, then
// stringifies the step into a fixed buffer of 2 * 65,536 bytes; a step whose JSON does not fit
// returns there (`catch return`): the head stays on the tape with no end, the next line written
// (an override, a step, det:over at the session's end) runs on from it, and the replay's parse
// fails at that line (std.json: the object never closes). A step is a session input line of any
// length (vm.zig:2169-2196); `det:ask <fifo> <id> <base64 parts>` is a whole REPL message in one
// step (vm.zig:1895-1899): an nREPL load-file of a 96 KiB namespace is 131,072 bytes of base64.
// The parse has a second bound: each line is parsed into the 64 KiB scratch every caller gives
// (main.zig:2612, 3332; node.zig:60): a step with escapes (quotes, line breaks) is copied there
// unescaped, so a shell step of about 64 KiB with quotes fails too (OutOfMemory). And
// steps_max/step_text_max (65,536 steps, 16 MiB, 513-522) bound only the replay.
// Property: README_AI.md "every timeline replays bit-identically"; vm.zig:2202-2203 ("A step
// the moment runs, on the timeline's own tape at the moment it ran: a replay of the timeline runs
// it there again"); vm.zig:3684-3687 ("instead of a tape no replay can read", CE20's fix).
// Where: src/core/tape.zig, beside "a session's steps on its timeline's tape parse back, with
// their moments" (after line 906). Needs only std; writes a temporary file.
// Fails at a7fe05d: compiled and run against a copy of tape.zig (scratch/zig6/tape, its
// write_all calling std.c.write so it runs on macOS): the parse fails (SyntaxError, then
// OutOfMemory for the second test).

fn tape_with_step(allocator: std.mem.Allocator, step: []const u8, tmp: *std.testing.TmpDir) ![]u8 {
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

test "a session's REPL message of 96 KiB (a det:ask step of 131,072 bytes) is read back from its tape" {
    const allocator = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const step = try allocator.alloc(u8, "det:ask /run/det/nrepl-in 7 ".len + 131_072);
    defer allocator.free(step);
    @memcpy(step[0.."det:ask /run/det/nrepl-in 7 ".len], "det:ask /run/det/nrepl-in 7 ");
    @memset(step["det:ask /run/det/nrepl-in 7 ".len..], 'Q'); // Base64: nothing to escape.
    const source = try tape_with_step(allocator, step, &tmp);
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

test "a session's shell step of 40,000 quoted words is read back from its tape" {
    const allocator = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    var step: std.ArrayList(u8) = .empty;
    defer step.deinit(allocator);
    try step.appendSlice(allocator, "det-nodes exec app sh -c 'printf \"%s\\n\"");
    for (0..20_000) |_| try step.appendSlice(allocator, " \"a\""); // 80,000 bytes, 40,000 escapes.
    try step.appendSlice(allocator, "'");
    const source = try tape_with_step(allocator, step.items, &tmp);
    defer allocator.free(source);
    const overrides = try Overrides.create(allocator);
    defer overrides.destroy();
    const scratch = try allocator.alloc(u8, 64 * 1024);
    defer allocator.free(scratch);
    _ = try parse(source, scratch, overrides);
    try std.testing.expectEqualStrings(step.items, overrides.step_of(overrides.steps_taped()[0]));
}

test "a session's REPL message of 33 KiB (a det:ask step of 45,000 bytes) is read back from its tape" {
    // Written whole (under the 128 KiB buffer), refused by the parse: 42,235 bytes is the longest
    // step a 64 KiB scratch reads (std.json's Value copies each string), measured on Zig 0.17.
    const allocator = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const step = try allocator.alloc(u8, 45_000);
    defer allocator.free(step);
    @memcpy(step[0.."det:ask /run/det/nrepl-in 7 ".len], "det:ask /run/det/nrepl-in 7 ");
    @memset(step["det:ask /run/det/nrepl-in 7 ".len..], 'Q');
    const source = try tape_with_step(allocator, step, &tmp);
    defer allocator.free(source);
    try std.testing.expect(std.mem.endsWith(u8, source, "\"det:over\"}\n")); // Every line whole.
    const overrides = try Overrides.create(allocator);
    defer overrides.destroy();
    const scratch = try allocator.alloc(u8, 64 * 1024);
    defer allocator.free(scratch);
    _ = try parse(source, scratch, overrides);
    try std.testing.expectEqualStrings(step, overrides.step_of(overrides.steps_taped()[0]));
}
