// Round 8, CE62 (what CE57's fix leaves): explain's `--draw <name>=<v>` varies the control's draw
// beside each of the value's m variants (c4f246e's variant_items, explain.zig:582-592), by its
// pull number in the recorded timeline (`controls[at]`). A variant's tape answers that pull
// number whatever draw takes it in the variant's own history (variant_tape: overrides by pull).
// A value that changes the history before that pull can leave it to a draw that decides nothing:
// the clock step removed (clock_step.ms 0, Datomic's #3 as the doc names it), there is no retry,
// and the retry's jitter pull, the control's, is taken by a request id. The m variants are one
// history again, counted m times.
// Property: explain.zig:10-15 (c4f246e: "m times each with the control's draw varied beside it
// (one tape replays one history)"), 29-34 (step 5: a verdict per detail against its control, by
// their 90% intervals); variant_items' own comment (582-588: "so each is a history of its own
// that compares with the control's"); README_AI.md (every timeline replays bit-identically).
// Run against a copy of each version's src/explain.zig (its scratch directory under the
// replica's, getpid from libc), with fake-explorer-retry.sh as the explorer: a timeline whose
// histories fail about 5 of 6 times whatever any one draw's value; with the step removed, its one
// history does not fail.
// Tests: each of a set value's 6 variants is a history of its own: red on c4f246e (1 history) and
// on df8f08b; a value whose one history does not fail is not called "needed": red on both (0 of 6
// against the control's 5 of 6). Control: a value that keeps the retry (8): 6 histories, green on
// c4f246e (CE57's fix), red on df8f08b.

const r8_root = R8_ROOT;

fn r8_explain(draw: [:0]const u8) !struct { histories: usize, needed: bool } {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const io = std.testing.io;
    const cwd = std.Io.Dir.cwd();
    cwd.deleteFile(io, r8_root ++ "/histories.log") catch {};
    const tape = r8_root ++ "/branch-3.jsonl";
    try cwd.writeFile(io, .{ .sub_path = tape, .data = "{\"tape\":2,\"inputs\":\"00000000000000aa\",\"branch\":3,\"branch_seed\":\"0000000000000006\"}\n" });
    const saved = std.c.dup(1);
    const out = std.c.open(r8_root ++ "/report-" ++ "out.json", .{ .ACCMODE = .WRONLY, .CREAT = true, .TRUNC = true }, @as(std.c.mode_t, 0o644));
    _ = std.c.dup2(out, 1);
    const status = run(arena, io, r8_root ++ "/fake-explorer-retry.sh", &.{
        "--tape", tape, "--property", "balances add up", "--variants", "6", "--jobs", "1", "--draw", draw, "--json",
    });
    _ = std.c.dup2(saved, 1);
    _ = std.c.close(out);
    try std.testing.expectEqual(@as(u8, 0), try status);
    const report_text = try cwd.readFileAlloc(io, r8_root ++ "/report-out.json", arena, .limited(1 << 20));
    std.debug.print("\n--draw {s}: {s}\n", .{ draw, report_text });
    // The set value's histories: those with its step (the control's keep the recorded 5200).
    const log = try cwd.readFileAlloc(io, r8_root ++ "/histories.log", arena, .limited(1 << 20));
    var seen: std.StringHashMapUnmanaged(void) = .empty;
    var lines = std.mem.tokenizeScalar(u8, log, '\n');
    while (lines.next()) |line| {
        if (std.mem.indexOf(u8, line, "step=5200") != null) continue;
        try seen.put(arena, line, {});
    }
    // The detail's verdict (the control's is not one).
    const detail = std.mem.indexOf(u8, report_text, "\"details\":") orelse return error.NoDetails;
    return .{ .histories = seen.count(), .needed = std.mem.indexOf(u8, report_text[detail..], "\"verdict\":\"needed\"") != null };
}

test "round 8, CE62: a set value that leaves the control's pull to another draw: each of its variants a history of its own" {
    try std.testing.expectEqual(@as(usize, 6), (try r8_explain("clock_step.ms=0")).histories);
}

test "round 8, CE62's consequence: the step removed, its one history not failing, is not called needed" {
    try std.testing.expect(!(try r8_explain("clock_step.ms=0")).needed);
}

test "round 8, CE62's control: a set value that keeps the retry, its variants 6 histories" {
    try std.testing.expectEqual(@as(usize, 6), (try r8_explain("clock_step.ms=8")).histories);
}
