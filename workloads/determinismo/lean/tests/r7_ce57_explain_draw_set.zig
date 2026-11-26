// Round 7, a new counterexample of df8f08b: explain's `--draw <name>=<values>` runs each value's
// m variants as one tape m times. Each variant is the timeline's tape with the named draw's
// pull answered the set value and nothing else changed, replayed from one snapshot: m copies of
// one deterministic replay, one history. Step 5 then judges them as m samples (Wilson's 90%
// interval over m), against a control whose m variants are m histories: a value whose one
// replay happens not to fail reads "needed" (0 of m) whatever the value does. The removal's
// variants vary the control's draw too for this reason ("so its failures compare with the
// control's"); the set values do not.
// Property: explain.zig:10-14 (`--draw <name>=0,1000` "sets it to each value given instead, m
// times each"), 29-34 (step 5: a verdict per detail from its variants against its control, by
// their 90% intervals; "Six variants once called a wait needed (0 of 6) that another six found
// half the time (3 of 6)"); README_AI.md (every timeline replays bit-identically: one tape, one
// history).
// Run against a copy of df8f08b's src/explain.zig (its scratch directory under the replica's,
// getpid from libc), with scratch/zig7/df/built/explain/fake-explorer.sh as the explorer: a
// timeline whose variants fail in about 5 of 6 histories whatever any one draw's value is.
// The tests: each of a set value's 6 variants is a history of its own (6 distinct tapes): red on
// df8f08b (1); a value whose one replay does not fail is not called "needed": red on df8f08b
// (0 of 6 against the control's 5 of 6: "needed"). Their control: `--draw <name>` without
// values (6 fresh values, 6 histories): green.

const r7_root = "scratch/zig7/df/built/explain";

fn r7_explain_variants(draw: [:0]const u8) !usize {
    return (try r7_explain(draw)).distinct;
}

fn r7_explain(draw: [:0]const u8) !struct { distinct: usize, needed: bool } {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const io = std.testing.io;
    const cwd = std.Io.Dir.cwd();
    cwd.deleteFile(io, r7_root ++ "/variants.log") catch {};
    const tape = r7_root ++ "/branch-3.jsonl";
    try cwd.writeFile(io, .{ .sub_path = tape, .data = "{\"tape\":2,\"inputs\":\"00000000000000aa\",\"branch\":3,\"branch_seed\":\"00000000000000ff\"}\n" });
    // Its report (stdout) into a file of its own.
    const saved = std.c.dup(1);
    const out = std.c.open(r7_root ++ "/report-" ++ "out.json", .{ .ACCMODE = .WRONLY, .CREAT = true, .TRUNC = true }, @as(std.c.mode_t, 0o644));
    _ = std.c.dup2(out, 1);
    const status = run(arena, io, r7_root ++ "/fake-explorer.sh", &.{
        "--tape", tape, "--property", "balances add up", "--variants", "6", "--jobs", "1", "--draw", draw, "--json",
    });
    _ = std.c.dup2(saved, 1);
    _ = std.c.close(out);
    try std.testing.expectEqual(@as(u8, 0), try status);
    const report_text = try cwd.readFileAlloc(io, r7_root ++ "/report-out.json", arena, .limited(1 << 20));
    std.debug.print("\n--draw {s}: {s}\n", .{ draw, report_text });
    const log = try cwd.readFileAlloc(io, r7_root ++ "/variants.log", arena, .limited(1 << 20));
    var seen: std.StringHashMapUnmanaged(void) = .empty;
    var lines = std.mem.tokenizeScalar(u8, log, '\n');
    while (lines.next()) |line| {
        if (std.mem.indexOf(u8, line, "{\"pull\":30,") == null) continue;
        try seen.put(arena, line, {});
    }
    return .{ .distinct = seen.count(), .needed = std.mem.indexOf(u8, report_text, "\"verdict\":\"needed\"") != null };
}

test "round 7, CE57: each of a set value's m variants is a history of its own" {
    try std.testing.expectEqual(@as(usize, 6), try r7_explain_variants("clock_step.ms=0"));
}

test "round 7, CE57's consequence: a value whose one history does not fail is not called needed" {
    // 8: the one replay of the timeline with clock_step.ms answered 8 does not fail (its
    // overrides hash to 0 modulo 6), its 6 copies "0 of 6", the control's 6 histories 5 of 6.
    try std.testing.expect(!(try r7_explain("clock_step.ms=8")).needed);
}

test "round 7, CE57's control: a named draw's m fresh values are m histories" {
    try std.testing.expectEqual(@as(usize, 6), try r7_explain_variants("clock_step.ms"));
}
