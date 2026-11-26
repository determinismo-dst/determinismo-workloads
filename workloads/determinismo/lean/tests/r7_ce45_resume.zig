// Round 7: CE45 against both versions. A run of two timelines, each passing its one evaluated
// `always`, whose catalog has an assertion no timeline reached: the run's verdict fails (its
// end judges the catalog, `r7_run_end`: each version's own lines). The complete run resumed
// again (`--resume` on its record: its process ends in resume_read with the record's verdict)
// must end as the run did: status 3.
// Property: main.zig (a7fe05d 2244-2246, df8f08b 2336-2338): "Judged from its record, as the run
// that recorded it would have been"; docs/ANTITHESIS.md's catalog (an assertion no timeline
// reached fails the run).
// Red on a7fe05d (0: the record has no catalog), green on df8f08b (RecordLine.catalog, 3).
// The second test is CE45's remainder (round 6's session path): a session's timeline took the
// run's number 1 (its line extends #0): resume_read never finds the run complete, the resumed
// run goes the explorer's way (status 100 here), where the recorded catalog is never read
// (Resumed.catalog_failing is read in complete_verdict alone) and an empty catalog is judged,
// then recorded: red on both.

fn r7_run_end(arguments: *const Arguments, catalog: *const R7Catalog, every_scenario: bool, failing_out: *u32) void {
    var failing_scenarios: u32 = 0;
    R7_RUN_END
    failing_out.* = failing_scenarios;
}

fn r7_resumed_status(record: []const u8) !u32 {
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.writeFile(io, .{ .sub_path = "record.jsonl", .data = record });
    var root_buffer: [4096]u8 = undefined;
    const root = root_buffer[0..try tmp.dir.realPathFile(io, ".", &root_buffer)];
    var path_buffer: [4200]u8 = undefined;
    const path = try std.fmt.bufPrint(&path_buffer, "{s}/record.jsonl", .{root});
    const child = std.c.fork();
    if (child == 0) {
        var arena_state: std.heap.ArenaAllocator = .init(std.heap.page_allocator);
        const arguments: Arguments = .{ .record_path = path };
        _ = resume_read(.{ .arena = arena_state.allocator(), .io = io }, &arguments, 0xaa) catch std.process.exit(101);
        std.process.exit(100); // Not complete: the explorer's way.
    }
    var status: c_int = 0;
    _ = std.c.waitpid(child, &status, 0);
    return @intCast((@as(u32, @bitCast(status)) >> 8) & 0xff);
}

fn r7_record(session_took_1: bool) ![]const u8 {
    report.lines = .empty;
    const header = "{\"run\":{\"inputs\":\"00000000000000aa\",\"seed\":\"0000000000000007\",\"branching\":\"flat\"}}\n";
    try report.lines.appendSlice(std.testing.allocator, header);
    const passing = "\"properties\":[{\"message\":\"a\",\"kind\":\"always\",\"hits\":1,\"trues\":1}]";
    try report.lines.appendSlice(std.testing.allocator, "{\"branch\":{\"index\":0," ++ passing ++ "}}\n");
    if (session_took_1) {
        try report.lines.appendSlice(std.testing.allocator, "{\"branch\":{\"index\":1,\"extends\":{\"branch\":0,\"vtime_ns\":5}," ++ passing ++ "}}\n");
    } else {
        try report.lines.appendSlice(std.testing.allocator, "{\"branch\":{\"index\":1," ++ passing ++ "}}\n");
    }
    // The run's end: its catalog judged, one assertion no timeline reached.
    var failing_scenarios: u32 = 0;
    const arguments: Arguments = .{};
    r7_run_end(&arguments, &.{ .failing = 1 }, true, &failing_scenarios);
    try std.testing.expectEqual(@as(u32, 1), failing_scenarios);
    return report.lines.items;
}

test "round 7, CE45: a complete run resumed again fails for its catalog as the run did" {
    defer report.lines.deinit(std.testing.allocator);
    try std.testing.expectEqual(@as(u32, 3), try r7_resumed_status(try r7_record(false)));
}

test "round 7, CE45's remainder: so does one whose missing number a session's timeline took" {
    defer report.lines.deinit(std.testing.allocator);
    try std.testing.expectEqual(@as(u32, 3), try r7_resumed_status(try r7_record(true)));
}
