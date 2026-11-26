// CE45: a resume that finds every timeline recorded judges the record's properties alone
// (main.zig:2212-2229: `failing_properties` over Resumed.merge_into, then exit): no catalog. Its
// comment (2215-2216): "A catalog's assertions no timeline reached are judged by the runs that
// ran timelines" — but the run that ran them was interrupted before its end, where system_run
// judges the catalog (main.zig:1157-1164) and writes `exit`. A record line keeps only the
// properties its timeline evaluated (report.zig:516, `hits == 0` skipped), so a declared
// `reachable` never reached, or a catalogued `sometimes` no timeline evaluated ("test command
// started: X" for a command never started), is nowhere: the resume exits 0 and writes `exit` "0"
// (serve: "passed", ended_status), where the run uninterrupted exits 3.
// A stop after the last record line and before the end is any stop during the end's replays
// (`--verify-replays`), its summary or its coverage: a deploy's restart of serve, a host's.
// Property: main.zig:2213-2214 ("Judged from its record, as the run that recorded it would have
// been"); serve.zig:5630-5633; CE29's.
// Where: src/main.zig, beside `test "what an explorer persists changes only with runs.state_format"`
// (after line 2332), on the complete path made a function of the record's lines
// (`resumed_verdict(lines) u8`, today inline at 2212-2229).
// Fails at 62e06e3 (the Lean replica: runs5/resume.txt; theorem ce45_complete_resume_skips_the_catalog).

test "a complete resume judges the catalog its record's run declared" {
    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    // Two timelines, each with the program's catalog as its setup declared it: `reachable
    // "leader elected"`, never reached. Their record lines as report.zig:513-560 writes them
    // (record_line_of: Multiverse.add's writer), after the run's line.
    var lines: std.ArrayList(u8) = .empty;
    try lines.appendSlice(arena, "{\"run\":{\"inputs\":\"00000000000000aa\",\"seed\":\"0000000000000007\",\"branching\":\"flat\"}}\n");
    for (0..2) |index| {
        var events: Events = .{};
        try events.declare(.reachable, "leader elected"); // As the setup's catalog declares it.
        try lines.appendSlice(arena, try record_line_of(arena, &events, @intCast(index)));
    }
    // Uninterrupted, the run exits 3 (Catalog.judge: a reachable no timeline reached); resumed
    // with both recorded, the same.
    try std.testing.expectEqual(@as(u8, 3), try resumed_verdict(arena, lines.items, 2));
}
