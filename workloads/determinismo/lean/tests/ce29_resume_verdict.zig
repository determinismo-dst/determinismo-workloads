// CE29: a stopped run resumed reads "passed" when a timeline recorded before the stop failed:
// the resumed explorer's verdict is the timelines it runs (the recorded ones skipped:
// explore_branches 3460-3462, nothing absorbed), and when every timeline was recorded
// resume_read exits 0 at once (2186-2192: "the run is complete"). Serve's state is that status
// (state 6226-6235); its properties page, over every timeline, says failing. The other way too:
// a `sometimes` made true only before the stop is judged never true by the resumed run (exit 3,
// "failed", the properties passing).
// serve.zig:5912: "A failing property fails the run, as explore exits"; serve.zig:5630-5633
// run_resume: "Continues a run that ended before its end ...: its explorer again".
// Where: src/main.zig 2103-2194 (resume_read), 3460-3462, 1106-1170 (system_run's verdict).

// Unit test, beside "a resumed run keeps the archive and pipeline its record says" (main.zig,
// after 2380): the verdict a resume starts from is its record's. Written against resume_read's
// parse made a function of the record's text (`resume_parse(arena, text, inputs, seed,
// branching, branches)`, the file read left to resume_read), keeping the recorded timelines'
// failing properties (each record line's `failing`, report.zig:483) and the status a complete
// record ends with (`status_when_complete`, what 2189-2192 exits with: 0 at 3939448):
test "a resumed run's verdict counts the timelines its record has" {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const record =
        \\{"run":{"seed":"0000000000000007","inputs":"00000000000000aa","branching":"flat"}}
        \\{"branch":{"index":0,"seed":"0000000000000001","outcome":"shutdown","failing":["balance is conserved"]}}
        \\{"branch":{"index":1,"seed":"0000000000000002","outcome":"shutdown","failing":[]}}
        \\
    ;
    const resumed = try resume_parse(arena, record, 0xaa, 7, .flat, 2);
    // Every timeline recorded: the run is over, and it failed (exit 3, not 0).
    try std.testing.expectEqual(@as(u8, 3), resumed.status_when_complete);
}

// e2e (serve): POST /runs {program: bank-test, scenario: bank, branches: 40, branching: flat};
// once timeline 2 (failing "balance is conserved") is in the record, POST /runs/<id>/stop; then
// POST /runs/<id>/resume and wait. Assert GET /runs/<id> "state": "failed" (its properties list
// the failing one). At 3939448: "passed" whenever no timeline after the stop fails, and at once
// when the stop came after the last timeline's line.
