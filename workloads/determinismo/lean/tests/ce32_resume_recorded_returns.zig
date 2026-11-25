// CE32: a resumed tree's judgment of its last recorded generation takes its returns from the
// record's timelines (recorded_returns, src/main.zig:6820-6841): one per (generation, branch,
// moment) key that has a recorded child, in the order of their first child. A return none of
// whose timelines finished before the stop is dropped, and two returns to one moment (CE26)
// are one. The resumed judgment then numbers the returns' timelines (judge_plan_one,
// 6263-6310) from that shorter list: a recorded timeline is planned under another return, or
// as fresh, and its summary judged so (archive_add: state.planned[i] the new plan). A later
// return to it replays another timeline than the one that ran (maker_begin 7704-7714 replays
// `parent.path` with `parent.seed`), and a recorded `ready` return's timeline that never ran is
// started from the setup snapshot under its path (6455-6466: "its timelines are planned from
// the setup snapshot, never started").
// Promise: --resume (main.zig:242-244: "continue that run, its recorded timelines skipped");
// tree_rejudge (4643-4646: "the queue is then the interrupted run's"); queue_take (4552-4561:
// "so that every index keeps its timeline"); 4136-4139 ("a resumed run judges the same
// generations again").
// Minimal case (Replica/Resume4.lean, theorem ce32_dropped_return): generation 0 = timelines 0
// to 3, returns to #0 at 10 ms, #1 at 20 ms, #2 at 30 ms (one branch each), numbered 4, 5, 6,
// the fill 7. Stopped after 6 alone finished. The resume: recorded_returns = [#2 at 30 ms],
// ready; 4 is planned #2's child (from the setup snapshot, never started: its record line says
// nothing), 5, 6, 7 fresh: timeline 6's summary is judged as a fresh timeline's.

// Unit test, in src/main.zig beside `test recorded_returns` (after 6859), on resume_read's parse
// of the record (2119-2165) made a function:
//     fn resume_parse(arena, source: []const u8, arguments: *const Arguments, inputs: u64) !*Resumed
// and with the fix's record of each judgment's returns (here, the generation line's "returns",
// which 3939448 ignores: RecordLine parses with ignore_unknown_fields).
test "a resumed run's recorded returns are its judgment's: one whose timelines did not finish, two at one moment" {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const arguments: Arguments = .{ .command = .explore, .branching = .tree, .generation_size = 4, .return_branches = 1, .pipeline = 1 };
    const record =
        \\{"run":{"inputs":"0000000000000000","seed":"0000000000000000","branching":"tree","generation":4,"pipeline":1,"archive":true,"return_branches":1,"queue":true}}
        \\{"generation":{"number":0,"branches":[0,1,2,3],"returns":[{"branch":0,"vtime_ns":10000000},{"branch":1,"vtime_ns":20000000},{"branch":2,"vtime_ns":30000000}]}}
        \\{"branch":{"index":0,"generation":0,"path":[]}}
        \\{"branch":{"index":1,"generation":0,"path":[]}}
        \\{"branch":{"index":2,"generation":0,"path":[]}}
        \\{"branch":{"index":3,"generation":0,"path":[]}}
        \\{"branch":{"index":6,"generation":1,"path":[{"branch":2,"vtime_ns":30000000}]}}
    ;
    const resumed = try resume_parse(arena, record, &arguments, 0);
    const returns = (try recorded_returns(arena, resumed, 1)).?;
    // The judgment's three returns, in its order: timeline 6 keeps its plan (#2's child).
    try std.testing.expectEqual(@as(usize, 3), returns.len);
    try std.testing.expectEqual(@as(u32, 0), returns[0].branch);
    try std.testing.expectEqual(@as(u32, 1), returns[1].branch);
    try std.testing.expectEqual(@as(u32, 2), returns[2].branch);
}

test "two returns to one moment stay two in a resumed judgment" {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var resumed: Resumed = .{};
    // Generation 0's returns: #0 at 10 ms twice (CE26), #2 at 30 ms; their children 4, 5 and 6,
    // all recorded.
    try resumed.first_child.put(arena, .{ .generation = 1, .branch = 0, .vtime_ns = 10 }, 4);
    try resumed.children.put(arena, .{ .generation = 1, .branch = 0, .vtime_ns = 10 }, 2);
    try resumed.first_child.put(arena, .{ .generation = 1, .branch = 2, .vtime_ns = 30 }, 6);
    try resumed.children.put(arena, .{ .generation = 1, .branch = 2, .vtime_ns = 30 }, 1);
    const returns = (try recorded_returns(arena, &resumed, 1)).?;
    // Numbered as recorded: #0's two (4, 5), then #2's (6). At 3939448: two returns, #2's
    // child numbered 5.
    try std.testing.expectEqual(@as(usize, 3), returns.len);
}

// e2e (tools/e2e.zig, beside the resume check): a tree of 64 timelines, --generation 16,
// --jobs 4, --record and --tape-dir, killed (SIGKILL) once its record has 24 timeline lines;
// resumed with --resume --verify-replays 100. Assert, over the whole record after the resume:
// for every timeline line whose path's last place is (P, t), its path before that place equals
// timeline P's own record line's path (a node is its parent's state: lineage consistent); and
// every replay verifies. At 3939448 both fail whenever a return's timelines were all unfinished
// at the kill (or two returns shared a moment).
