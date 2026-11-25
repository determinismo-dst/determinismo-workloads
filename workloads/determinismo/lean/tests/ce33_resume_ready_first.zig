// CE33: a resumed tree's last recorded generation is judged by the run's loop (rejudge_load
// 4720-4723, `.last`), whose polls plan each made node's timelines as it comes
// (tree_judge_poll 6219-6233, judge_plan_ready 6254-6261). A return whose timelines are all
// recorded is `ready` from the start (6455-6466): planned at the first poll, before returns
// whose nodes are still being made, so its timelines take the first numbers. The record's
// order (recorded_returns, by first child) is lost: recorded timelines are judged under
// another return, and a timeline that never ran gets a ready return's plan: it starts from the
// setup snapshot (the ready making's snapshot) while its path, its events' header and its tape's
// chain say it begins inside the return's timeline.
// Promise: main.zig:242-244, 4643-4646, 4552-4561 (as CE32); README_AI.md ("every timeline
// replays bit-identically"); docs/ANTITHESIS.md, Branching ("every timeline's path in its record
// and tape (it replays alone)").
// Minimal case (Replica/Resume4.lean, theorem ce33_ready_first): generation 0 = timelines 0 to
// 4, returns to #0 at 10 ms and #1 at 20 ms (two branches each): 5, 6 (#0's), 7, 8 (#1's), the
// fill 9. Stopped after 6, 7 and 8 finished. The resume: recorded_returns [#0, #1], #1 ready
// (its 2 timelines recorded), #0 made (by a replay, in the makings' order). The first poll plans
// #1's: 5 and 6; #0's node, made, gets 7 and 8. Timeline 5 never ran and starts at the setup
// snapshot as #1's child; 6 (#0's) is judged as #1's, 7 and 8 (#1's) as #0's.

// Unit test, in src/main.zig beside "a resumed run's recorded generations: the earlier ones
// judged at once, the last left to the run's loop" (after 4772), on judge_plan_ready's choice of
// the next making to plan made a function:
//     fn plan_next(makings: []const NodeMaking, in_order: bool) ?usize
// (the first making not planned that is ready; with `in_order`, a resumed generation's, the first
// not planned, and none until it is ready).
test "a resumed generation's timelines are numbered in its record's order, ready returns waiting their turn" {
    var makings = [_]NodeMaking{
        .{ .back = .{ .branch = 0, .vtime_ns = 10, .why = "Recorded" }, .parent = .{ .index = 0, .seed = 0, .snapshot = undefined } },
        .{ .back = .{ .branch = 1, .vtime_ns = 20, .why = "Recorded" }, .parent = .{ .index = 1, .seed = 1, .snapshot = undefined }, .ready = true },
    };
    // #0's node is still being made: nothing is planned yet (its timelines come first).
    try std.testing.expectEqual(@as(?usize, null), plan_next(&makings, true));
    makings[0].ready = true;
    try std.testing.expectEqual(@as(?usize, 0), plan_next(&makings, true));
    makings[0].planned = true;
    try std.testing.expectEqual(@as(?usize, 1), plan_next(&makings, true));
}

// e2e: CE32's (the lineage check and --verify-replays 100 after a resume); kill the run once a
// generation's later returns' timelines have all finished and an earlier one's have not
// (--jobs 4, a return whose first child is slow: `--generation 8 --return-branches 2`). Also:
// each resumed timeline's events start at or after its path's last moment (`SELECT min(vtime_ns)
// FROM events WHERE branch = i` against the path's last vtime): at 3939448 a ready return's
// unrecorded child starts at the setup's.
