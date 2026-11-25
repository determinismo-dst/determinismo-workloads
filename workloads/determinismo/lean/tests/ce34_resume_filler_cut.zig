// CE34: while a judgment's nodes are made, a worker that frees up with nothing queued takes a
// fresh filler at the next index, recorded `{"fresh":{generation,index}}` (queue_take
// 4562-4574); the judgment's made nodes are planned as they come (judge_plan_ready). A filler
// taken between two of a judgment's plans has an index between theirs. rejudge_load (4694-4698)
// queues a generation's recorded fillers first, each at the next index, and `.cut`s the resume
// when one is not: "The fresh timelines taken while it was judged, before its plan as they were"
// (4692). After the cut the run's loop takes the recorded members from the queue (their
// summaries, 4303-4310), judges the generation again (recording it a second time), and numbers
// its returns' timelines and new fillers by the resumed host's timing: the recorded filler's
// index goes to a return's child, its summary judged so; the later generations' records are
// never judged again.
// Promise: tree_rejudge (4643-4646: "A resumed run's recorded generations judged again ... the
// queue is then the interrupted run's. A generation whose summaries the interruption cut ends
// it"); Rejudged.cut (4665-4669: "Not the plan its record was made with, or cut by the
// interruption"): here the record is this plan's and whole.
// Minimal case (Replica/Resume4.lean, theorem ce34_filler_cut): generation 0 = 0 to 4, returns
// #0 at 10 ms and #1 at 20 ms (two branches each). #0's node made: 5, 6; two workers take them;
// a third frees up: filler 7; #1's node made: 8, 9; the fill 10. Stopped after 7 finished. The
// resume: fresh [7] while next_index is 5: `.cut`; the loop judges generation 0 again: #0's 5, 6
// and #1's 7, 8 (no worker freed up between), 9 fresh: timeline 7 (a filler from the setup
// snapshot) is judged as #1's child.

// Unit test, in src/main.zig beside "a resumed run's recorded generations: the earlier ones
// judged at once, the last left to the run's loop" (after 4772), with that test's state:
test "a filler taken between a judgment's plans keeps the resume going" {
    const arena = std.testing.allocator;
    var state: TreeState = undefined;
    state.queue = .empty;
    state.queue_head = 0;
    state.filler_start = 0;
    state.users = .empty;
    state.generation = 0;
    state.rejudge_last = false;
    state.next_index = 5;
    state.total = 64;
    state.tape_directory = null;
    state.base = 1;
    defer state.queue.deinit(arena);
    defer state.users.deinit(arena);
    const setup: *const Snapshot = @ptrFromInt(@alignOf(Snapshot));
    for (0..5) |index| try queue_push(arena, &state, .{ .index = @intCast(index), .seed = index, .snapshot = setup });
    const items = try arena.alloc(Summary, 5);
    defer arena.free(items);
    var batch: Batch = .{ .items = items, .scratch = &.{}, .spare = &.{} };
    batch.summaries.items = items;
    defer batch.plan.deinit(arena);
    var resumed: Resumed = .{};
    defer resumed.summaries.deinit(arena);
    defer resumed.generations.deinit(arena);
    defer resumed.fresh.deinit(arena);
    var recorded: [5]SummaryHeader = undefined;
    for (&recorded, 0..) |*header, index| {
        header.* = .{ .index = @intCast(index), .behavior_count = 0, .start_ns = 0, .end_ns = 100, .trace_hash = index, .last_pull_ns = 0, .cut = 0 };
        try resumed.summaries.put(arena, @intCast(index), std.mem.asBytes(header));
    }
    try resumed.generations.append(arena, &.{ 0, 1, 2, 3, 4 });
    // Its judgment planned #0's 5 and 6, a worker took filler 7, then #1's 8 and 9.
    try resumed.fresh.append(arena, .{ .generation = 0, .index = 7 });
    // The record is this plan's and whole: judged again (the loop's, as the last), never cut.
    // At 3939448: Rejudged.cut (7 != next_index 5).
    try std.testing.expectEqual(Rejudged.last, try rejudge_load(arena, &state, &batch, &resumed, 0, setup));
}

// e2e: as CE32's, with fillers between plans made likely (--jobs 8, --pipeline 1, a system whose
// node replays take longer than its timelines): after the resume, the log has no generation line
// twice in the record (`{"generation":{"number":g` once per g), and the lineage check holds.
