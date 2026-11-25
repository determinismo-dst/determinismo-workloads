// CE23: a timeline given another seed by its strategy (`branch` reply, docs/PLUGINS.md) is
// returned to with the seed the tree planned for it, not the one it ran with: its children's
// tapes name the planned seed in their chain, so they do not replay; and a node replayed from
// its parent's start (no holder, or a deciding strategy, or an archive return to an earlier
// generation's timeline) is a state the parent never had.
// Where: src/main.zig. Fails at 3939448:
//   - explore_branches 3474-3486: `if (choice.seed) |seed| place.seed = seed;` in the worker;
//   - Summaries.note 3898-3937: the summary carries the jitter seed the worker used, not the seed;
//   - tree_judge_begin 6362-6365: only `jitter_seed` is copied back into the plan entry;
//   - judge_plan_one 6280-6286: `.seed = parent.seed` (the plan's) in the children's path;
//   - maker_begin 7704-7712: `Recorded.load(..., parent.index, parent.seed, ...)`, node_make_start
//     7485 `assert(parent_recorded.seed == parent.seed)`: the replay with the plan's seed
//     (src/core/node.zig:30-39 Recorded.load takes the seed it is given); branch_announce
//     3754-3780 writes `.branch_seed = place.seed` (the strategy's) and `.chain = place.path`.
// The e2e check `branch-seeds` (tools/e2e.zig:2148-2178) runs 3 flat branches only.

// 1. Unit test, beside "a plugin's returns are kept whole and the archive fills around them"
// (main.zig, after 5917): the plan a judged timeline's returns are built from has the seed it
// ran with. It needs Summary to carry it (as it carries `jitter_seed`), and tree_judge_begin to
// copy it as it copies the jitter (6362-6365); written against that copy, made a function:
//     fn plan_as_ran(plan: []Planned, done: []const *const Summary) void
test "a judged timeline's plan has the seed it ran with: its children's chain replays it" {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var plan = [_]Planned{.{ .index = 4, .seed = branch_seed(7, 4), .snapshot = @ptrFromInt(@alignOf(Snapshot)) }};
    const summary = try arena.create(Summary);
    summary.index = 4;
    summary.jitter_seed = null;
    summary.seed = 0x42; // plugins/python/same_seed.py's, given at its `branch`.
    const done = [_]*const Summary{summary};
    plan_as_ran(&plan, &done);
    try std.testing.expectEqual(@as(u64, 0x42), plan[0].seed);
}

// 2. e2e, beside check_branch_seeds (tools/e2e.zig:2151): the same plugin in a tree.
fn check_branch_seeds_tree(context: *Context) !void {
    const arena = context.arena;
    const program = try std.fs.path.join(arena, &.{ context.bin, "bank-test" });
    const tapes = try std.fs.path.join(arena, &.{ context.scratch, "seed-tree-tapes" });
    // Two generations of 16 and their returns: timelines 48 and on start inside others.
    const report = try explore(context, &.{
        "--program",    program,     "--scenario", "bank", "--seed", "3",
        "--branches",   "64",        "--jobs",     "1",    "--branching", "tree",
        "--strategy",   "python3 plugins/python/same_seed.py 0x42", "--tape-dir", tapes,
    });
    var branches: [64]Branch = undefined;
    const count = parse_branches(report, &branches);
    var returned: ?usize = null;
    for (branches[0..count], 0..) |branch, at| if (branch.index >= 48) {
        returned = at;
        break;
    };
    const at = returned orelse return expect_all(context, &.{.{ "a returned timeline", false }}, "branch seeds in a tree", .{});
    const tape = try std.fmt.allocPrint(arena, "{s}/branch-{d}.jsonl", .{ tapes, branches[at].index });
    const replay = try explore(context, &.{ "--program", program, "--scenario", "bank", "--seed", "3", "--tape", tape });
    var replayed: [1]Branch = undefined;
    const same = parse_branches(replay, &replayed) == 1 and std.mem.eql(u8, replayed[0].events_hash, branches[at].events_hash);
    expect_all(context, &.{
        // At 3939448 the replay runs its parent's part with branch_seed(3, parent), not 0x42.
        .{ "a timeline returned to inside one the strategy seeded replays alone from its tape", same },
    }, "branch seeds in a tree", .{});
}
