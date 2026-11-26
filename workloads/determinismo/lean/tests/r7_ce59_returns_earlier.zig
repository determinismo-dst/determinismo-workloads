// Round 7, a new counterexample of df8f08b (CE26's remainder): CE26's fix keeps archive_returns
// from taking a moment the generation already returns to (main.zig:7482-7486), but the
// generation's returns are then moved by returns_earlier (main.zig:6699, 7212-7226: a return
// with `earliest_ns`, the frontier's and every archive cell's, lands earlier by an offset drawn
// from --return-offsets, by default 0 half the time, else 1, 5 or 30 s). Two distinct moments
// of one timeline 1, 4, 5, 25, 29 or 30 s apart become one: two nodes and their branches at one
// moment again, and two `planned` lines under one key (generation, branch, moment), of which a
// resume keeps the last (Resumed.plan_note's `put`): the first's numbers passed over, never run.
// Property: df8f08b's test "a generation never returns twice to one moment" (main.zig:6072);
// CE26's fix's comment (7482-7486).
// Run against copies of returns_earlier, TreeReturn and return_offsets_default (main.zig, both
// versions identical there). The test: over 64 seeds of the generation's draw, a frontier return
// and an archive cell's place on #0, 5 s apart, never meet: red on df8f08b (and a7fe05d). Its
// control: 3 s apart (no two offsets differ by 3 s): green.

fn r7_meet(apart_ns: u64) !u32 {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const start_ns = 2 * std.time.ns_per_s;
    const returns = [_]TreeReturn{
        .{ .branch = 0, .vtime_ns = start_ns + 40 * std.time.ns_per_s + 1000, .why = "the frontier", .earliest_ns = start_ns + 1000 },
        .{ .branch = 0, .vtime_ns = start_ns + 40 * std.time.ns_per_s + 1000 + apart_ns, .why = "the archive", .cell = 7, .earliest_ns = start_ns + 1000 },
    };
    var met: u32 = 0;
    for (0..64) |seed| {
        var random: std.Random.DefaultPrng = .init(seed);
        const moved = try returns_earlier(arena, &return_offsets_default, &returns, &random);
        if (moved[0].branch == moved[1].branch and moved[0].vtime_ns == moved[1].vtime_ns) met += 1;
    }
    return met;
}

test "round 7, CE59: a generation's returns, moved earlier, never meet at one moment" {
    try std.testing.expectEqual(@as(u32, 0), try r7_meet(5 * std.time.ns_per_s));
}

test "round 7, CE59's control: returns 3 s apart never meet" {
    try std.testing.expectEqual(@as(u32, 0), try r7_meet(3 * std.time.ns_per_s));
}
