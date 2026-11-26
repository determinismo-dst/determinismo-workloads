
// Round 8: CE59's recheck beyond its minimal case. Lists of 2 to 6 returns on two branches, at
// distinct whole seconds from 30 to 41 (moments 1, 4, 5, 25, 29 or 30 s apart are common), each
// moved (a frontier's or archive's: earliest at 1 s) or not (a strategy's), over 2,000 lists and
// a seed each; returns_earlier with the default offsets (0 half the time, else 1, 5 or 30 s).
// Property: main.zig's test "a generation never returns twice to one moment" (CE26), and
// c4f246e's returns_earlier comment (7271-7273: "Never onto a moment another return of the
// generation has"). Red on df8f08b; green on c4f246e.
test "round 8, CE59: a generation's returns, moved earlier, never meet, whatever their moments" {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const s = std.time.ns_per_s;
    var met: usize = 0;
    var lists = std.Random.DefaultPrng.init(8);
    for (0..2000) |seed| {
        const r = lists.random();
        const count = 2 + r.uintLessThan(usize, 5);
        var returns: [6]TreeReturn = undefined;
        var made: usize = 0;
        while (made < count) {
            const branch = r.uintLessThan(u32, 2);
            const at = (30 + r.uintLessThan(u64, 12)) * s;
            const taken = for (returns[0..made]) |other| {
                if (other.branch == branch and other.vtime_ns == at) break true;
            } else false;
            if (taken) continue;
            returns[made] = .{ .branch = branch, .vtime_ns = at, .why = "a return", .earliest_ns = if (r.boolean()) s else null };
            made += 1;
        }
        var random: std.Random.DefaultPrng = .init(seed);
        const moved = try returns_earlier(arena, &return_offsets_default, returns[0..count], &random);
        for (moved, 0..) |a, i| for (moved[i + 1 ..]) |b| {
            if (a.branch == b.branch and a.vtime_ns == b.vtime_ns) met += 1;
        };
    }
    try std.testing.expectEqual(@as(usize, 0), met);
}
