
// Round 8, CE65: c4f246e records an assertion declared and not reached as a record line of its own,
// "once a run; a worker's" (report.zig:553-557), "the first time the run saw it" (main.zig:2264,
// RecordLine.declared), skipping a property its multiverse knows (aggregate_known). A tree's
// timeline runs in a process of its own (timeline_start, main.zig:5345-5361: worker_run for one
// timeline), whose multiverse starts empty (worker_run, main.zig:3394 `mine.multiverse.* = .{}`):
// every timeline of a tree writes a line for each declaration it did not reach. A run's record
// then grows by its unreached declarations times its timelines (the record is read whole by a
// resume, and serve reads at most 256 MiB of it: serve.zig run_file).
// Property: report.zig:553-557 ("its declaration a record line of its own (once a run; a
// worker's)"), main.zig:2264 ("An assertion declared and not reached, the first time the run saw
// it").
// The test: 4 timelines, each declaring reachable "r" and never reaching it: a tree's (a fresh
// multiverse each, as each timeline's process has) writes one line for the run. Red on c4f246e
// (4). Its control: a flat run's worker (one multiverse for its 4 timelines): 1, green.
fn r8_declared(vm: *const R8Vm, multiverse: *Multiverse) void {
    R8_DECLARED_STATEMENT
}

fn r8_timeline(multiverse: *Multiverse, index: u32) !void {
    var vm: R8Vm = .{};
    vm.events.properties[0] = .{ .kind = .reachable, .message = "r" };
    vm.events.properties[1] = .{ .kind = .always, .message = "a", .hits = 1, .trues = 1 };
    vm.events.property_count = 2;
    r8_declared(&vm, multiverse);
    // Then, as Multiverse.add goes on (report.zig:584-585), every property merged.
    for (vm.events.properties[0..vm.events.property_count]) |*property| try multiverse.merge(property, index);
}

test "round 8, CE65: a tree's run records a declaration once" {
    r8_declared_lines = 0;
    for (0..4) |index| {
        var multiverse: Multiverse = .{}; // Each timeline's process (main.zig:3394).
        try r8_timeline(&multiverse, @intCast(index));
    }
    try std.testing.expectEqual(@as(usize, 1), r8_declared_lines);
}

test "round 8, CE65's control: a flat run's worker records it once" {
    r8_declared_lines = 0;
    var multiverse: Multiverse = .{};
    for (0..4) |index| try r8_timeline(&multiverse, @intCast(index));
    try std.testing.expectEqual(@as(usize, 1), r8_declared_lines);
}
