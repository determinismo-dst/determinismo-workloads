// CE13 (lean/determinismo REPORT.md): a checkpoint whose event count the replay passes on a
// VM-made event (a kernel line, a strategy's decision event: vm.zig emits them without
// vm.checkpoint) is never compared, and neither is any later one. Red on 0dea225's tape.zig:
// the replay's hashes differ from the tape's at every later checkpoint, and check() reports none.
const std = @import("std");
const tape = @import("tape.zig");

test "a replay that passes over a checkpoint's count still reports its divergence" {
    const overrides = try std.testing.allocator.create(tape.Overrides);
    defer std.testing.allocator.destroy(overrides);
    overrides.* = .{ .entries = undefined, .count = 0, .cursor = 0 };
    // The recording: checkpoints at events 64, 128 and 192 (guest lines there).
    for ([_]u64{ 64, 128, 192 }, 1..) |events, i| {
        overrides.checkpoints[overrides.checkpoint_count] = .{ .events = events, .branches = 0, .events_hash = i };
        overrides.checkpoint_count += 1;
    }
    // The replay: one extra kernel line before event 64, so event 64 is that line (no check
    // call), and the guest lines at 128 and 192 carry other hashes.
    var diverged = false;
    for ([_]u64{ 128, 192 }) |events| {
        overrides.check(.{ .events = events, .branches = 0, .events_hash = 999 }) catch |err| {
            try std.testing.expectEqual(error.ReplayDiverged, err);
            diverged = true;
        };
    }
    try std.testing.expect(diverged);
}

test "control: the same divergence at a compared count is reported" {
    const overrides = try std.testing.allocator.create(tape.Overrides);
    defer std.testing.allocator.destroy(overrides);
    overrides.* = .{ .entries = undefined, .count = 0, .cursor = 0 };
    overrides.checkpoints[0] = .{ .events = 64, .branches = 0, .events_hash = 1 };
    overrides.checkpoint_count = 1;
    try std.testing.expectError(error.ReplayDiverged, overrides.check(.{ .events = 64, .branches = 0, .events_hash = 999 }));
}
