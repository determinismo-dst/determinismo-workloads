// CE42: a second driver phase starts drivers past half the timeline's limit. run_drivers draws its
// stop from its own start (`stop_ns = now_ns() + limit_ns / 2`, composer.zig:797); drive_again
// (1025-1028) asks for another phase up to a quarter of the limit after the first began, so the
// second phase's stop lies up to three quarters of the limit after the drivers began, and its
// starts after the half run on (CE5's fix, 809-813, bounds each slot wait by that later stop).
// The explorer answers `composer.again` yes once for every return to an objective's best
// (advisor.zig:79-83, `--objective-extend` on by default, main.zig:540); the stop exists with a
// timeline limit (an hour by default) and no length (`--drive-max none`).
// Property: composer.zig:792-795: "No driver starts past half the timeline's limit".
// Where: tests/selftest/selftest.zig, a scenario beside CE5's (`slot_wait`); run with
//   determinismo explore --program selftest --scenario half_limit_again --drive-max none \
//     --timeline-limit 600s --branches 8 --decide composer.parallelism_log2=0
// and a return asked for (an objective's best: the scenario's `sdk.optimize`), or the composer's
// `composer.again` answered 1 by --decide.
// Fails at 62e06e3: the Lean replica's world 17 (runs5/stop-world17.txt; theorem
// ce42_second_phase_starts_past_half): four starts at 0, 10, 20 and 30 ms (the fourth runs 270),
// the second phase asked at 30 ms with its stop at 330; its drivers start at 300 and 310, past 300.

const std = @import("std");
const sdk = @import("determinismo");

/// The scenario: one parallel driver (one at a time), a timeline limit of 600 s, no length; the
/// driver checks that the time since the drivers began (the first `drive` start, noted in a
/// file) is under half the limit when it starts.
pub fn half_limit_again(s: *sdk.Scenario) void {
    s.parallel_max = 1;
    s.parallel_driver("drive", drive);
}

const began_path = "/tmp/drivers-began-ns";
const limit_ns: u64 = 600 * std.time.ns_per_s;

fn drive() !void {
    const now: u64 = @intCast(std.time.nanoTimestamp());
    const began = read_began() orelse blk: {
        write_began(now);
        break :blk now;
    };
    sdk.always(now - began <= limit_ns / 2, "no driver starts past half the timeline's limit", .{ .since_ms = (now - began) / std.time.ns_per_ms });
    // Long enough that the second phase's slot wait crosses the first phase's half.
    std.Thread.sleep(270 * std.time.ns_per_s);
}

fn read_began() ?u64 {
    var buffer: [32]u8 = undefined;
    const text = std.fs.cwd().readFile(began_path, &buffer) catch return null;
    return std.fmt.parseInt(u64, std.mem.trim(u8, text, " \n"), 10) catch null;
}

fn write_began(ns: u64) void {
    var buffer: [32]u8 = undefined;
    const text = std.fmt.bufPrint(&buffer, "{d}\n", .{ns}) catch return;
    std.fs.cwd().writeFile(.{ .sub_path = began_path, .data = text }) catch {};
}
