// CE44: CE15's fix bounds the default jump (30 minutes) plus one default driver phase (20) under a
// token's hour, and its comment says a timeline failing on the jump "takes a credential shorter
// than that" (composer.zig:907-912). A timeline's wall time after the jump is longer than one
// phase: a second phase for every return to an objective's best (drive_again, 1025-1028: asked
// while the first phase is under a quarter of the limit, 15 minutes), the length's 30 s grace
// (751), and the ending's command, up to 20 minutes (1113); all of it under the timeline limit
// (an hour), so none of it a hang. With the jump at its cap, a timeline of more than 30 minutes
// uses a setup's hour token past its expiry, which without the jump it never does.
// Where: guest/runtime/composer.zig, beside "the default wall clock start and the longest default
// drive stay within an hour" (after line 979).
// Fails at 62e06e3: 30 min + 15 min + 20 min = 65 min. The Lean replica counts 4,452 of 1,000,000
// drawn timelines of objective returns (endings of 1 s to 20 min), 1,315 of 1,000,000 with one
// phase, 0 of 1,000,000 with one phase and a 1 s ending (the case the fix's test checks).

test "the default wall clock start and a timeline under its limit stay within an hour" {
    const ending_ms_max = ending_ms_max_default;
    const quarter_ms = std.time.ms_per_hour / 4; // drive_again's bound, the default limit's quarter
    const drive_ms_max_default = 20 * std.time.ms_per_min;
    const bands = clock_start_bands(clock_start_max_default_ms);
    const jump_max = clock_start_band(clock_start_max_default_ms, bands - 1).high;
    // An objective's return: a first phase just under the quarter, a second at its longest, the
    // grace, then a check that ran its window (a system slow to come back).
    const timeline_ms = (quarter_ms - 1) + drive_ms_max_default + length_grace_ns / std.time.ns_per_ms + ending_ms_max;
    try std.testing.expect(timeline_ms < std.time.ms_per_hour); // Not a hang.
    try std.testing.expect(jump_max + timeline_ms < std.time.ms_per_hour);
}
