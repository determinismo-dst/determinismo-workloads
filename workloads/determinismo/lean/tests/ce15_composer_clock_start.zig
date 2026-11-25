// CE15: a timeline's drawn wall clock start reaches the cap, a setup's token's hour.
// Where: guest/runtime/composer.zig, beside `test clock_start_bands` (after line 957).
// Fails at 3939448: clock_start_band(hour, 11).high == hour.

test "a timeline's drawn wall clock start never reaches what a setup made to expire" {
    // clock_start_draw's comment: "not past what a setup made to expire (a token's hour, a
    // lease)". The default cap is an hour, and the last band ends at the cap itself: a token the
    // setup issued for an hour is expired as the drivers begin (the time since the setup comes
    // on top). Every band must end short of the cap by the time a timeline spends between its
    // setup and its drivers (here: any at all).
    const hour = std.time.ms_per_hour;
    var band: u64 = 0;
    while (band < clock_start_bands(hour)) : (band += 1) {
        try std.testing.expect(clock_start_band(hour, band).high < hour);
    }
}
