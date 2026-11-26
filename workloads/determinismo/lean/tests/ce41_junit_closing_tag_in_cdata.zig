// CE41: CE16's fix skips a case's `<system-out>`/`<system-err>` to the first closing tag after it
// (junit.zig:72-81, `indexOfPos(body, tag_end, "</system-out>")`), whatever lies between: a CDATA
// section of captured output that holds that closing tag ends the skip early, and an `<error` or
// `<failure` printed after it fails a passing test, in every timeline. A test of anything that
// writes JUnit XML (a reporter, a CI tool, a test framework's own suite) prints exactly that;
// Surefire, jest-junit and go-junit-report write the output in CDATA as is.
// Where: guest/runtime/junit.zig, beside "a test case's captured output never fails it" (after
// line 205). Needs only std.
// Fails at 62e06e3: compiled and run against a copy of junit.zig (scratch/zig5/junit).

test "captured output that prints its own closing tag never fails its test" {
    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const report =
        \\<testsuite>
        \\<testcase classname="report.WriterTest" name="writes_an_error" time="0.1"><system-out><![CDATA[expected:
        \\<system-out>log</system-out><error message="boom"/>
        \\]]></system-out></testcase>
        \\<testcase classname="report.WriterTest" name="writes_a_failure" time="0.1"><system-err><![CDATA[</system-err><failure message="no"/>]]></system-err></testcase>
        \\</testsuite>
    ;
    const found = try cases(arena_state.allocator(), report);
    try std.testing.expectEqual(@as(usize, 2), found.len);
    try std.testing.expect(!found[0].failed);
    try std.testing.expect(!found[1].failed);
}
