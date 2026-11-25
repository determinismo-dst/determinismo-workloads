// CE16: a passing test whose captured output mentions an error or failure element is judged
// failing in every timeline.
// Where: guest/runtime/junit.zig, beside its tests (after line 149).
// Fails at 3939448: `cases` looks for the text "<failure" or "<error" anywhere in the body
// (junit.zig:32), CDATA output included.

test "a test case's captured output never fails it" {
    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    // Surefire, jest-junit and go-junit-report write a case's output in CDATA, as is.
    const report =
        \\<testsuite>
        \\<testcase classname="api.ErrorsTest" name="renders_503" time="0.1"><system-out><![CDATA[<error code="503">unavailable</error>]]></system-out></testcase>
        \\<testcase classname="api.ErrorsTest" name="logs_failure" time="0.1"><system-err><![CDATA[<failure reason="timeout"/>]]></system-err></testcase>
        \\<testcase classname="api.ErrorsTest" name="fails" time="0.1"><failure message="no">x</failure><system-out><![CDATA[ok]]></system-out></testcase>
        \\</testsuite>
    ;
    const found = try cases(arena_state.allocator(), report);
    try std.testing.expectEqual(@as(usize, 3), found.len);
    try std.testing.expect(!found[0].failed);
    try std.testing.expect(!found[1].failed);
    try std.testing.expect(found[2].failed);
}
