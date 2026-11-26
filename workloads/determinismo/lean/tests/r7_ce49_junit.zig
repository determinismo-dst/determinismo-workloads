// Round 7: CE49 against both versions. Round 6's test (tests/ce49_junit_printed_testcase.zig),
// renamed, appended to copies of a7fe05d's and df8f08b's guest/runtime/junit.zig. Red on
// a7fe05d's ("expected 2, found 3"), green on df8f08b's (case_index skips CDATA and comments;
// captured_end finds a case's own </testcase>).

test "round 7, CE49: captured output that prints test cases makes no test of its own and hides no failure" {
    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const report =
        \\<testsuite>
        \\<testcase classname="report.WriterTest" name="writes_a_report" time="0.1"><system-out><![CDATA[<testsuite>
        \\<testcase classname="printed" name="ok"></testcase>
        \\<testcase classname="printed" name="bad"><failure message="x"/></testcase>
        \\</testsuite>]]></system-out></testcase>
        \\<testcase classname="report.WriterTest" name="closes_a_case" time="0.1"><system-out><![CDATA[</testcase>]]></system-out><failure message="expected two cases"/></testcase>
        \\</testsuite>
    ;
    const found = try cases(arena_state.allocator(), report);
    try std.testing.expectEqual(@as(usize, 2), found.len);
    try std.testing.expectEqualStrings("report.WriterTest::writes_a_report", found[0].name);
    try std.testing.expect(!found[0].failed);
    try std.testing.expectEqualStrings("report.WriterTest::closes_a_case", found[1].name);
    try std.testing.expect(found[1].failed);
}
