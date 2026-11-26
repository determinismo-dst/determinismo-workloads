// CE49: CE41's fix made a captured element's closing tag CDATA-aware (captured_end,
// junit.zig:92-103), but `cases` (junit.zig:14-20) still ends a case's body at the first
// `</testcase>` after its tag and looks for the next `<testcase` from there, through any CDATA:
// a test that prints test cases (a test of a JUnit writer, a reporter, a CI tool, a test
// framework's own suite; Surefire, jest-junit and go-junit-report write output in CDATA as is)
// has its body cut inside its own output. What follows is read as the report's: a printed
// `<testcase ...><failure .../>` becomes a test of its own, failing in every timeline (the job
// fails; a printed name equal to a real test's adds its failure to that test), and a real
// `<failure>` after such output is never seen (the test passes). The same with a suite's own
// `<system-out>` that prints a `<testcase` (go-junit-report writes the package's output there).
// Property: junit.zig:2-6 ("each `<testcase>`'s classname and name, whether it holds a
// `<failure>` or an `<error>`"); a7fe05d's test "captured output that prints its own closing tag
// never fails its test"; docs/CI.md (Verdicts per test: "each test is a property of its own").
// Where: guest/runtime/junit.zig, beside "captured output that prints its own closing tag never
// fails its test" (after line 240). Needs only std.
// Fails at a7fe05d: compiled and run against a copy of junit.zig (scratch/zig6/junit).

test "captured output that prints test cases makes no test of its own and hides no failure" {
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
