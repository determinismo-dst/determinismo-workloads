// CE37: tests_judge (src/products/ci.zig:440-485) counts the timelines without their JUnit
// report as `timelines - reported`, where `reported` is the most timelines any one test was hit
// in over the whole run, every shard's tests together (458), and `timelines` one shard's (474).
// A shard whose runner died before its report in some timelines goes unnoticed as soon as
// another shard's tests were reported in all of theirs: the line says no timeline lacked its
// report, the tests' verdict is not "error", and the job's exit depends on whether another
// shard passed: the same failing timeline gives exit 1 (one shard: "error") or 2 (two shards:
// "flaky" from the shard's own property). The shard's tests read "pass" over the timelines that
// reported them.
// Promise: ci.zig:436-438 (tests_judge: "\"error\" when a timeline stated no test (the run
// command died before its report)"); ci.zig:477 ("<k> timelines without their JUnit report");
// docs/CI.md ("each test gets its own verdict across its shard's timelines").
// Minimal case (Replica/Ci4.lean, theorem ce37_unreported_missed, and the general theorem
// unreported_zero_of_one_full): three tests, two shards of 2 timelines, junit; shard 1 passes in
// both; shard 2's runner dies before its report in one: "0 timelines without their JUnit
// report", the job flaky (exit 2). With one shard, the same timeline: error (exit 1).

// Unit test, in src/store.zig beside CE28's (store tests over ingested events), on the count
// made SQL in ci.zig (pub), each timeline that stated its shard's property and no test:
//     pub const unreported_sql = "SELECT count(DISTINCT timeline) AS count FROM explored_timeline_events e " ++
//         "WHERE name = 'the CI shard''s tests pass' AND NOT EXISTS (SELECT 1 FROM explored_timeline_events t " ++
//         "WHERE t.timeline = e.timeline AND t.name LIKE 'test passes: %')";
// (and hung timelines, which state neither: the run's timelines less those that stated the
// shard property; CE27's).
test "a CI run's timelines without their JUnit report are counted per timeline, whatever the other shards reported" {
    // Events: timelines 0 and 2 (shard 1) state "test passes: a::t1" and the shard property;
    // timeline 1 (shard 2) states "test passes: a::t2" and the shard property; timeline 3
    // (shard 2) states the shard property alone (false: its runner died before the report).
    // Ingested as CE28's test does; then:
    //     const rows = try attached.rows(Count, arena, ci.unreported_sql, .{});
    //     try testing.expectEqual(1, rows[0].count);
    // At 3939448 tests_judge's own count over these properties is 2 - max(2, 1) = 0.
    try store_ci_unreported_per_timeline();
}

// e2e: examples/ci-demo with ci-shard.json's `{shard}` mode and 2 shards, a test in shard 2 that
// kills its runner (os._exit(3) before pytest writes /tmp/junit.xml) when a random byte is low:
// assert the log says "<k> timelines without their JUnit report" with k > 0 whenever a shard
// line says it failed in some timelines with no failing test.
