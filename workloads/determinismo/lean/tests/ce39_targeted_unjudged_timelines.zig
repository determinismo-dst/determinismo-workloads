// CE39: a targeted run (--changed) counts the timelines that ran each hunk in tree_judge_begin
// (src/main.zig:6363-6381), over the timelines of the generations judged; the run's last
// timelines are in no judged generation when the run ends with fewer than a generation's size
// since its last judgment and every timeline planned (4360-4363: `state.next_index <
// state.total` false), or past its budget (`!late`). Change.summarize (src/changed.zig:66-85)
// then prints "NEVER RAN" for a hunk that ran only there, and "ran in <c>/<next_index>
// timelines" with c short of the timelines that ran it (and next_index counting timelines planned
// and never run, past a budget). The record's `changed` line (4383-4391), which serve's page
// shows, says the same.
// Promise: docs/AGENTS.md:319-322 ("reports which hunks ran in how many timelines and which never
// did"); README_AI.md:319-320; docs/ANTITHESIS.md:131.
// Minimal case (Replica/Steer4.lean, theorem ce39_never_ran): generations of 2, 3 timelines:
// timeline 2 alone runs the hunk; generation 0 (0 and 1) judged; 2 ends with next_index = total
// = 3: never judged: "NEVER RAN". Default shape: --generation 16, 20 timelines: the last 4
// uncounted; with a budget, every timeline since the last judgment.

// Unit test, in src/main.zig beside test judge_count (after 4630), on the targeted counts made a
// function of the run's summaries at its end (the loop's last step, 4360-4366, counting what
// tree_judge_begin counts):
//     fn changed_count(target: *changed.Change, summaries: []const Summary, judged: u32) void
// with the fix counting every ended timeline's hunks (judged or not) before summarize.
test "a targeted run counts the hunks of every timeline that ran, judged or not" {
    // A change of one hunk, src/x.zig:10-12; three ended timelines, the last one's behaviors
    // `line src/x.zig:11`; generations of 2 (0 and 1 judged).
    try targeted_counts_unjudged();
    // Assert target.timelines[0] == 1 and target.first[0] == 2. At 3939448: 0 ("NEVER RAN").
}

// e2e (the e2e's `changed` check): its maze system with --changed on a hunk its last timelines
// reach, --branches 20 --generation 16: assert the record's changed line counts the hunk in every
// timeline whose events have its line (`SELECT count(DISTINCT branch) FROM events WHERE
// name = 'coverage' AND details LIKE '%x.zig:11%'`).
