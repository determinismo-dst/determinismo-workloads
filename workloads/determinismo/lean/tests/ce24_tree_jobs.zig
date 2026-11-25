// CE24: the same seed grows another tree with another number of workers: README_AI.md says
// "--jobs, same timelines as one worker", ARCHITECTURE.md §9 "(a seed gives the same tree)".
// Where: src/main.zig. Fails at 3939448 two ways:
//   - the generation's size is the workers' (`tree.generation_for`, 3973-3975; main.zig:8883
//     `if (!arguments.generation_given) arguments.generation_size =
//     tree.generation_for(jobs_count(&arguments))`): 16 with one worker, 32 with 32 to 47;
//     timeline 48 is generation 0's first return with one worker, a fresh start with 32;
//   - a generation is the next `size` timelines to finish (4158-4166, timeline_reaped 5309-5341,
//     judge_count 4614-4620): with more than one worker, which timelines form it is the host's
//     timing (main.zig:3955-3960 says so: "the same seed can grow another tree on other workers").

// Unit test, beside `test generation_for` (main.zig:3977).
test "a seed's tree does not depend on the workers" {
    try std.testing.expectEqual(tree.generation_for(1), tree.generation_for(40));
}

// e2e (the finishing order, --generation given): the bank, one worker against eight.
//   determinismo explore ... --program bank-test --scenario bank --seed 7 --branches 96 \
//     --generation 16 --jobs 1 --record one.jsonl
//   determinismo explore ... same, --jobs 8 --record eight.jsonl
// Assert: for every index, the two records' `path` (and seed) are equal. At 3939448 the first
// return's index and its parent differ as soon as a generation-0 timeline finishes after a
// filler one (the replica: timeline 9 from #2 at 26 µs with two workers, from #1 with one).
