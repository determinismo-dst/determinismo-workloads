// CE30: the coverage gate stops an instrumented run, saying "its system runs without its
// language's instrumentation", when its first 4 timelines reach only code its setup ran: a
// coverage event is sent the first time a process of the timeline runs an edge no process of
// the timeline ran (sdk/zig/determinismo.zig:2122-2200, the C SDK's and libvoidstar's the
// same), the bits in /opt/determinismo/coverage, a tmpfs mounted at boot (init.zig:214-223) and
// so in the setup's snapshot: a timeline repeating its setup's paths reports none. The gate
// counts `timelines` rows with sessions among them (a session opened early counts as one of
// "its first 4 ended timelines").
// docs/SDKS.md:101-105, serve.zig:689-700 and 731-733 (the stop's reason); docs/CI.md: "serve
// can tell a job that ran from one that did not".
// Where: src/serve.zig:703-752 coverage_gate (`covered_sql` over the timelines' events alone;
// `SELECT count(*) FROM timelines`).

// Unit test, in src/serve.zig beside coverage_gate: a run whose setup's events carry coverage
// (setup.jsonl, ingested as the setup's: events with a null branch) and whose 4 timelines
// repeat it, none of theirs, is not stopped. Through serve's own test server (as the tests of
// run_show do): a run directory with record.jsonl, request.json {} and events/ holding
//   setup.jsonl:      {"seq":1,"vtime_ns":10,"event":{"event":"coverage","details":{"name":"line /src/server.zig:42"}}}
//   branch-0..3.jsonl: {"seq":..,"vtime_ns":900,"event":{"assert":{"type":"always","message":"ok","condition":true}}}
//   timelines.jsonl:  timelines 0 to 3
// run_update(server, id) with the run going. Assert: no `stopped` file in the run's directory.
// At 3939448 `stopped` holds "no coverage in its first 4 timelines: its system runs without its
// language's instrumentation".
