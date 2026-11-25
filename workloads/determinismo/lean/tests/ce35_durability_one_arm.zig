// CE35: a node's sync_stall (a condition: faults.zig:1580-1585) and durable_crash (a process
// fault) may run together (node_admits 1632-1641: the other layer's fault admitted as the
// regime's overlap draws, 0 to 8 eighths), and both arm the guest module for the node's cgroup
// (durable_arm 3224-3258). The module keeps one arm a cgroup: each arm replaces it ("Replaced
// (or disarmed)", guest/module/det_guest.c:466-474), and either fault's end disarms it
// (durable_disarm, faults.zig:2245-2250). So a durable_crash begun over a sync_stall turns the
// stall's syncs into crash decisions (no stall while the sync_stall lasts), a sync_stall begun
// over a durable_crash turns its syncs into stalls, and the first of the two to end leaves the
// other with nothing armed: no sync of the node is a decision until it ends. Its fault events
// say it is under way.
// Promise: ARCHITECTURE.md:360-368 ("While a `sync_stall` or `durable_crash` fault lasts, each
// of its syncs is a decision (one randomness pull), and one in a few is picked"); docs/ANTITHESIS.md
// (Durability points); faults.zig:53-60 ("while the fault lasts, the guest module makes each of
// the node's fsyncs and sync writes a decision").
// Minimal cases (Replica/Durable.lean, theorems ce35_crash_replaces_stall and
// ce35_stall_end_disarms_crash): sync_stall, then durable_crash over it, a sync: a crash_before
// decision while the sync_stall lasts. durable_crash, sync_stall over it, the sync_stall ends, a
// sync: no decision while the durable_crash lasts.

// Selftest scenario (the selftest's durability checks, beside its sync_stall check), on a node
// whose program fsyncs a file every 10 ms and counts its syncs:
//   1. det-faults inject '{"kind":"durable_crash","node":"n","duration_ms":4000}' (with
//      "after_sync": false), then at once
//      det-faults inject '{"kind":"sync_stall","node":"n","duration_ms":1000}' (injected faults
//      are admitted over another layer's: faults.zig:1636-1639);
//   2. wait 4 s.
// Assert: from the sync_stall's end (1 s) to the durable_crash's end (4 s), the node's syncs are
// decisions (`/proc/det_guest`'s pull count grows with them, or with one_in 1, a `durable_crash`
// event comes at the first sync after 1 s). At 3939448: no decision, no crash, the fault's
// `fault_ended` at 4 s.
// And the other order: sync_stall for 4 s, durable_crash for 1 s over it: from 1 s to 4 s
// `sync_stalled` events come (with one_in 1, at each sync). At 3939448: none.
//
// Unit test (guest/runtime/faults.zig, beside "a node takes one fault a layer, and one in each
// only as the regime's overlap draws"), on the arm a node should have, made a function of its
// two layers' faults:
//     fn durability_arm_of(process: ?NodeFault, condition: ?NodeFault) ?DurabilityMode
test "a node's durability arm follows both of its faults" {
    const crash: NodeFault = .{ .applied = .{ .kind = .durable_crash, .node = "n", .duration_ns = 0 }, .end_ns = 4 };
    const stall: NodeFault = .{ .applied = .{ .kind = .sync_stall, .node = "n", .duration_ns = 0 }, .end_ns = 1 };
    // Both under way: the module must make each sync a decision for both (an arm per kind).
    try std.testing.expect(durability_arm_of(crash, stall) != null);
    // The sync_stall ended: the durable_crash's arm stays (3939448 disarms the node).
    try std.testing.expectEqual(@as(?DurabilityMode, .crash_before), durability_arm_of(crash, null));
}
