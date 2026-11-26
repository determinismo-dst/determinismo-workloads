// CE43: corrupt_reads's reads are named by a reader process of the tracefs instance's trace_pipe
// (nodes.zig:2173-2229, 2232-2266), and the heal kills it with SIGKILL right after the table is
// back (2412-2415, 2309-2324). A read bio queued while the fault lasts waits in the instance's
// ring buffer until that reader is scheduled; one the reader has not yet taken when the heal
// comes is never named in its fault: the kill drops it, and the instance's removal (`rmdir`,
// 2323) either frees it or fails (EBUSY: the killed reader may still hold the pipe, kill(2)
// returning before its target exits), leaving the instance and its unread lines for the node's
// next corrupt_reads fault, whose reader then names the old reads under the new fault, with
// its own corrupt_byte (a byte that fault never changed).
// Properties: sdk/zig/schema.zig:520-524 ("Every read it corrupts is an event ...: a loss
// outside every such read is the system's"); nodes.zig:2052-2055 ("a read just before is named
// too: never one missed"); 2415 ("After the table heals: a read just before it is named too").
// Where: guest/runtime/nodes.zig, beside `test bio_read_line` (after line 2306): a guest test
// (it needs tracefs, device-mapper and root: the selftest's disk node), run as the selftest's
// `disk` scenario runs its node tests.
// Fails at 62e06e3: the reads queued after the reader last ran and before the heal are missing
// from the events (the Lean replica: runs5/disk.txt, theorems ce43_*). A fix drains the pipe
// before the kill (read until empty with the tracepoint disabled), and removes a stale instance
// (or its buffer) before a fault's reader opens it.

test "every read a corrupt_reads fault corrupts is named, the last one before the heal too" {
    if (linux.getuid() != 0) return error.SkipZigTest;
    // A node with a disk (the selftest's `disk` node: ext4 on its loop and device-mapper).
    const name = "det-selftest-disk";
    var paths: Paths = undefined;
    try paths.init(name);
    const file = "data/reads";
    // The file written and synced, then dropped from the cache: each read below a bio.
    try selftest_file_write(name, file, 64 * 4096);
    try disk_fail(name, .{ .failure = .corrupt_reads, .file = file, .corrupt_byte = 7, .corrupt_value = 0x55 });
    var reads: u32 = 0;
    for (0..64) |page| {
        try selftest_cache_drop(name, file);
        try selftest_read_page(name, file, page); // A bio, its line in the instance.
        reads += 1;
    }
    // The heal at once after the last read, as the injector's fault end may come.
    _ = try disk_heal(name);
    // Every read named: the timeline's disk_corrupt_read events for this file.
    try std.testing.expectEqual(reads, events_count("disk_corrupt_read", file));
    // And the next fault's reader names none of them again.
    try disk_fail(name, .{ .failure = .corrupt_reads, .file = file, .corrupt_byte = 9, .corrupt_value = 0x66 });
    std.Thread.sleep(100 * std.time.ns_per_ms);
    _ = try disk_heal(name);
    try std.testing.expectEqual(reads, events_count("disk_corrupt_read", file));
}
