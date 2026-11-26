// Round 7: CE54 against both versions, through the reader itself (disk_reads_read), not a
// helper only df8f08b has. The trace pipe is a pipe: block_bio_queue lines as the kernel writes
// them, then the heal's marker. dm-flakey changes byte `corrupt_byte` of each clone over an
// aimed extent, counted from the clone's start (device-mapper splits a bio at its table's
// segments): the bytes the fault changed. Every disk_corrupt_read must name one of them, and
// each of them must be named.
// Property: sdk/zig/schema.zig (`corrupt_reads`: "Every read it corrupts is named ... the
// byte"); nodes.zig (a7fe05d 2278, df8f08b 2281): ".byte: The device's byte the fault changed".
// Red on a7fe05d's reader (it names each bio's first sector's byte: 92 * 512 + 4 for a read
// that began in the linear part before the extent, one byte for a read over two extents);
// green on df8f08b's (read_corrupted_parts: one part per aimed extent overlap).

fn r7_bytes_named(extents: []const Extent, lines: []const u8, corrupt_byte: u32) ![]const u64 {
    var pipe: [2]std.c.fd_t = undefined;
    if (std.c.pipe(&pipe) != 0) return error.Pipe;
    _ = std.c.write(pipe[1], lines.ptr, lines.len);
    _ = std.c.close(pipe[1]);
    events_count = 0;
    disk_reads_read(pipe[0], "n1", "/data/db.bin", extents, corrupt_byte, 252, 0);
    _ = std.c.close(pipe[0]);
    var bytes: std.ArrayList(u64) = .empty;
    for (events_seen[0..events_count]) |seen| {
        if (std.mem.eql(u8, seen.name, "disk_corrupt_read")) try bytes.append(std.testing.allocator, seen.byte);
    }
    return bytes.toOwnedSlice(std.testing.allocator);
}

test "round 7, CE54: an aimed corrupt_reads names the bytes the fault changed, and only those" {
    const marker = "  det-1 [000] ..... 9.0: tracing_mark_write: det-corrupt-reads-end\n";
    // The file's extent: sectors 100-107. The hole before it, written during the fault at ext4's
    // goal (92-99), is read with it: one bio from 92, dm splits it at 100.
    const one = [_]Extent{.{ .start = 100, .count = 8 }};
    const read_across = "  app-7 [000] ..... 8.5: block_bio_queue: 252,0 R 92 + 16 [app]\n" ++ marker;
    const named = try r7_bytes_named(&one, read_across, 5);
    defer std.testing.allocator.free(named);
    try std.testing.expectEqualSlices(u64, &.{100 * 512 + 4}, named);
    // Two extents, the hole between them filled: one bio over both, two clones, two bytes.
    const two = [_]Extent{ .{ .start = 100, .count = 8 }, .{ .start = 116, .count = 8 } };
    const read_both = "  app-7 [000] ..... 8.5: block_bio_queue: 252,0 R 100 + 24 [app]\n" ++ marker;
    const named_two = try r7_bytes_named(&two, read_both, 5);
    defer std.testing.allocator.free(named_two);
    try std.testing.expectEqualSlices(u64, &.{ 100 * 512 + 4, 116 * 512 + 4 }, named_two);
}

test "round 7, CE54's control: a read inside one extent is named with its own first byte" {
    const one = [_]Extent{.{ .start = 100, .count = 8 }};
    const lines = "  app-7 [000] ..... 8.5: block_bio_queue: 252,0 R 104 + 4 [app]\n" ++
        "  det-1 [000] ..... 9.0: tracing_mark_write: det-corrupt-reads-end\n";
    const named = try r7_bytes_named(&one, lines, 5);
    defer std.testing.allocator.free(named);
    try std.testing.expectEqualSlices(u64, &.{104 * 512 + 4}, named);
}
