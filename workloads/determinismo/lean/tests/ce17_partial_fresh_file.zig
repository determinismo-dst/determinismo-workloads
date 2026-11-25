// CE17: a fresh file's later range of new data is kept while an earlier one is lost.
// Where: guest/runtime/nodes.zig, beside "partial persistence draws the same files and pages
// from the same seed, nested ones too" (after line 1382); run on the disk the tests run from
// (ext4, delayed allocation), as that test does.
// Fails at 3939448: partial_file starts the new data's run at a drawn range
// (`random.uintLessThan(u32, unallocated.ranges)`, nodes.zig:946), any of a fresh file's.

test "a fresh file's new data is written back from its first range" {
    var later_first: u32 = 0;
    var seed: u64 = 1;
    while (seed <= 64) : (seed += 1) {
        var path_buffer: [path_size_max]u8 = undefined;
        const path = try print_z(&path_buffer, ".det-partial-fresh-{d}-{d}", .{ linux.getpid(), seed });
        const opened = linux.open(path, .{ .ACCMODE = .RDWR, .CREAT = true, .EXCL = true, .CLOEXEC = true }, 0o644);
        try std.testing.expect(linux.errno(opened) == .SUCCESS);
        const fd: linux.fd_t = @intCast(opened);
        defer {
            _ = linux.close(fd);
            _ = linux.unlink(path);
        }
        // Pages 0 and 4 written, never synced; 1 to 3 a hole: a fresh file with two ranges of
        // new data (a sparse write, a preallocated layout's first pages).
        const page: [partial_page_size]u8 = @splat('x');
        _ = linux.pwrite(fd, &page, page.len, 0);
        _ = linux.pwrite(fd, &page, page.len, 4 * partial_page_size);
        const before = unallocated_of(fd) orelse continue;
        if (before.ranges != 2) continue; // The host's flusher wrote it back first.
        var prng = std.Random.DefaultPrng.init(seed);
        var count: PartialCount = .{};
        partial_file(path, prng.random(), &count);
        const after = unallocated_of(fd) orelse continue;
        // Page 4 written back and page 0 not: after the power loss (journal committed) page 0
        // reads zeros under the file's size, before a kept page.
        if (!after.contains(4) and after.contains(0)) later_first += 1;
    }
    try std.testing.expectEqual(@as(u32, 0), later_first);
}
