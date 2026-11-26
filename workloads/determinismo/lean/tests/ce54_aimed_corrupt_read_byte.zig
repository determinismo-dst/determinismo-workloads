// CE54: an aimed corrupt_reads (nodes.zig:2041-2061) fails only the file's extents as they were
// at the fault's start (file_extents 2375-2410; aimed_record 2415-2434: dm-flakey over each
// extent, linear between). device-mapper splits a bio at segment boundaries (dm.c,
// max_io_len_target_boundary) and dm-flakey changes byte `corrupt_bio_byte` of each read clone
// it completes, counted from the clone's start (dm-flakey.c corrupt_bio_data). disk_reads_read
// names one byte a bio, its first sector's (2278: `.byte = read.sector * 512 + corrupt_byte - 1,
// // The device's byte the fault changed.`). A bio that starts in a linear part and reaches an
// extent, or crosses two, changes other bytes than the one named: the hole before a file's first
// extent written during the fault goes just before it (ext4_ext_find_goal: the extent's block
// less the distance), a hole between two extents just after the left one; a read over them
// (readahead, one bio over contiguous blocks) is then split. A database's preallocated,
// sparse file written out of order (bbolt, LMDB) does exactly that.
// Property: sdk/zig/schema.zig (corrupt_reads: "Every read it corrupts is named
// (`disk_corrupt_read`: node, file, sectors, the byte ...), so a durability judge excludes those
// pages, or flags a loss inside one, without guessing"); nodes.zig:2278.
// Where: guest/runtime/nodes.zig, beside `test aimed_record` (after line 2445). Needs only std:
// `read_changed_bytes` names the function the fix makes of the naming (each aimed extent a bio
// overlaps, the byte at its part's start; the segments as aimed_record writes them).
// Fails at a7fe05d: the function does not exist; the inline naming gives one byte, the bio's
// first sector's (by the model: Replica/Aimed6.lean, theorem ce54_named_byte_not_the_changed_one).

test "a read over a linear part and two aimed extents names each byte the fault changed" {
    // The file's extents at the fault's start: sectors 100-107 and 116-123 (a hole between, and
    // one before). During the fault the holes were written at 92-99 and 108-115.
    const aimed = [_]Extent{ .{ .start = 100, .count = 8 }, .{ .start = 116, .count = 8 } };
    var bytes: [fiemap_extents_max]u64 = undefined;
    // One bio of 32 sectors from 92: the linear 92-99, flakey 100-107, linear 108-115, flakey 116-123.
    const changed = read_changed_bytes(&aimed, 92, 32, 5, &bytes);
    try std.testing.expectEqualSlices(u64, &.{ 100 * 512 + 4, 116 * 512 + 4 }, changed);
    // A read inside one extent: its own first sector's byte, as named today.
    try std.testing.expectEqualSlices(u64, &.{ 104 * 512 + 4 }, read_changed_bytes(&aimed, 104, 4, 5, &bytes));
}
