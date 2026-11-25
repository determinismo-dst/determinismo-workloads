// CE31: corrupt_reads, one of the disk failures "that keep what was stored" (faults.zig:954-964,
// drawn alone when a node's `disk_lost_writes` is off, schema.zig:515-520: "Its other failures
// leave what is stored intact, so durability stays judgeable under them"; nodes.zig:1936-1937:
// "Reads return one byte of each request changed (bit rot); what is stored is intact"), stores a
// corrupted byte: a buffered write to part of a page not in the cache reads the page first
// through dm-flakey's corrupt_bio_byte, and the page written back carries the corrupted byte. A
// page read while the fault lasts stays in the page cache corrupted after the heal (disk_heal
// 2179-2198 swaps the table back and leaves a running node's cache as it is), so reads after the
// fault "for a while" still return it, and a later write to that page stores it.
// Where: guest/runtime/nodes.zig:1979-1983 (`corrupt_bio_byte <n> r <value> 0`), 2179-2198.

// Selftest scenario (guest/runtime's selftest disk check, beside "partial persistence draws the
// same files and pages from the same seed", nodes.zig:1382), on a durable node whose disk is a
// device-mapper device over its loop device:
//   1. a file of two 4 KiB pages, every byte 0x11, synced; drop the page cache
//      (echo 1 > /proc/sys/vm/drop_caches);
//   2. disk_fail(node, .{ .failure = .corrupt_reads, .corrupt_byte = 1, .corrupt_value = 0xee });
//   3. pwrite one byte 0x22 at offset 100 of page 0 (buffered), fsync;
//   4. read page 1 (buffered);
//   5. disk_heal(node); fsync;
//   6. read page 1 again; drop the caches; read the device's blocks of the file (O_DIRECT).
// Assert: page 0 stored is 0x11 everywhere but byte 100 (0x22); page 1 reads 0x11 after the heal
// (step 6, before and after dropping the caches). At 3939448: page 0 stores 0xee at byte 0 (the
// read-modify-write of step 3), and page 1 reads 0xee at byte 0 after the heal from the cache.
test "a disk fault that keeps what is stored stores no byte the node did not write" {
    // As a unit test where the selftest's helpers run (Linux, root, a loop device):
    try selftest_disk_corrupt_reads_keep_stored();
}
