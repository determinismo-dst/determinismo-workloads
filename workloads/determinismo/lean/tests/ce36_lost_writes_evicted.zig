// CE36: under a lost_writes disk fault (dm-flakey drop_writes, guest/runtime/nodes.zig:1972-1976),
// writeback "succeeds" and stores nothing, leaving the page clean in the cache with the node's
// data. Memory pressure may evict a clean page; the next read reads the disk: the node reads
// its old data back while it runs, no crash having come (and so does a node that exited during
// the fault: disk_heal 2192-2196 unmounts it). A system that re-reads its log or its pages
// (a database's buffer pool, a log reader) sees its acknowledged, synced write gone mid-run, a
// state a crash never makes (a crash restarts it).
// Promise: docs/ANTITHESIS.md:56 ("writes acknowledged and never stored (gone at the next crash,
// synced or not)"); nodes.zig:1932-1934 (lost_writes: "a crash after loses them although they
// were synced").
// Minimal case (Replica/Durable.lean, theorem ce36_lost_write_read_back): the node writes 1, then
// 2, to a page; the disk drops writes; the flusher writes the page back (dropped); memory
// pressure evicts the clean page; the node's read returns 0. (No eviction: the search over the
// same steps finds none: 200,000 timelines.)

// Selftest scenario (the selftest's disk check, beside CE31's), on a durable node:
//   1. a file of one 4 KiB page, 0x11, synced;
//   2. disk_fail(node, .{ .failure = .lost_writes });
//   3. pwrite the page 0x22 (buffered), fsync (0);
//   4. posix_fadvise(fd, 0, 4096, POSIX_FADV_DONTNEED) (a clean page dropped, as reclaim does);
//   5. read the page (buffered).
// Assert, as the docs say: it reads 0x22 until the next crash. At 3939448 it reads 0x11.
// (The fix may be the docs': "gone at the next crash, or once the kernel drops the page from its
// cache"; then assert that the run's events say so: a `disk_lied` note.)
test "lost writes read back until the next crash" {
    try selftest_disk_lost_writes_until_crash();
}
