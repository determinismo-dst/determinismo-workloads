
// Round 8, CE64: podman_cpuset (c4f246e, cpus.zig:977-996) reads the user manager's
// cpuset.cpus.effective with one read into 512 bytes. The kernel prints a cpuset as ranges and
// single CPUs ("0-8,44-52"); one of more than about 128 separate CPUs or ranges (one hyperthread
// of each core where siblings are numbered side by side, on a host of 256 CPUs or more) is
// longer: what passes 512 bytes is dropped, and the last number read is cut short ("…,254" read
// as "…,25"), a CPU the user manager's cpuset never had.
// Property: cpus.zig:977-982 ("its own CPUs, as far as the user manager's cpuset reaches"), and
// the function's own test (1037-1052).
// The test: the process on the even CPUs 0 to 598, the user manager's cpuset the same 300 CPUs
// (a 1,145-byte list): the build's CPUs are those 300. Red on c4f246e. Its control, today's srv4
// and an unconfined user manager (the function's own test's lists): green.
fn r8_cpuset(mine: []const usize, list: ?[]const u8) !?[]const u8 {
    const io = std.testing.io;
    var mask: linux.cpu_set_t = @splat(0);
    for (mine) |cpu| set_add(&mask, cpu);
    given_mask = mask;
    const path = "scratch/zig8/tmp/cpuset.cpus.effective";
    if (list) |text| {
        try std.Io.Dir.cwd().writeFile(io, .{ .sub_path = path, .data = text });
        r8_cgroup_file = path;
    } else r8_cgroup_file = null;
    return podman_cpuset(std.heap.page_allocator);
}

test "round 8, CE64: a podman build's CPUs are the process's within the user manager's cpuset, however long its list" {
    var mine: [300]usize = undefined;
    var list: std.ArrayList(u8) = .empty;
    for (&mine, 0..) |*cpu, at| {
        cpu.* = 2 * at;
        if (at > 0) try list.append(std.heap.page_allocator, ',');
        try list.print(std.heap.page_allocator, "{d}", .{2 * at});
    }
    const expected = list.items;
    try list.append(std.heap.page_allocator, '\n');
    std.debug.print("\nthe user manager's cpuset: {d} bytes\n", .{list.items.len});
    const got = (try r8_cpuset(&mine, list.items)).?;
    std.debug.print("podman's --cpuset-cpus: {d} bytes, ending ...{s}\n", .{ got.len, got[got.len -| 24..] });
    try std.testing.expectEqualStrings(expected, got);
}

test "round 8, CE64's control: the function's own lists" {
    var hunt: [35]usize = undefined;
    for (&hunt, 9..) |*cpu, at| cpu.* = at;
    try std.testing.expectEqual(@as(?[]const u8, null), try r8_cpuset(&hunt, "0-8,44-52\n"));
    try std.testing.expectEqualStrings("9-43", (try r8_cpuset(&hunt, "0-52\n")).?);
    try std.testing.expectEqualStrings("9-43", (try r8_cpuset(&hunt, null)).?);
}
