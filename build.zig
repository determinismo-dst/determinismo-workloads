// SPDX-License-Identifier: MIT
//! The workloads' test programs, the platform a Zig dependency (build.zig.zon): `zig build
//! <workload>`, each into zig-out/bin. A Clojure workload is packed into one file, a shell script
//! that runs itself as a jar of its sources and the platform's Clojure SDK (the platform's
//! tools/program_pack.zig).
const std = @import("std");

/// The workloads in Clojure (the platform's sdk/clojure, determinismo.workload): each its program's
/// name, its main namespace and its sources under workloads/.
const clojure_programs = [_]struct { name: []const u8, main: []const u8, sources: []const u8 }{
    .{ .name = "datalevin-test", .main = "datalevin-workload", .sources = "workloads/datalevin/workload" },
};

pub fn build(b: *std.Build) void {
    // Test programs run inside the guest: x86-64 Linux, as the platform's.
    const target = b.standardTargetOptions(.{
        .default_target = .{ .cpu_arch = .x86_64, .os_tag = .linux, .abi = .musl },
    });
    const optimize = b.standardOptimizeOption(.{ .preferred_optimize_mode = .ReleaseSafe });
    const determinismo = b.dependency("determinismo", .{ .target = target, .release = optimize != .debug });
    const program_pack = b.addExecutable(.{
        .name = "det-program-pack",
        .root_module = b.createModule(.{
            .root_source_file = determinismo.path("tools/program_pack.zig"),
            .target = b.graph.host,
            .optimize = .Debug,
        }),
    });
    const all = b.step("workloads", "Every workload");
    for (clojure_programs) |program| {
        const pack = b.addRunArtifact(program_pack);
        const packed_program = pack.addOutputFileArg(program.name);
        pack.addArg("clojure");
        pack.addArg(program.main);
        pack.addDirectoryArg(b.path(program.sources));
        pack.addDirectoryArg(determinismo.path("sdk/clojure"));
        // Each source an input: a directory argument is its path, not its files.
        inputs(b, pack, program.sources);
        inputs(determinismo.builder, pack, "sdk/clojure");
        const installed = b.addInstallFileWithDir(packed_program, .bin, program.name);
        const step = b.step(program.name, b.fmt("The {s} workload: its test program (Clojure)", .{program.name}));
        step.dependOn(&installed.step);
        all.dependOn(step);
        b.getInstallStep().dependOn(&installed.step);
    }
}

/// Each .clj file under `directory` (relative to `b`'s root: this build's or the platform's) an
/// input of `run`.
fn inputs(b: *std.Build, run: *std.Build.Step.Run, directory: []const u8) void {
    const io = b.graph.io;
    var dir = b.root.openDir(io, directory, .{ .iterate = true }) catch |err|
        std.debug.panic("{s}: {t}", .{ directory, err });
    defer dir.close(io);
    var walker = dir.walk(b.allocator) catch @panic("out of memory");
    defer walker.deinit();
    while (walker.next(io) catch |err| std.debug.panic("{s}: {t}", .{ directory, err })) |entry| {
        if (entry.kind != .file or !std.mem.endsWith(u8, entry.path, ".clj")) continue;
        run.addFileInput(b.path(b.pathJoin(&.{ directory, entry.path })));
    }
}
