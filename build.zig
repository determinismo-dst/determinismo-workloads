// SPDX-License-Identifier: MIT
//! The workloads' test programs, the platform a Zig dependency (build.zig.zon): `zig build
//! <workload>`, each into zig-out/bin. A Clojure workload is packed into one file, a shell script
//! that runs itself as a jar of its sources and the platform's Clojure SDK (the platform's
//! tools/program_pack.zig).
const std = @import("std");

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
    // Each workload found by its layout, nothing to list: workloads/<name>/workload/ holds a
    // Clojure program (the platform's sdk/clojure, determinismo.workload), built as <name>-test,
    // its main namespace <name>-workload; workloads/<name>/<name>_test.zig a Zig one, <name>-test
    // too, with the platform's modules (determinismo, tcp, resp, nrepl, pg). Moving a workload here
    // is moving its directory.
    var workloads_dir = b.root.openDir(b.graph.io, "workloads", .{ .iterate = true }) catch @panic("no workloads/");
    defer workloads_dir.close(b.graph.io);
    var names: std.ArrayList([]const u8) = .empty;
    var listing = workloads_dir.iterate();
    while (listing.next(b.graph.io) catch @panic("workloads/")) |entry| {
        if (entry.kind != .directory) continue;
        names.append(b.allocator, b.dupe(entry.name)) catch @panic("out of memory");
    }
    std.mem.sort([]const u8, names.items, {}, struct {
        fn less(_: void, x: []const u8, y: []const u8) bool {
            return std.mem.lessThan(u8, x, y);
        }
    }.less);
    for (names.items) |name| {
        const zig_path = b.fmt("workloads/{s}/{s}_test.zig", .{ name, name });
        if (b.root.access(b.graph.io, zig_path, .{})) {
            const exe = b.addExecutable(.{
                .name = b.fmt("{s}-test", .{name}),
                .root_module = b.createModule(.{
                    .root_source_file = b.path(zig_path),
                    .target = target,
                    .optimize = optimize,
                    .imports = &.{
                        .{ .name = "determinismo", .module = determinismo.module("determinismo") },
                        .{ .name = "tcp", .module = determinismo.module("tcp") },
                        .{ .name = "resp", .module = determinismo.module("resp") },
                        .{ .name = "nrepl", .module = determinismo.module("nrepl") },
                        .{ .name = "pg", .module = determinismo.module("pg") },
                    },
                }),
            });
            const installed = b.addInstallArtifact(exe, .{});
            const step = b.step(exe.name, b.fmt("The {s} workload: its test program (Zig)", .{exe.name}));
            step.dependOn(&installed.step);
            all.dependOn(step);
            b.getInstallStep().dependOn(&installed.step);
            continue;
        } else |_| {}
        workloads_dir.access(b.graph.io, b.pathJoin(&.{ name, "workload" }), .{}) catch continue;
        const program = .{
            .name = b.fmt("{s}-test", .{name}),
            .main = b.fmt("{s}-workload", .{name}),
            .sources = b.fmt("workloads/{s}/workload", .{name}),
        };
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
