// SPDX-License-Identifier: MIT
//! Example test program: Flecs, an in-memory entity component system, under a stress harness
//! (workloads/flecs/stress.c): one node runs rounds of random operations against Flecs, worker
//! threads included, checking each against a model and reporting through the C SDK; Flecs's own
//! sanitize checks, the build's undefined-behavior traps and the SDK's assertions in Flecs's own
//! source (assertions.patch) report too. The node is built from Flecs's source (Dockerfile), every
//! edge of it and of the harness covered.
//!
//! What varies a library's behavior is scheduling, not the network or restarts (its state is its
//! memory): the faults are pauses of the process or of one of its threads (ptrace), CPU throttling
//! and clock skips (Flecs reads the clock for frame times), with the SDK's buggify at Flecs's own
//! synchronization points (its mutex, condition variable, thread and atomic hooks).
//!
//!   determinismo explore ... --program zig-out/bin/flecs-test --scenario stress
const std = @import("std");
const sdk = @import("determinismo");

const Nodes = struct { flecs: sdk.Node };
const System = sdk.System(Nodes);

pub fn main(init: std.process.Init) !void {
    return System.main(init, .{ .describe = describe, .scenarios = .{ .stress = stress } });
}

fn describe(d: *System.Describe) !void {
    const profile = try d.profile("default");
    profile.node(.flecs, .{
        // workloads/flecs/Dockerfile built on a host of ours (host/push-images.sh, with images.json's
        // build arguments: the coverage set below, which they must match) and pushed
        // (push-image.yml), pinned by digest: pushed again and pinned here when the Dockerfile,
        // its files or the coverage set change.
        .image = "ghcr.io/determinismo-dst/flecs-flecs@sha256:b175f0c4823b81ceb20ed1a9aa330e449b581ab596251d498452e45ea377ca2e",
        // Flecs's sources and the harness, as the Dockerfile compiles them (/src).
        .coverage = .{ .include = &.{"/src/"} },
        .faults = .{
            .pause = true,
            .process_pause = true, // And one of its threads alone.
            .throttle = true,
            .isolate = false,
            .partition = false,
            .degrade = false,
            .sync_stall = false,
        },
    });
}

fn stress(s: *System.Scenario) void {
    s.clock_skip = true;
    // The node works on its own; the timeline lasts while drivers wait.
    s.singleton_driver("wait", wait);
}

fn wait(_: *System.Context) !void {
    sdk.sleep_ms(1000 + sdk.random_below(9000));
}
