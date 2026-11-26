// Round 8: CE45's paths and CE61 against df8f08b and c4f246e.
// Each test writes a run's record as that version's explorer writes it (c4f246e: a `declared`
// line for an assertion declared and not reached, report.zig:553-568, written through the same
// `report.Recorded` value; df8f08b: none, its RecordLine has no such field), and the run's own end
// lines that judge its catalog (`r8_run_end`: main.zig:1170-1175, each version's). The resume
// (`--resume` on that record) runs in a child process: resume_read verbatim; a complete run ends
// there with the record's verdict; otherwise the explorer's way, as main.zig goes on: the record's
// timelines merged (Resumed.merge_into, verbatim), then those the resume runs (the test gives
// their properties), their catalog judged (the shim's report.Catalog) and the run's end lines
// (verbatim) give the status.
// Property: main.zig (c4f246e 2365-2367, df8f08b 2336-2338): "Judged from its record, as the run
// that recorded it would have been"; RecordLine.catalog: "the last such line the run's verdict";
// docs/ANTITHESIS.md's catalog (an assertion no timeline reached fails the run).
// CE45's three remaining paths (round 7): red on df8f08b, green on c4f246e.
// CE61 (round 8): a run drained after two timelines (its end wrote a catalog line judged over
// those two: "r" unreached), resumed, the resume's last timeline reaching "r", interrupted after
// that timeline's line and before its end; resumed again: complete, its catalog line the drain's.
// The run's verdict is 0 ("r" reached, "a" passing everywhere): red on both.

fn r8_run_end(arguments: *const Arguments, catalog: *const report.Catalog, every_scenario: bool, failing_out: *u32) void {
    var failing_scenarios: u32 = 0;
    R8_RUN_END
    failing_out.* = failing_scenarios;
}

const r8_declares = @hasField(RecordLine, "declared");

/// The resume of `record`: its exit status. `rest`: the properties of the timelines the
/// resume runs (the explorer's way), one list a timeline.
fn r8_resumed_status(record: []const u8, branches: u32, rest: []const []const report.Recorded) !u32 {
    const io = std.testing.io;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.writeFile(io, .{ .sub_path = "record.jsonl", .data = record });
    var root_buffer: [4096]u8 = undefined;
    const root = root_buffer[0..try tmp.dir.realPathFile(io, ".", &root_buffer)];
    var path_buffer: [4200]u8 = undefined;
    const path = try std.fmt.bufPrint(&path_buffer, "{s}/record.jsonl", .{root});
    const child = std.c.fork();
    if (child == 0) {
        var arena_state: std.heap.ArenaAllocator = .init(std.heap.page_allocator);
        const arguments: Arguments = .{ .record_path = path, .branches = branches };
        const resumed = resume_read(.{ .arena = arena_state.allocator(), .io = io }, &arguments, 0xaa) catch std.process.exit(101);
        // Not complete: the explorer's way (main.zig:2991-2993 merge_into, then its timelines).
        var multiverse: report.Multiverse = .{};
        resumed.merge_into(&multiverse) catch std.process.exit(102);
        for (rest) |timeline| for (timeline) |*property| {
            multiverse.recorded_merge(property, 9) catch std.process.exit(103);
        };
        var catalog: report.Catalog = .{};
        multiverse.catalog_reached(&catalog);
        var failing_scenarios: u32 = 0;
        if (multiverse.failing_properties() > 0) failing_scenarios += 1;
        var ended: u32 = 0;
        r8_run_end(&arguments, &catalog, true, &ended);
        failing_scenarios += ended;
        std.process.exit(if (failing_scenarios > 0) 3 else 0);
    }
    var status: c_int = 0;
    _ = std.c.waitpid(child, &status, 0);
    return @intCast((@as(u32, @bitCast(status)) >> 8) & 0xff);
}

const r8_header = "{\"run\":{\"inputs\":\"00000000000000aa\",\"seed\":\"0000000000000007\",\"branching\":\"flat\"}}\n";
const r8_passing = "\"properties\":[{\"message\":\"a\",\"kind\":\"always\",\"hits\":1,\"trues\":1}]";
const r8_reaching = "\"properties\":[{\"message\":\"a\",\"kind\":\"always\",\"hits\":1,\"trues\":1},{\"message\":\"r\",\"kind\":\"reachable\",\"hits\":1,\"trues\":1}]";

fn r8_line(text: []const u8) void {
    report.lines.appendSlice(std.heap.page_allocator, text) catch unreachable;
}

/// A timeline that declared reachable "r" and never reached it, as this version's worker
/// records it before the timeline's own line (report.zig:553-568 at c4f246e; nothing before).
fn r8_declared_r() void {
    if (!r8_declares) return;
    report.record(.{ .declared = report.Recorded{ .message = "r", .hash = 0, .kind = .reachable, .hits = 0, .trues = 0, .failure = null } });
}

/// The run's end: its catalog judged ("r" unreached by its timelines so far: 1 failing).
fn r8_end(r_reached: bool) void {
    var catalog: report.Catalog = .{};
    catalog.note(.reachable, "r", r_reached);
    catalog.note(.always, "a", true);
    var failing: u32 = 0;
    r8_run_end(&.{}, &catalog, true, &failing);
}

const r8_rest_passing = [_]report.Recorded{.{ .message = "a", .kind = .always, .hits = 1, .trues = 1 }};

test "round 8, CE45: a complete run resumed again fails for its catalog as the run did" {
    report.lines = .empty;
    r8_line(r8_header);
    r8_declared_r();
    r8_line("{\"branch\":{\"index\":0," ++ r8_passing ++ "}}\n");
    r8_line("{\"branch\":{\"index\":1," ++ r8_passing ++ "}}\n");
    r8_end(false);
    try std.testing.expectEqual(@as(u32, 3), try r8_resumed_status(report.lines.items, 2, &.{}));
}

test "round 8, CE45's session path: a run whose missing number a session's timeline took fails for its catalog" {
    // Timeline 0 declared "r"; the session's timeline took number 1 (its line extends #0): never
    // complete, the explorer's way passes the number over and runs nothing.
    report.lines = .empty;
    r8_line(r8_header);
    r8_declared_r();
    r8_line("{\"branch\":{\"index\":0," ++ r8_passing ++ "}}\n");
    r8_line("{\"branch\":{\"index\":1,\"extends\":{\"branch\":0,\"vtime_ns\":5}," ++ r8_passing ++ "}}\n");
    try std.testing.expectEqual(@as(u32, 3), try r8_resumed_status(report.lines.items, 2, &.{}));
}

test "round 8, CE45's stop before the end: a complete run stopped before its end fails for its catalog" {
    report.lines = .empty;
    r8_line(r8_header);
    r8_declared_r();
    r8_line("{\"branch\":{\"index\":0," ++ r8_passing ++ "}}\n");
    r8_line("{\"branch\":{\"index\":1," ++ r8_passing ++ "}}\n");
    try std.testing.expectEqual(@as(u32, 3), try r8_resumed_status(report.lines.items, 2, &.{}));
}

test "round 8, CE45's interrupted run: the declarations of the timelines it skips stay in its catalog" {
    // Stopped after timeline 0 (which declared "r"); timeline 1 runs on resume and declares none.
    report.lines = .empty;
    r8_line(r8_header);
    r8_declared_r();
    r8_line("{\"branch\":{\"index\":0," ++ r8_passing ++ "}}\n");
    try std.testing.expectEqual(@as(u32, 3), try r8_resumed_status(report.lines.items, 2, &.{&r8_rest_passing}));
}

test "round 8, CE61: a run drained, resumed and interrupted before its end is judged by its last timelines too" {
    report.lines = .empty;
    r8_line(r8_header);
    r8_declared_r();
    r8_line("{\"branch\":{\"index\":0," ++ r8_passing ++ "}}\n");
    r8_line("{\"branch\":{\"index\":1," ++ r8_passing ++ "}}\n");
    r8_end(false); // The drain's end: "r" unreached by timelines 0 and 1.
    // The resume: timeline 2 reaches "r"; interrupted after its line, before its end.
    r8_line("{\"branch\":{\"index\":2," ++ r8_reaching ++ "}}\n");
    try std.testing.expectEqual(@as(u32, 0), try r8_resumed_status(report.lines.items, 3, &.{}));
}

test "round 8, CE61's control: the same resume that reached its end" {
    report.lines = .empty;
    r8_line(r8_header);
    r8_declared_r();
    r8_line("{\"branch\":{\"index\":0," ++ r8_passing ++ "}}\n");
    r8_line("{\"branch\":{\"index\":1," ++ r8_passing ++ "}}\n");
    r8_end(false);
    r8_line("{\"branch\":{\"index\":2," ++ r8_reaching ++ "}}\n");
    r8_end(true); // The resume's own end: every timeline judged, "r" reached.
    try std.testing.expectEqual(@as(u32, 0), try r8_resumed_status(report.lines.items, 3, &.{}));
}
