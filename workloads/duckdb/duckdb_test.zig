// SPDX-License-Identifier: MIT
//! Example test program: DuckDB 2.0.1, embedded as Jepsen's DuckDB test embeds it (jepsen-io/duckdb:
//! a local node holding one database file, transactions submitted to it), its file on the
//! node's own disk. Jepsen's two workloads, each checked by Elle at strong snapshot isolation (as
//! Jepsen's test checks: DuckDB's optimistic concurrency, each transaction reading its snapshot,
//! a conflict at the commit rolling it back; Jepsen found it allowing G2-item, so no more):
//!
//!   append          Jepsen's list-append: three tables, a key's list a text (even keys) or an
//!                   INTEGER[] (odd ones), each append an INSERT ... ON CONFLICT or a MERGE INTO,
//!                   each read by the primary key or the unindexed secondary one
//!   fkey_register   Jepsen's fkey-register: a register behind a foreign key (`logical` maps a
//!                   key to its `physical` row), each write updating the physical row in place or
//!                   pointing the key at a fresh one; Elle's rw-register. Snapshot isolation
//!                   promises the key's register only because every write of it writes its
//!                   `logical` row (the in-place one too): Jepsen's writes, as they are, write
//!                   disjoint rows, which it commits both (README, hunt run 1983)
//!   trigger         DuckDB 2.0's triggers: statement triggers over transition tables copying
//!                   `ev`'s inserts and deletes into `ev_mirror`, a row trigger copying `rows` into
//!                   `rows_mirror`; every snapshot's mirrors hold their tables' rows, and once
//!                   faults stop every committed insert is there (and its copy), every committed
//!                   delete gone
//!
//! Profiles: `default`, the embedded database (Jepsen's); `quack`, DuckDB 2.0's client-server
//! protocol: the database in a Quack server (`db`, quack_server.py), the drivers' connections
//! Quack sessions from two client nodes (`c1`, `c2`: local_node.py --quack db, each connection
//! ATTACHing and CONNECTing to the server), faults on the server, the clients and the links
//! between; `quack-reconnects`, the same with Quack's reconnect support on. Each transaction draws
//! how its values go: bound as a prepared statement's parameters (what applications write) or
//! written into the SQL as literals. Bound parameters must reach the database: 2.0.0's Quack
//! refuses them (duckdb#27628, fixed after the release), which fails that property in the Quack
//! profiles, and the literal transactions test the rest.
//!
//! Drivers open connections to the node (local_node.py: a DuckDB connection each) and run their
//! transactions there. Outcomes: `ok` with the reads; `fail` when nothing was applied (an error
//! before the commit, or a conflict at it); `info` when the commit got no answer or another
//! error. Faults: restarts, graceful stops, power losses (DuckDB syncs its WAL at each commit: a
//! committed transaction must survive) and the default ones. Once faults stop, every committed
//! append must be in its key's list (sdk.elle.final_reads).
//!
//!   determinismo explore ... --memory-mib 2048 --program zig-out/bin/duckdb-test --scenario append
const std = @import("std");
const linux = std.os.linux;
const sdk = @import("determinismo");
const tcp = sdk.tcp;

const Nodes = struct { duck: ?sdk.Node, db: ?sdk.Node, c1: ?sdk.Node, c2: ?sdk.Node };
const System = sdk.System(Nodes);

const port = 7000;
const transactions_per_driver = 20;
const mops_max = 4;
/// Keys move with virtual time, a few at once, so lists stay short.
const keys_window = 4;
const window_s = 5;
const setup_attempts_max = 600;
const final_attempts_max = 240;
/// A final check's whole window once faults stop: a request to a database that never opens again
/// waits out its timeout at each attempt, and 240 of them held a timeline for four hours of
/// virtual time (trial run 1200's timeline 3: the server's WAL refused for good).
const final_window_ns = 600 * std.time.ns_per_s;
const timeout_ms = 60_000;
const line_size_max = 64 * 1024;
const registers = 8;

pub fn main(init: std.process.Init) !void {
    // Every reply is judged (bound parameters, a VARIANT's shape, a trigger's mirrors): each
    // assertion's first pass and first failure a process as events, the verdicts the same
    // (hunt run 1205: 10.4 GB of events per virtual hour with every evaluation).
    sdk.assertion_events = .first;
    return System.main(init, .{
        .describe = describe,
        .scenarios = .{
            .append = append_scenario,
            .fkey_register = register_scenario,
            .trigger = trigger_scenario,
            .variant = variant_scenario,
        },
        .checks = .{
            .elle = sdk.elle.check(.{ .consistency = "strong-snapshot-isolation" }),
            .elle_rw = sdk.elle.check(.{ .model = "rw-register", .consistency = "strong-snapshot-isolation" }),
        },
    });
}

/// The nodes' image: workloads/duckdb/Dockerfile built on a host of ours (host/push-images.sh,
/// with images.json's build arguments: the coverage set below, which they must match) and pushed
/// (push-image.yml), pinned by digest: DuckDB's engine from source takes half an hour of a free
/// runner. A change to the Dockerfile, its files or the coverage set is pushed again and pinned
/// here.
const image = "ghcr.io/determinismo-dst/duckdb-duck@sha256:de02eb5ccd41d0bf42783236aa874d2c26df07d77f890aa6ea8c2851d2a6990f";
/// DuckDB built from its release's source with coverage (Dockerfile): the engine, Quack and httpfs
/// (their sources and the build's unity files under /opt/duckdb, third-party libraries left out),
/// and the nodes' Python with DuckDB's Python package (the Python SDK).
const coverage: sdk.schema.Coverage = .{
    .include = &.{ "/opt/duckdb/", "/usr/local/lib/python3.12/site-packages/duckdb/" },
    .exclude = &.{"/opt/duckdb/src/external/duckdb/third_party/"},
};
const quack_port = 9494;

fn describe(d: *System.Describe) !void {
    const profile = try d.profile("default");
    profile.node(.duck, .{
        .image = image,
        .coverage = coverage,
        .ready = .{ .tcp = port },
        .faults = .{ .restart = true, .crash = true, .stop = true },
    });
    inline for (.{ .{ "quack", false }, .{ "quack-reconnects", true } }) |entry| {
        const quack = try d.profile(entry[0]);
        const env: []const []const u8 = if (entry[1]) &.{"QUACK_RECONNECTS=1"} else &.{};
        quack.node(.db, .{
            .image = image,
            .coverage = coverage,
            .entrypoint = &.{ "python3", "-u", "/opt/duckdb/quack_server.py" },
            .env = env,
            .ready = .{ .tcp = quack_port },
            .faults = .{ .restart = true, .crash = true, .stop = true },
        });
        inline for (.{ .c1, .c2 }) |name| {
            quack.node(name, .{
                .image = image,
                .coverage = coverage,
                // After the image's entrypoint (local_node.py 7000).
                .command = &.{ "--quack", "db" },
                .env = env,
                .ready = .{ .tcp = port },
                .after = &.{.db},
                .faults = .{ .restart = true, .stop = true },
            });
        }
    }
}

/// This transaction's values: bound as parameters, or written in as literals (a draw each).
fn values_literal() bool {
    return sdk.random_below_named("duckdb.values_literal", 2) == 0;
}

fn trigger_scenario(s: *System.Scenario) void {
    s.setup("tables", tables_create);
    s.parallel_driver("trigger", trigger_transactions);
    s.parallel_driver("checkpoint", checkpoints);
    s.workload("trigger");
    s.finally("mirrors", mirrors_final);
}

fn append_scenario(s: *System.Scenario) void {
    s.setup("tables", tables_create);
    s.parallel_driver("append", appends);
    s.parallel_driver("checkpoint", checkpoints);
    s.workload("append");
    s.finally("final reads", final_reads);
}

fn register_scenario(s: *System.Scenario) void {
    s.setup("tables", tables_create);
    s.parallel_driver("register", register_transactions);
    s.parallel_driver("checkpoint", checkpoints);
    s.workload("register");
}

fn variant_scenario(s: *System.Scenario) void {
    s.setup("tables", tables_create);
    s.parallel_driver("variant", variant_transactions);
    s.parallel_driver("checkpoint", checkpoints);
    s.workload("variant");
}

const Client = struct {
    connection: tcp.Connection,
    line: [line_size_max]u8 = undefined,

    /// The embedded database's node, or one of the Quack clients, whose session this connection
    /// draws: CONNECT-ed (Quack's recommended way) or the server attached as the default catalog.
    fn open(client: *Client, context: *System.Context) !void {
        try client.open_plain(context);
        if (context.nodes.duck != null) return;
        const attach = sdk.random_below_named("duckdb.quack_session_attach", 2) == 0;
        const reply = try client.request("session {s}", .{if (attach) "attach" else "connect"});
        if (!std.mem.eql(u8, reply, "ok")) return error.BadReply;
    }

    /// Setup's: a Quack client's default session (CONNECT-ed: its triggers' DDL).
    fn open_plain(client: *Client, context: *System.Context) !void {
        const node = context.nodes.duck orelse if (sdk.random_below(2) == 0) context.nodes.c1.? else context.nodes.c2.?;
        try client.connection.open(node.address, port, .{ .timeout_ms = timeout_ms });
    }

    /// One request line, one reply line (valid until the next request).
    fn request(client: *Client, comptime format: []const u8, arguments: anytype) ![]const u8 {
        const line = try std.fmt.bufPrint(&client.line, format ++ "\n", arguments);
        try client.connection.write_all(line);
        return client.connection.read_line();
    }
};

fn tables_create(context: *System.Context) !void {
    _ = try sdk.retry(setup_attempts_max, 500, tables_try, .{context});
}

fn tables_try(context: *System.Context) !void {
    var client: Client = undefined;
    try client.open_plain(context); // Retried until the node answers.
    defer client.connection.close();
    const reply = try client.request("setup", .{});
    if (std.mem.eql(u8, reply, "ok")) return;
    sdk.event("duckdb_error", .{ .command = "setup", .reply = clip(reply) });
    return error.NotCreated;
}

const Outcome = enum { committed, not_committed, unknown };

/// The node's verdict on a transaction (its results after "ok "). Bound parameters must reach
/// the database where the session supports them: embedded, and a Quack server attached as a
/// catalog (2.0.0 and 2.0.1's pre-release refuse them there: "Values were not provided"). A
/// CONNECT-ed session refuses them by design (DuckDB's fix for #27628), marked by the node.
fn outcome_of(reply: []const u8) Outcome {
    const refused_by_design = std.mem.startsWith(u8, reply, "fail unsupported-while-connected");
    sdk.always(refused_by_design or std.mem.indexOf(u8, reply, "Values were not provided for the following parameters") == null, "a statement's bound parameters reach the database", .{ .reply = clip(reply) });
    if (refused_by_design) sdk.event("duckdb_bound_refused_connected", .{});
    if (std.mem.startsWith(u8, reply, "ok")) return .committed;
    if (std.mem.startsWith(u8, reply, "fail")) {
        sdk.event("duckdb_fail", .{ .reply = clip(reply) });
        return .not_committed;
    }
    sdk.event("duckdb_reply", .{ .reply = clip(reply) });
    return .unknown;
}

// Jepsen's append ----------------------------------------------------------------------------------

const Mop = struct { append: bool, key: u64, value: u64 };

fn appends(context: *System.Context) !void {
    const arena = context.init.arena.allocator();
    var client: Client = undefined;
    client.open(context) catch |err| return reachable_or(err);
    // A reconnection that failed left it closed already.
    defer if (client.connection.fd >= 0) client.connection.close();
    const history: sdk.elle.History = .{};
    const id = sdk.random_below(1 << 32);
    var process = sdk.elle.process_new();
    for (0..transactions_per_driver) |sequence| {
        var mops: [mops_max]Mop = undefined;
        const count: u32 = @intCast(1 + sdk.swarm_index("duckdb.mops", mops_max)); // Stretches of one size.
        const base = monotonic_ns() / std.time.ns_per_s / window_s;
        const literal = values_literal();
        var line: std.ArrayList(u8) = .empty;
        try line.appendSlice(arena, if (literal) "txnl" else "txn");
        for (mops[0..count], 0..) |*mop, position| {
            mop.* = .{
                .append = sdk.swarm_index("duckdb.append_mop", 2) == 0,
                .key = base + sdk.swarm_index("duckdb.append_key", keys_window),
                // Unique per key: the driver, its transaction, the micro-operation.
                .value = (id << 20) | (sequence << 4) | position,
            };
            // Jepsen's choices: ON CONFLICT or MERGE INTO; the primary key or the secondary.
            if (mop.append) {
                try line.print(arena, " a:{d}:{d}:{c}", .{ mop.key, mop.value, "cm"[sdk.random_below(2)] });
            } else {
                try line.print(arena, " r:{d}:{c}", .{ mop.key, "is"[sdk.random_below(2)] });
            }
        }
        try history.invoke(arena, process, try elle_mops(arena, mops[0..count], null));
        var reads: [mops_max]?[]const u64 = @splat(null);
        const reply = client.request("{s}", .{line.items}) catch {
            try history.info(arena, process, try elle_mops(arena, mops[0..count], null));
            process = sdk.elle.process_new();
            client.connection.close();
            client.open(context) catch return;
            continue;
        };
        var outcome = outcome_of(reply);
        if (outcome == .committed) reads_parse(arena, reply, mops[0..count], &reads) catch {
            sdk.event("duckdb_reply", .{ .reply = clip(reply) });
            outcome = .unknown;
        };
        switch (outcome) {
            .committed => {
                try history.ok(arena, process, try elle_mops(arena, mops[0..count], &reads));
                sdk.sometimes(true, "a transaction committed", .{});
                sdk.sometimes(!literal, "a transaction with bound parameters committed", .{});
            },
            .not_committed => {
                try history.fail(arena, process, try elle_mops(arena, mops[0..count], null));
                sdk.sometimes(true, "a transaction was refused", .{});
            },
            .unknown => {
                try history.info(arena, process, try elle_mops(arena, mops[0..count], null));
                sdk.sometimes(true, "a transaction's outcome is unknown", .{});
                process = sdk.elle.process_new(); // Elle's rule: one operation at a time.
            },
        }
    }
}

/// "ok <field>...": a field per mop, in order, `-` for an append, `[v1,v2,...]` for a read.
fn reads_parse(arena: std.mem.Allocator, reply: []const u8, mops: []const Mop, reads: *[mops_max]?[]const u64) !void {
    var fields = std.mem.tokenizeScalar(u8, reply["ok".len..], ' ');
    for (mops, 0..) |mop, position| {
        const field = fields.next() orelse return error.BadReply;
        if (mop.append) {
            if (!std.mem.eql(u8, field, "-")) return error.BadReply;
            continue;
        }
        reads[position] = try list_parse(arena, field);
    }
    if (fields.next() != null) return error.BadReply;
}

/// "[v1,v2,...]" to its values.
fn list_parse(arena: std.mem.Allocator, field: []const u8) ![]const u64 {
    if (field.len < 2 or field[0] != '[' or field[field.len - 1] != ']') return error.BadReply;
    var values: std.ArrayList(u64) = .empty;
    var items = std.mem.tokenizeScalar(u8, field[1 .. field.len - 1], ',');
    while (items.next()) |item| try values.append(arena, try std.fmt.parseInt(u64, item, 10));
    return values.items;
}

fn elle_mops(arena: std.mem.Allocator, mops: []const Mop, reads: ?*const [mops_max]?[]const u64) ![]const sdk.elle.Mop {
    const out = try arena.alloc(sdk.elle.Mop, mops.len);
    for (mops, out, 0..) |mop, *elle_mop, position| {
        elle_mop.* = if (mop.append)
            .{ .append = .{ .key = mop.key, .value = mop.value } }
        else
            .{ .read = .{ .key = mop.key, .list = if (reads) |known| known[position] orelse &.{} else null } };
    }
    return out;
}

/// Every committed append is in its key's list, read in a transaction of its own
/// (sdk.elle.final_reads).
fn final_reads(context: *System.Context) !void {
    const arena = context.init.arena.allocator();
    const history: sdk.elle.History = .{};
    var reader: FinalReader = .{ .context = context };
    defer if (reader.connected) reader.client.connection.close();
    try sdk.elle.final_reads(arena, &history, &reader);
}

const FinalReader = struct {
    context: *System.Context,
    client: Client = undefined,
    connected: bool = false,
    attempts: u32 = 0,
    deadline_ns: u64 = 0,

    pub fn read_list(reader: *FinalReader, arena: std.mem.Allocator, key: u64) ?[]const u64 {
        if (reader.deadline_ns == 0) reader.deadline_ns = monotonic_ns() + final_window_ns;
        while (reader.attempts < final_attempts_max and monotonic_ns() < reader.deadline_ns) {
            if (!reader.connected) {
                reader.client.open(reader.context) catch {
                    reader.attempts += 1;
                    sdk.sleep_ms(500);
                    continue;
                };
                reader.connected = true;
            }
            const reply = reader.client.request("{s} {d}", .{ if (values_literal()) "readl" else "read", key }) catch {
                reader.client.connection.close();
                reader.connected = false;
                reader.attempts += 1;
                continue;
            };
            _ = outcome_of(reply);
            if (std.mem.startsWith(u8, reply, "ok ")) {
                if (list_parse(arena, reply["ok ".len..])) |list| return list else |_| {}
            }
            sdk.event("duckdb_final_read", .{ .key = key, .reply = clip(reply) });
            reader.attempts += 1;
            sdk.sleep_ms(500);
        }
        return null;
    }
};

// Jepsen's fkey-register ---------------------------------------------------------------------------

const RegisterMop = struct { write: bool, key: u64, value: u64 };

fn register_transactions(context: *System.Context) !void {
    return registers_run(context, .fkey);
}

/// DuckDB 2.0's VARIANT: a register whose values are variants of four shapes (local_node.py), the
/// shape drawn for each write and kept in the value's low bits; Elle's rw-register on the values,
/// and each read the shape its value was written with.
fn variant_transactions(context: *System.Context) !void {
    return registers_run(context, .variant);
}

const RegisterKind = enum { fkey, variant };

/// variant_typeof's answer for each shape (value mod 4), as local_node.py writes them.
const variant_types = [4][]const u8{ "INT64", "VARCHAR", "ARRAY(2)", "OBJECT(tag,v)" };

fn registers_run(context: *System.Context, comptime kind: RegisterKind) !void {
    const arena = context.init.arena.allocator();
    var client: Client = undefined;
    client.open(context) catch |err| return reachable_or(err);
    // A reconnection that failed left it closed already.
    defer if (client.connection.fd >= 0) client.connection.close();
    const history: sdk.elle.History = .of("elle_rw");
    // Values unique: a collision would read as an anomaly.
    const id = sdk.random_below(1 << 40);
    var process = sdk.elle.process_new();
    for (0..transactions_per_driver) |sequence| {
        var mops: [mops_max]RegisterMop = undefined;
        const count: u32 = @intCast(1 + sdk.swarm_index("duckdb.mops", mops_max)); // Stretches of one size.
        var line: std.ArrayList(u8) = .empty;
        try line.appendSlice(arena, if (values_literal()) "txnl" else "txn");
        for (mops[0..count], 0..) |*mop, position| {
            mop.* = .{
                .write = sdk.swarm_index("duckdb.register_mop", 2) == 0,
                .key = sdk.swarm_index("duckdb.register_key", registers),
                .value = (id << 10) | (sequence << 4) | (position << 2) | sdk.random_below(4),
            };
            if (kind == .variant) {
                if (mop.write) try line.print(arena, " vw:{d}:{d}", .{ mop.key, mop.value }) else try line.print(arena, " vg:{d}", .{mop.key});
            } else if (mop.write) {
                // Jepsen's: the physical row in place, or a fresh one the key points to.
                try line.print(arena, " w:{d}:{d}:{c}", .{ mop.key, mop.value, "pl"[sdk.random_below(2)] });
            } else {
                try line.print(arena, " g:{d}", .{mop.key});
            }
        }
        const asked = try register_mops(arena, mops[0..count], null);
        try history.invoke(arena, process, asked);
        const reply = client.request("{s}", .{line.items}) catch {
            try history.info(arena, process, asked);
            process = sdk.elle.process_new();
            client.connection.close();
            client.open(context) catch return;
            continue;
        };
        switch (outcome_of(reply)) {
            .committed => {
                var fields = std.mem.tokenizeScalar(u8, reply["ok".len..], ' ');
                var values: [mops_max]?u64 = @splat(null);
                for (mops[0..count], 0..) |mop, position| {
                    const field = fields.next() orelse "";
                    if (!mop.write) values[position] = if (kind == .variant) variant_value(field) else std.fmt.parseInt(u64, field, 10) catch null;
                }
                try history.ok(arena, process, try register_mops(arena, mops[0..count], &values));
                sdk.sometimes(true, "a register transaction committed", .{});
                if (kind == .variant) sdk.sometimes(true, "a VARIANT transaction committed", .{});
            },
            .not_committed => try history.fail(arena, process, asked),
            .unknown => {
                try history.info(arena, process, asked);
                process = sdk.elle.process_new();
            },
        }
    }
}

/// A VARIANT read's value ("<v>:<type>", or "null"), its type judged against the shape the value
/// was written with.
fn variant_value(field: []const u8) ?u64 {
    if (std.mem.eql(u8, field, "null")) return null;
    const colon = std.mem.indexOfScalar(u8, field, ':') orelse return null;
    const value = std.fmt.parseInt(u64, field[0..colon], 10) catch return null;
    const kind = field[colon + 1 ..];
    sdk.always(std.mem.eql(u8, kind, variant_types[value % 4]), "a VARIANT reads back the shape it was written with", .{
        .value = value,
        .type = kind,
        .written = variant_types[value % 4],
    });
    return value;
}

fn register_mops(arena: std.mem.Allocator, mops: []const RegisterMop, values: ?*const [mops_max]?u64) ![]const sdk.elle.Mop {
    const out = try arena.alloc(sdk.elle.Mop, mops.len);
    for (mops, out, 0..) |mop, *elle_mop, position| {
        elle_mop.* = if (mop.write)
            .{ .write = .{ .key = mop.key, .value = mop.value } }
        else
            .{ .read_register = .{ .key = mop.key, .value = if (values) |known| known[position] else null } };
    }
    return out;
}

// DuckDB 2.0's triggers ----------------------------------------------------------------------------

/// What the trigger drivers did, for the final check (the runner's /tmp, a timeline's own):
/// `+e <id>` an insert into ev committed, `?x <id>` a delete of it sent (written before it is),
/// `-e <id>` that delete committed, `!x <id>` refused, `+r <id>` an insert into rows committed.
/// An id with an outcome unknown (or a driver killed mid-call) is in neither list: either way.
const trigger_log_path = "/tmp/duckdb-triggers.log";
const trigger_batch = 64;

const TriggerMop = struct { kind: u8, id: u64 };

fn trigger_transactions(context: *System.Context) !void {
    const arena = context.init.arena.allocator();
    var client: Client = undefined;
    client.open(context) catch |err| return reachable_or(err);
    defer if (client.connection.fd >= 0) client.connection.close();
    const id = sdk.random_below(1 << 40);
    // This driver's committed inserts into ev it has not tried to delete.
    var inserted: std.ArrayList(u64) = .empty;
    for (0..transactions_per_driver) |sequence| {
        var mops: [mops_max]TriggerMop = undefined;
        const count: u32 = @intCast(1 + sdk.swarm_index("duckdb.mops", mops_max)); // Stretches of one size.
        var line: std.ArrayList(u8) = .empty;
        try line.appendSlice(arena, if (values_literal()) "txnl" else "txn");
        var deleting: ?u64 = null;
        for (mops[0..count], 0..) |*mop, position| {
            const fresh = (id << 8) | (sequence << 2) | position;
            const kind = sdk.random_below(4);
            mop.* = if (kind == 1 and deleting == null and inserted.items.len > 0) delete: {
                const victim = inserted.swapRemove(sdk.random_below(inserted.items.len));
                deleting = victim;
                break :delete .{ .kind = 'x', .id = victim };
            } else switch (kind) {
                2 => .{ .kind = 'o', .id = fresh },
                3 => .{ .kind = 'm', .id = 0 },
                else => .{ .kind = 'i', .id = fresh },
            };
            switch (mop.kind) {
                'i', 'o' => try line.print(arena, " {c}:{d}:{d}", .{ mop.kind, mop.id, sequence }),
                'x' => try line.print(arena, " x:{d}", .{mop.id}),
                else => try line.appendSlice(arena, " m"),
            }
        }
        if (deleting) |victim| trigger_log("?x", victim);
        const reply = client.request("{s}", .{line.items}) catch {
            client.connection.close();
            client.open(context) catch return;
            continue;
        };
        switch (outcome_of(reply)) {
            .committed => {
                mirrors_judge(reply, mops[0..count]);
                for (mops[0..count]) |mop| switch (mop.kind) {
                    'i' => {
                        trigger_log("+e", mop.id);
                        try inserted.append(arena, mop.id);
                    },
                    'x' => trigger_log("-e", mop.id),
                    'o' => trigger_log("+r", mop.id),
                    else => {},
                };
                sdk.sometimes(deleting != null, "a delete fires its trigger", .{});
            },
            .not_committed => {
                if (deleting) |victim| trigger_log("!x", victim);
                // Its inserts never happened: their ids are not used again (fresh ones each).
            },
            .unknown => {},
        }
    }
}

/// A committed transaction's snapshots (its `m` results): each mirror the same rows as its table.
fn mirrors_judge(reply: []const u8, mops: []const TriggerMop) void {
    var fields = std.mem.tokenizeScalar(u8, reply["ok".len..], ' ');
    for (mops) |mop| {
        const field = fields.next() orelse return;
        if (mop.kind != 'm') continue;
        var digests = std.mem.splitScalar(u8, field, '|');
        const ev = digests.next() orelse "";
        const ev_mirror = digests.next() orelse "";
        const rows = digests.next() orelse "";
        const rows_mirror = digests.next() orelse "";
        sdk.always(std.mem.eql(u8, ev, ev_mirror) and std.mem.eql(u8, rows, rows_mirror), "each snapshot's trigger mirrors hold their tables' rows", .{
            .ev = ev,
            .ev_mirror = ev_mirror,
            .rows = rows,
            .rows_mirror = rows_mirror,
        });
        sdk.sometimes(!std.mem.startsWith(u8, ev, "0:"), "a snapshot reads a trigger's copies", .{});
    }
}

fn trigger_log(comptime tag: []const u8, id: u64) void {
    var buffer: [48]u8 = undefined;
    const line = std.fmt.bufPrint(&buffer, tag ++ " {d}\n", .{id}) catch return;
    const flags: linux.O = .{ .ACCMODE = .WRONLY, .CREAT = true, .APPEND = true, .CLOEXEC = true };
    const fd = linux.open(trigger_log_path, flags, 0o644);
    if (linux.errno(fd) != .SUCCESS) return;
    defer _ = linux.close(@intCast(fd));
    _ = linux.write(@intCast(fd), line.ptr, line.len);
}

const Expected = struct { inserted: bool = false, delete_sent: u32 = 0, deleted: bool = false, refused: u32 = 0, row: bool = false };

/// Once faults stop: every committed insert into ev not possibly deleted is in ev and its mirror,
/// every committed delete gone from both, every committed insert into rows in rows and its
/// mirror; and the mirrors hold what their tables do.
fn mirrors_final(context: *System.Context) !void {
    const arena = context.init.arena.allocator();
    var expected: std.AutoArrayHashMapUnmanaged(u64, Expected) = .empty;
    const log = std.Io.Dir.cwd().readFileAlloc(context.init.io, trigger_log_path, arena, .limited(64 << 20)) catch "";
    var lines = std.mem.tokenizeScalar(u8, log, '\n');
    while (lines.next()) |line| {
        if (line.len < 4) continue;
        const id = std.fmt.parseInt(u64, line[3..], 10) catch continue;
        const entry = try expected.getOrPut(arena, id);
        if (!entry.found_existing) entry.value_ptr.* = .{};
        const tag = line[0..2];
        if (std.mem.eql(u8, tag, "+e")) entry.value_ptr.inserted = true;
        if (std.mem.eql(u8, tag, "?x")) entry.value_ptr.delete_sent += 1;
        if (std.mem.eql(u8, tag, "-e")) entry.value_ptr.deleted = true;
        if (std.mem.eql(u8, tag, "!x")) entry.value_ptr.refused += 1;
        if (std.mem.eql(u8, tag, "+r")) entry.value_ptr.row = true;
    }
    var reader: TriggerReader = .{ .context = context };
    defer if (reader.connected) reader.client.connection.close();
    const digests = reader.ask(arena, "m") orelse return sdk.assert_unreachable("the trigger tables answer once faults stop", .{});
    mirrors_judge(digests, &.{.{ .kind = 'm', .id = 0 }});
    const ids = expected.keys();
    var start: usize = 0;
    while (start < ids.len) : (start += trigger_batch) {
        const batch = ids[start..@min(ids.len, start + trigger_batch)];
        var line: std.ArrayList(u8) = .empty;
        for (batch, 0..) |id, position| try line.print(arena, "{s}k:{d}", .{ if (position == 0) "" else " ", id });
        const reply = reader.ask(arena, line.items) orelse return sdk.assert_unreachable("the trigger tables answer once faults stop", .{});
        var fields = std.mem.tokenizeScalar(u8, reply["ok".len..], ' ');
        for (batch) |id| {
            const flags = fields.next() orelse "";
            if (flags.len != 4) return sdk.assert_unreachable("the trigger tables answer once faults stop", .{ .reply = clip(reply) });
            const want = expected.get(id).?;
            const in_ev = flags[0] == '1';
            const in_ev_mirror = flags[1] == '1';
            const in_rows = flags[2] == '1';
            const in_rows_mirror = flags[3] == '1';
            const kept = want.inserted and (want.delete_sent == want.refused);
            sdk.always(!kept or (in_ev and in_ev_mirror), "a committed insert and its trigger's copy survive", .{ .id = id, .ev = in_ev, .ev_mirror = in_ev_mirror });
            sdk.always(!want.deleted or (!in_ev and !in_ev_mirror), "a committed delete takes the row and its trigger's copy", .{ .id = id, .ev = in_ev, .ev_mirror = in_ev_mirror });
            sdk.always(!want.row or (in_rows and in_rows_mirror), "a committed row and its row trigger's copy survive", .{ .id = id, .rows = in_rows, .rows_mirror = in_rows_mirror });
            sdk.always(in_ev == in_ev_mirror and in_rows == in_rows_mirror, "a row is in its trigger's mirror exactly when in its table", .{ .id = id, .flags = flags });
        }
    }
    sdk.event("trigger_final", .{ .ids = ids.len });
}

/// One transaction of the final check through any client that answers, its values drawn.
const TriggerReader = struct {
    context: *System.Context,
    client: Client = undefined,
    connected: bool = false,
    attempts: u32 = 0,
    deadline_ns: u64 = 0,

    fn ask(reader: *TriggerReader, arena: std.mem.Allocator, mops: []const u8) ?[]const u8 {
        if (reader.deadline_ns == 0) reader.deadline_ns = monotonic_ns() + final_window_ns;
        while (reader.attempts < final_attempts_max and monotonic_ns() < reader.deadline_ns) {
            if (!reader.connected) {
                reader.client.open(reader.context) catch {
                    reader.attempts += 1;
                    sdk.sleep_ms(500);
                    continue;
                };
                reader.connected = true;
            }
            const reply = reader.client.request("{s} {s}", .{ if (values_literal()) "txnl" else "txn", mops }) catch {
                reader.client.connection.close();
                reader.connected = false;
                reader.attempts += 1;
                continue;
            };
            if (outcome_of(reply) == .committed) return arena.dupe(u8, reply) catch null;
            reader.attempts += 1;
            sdk.sleep_ms(500);
        }
        return null;
    }
};

/// DuckDB's checkpoint (its WAL folded into the database file) beside the workload: past a 16 MB
/// WAL by default, which a timeline never writes, so a nemesis of the workload's own asks for
/// one, now and then forced (FORCE CHECKPOINT aborts the transactions under way), and each node
/// start draws its automatic threshold (local_node.py). Committed transactions must survive it,
/// its interruption and the power losses around it: the scenario's own properties judge them.
fn checkpoints(context: *System.Context) !void {
    var client: Client = undefined;
    client.open(context) catch |err| return reachable_or(err);
    defer if (client.connection.fd >= 0) client.connection.close();
    for (0..3) |_| {
        sdk.sleep_ms(500 + sdk.random_below(5_000));
        const force = sdk.random_below(4) == 0;
        sdk.event("duckdb_checkpoint", .{ .force = force, .reply = "sent" });
        const reply = client.request("{s}", .{if (force) "checkpoint force" else "checkpoint"}) catch return;
        const done = std.mem.eql(u8, reply, "ok");
        sdk.event("duckdb_checkpoint", .{ .force = force, .reply = clip(reply) });
        sdk.sometimes(done, "a checkpoint completes under the workload", .{});
        sdk.sometimes(done and force, "a forced checkpoint completes under the workload", .{});
    }
}

/// A driver whose node is down (a fault) ends quietly; any other error is the driver's.
fn reachable_or(err: anyerror) anyerror!void {
    if (!tcp.unavailable(err)) return err;
    sdk.sometimes(true, "a driver finds its node down", .{});
}

fn clip(text: []const u8) []const u8 {
    return text[0..@min(text.len, 400)];
}

fn monotonic_ns() u64 {
    var now: linux.timespec = undefined;
    _ = linux.clock_gettime(.MONOTONIC, &now);
    return @as(u64, @intCast(now.sec)) * std.time.ns_per_s + @as(u64, @intCast(now.nsec));
}
