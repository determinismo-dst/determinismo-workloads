# SPDX-License-Identifier: MIT
# The DuckDB node, as Jepsen's local node (jepsen-io/duckdb's local-node): one process embedding
# DuckDB, its database the file /data/jepsen.duckdb, serving determinismo's drivers over a line
# protocol, one DuckDB connection (a cursor of the one database) each:
#
#   setup                          -> ok | error <reason>
#   txn <mop>...                   -> ok <result>... | fail <reason> | unknown <reason>
#   read <k>                       -> ok [v,...] | fail <reason>
#   checkpoint [force]             -> ok | fail <reason> (FORCE CHECKPOINT aborts the
#                                     transactions under way)
#
# Append mops (Jepsen's append workload, its three tables append0..2, a key's table k mod 3, its
# list a text `val_text` for even keys or a BIGINT[] `val_list` for odd ones, Jepsen's
# INTEGER[] widened: our values are unique across drivers, wider than 32 bits):
#   r:<k>:<col>        a read of key k by `id` (col i) or by the unindexed `sk` (col s): [v,...]
#   a:<k>:<v>:<how>    an append, through INSERT ... ON CONFLICT (how c) or MERGE INTO (how m): -
# Foreign-key register mops (Jepsen's fkey-register: `logical` maps a key to a `physical` row):
#   g:<k>              a read: the value, or null
#   w:<k>:<v>:<mode>   a write: the physical row updated in place (mode p) or a fresh physical row
#                      the logical key then points to (mode l): -
#
# Trigger mops (DuckDB 2.0's triggers: `ev` copied into `ev_mirror` by statement triggers over
# their transition tables, on insert and on delete; `rows` into `rows_mirror` by a row trigger):
#   i:<id>:<v>         an insert into ev: -
#   x:<id>             a delete from ev: -
#   o:<id>:<v>         an insert into rows: -
#   m                  ev, ev_mirror, rows and rows_mirror in one snapshot, each as its ids'
#                      count, sum and sum of squares: <c>:<s>:<q>|<c>:<s>:<q>|<c>:<s>:<q>|<c>:<s>:<q>
#   k:<id>             where id is: a digit each for ev, ev_mirror, rows, rows_mirror (1 present)
#
# VARIANT register mops (DuckDB 2.0's VARIANT type: a register `variants`, its values of four
# shapes, the shape v mod 4: an integer, a text, a list [v, v+1], a struct {'v': v, 'tag': ...}):
#   vw:<k>:<v>         a write (INSERT OR REPLACE): -
#   vg:<k>             a read: <v>:<type> (the value the variant holds, variant_typeof's answer),
#                      or null
#
# A transaction is BEGIN, its mops, COMMIT. An error before the commit rolls it back: fail.
# A commit refused for a conflict (DuckDB's optimistic concurrency, "Conflict on ..."): fail. Any
# other error at the commit: unknown. Every choice (key, statement, column, mode) is the driver's.
#
# `local_node.py <port> --quack <host>`: a client of DuckDB 2.0's Quack server on <host> instead
# (quack_server.py), the database there: each driver's connection a DuckDB of its own that
# ATTACHes the server and CONNECTs to it (Quack's recommended way: the whole session routed to
# the server, transactions forwarded), or, after `session attach`, uses it as its default
# catalog (`USE qk`: plans run in the client, tables on the server). QUACK_RECONNECTS=1 turns the
# client's reconnect support on (the server's too, there).
#   session connect|attach         -> ok (the connection's next session of that kind)
#
# Two ways to send a statement's values, the driver's choice for each transaction: `txn` binds
# them as parameters (a prepared statement, what applications write), `txnl` writes them into the
# statement's text as literals. 2.0.0 refuses bound parameters through a Quack session ("Values
# were not provided for the following parameters", fixed after the release: duckdb#27628): the
# drivers' property on `txn` reports it, and `txnl` keeps every other part of Quack tested.
import os
import socket
import sys
import threading

import duckdb

import determinismo as det

PATH = "/data/jepsen.duckdb"
TABLES = 3
TOKEN = "determinismo-token"
EXTENSIONS = {"extension_directory": "/opt/duckdb/extensions"}  # Quack and httpfs are built in (Dockerfile); none installed.
# DuckDB folds its WAL into the database file (a checkpoint) once the WAL passes 16 MB, which a
# timeline's few MB never reach: each start draws the threshold ($DETERMINISMO_DRAW, the number
# determinismo draws for it; DuckDB's default outside it), so checkpoints run under the faults.
THRESHOLDS = ("16MB", "1MB", "64KB", "8KB")
THRESHOLD = THRESHOLDS[(int(os.environ.get("DETERMINISMO_DRAW", "0")) >> 8) % len(THRESHOLDS)]
QUACK_HOST = sys.argv[sys.argv.index("--quack") + 1] if "--quack" in sys.argv else None
RECONNECTS = os.environ.get("QUACK_RECONNECTS") == "1"

database = None
database_lock = threading.Lock()


def reason(error):
    text = str(error).replace("\n", " ").replace("\r", " ")
    return (type(error).__name__ + ": " + text)[:300]


def opened():
    global database
    with database_lock:
        if database is None:
            database = duckdb.connect(PATH, config={"checkpoint_threshold": THRESHOLD})
            print("local_node: checkpoint_threshold", THRESHOLD, flush=True)
        return database


def session(kind="connect"):
    """A driver's connection: a cursor of the embedded database, or a Quack session, `connect`
    (the whole session routed to the server, Quack's recommended way) or `attach` (the server a
    catalog of this DuckDB, made the default one: its plans run here, its tables there)."""
    if QUACK_HOST is None:
        return opened().cursor()
    connection = duckdb.connect(config=EXTENSIONS)
    connection.execute("LOAD quack")
    if RECONNECTS:
        connection.execute("SET quack_enable_reconnects = true")
    connection.execute("ATTACH 'quack:%s' AS qk (TOKEN '%s', DISABLE_SSL true)" % (QUACK_HOST, TOKEN))
    connection.execute("CONNECT qk" if kind == "connect" else "USE qk")
    return connection


# A parameterized prepared statement while CONNECT-ed is refused by design ("Parameterized
# prepared statements cannot be executed while CONNECT-ed", DuckDB's fix for #27628; 2.0.0 says
# "Values were not provided"): such a refusal is marked, so that the drivers' property on bound
# parameters judges the sessions that support them (embedded, attached).
BOUND_REFUSED = ("Values were not provided for the following parameters",
                 "Parameterized prepared statements cannot be executed while CONNECT-ed")


def literal(value):
    if isinstance(value, bool) or value is None:
        raise ValueError("no literal for %r" % (value,))
    if isinstance(value, int):
        return str(value)
    return "'" + str(value).replace("'", "''") + "'"


mode = threading.local()  # The thread's statements: values bound, or inlined (`literals`).


def run(cursor, sql, parameters=()):
    """A statement with its parameters: bound, or written in as literals (`txnl`, `readl`)."""
    if not parameters:
        return cursor.execute(sql)
    if not getattr(mode, "literals", False):
        return cursor.execute(sql, list(parameters))
    pieces = sql.split("?")
    assert len(pieces) == len(parameters) + 1, sql
    text = pieces[0] + "".join(literal(value) + piece for value, piece in zip(parameters, pieces[1:]))
    return cursor.execute(text)


def table(key):
    return "append%d" % (key % TABLES)


def text_key(key):
    return key % 2 == 0


def setup(cursor):
    cursor.execute("BEGIN TRANSACTION")
    for i in range(TABLES):
        cursor.execute(
            "CREATE TABLE IF NOT EXISTS append%d (id INT NOT NULL PRIMARY KEY, sk INT NOT NULL, "
            "val_text TEXT, val_list BIGINT[])" % i)
    cursor.execute("CREATE SEQUENCE IF NOT EXISTS physical_id_seq")
    cursor.execute(
        "CREATE TABLE IF NOT EXISTS physical (id INT NOT NULL PRIMARY KEY "
        "DEFAULT nextval('physical_id_seq'), val BIGINT NOT NULL)")
    cursor.execute(
        "CREATE TABLE IF NOT EXISTS logical (id INT NOT NULL PRIMARY KEY, "
        "physical_id INT NOT NULL REFERENCES physical(id))")
    cursor.execute("CREATE TABLE IF NOT EXISTS variants (id BIGINT PRIMARY KEY, v VARIANT NOT NULL)")
    for name in ("ev", "ev_mirror", "rows", "rows_mirror"):
        cursor.execute("CREATE TABLE IF NOT EXISTS %s (id BIGINT PRIMARY KEY, v BIGINT NOT NULL)" % name)
    existing = {row[0] for row in cursor.execute("SELECT trigger_name FROM duckdb_triggers()").fetchall()}
    triggers = {
        # Statement triggers over their transition tables, on insert and on delete.
        "ev_copy": "CREATE TRIGGER ev_copy AFTER INSERT ON ev REFERENCING NEW TABLE AS inserted "
                   "FOR EACH STATEMENT INSERT INTO ev_mirror SELECT * FROM inserted",
        "ev_drop": "CREATE TRIGGER ev_drop AFTER DELETE ON ev REFERENCING OLD TABLE AS removed "
                   "FOR EACH STATEMENT DELETE FROM ev_mirror WHERE id IN (SELECT id FROM removed)",
        # A row trigger, on a table of its own (2.0.0 does not mix the two kinds on one table).
        "rows_copy": "CREATE TRIGGER rows_copy AFTER INSERT ON rows FOR EACH ROW "
                     "INSERT INTO rows_mirror VALUES (NEW.id, NEW.v)",
    }
    for name, statement in triggers.items():
        if name not in existing:
            cursor.execute(statement)
    cursor.execute("COMMIT")


def digest(cursor, name):
    row = cursor.execute(
        "SELECT count(*), coalesce(sum(id::HUGEINT), 0), coalesce(sum(id::HUGEINT * id), 0) FROM %s" % name).fetchone()
    return "%d:%d:%d" % (row[0], row[1], row[2])


def present(cursor, key):
    return "".join(
        "1" if run(cursor, "SELECT 1 FROM %s WHERE id = ?" % name, [key]).fetchone() else "0"
        for name in ("ev", "ev_mirror", "rows", "rows_mirror"))


def list_read(cursor, key, column):
    row = run(cursor,
        "SELECT val_text, val_list FROM %s WHERE %s = ?" % (table(key), column), [key]).fetchone()
    if row is None:
        return "[]"
    if text_key(key):
        return "[" + (row[0] or "") + "]"
    return "[" + ",".join(str(v) for v in (row[1] or [])) + "]"


def append(cursor, key, value, how):
    name = table(key)
    if how == "c":
        if text_key(key):
            run(cursor,
                "INSERT INTO %s AS t (id, sk, val_text) VALUES (?, ?, ?) ON CONFLICT (id) DO UPDATE "
                "SET val_text = CONCAT(t.val_text, ',', ?) WHERE t.id = ?" % name, [key, key, str(value), str(value), key])
        else:
            run(cursor,
                "INSERT INTO %s AS t (id, sk, val_list) VALUES (?, ?, [?]::BIGINT[]) ON CONFLICT (id) "
                "DO UPDATE SET val_list = list_append(t.val_list, ?) WHERE t.id = ?" % name, [key, key, value, value, key])
    else:
        if text_key(key):
            run(cursor,
                "MERGE INTO %s AS t USING (SELECT ? AS id, ? AS sk, ? AS val_text, NULL AS val_list) "
                "AS upserts USING (id) WHEN MATCHED THEN UPDATE SET val_text = CONCAT(t.val_text, ',', ?) "
                "WHEN NOT MATCHED THEN INSERT" % name, [key, key, str(value), str(value)])
        else:
            run(cursor,
                "MERGE INTO %s AS t USING (SELECT ? AS id, ? AS sk, NULL AS val_text, "
                "[?]::BIGINT[] AS val_list) AS upserts USING (id) WHEN MATCHED THEN UPDATE SET "
                "val_list = list_append(t.val_list, ?) WHEN NOT MATCHED THEN INSERT" % name, [key, key, value, value])


def register_read(cursor, key):
    row = run(cursor,
        "SELECT physical.val FROM physical INNER JOIN logical ON logical.physical_id = physical.id "
        "WHERE logical.id = ?", [key]).fetchone()
    return "null" if row is None else str(row[0])


def physical_insert(cursor, value):
    return run(cursor, "INSERT INTO physical (val) VALUES (?) RETURNING id", [value]).fetchone()[0]


def register_write(cursor, key, value, mode):
    if mode == "p":
        row = run(cursor, "SELECT physical_id FROM logical WHERE id = ?", [key]).fetchone()
        if row is not None:
            # The key's own row written too: an update in place and a repoint (mode l) otherwise
            # write disjoint rows, which snapshot isolation commits both (write skew on rows, a
            # lost update on the key: DuckDB 2.0.0 checked natively; hunt run 1983, 37 timelines
            # of Elle's lost-update). Jepsen's write-physical! means them to contend on the
            # logical key; with this every two writes of a key conflict.
            run(cursor, "UPDATE logical SET physical_id = physical_id WHERE id = ?", [key])
            run(cursor, "UPDATE physical SET val = ? WHERE id = ?", [value, row[0]])
            return
        physical = physical_insert(cursor, value)
        run(cursor, "INSERT INTO logical VALUES (?, ?)", [key, physical])
    else:
        physical = physical_insert(cursor, value)
        run(cursor, "INSERT OR REPLACE INTO logical VALUES (?, ?)", [key, physical])


VARIANT_SHAPES = (
    "?::BIGINT::VARIANT",
    "?::VARCHAR::VARIANT",
    "[?::BIGINT, ?::BIGINT + 1]::VARIANT",
    "{'v': ?::BIGINT, 'tag': 'determinismo'}::VARIANT",
)


def variant_write(cursor, key, value):
    shape = VARIANT_SHAPES[value % 4]
    parameters = [value] * shape.count("?")
    run(cursor, "INSERT OR REPLACE INTO variants VALUES (?, %s)" % shape, [key] + parameters)


def variant_read(cursor, key):
    row = run(cursor, "SELECT v::VARCHAR, variant_typeof(v) FROM variants WHERE id = ?", [key]).fetchone()
    if row is None:
        return "null"
    text, kind = row
    digits = ""
    for character in text:
        if character.isdigit():
            digits += character
        elif digits:
            break
    return "%s:%s" % (digits or "?", kind.replace(" ", ""))


def mop(cursor, text):
    if text == "m":
        return "|".join(digest(cursor, name) for name in ("ev", "ev_mirror", "rows", "rows_mirror"))
    parts = text.split(":")
    kind, key = parts[0], int(parts[1])
    if kind == "r":
        return list_read(cursor, key, "id" if parts[2] == "i" else "sk")
    if kind == "a":
        append(cursor, key, int(parts[2]), parts[3])
        return "-"
    if kind == "g":
        return register_read(cursor, key)
    if kind == "w":
        register_write(cursor, key, int(parts[2]), parts[3])
        return "-"
    if kind == "i":
        run(cursor, "INSERT INTO ev VALUES (?, ?)", [key, int(parts[2])])
        return "-"
    if kind == "x":
        run(cursor, "DELETE FROM ev WHERE id = ?", [key])
        return "-"
    if kind == "o":
        run(cursor, "INSERT INTO rows VALUES (?, ?)", [key, int(parts[2])])
        return "-"
    if kind == "k":
        return present(cursor, key)
    if kind == "vw":
        variant_write(cursor, key, int(parts[2]))
        return "-"
    if kind == "vg":
        return variant_read(cursor, key)
    raise ValueError("unknown mop " + text)


def txn(cursor, mops):
    try:
        cursor.execute("BEGIN TRANSACTION")
    except Exception as error:
        return "fail begin: " + reason(error)
    results = []
    try:
        for text in mops:
            results.append(mop(cursor, text))
    except Exception as error:
        try:
            cursor.execute("ROLLBACK")
        except Exception:
            pass
        return "fail " + reason(error)
    try:
        cursor.execute("COMMIT")
    except Exception as error:
        # Optimistic concurrency: a conflict found at the commit rolls it back. Anything else
        # (a Quack session's link lost as the commit went, whatever its exception's class) may
        # have committed.
        if not (isinstance(error, duckdb.TransactionException) and "onflict" in str(error)):
            return "unknown commit: " + reason(error)
        try:
            cursor.execute("ROLLBACK")
        except Exception:
            pass
        return "fail commit: " + reason(error)
    return "ok " + " ".join(results)


def handle(cursor, line):
    words = line.split()
    if not words:
        return "error empty"
    if words[0] == "setup":
        try:
            setup(cursor)
            return "ok"
        except Exception as error:
            try:
                cursor.execute("ROLLBACK")
            except Exception:
                pass
            return "error " + reason(error)
    if words[0] == "checkpoint":
        try:
            cursor.execute("FORCE CHECKPOINT" if words[1:] == ["force"] else "CHECKPOINT")
            return "ok"
        except Exception as error:
            return "fail " + reason(error)
    mode.literals = words[0] in ("txnl", "readl")
    if words[0] in ("txn", "txnl"):
        return txn(cursor, words[1:])
    if words[0] in ("read", "readl"):
        key = int(words[1])
        try:
            cursor.execute("BEGIN TRANSACTION")
            try:
                return "ok " + list_read(cursor, key, "id")
            finally:
                cursor.execute("ROLLBACK")
        except Exception as error:
            return "fail " + reason(error)
    return "error unknown command " + words[0]


# A Quack session the server no longer has (restarted: "Invalid connection id") or cannot be
# reached through: a new one for the next request, as an application's pool would open.
SESSION_LOST = ("Invalid connection id", "Failed to send message", "Could not connect")


def serve(connection):
    cursor = None
    kind = "connect"  # Until the driver asks for another (`session <kind>`).
    reader = connection.makefile("r", encoding="utf-8")
    try:
        for line in reader:
            words = line.split()
            if words[:1] == ["session"] and len(words) == 2 and words[1] in ("connect", "attach"):
                if cursor is not None:
                    cursor.close()
                    cursor = None
                kind = words[1]
                connection.sendall(b"ok\n")
                continue
            if cursor is None:
                try:
                    cursor = session(kind)
                except Exception as error:
                    connection.sendall(("fail open: " + reason(error) + "\n").encode())
                    continue
            reply = handle(cursor, line.strip())
            if QUACK_HOST is not None and kind == "connect" and reply.startswith("fail ") and any(text in reply for text in BOUND_REFUSED):
                reply = "fail unsupported-while-connected " + reply[len("fail "):]
            if QUACK_HOST is not None and any(text in reply for text in SESSION_LOST):
                try:
                    cursor.close()
                except Exception:
                    pass
                cursor = None
            connection.sendall((reply + "\n").encode())
    except Exception:
        pass  # The driver went away.
    finally:
        if cursor is not None:
            cursor.close()
        connection.close()


def main():
    # The platform's coverage (the Python SDK, sys.monitoring): this node's code and DuckDB's
    # Python package, each line a "coverage" event the first time it runs. DuckDB's engine is
    # C++, not covered (serve's gate: a run without coverage is stopped, "coverage always").
    det.coverage_start([os.path.dirname(os.path.abspath(__file__)), os.path.dirname(duckdb.__file__)])
    port = int(sys.argv[1])
    if QUACK_HOST is None:
        opened()  # The database opened (its WAL replayed) before the node listens: ready.
    server = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    server.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    server.bind(("0.0.0.0", port))
    server.listen(64)
    while True:
        connection, _ = server.accept()
        threading.Thread(target=serve, args=(connection,), daemon=True).start()


if __name__ == "__main__":
    main()
