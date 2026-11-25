import Determinismo
import Jank.Nrepl.Runtime

/-!
# The nREPL server in the Threads world (jank 7135b7708)

Threads, each step atomic (one syscall, one stdio call, one parse, one handler):

- the accept loop (core.jank `-main`, line 108; loop at 129–143): `(while true (let [client*
  (accept server*)] (future (try (handle-client client*) (catch ...)))))`;
- one thread per connection (the `future`), running `handle-client` (core.jank:79). Since
  7135b7708 the handling of one request is inside a `try` (lines 85–105): an exception from
  `handle-message` or `write-message` (`std::exception`, a jank `object_ref`, an `error_ref`) is
  answered `(response-for req {:status [:error :done] :err (str "An exception was thrown from the
  nREPL handler:" ...)})` and the loop goes on;
- the clients, each a scripted nREPL client: connect, send requests, read and decode replies
  (with the spec decoder), wait for each request's `done`, close.

## server.cpp, with the OS as decisions

- `native_server::impl::accept` (server.cpp:92) → `native_client::impl::accept` (line 21):
  `acceptor.accept(socket_)` blocks until a client connects. The overload without an
  `error_code` throws `boost::system::system_error` on failure (Boost.Asio's documented
  behaviour; assumption A3): with no free descriptor (EMFILE) the exception leaves `-main`, whose
  `future` keeps it unread: the accept loop is over.
- `native_client::impl::read_some` (line 32): `socket_.read_some(buffer(rx_buf_, 1 MiB), error)`
  returns one or more of the available bytes (a decision: all, or a cut). Since 7135b7708 any
  error (lines 37–41: eof, reset, and also EINTR, a decision) sets `connected_ = false` and
  returns `""`.
- `native_client::impl::write` (line 46): `boost::asio::write(socket_, buffer(message), error)`
  writes every byte or fails (Asio's documented composed operation); an error sets
  `connected_ = false` (lines 51–54). The peer having closed is such an error.
- Descriptors are allocated lowest first up to `fdLimit` (POSIX `dup`, `mkstemp`, `accept`); the
  client socket of a finished connection is never closed (server.cpp:127–129 leaks the
  `native_client`; fork C, C15).

## capture.jank (unchanged; sequential replica; the cross-thread race is fork C's C9)

`start` (line 18): `dup(fd)`, `mkstemp` + `(assert (not= fd -1) ...)`, `fflush`, `dup2(temp, fd)`,
`close(temp)`; `end` (line 39): `fflush`, `dup2(bak, fd)`, `close(bak)`; `readback` (line 52):
`slurp`, `unlink`. `with-capture` (line 60) calls both `start`s before its `try`, so an exception in
the second `start` leaves the first stream redirected.
-/

namespace Jank.NreplServer

open Determinismo

/-! ## The process -/

/-- An open file description an fd refers to. -/
inductive Desc where
  | terminal
  | temp (name : String)
  | sock (cid : Nat)
  | listener
  | held (k : Nat)
  deriving Repr, BEq, Inhabited

structure Sock where
  /-- Client → server bytes not yet read. -/
  inbox : Bytes := []
  /-- The client closed its end. -/
  closed : Bool := false
  /-- Server → client bytes delivered. -/
  outbox : Bytes := []
  deriving Repr, Inhabited

structure Config where
  plat : Platform := {}
  /-- A build without NDEBUG: `jank_debug_assert` aborts. -/
  debugBuild : Bool := false
  partialReads : Bool := true
  /-- A signal may interrupt a blocked `read_some` (EINTR). -/
  eintr : Bool := false
  /-- RLIMIT_NOFILE (soft). -/
  fdLimit : Nat := 32
  /-- Descriptors open before the first client: 0–2 the terminal, 3 the listener, then others. -/
  baseFds : Nat := 4
  /-- stdout is a terminal: line buffered. -/
  lineBuffered : Bool := true
  /-- Scheduler rounds (blocked picks included) before a timeline is cut. -/
  maxSteps : Nat := 4000
  /-- A timeline cut by `maxSteps` counts as a violation of the model's bound (off where EINTR
  storms can last). -/
  requireFinish : Bool := true
  deriving Repr, Inhabited

/-- A client's request, as scripted. Session `n` is the session of the client's `n`-th clone. -/
inductive Req where
  | clone
  | close (sess : Nat)
  | describe
  | eval (sess : Nat) (code : String) (ns : Option String := some "user")
    (inspect : Option JVal := none)
  | loadFile (sess : Nat) (file : String)
  | lookup (ns sym : String)
  /-- The `info` op (lookup.jank:40): the info map itself. -/
  | info (ns sym : String)
  | completions (ns pfx : String)
  /-- A request with this op (none: no "op" key at all). -/
  | unknown (op : Option String)
  /-- Bytes sent as they are (no reply awaited). -/
  | raw (b : Bytes)
  deriving Repr, Inhabited

/-- A request a client sent. -/
structure Sent where
  cid : Nat
  id : String
  req : Req
  session : Option String
  deriving Inhabited

structure Mem where
  cfg : Config
  fds : Array (Option Desc)
  /-- Temp files: name, content, linked. -/
  temps : List (String × Bytes × Bool) := []
  nextTemp : Nat := 0
  terminal : Bytes := []
  /-- `FILE* stdout`'s buffer. -/
  outBuf : Bytes := []
  socks : Array Sock
  /-- Clients connected, not yet accepted. -/
  pending : List Nat := []
  nClients : Nat
  accepted : Nat := 0
  nextUuid : Nat := 0
  /-- Replies each client decoded: (client, reply). -/
  replies : Array (Nat × JVal) := #[]
  sent : Array Sent := #[]
  crashed : Option String := none
  acceptDied : Option String := none
  /-- Handler exceptions answered with `{:status [:error :done]}` (core.jank:91–105). -/
  handlerErrors : List (Nat × String) := []
  /-- Connection threads whose loop ended (`connected_` false); their sockets stay open. -/
  connEnded : List Nat := []
  deriving Inhabited

/-! ## Descriptors and stdio -/

def Mem.fd (m : Mem) (i : Nat) : Option Desc := m.fds.getD i none

def Mem.lowestFree (m : Mem) : Option Nat :=
  (List.range m.cfg.fdLimit).find? fun i => (m.fd i).isNone

def Mem.setFd (m : Mem) (i : Nat) (d : Option Desc) : Mem :=
  if i < m.fds.size then { m with fds := m.fds.set! i d } else m

/-- `write(fd, b)`: to whatever the descriptor refers to now; a closed one loses it (EBADF). -/
def Mem.writeFd (m : Mem) (fd : Nat) (b : Bytes) : Mem :=
  match m.fd fd with
  | some .terminal => { m with terminal := m.terminal ++ b }
  | some (.temp n) =>
    { m with temps := m.temps.map fun (n', c, l) => if n' == n then (n', c ++ b, l) else (n', c, l) }
  | _ => m

/-- `fwrite`/`putc` on `stdout`: buffered; line buffering writes the buffer out at a newline. -/
def Mem.fwriteOut (m : Mem) (b : Bytes) : Mem :=
  let buf := m.outBuf ++ b
  if m.cfg.lineBuffered && b.contains 10 then { m.writeFd 1 buf with outBuf := [] }
  else { m with outBuf := buf }

def Mem.fflush (m : Mem) (fd : Nat) : Mem :=
  if fd == 1 then { m.writeFd 1 m.outBuf with outBuf := [] } else m

/-! ## Threads -/

/-- The map `start` returns (capture.jank:35): the descriptor, `bak-fd`, `temp-name`. -/
structure Handle where
  fd : Nat
  bak : Int
  temp : String
  deriving Repr, Inhabited

/-- The registers of one `do-eval`. -/
structure EvalRegs where
  req : JVal := .nil
  target : String := "user"
  inspect : Option Bool := none
  /-- `start` in progress: its `bak-fd`, temp fd, temp name. -/
  bak : Int := -1
  tempFd : Int := -1
  tempName : String := ""
  outH : Option Handle := none
  errH : Option Handle := none
  forms : List Form := []
  /-- A form ran (`eval_string`'s `no_op` false). -/
  ran : Bool := false
  last : RVal := .nil
  thrown : Option RVal := none
  /-- `println`'s `putc('\n')` is next. -/
  putcNext : Bool := false
  success : Bool := false
  resNs : String := "user"
  stdout : Bytes := []
  stderr : Bytes := []
  deriving Inhabited

/-- One instruction of a connection thread: one step each. -/
inductive CI where
  /-- `handle-client`'s loop head: `(when (connected? client*) (when req ...) (recur ...))`. -/
  | top (req : Option JVal)
  /-- `read-message` (core.jank:58). -/
  | readMsg
  /-- `handle-message` (handler.jank:3) on a request. -/
  | dispatch (req : JVal)
  /-- `(doseq [resp resps] (write-message client* resp))`, for request `req`. -/
  | writeOut (req : JVal) (resps : List JVal)
  | capDup (fd : Nat)
  | capMkstemp (fd : Nat)
  | capFlush (fd : Nat)
  | capDup2 (fd : Nat)
  | capClose (fd : Nat)
  /-- `(binding [*ns* target-ns *file* file-path] ...)`: the push. -/
  | bind
  /-- `eval_string`: the next form (or `println`'s `putc`). -/
  | form
  /-- `safe_eval` after `eval_string`: `unwrap`, `*1`..`*3`, or `*e`. -/
  | finishEval
  /-- The binding's `finally`: the pop (and the `*ns*` read just before it). -/
  | unbind
  | endFlush (fd : Nat)
  | endDup2 (fd : Nat)
  | endClose (fd : Nat)
  | slurp (fd : Nat)
  | unlink (fd : Nat)
  /-- `do-eval`'s `cond`: the replies, then `responses-for`. -/
  | evalReplies
  /-- An exception from handling `req` (core.jank:91–105): the error reply is written, the loop
  goes on. -/
  | handlerError (req : JVal) (msg : String)
  deriving Repr, Inhabited

structure ConnLoc where
  cid : Nat
  /-- `native_client::impl::connected_`. -/
  connected : Bool := true
  remainder : Option Bytes := none
  instrs : List CI := [.top none]
  ev : EvalRegs := {}
  /-- `*ns*` on this thread: binding frames, newest first (the conveyed one last). -/
  nsStack : List String := ["user"]
  /-- `*1`, `*2`, `*3`, `*e` of this thread (one box each, shared by its frames). -/
  star1 : RVal := .nil
  star2 : RVal := .nil
  star3 : RVal := .nil
  starE : RVal := .nil
  deriving Inhabited

inductive Phase where
  | connect
  | send
  | wait (id : String)
  | close
  deriving Repr, BEq, Inhabited

structure ClientLoc where
  cid : Nat
  script : Array Req
  k : Nat := 0
  phase : Phase := .connect
  cursor : Nat := 0
  sessions : Array String := #[]
  /-- Connect only once this client has closed (reconnections, one after the other). -/
  after : Option Nat := none
  deriving Inhabited

inductive Th where
  | acceptor
  | conn (c : ConnLoc)
  | client (c : ClientLoc)
  deriving Inhabited

abbrev SM := ProcessM Mem Th

def mem : SM Mem := do pure (← get).memory
def setMem (m : Mem) : SM Unit := modify fun p => { p with memory := m }
def note (s : String) : SM Unit := Process.note (M := Mem) (L := Th) s

/-! ## Replies built by the handlers -/

def kmap (kvs : List (String × JVal)) : JVal := .map (kvs.map fun (k, v) => (JVal.k k, v))
def statusOf (xs : List String) : JVal := .vec (xs.map JVal.k)

/-- core.jank `response-for` (line 33): `(merge resp (select-keys req ["id" "session"]))`. -/
def responseFor (req resp : JVal) : JVal := merge [resp, selectKeys req [JVal.s "id", JVal.s "session"]]

/-- core.jank `responses-for` (line 39): `(if (sequential? r) r [r])`, each through `response-for`. -/
def responsesFor (req : JVal) (r : JVal) : List JVal :=
  let resps := match r with
    | .vec xs => xs
    | .list xs => xs
    | x => [x]
  resps.map (responseFor req)

/-- A string field of a request. -/
def strField (m : JVal) (k : String) : Option String :=
  match jget m (JVal.s k) with
  | .str b => String.fromUTF8? (ByteArray.mk b.toArray)
  | _ => none

/-- The ops handler/describe.jank (line 5) lists under `:ops` (lines 7–15). -/
def describedOps : List String :=
  ["clone", "describe", "eval", "load-file", "lookup", "info", "completions", "complete", "close"]

/-- handler/describe.jank (line 5). -/
def describeReply : JVal :=
  kmap [("aux", .map []),
        ("ops", kmap (describedOps.map fun o => (o, .map []))),
        ("versions", kmap [("jank", kmap [("version-string", JVal.s "jank-version")])]),
        ("status", statusOf ["done"])]

/-- The ops `handle-message` has a method for (handler/*.jank `defmethod`s). -/
def implementedOps : List String :=
  ["clone", "close", "completions", "complete", "describe", "eval", "load-file", "lookup", "info"]

/-- handler/completions.jank `special-forms` (line 7). -/
def specialForms : List String :=
  ["def", "fn*", "recur", "do", "let*", "letfn*", "loop*", "if", "quote", "var", "throw", "try",
   "case*", "cpp/raw", "cpp/dsl", "cpp/value", "cpp/cast", "cpp/unsafe-cast", "cpp/box",
   "cpp/unbox", "cpp/new", "cpp/delete"]

/-- completions.jank `candidate-type` (line 46). -/
def candidateType (v : VarInfo) : String :=
  if v.isMacro then "macro" else if v.arglists.isSome then "function" else "var"

/-- completions.jank `vars-candidates` (54), `special-candidates` (31) and `handle` (66; prefix
from "prefix" or "symbol"), for `:completions` (76) and `:complete` (79). -/
def completionsReply (req : JVal) : JVal :=
  let pfx := match strField req "prefix" with
    | some p => some p
    | none => strField req "symbol"
  match (strField req "ns").bind findNs, pfx with
  | some n, some pfx =>
    let vars := n.mappings.filterMap fun (k, v) =>
      if k.startsWith pfx then
        some (kmap [("ns", JVal.s n.name), ("type", JVal.k (candidateType v)), ("candidate", JVal.s k)])
      else none
    let specials := specialForms.filterMap fun k =>
      if k.startsWith pfx then some (kmap [("type", JVal.k "special-form"), ("candidate", JVal.s k)])
      else none
    kmap [("completions", .vec (vars ++ specials)), ("status", statusOf ["done"])]
  | _, _ => kmap [("status", statusOf ["done", "namespace-not-found"])]

/-- handler/lookup.jank `lookup` (line 5: the ns, else `default-ns`, line 11) and `handle`
(line 18: sym from "sym" or "symbol"; `:ns` is `(get-in m [:jank/source :module])`, line 23;
`{:info info}` for op "lookup", the info itself for "info", line 31; a miss is
`{:status [:no-info :done]}`, line 35). `current` is the connection thread's `*ns*`, which
`ns-resolve` uses for aliases. -/
def lookupReply (current : String) (req : JVal) : JVal :=
  let ns := strField req "ns"
  let sym := match strField req "sym" with
    | some s => some s
    | none => strField req "symbol"
  let ns' := match ns.bind findNs with
    | some n => some n
    | none => findNs "user"
  let m := match ns', sym with
    | some n, some s => jankNsResolve current n (splitSym s)
    | _, _ => none
  match m with
  | some v =>
    let info := merge [kmap [("ns", (v.module.map JVal.s).getD .nil), ("name", (sym.map JVal.s).getD .nil)],
      (match v.doc with | some d => kmap [("doc", JVal.s d)] | none => .nil),
      (match v.arglists with
        | some a => kmap [("arglists", a), ("arglists-str", JVal.s (JVal.render a))]
        | none => .nil)]
    let body := if strField req "op" == some "info" then info else kmap [("info", info)]
    merge [body, kmap [("status", statusOf ["done"])]]
  | none => kmap [("status", statusOf ["no-info", "done"])]

/-- util.jank `abbreviate` (line 4): `(postwalk inner form)` where `inner` cuts a string of `n` or
more bytes to `(str (subs x 0 n) "…")`. `handle-client` calls it on every request and reply as an
argument of `log` (core.jank:86, 89), which evaluates it whether or not `*verbose` is set; its
result is printed only with `-v`. `subs` counts bytes, so a multi-byte character can be cut. -/
partial def abbreviate (n : Nat) : JVal → JVal
  | .str b => if b.length ≥ n then .str (b.take n ++ bytes "…") else .str b
  | .vec xs => .vec (xs.map (abbreviate n))
  | .list xs => .list (xs.map (abbreviate n))
  | .set xs => .set (xs.map (abbreviate n))
  | .map kvs => .map (kvs.map fun (k, v) => (abbreviate n k, abbreviate n v))
  | x => x

/-! ## The connection thread -/

def setConn (c : ConnLoc) (instrs : List CI) : StepResult Th := .ran (.conn { c with instrs })

/-- The decision of how many bytes `read_some` returns. -/
def readLen (avail : Nat) : SM Nat := do
  let m ← mem
  if !m.cfg.partialReads || avail ≤ 1 then return avail
  if (← decideWeighted (σ := Process Mem Th) "net.read.split" [6, 1]) == 0 then return avail
  pure (1 + (← decide (σ := Process Mem Th) "net.read.len" (avail - 1)))

/-- `do-eval`'s instructions (handler/eval.jank:22), with `with-capture` (capture.jank:60). -/
def evalInstrs : List CI :=
  [.capDup 1, .capMkstemp 1, .capFlush 1, .capDup2 1, .capClose 1,
   .capDup 2, .capMkstemp 2, .capFlush 2, .capDup2 2, .capClose 2,
   .bind, .form, .finishEval, .unbind,
   .endFlush 1, .endDup2 1, .endClose 1, .endFlush 2, .endDup2 2, .endClose 2,
   .slurp 1, .unlink 1, .slurp 2, .unlink 2, .evalReplies]

/-- The pr-str of `*1` for inspection (inspect.jank `inspect-str`), abstractly. -/
def inspectStr (v : RVal) : String := s!"(\"--- Type\" ... (:value \"{v.pr}\") ...)"

def connStep (t : Nat) (c : ConnLoc) : SM (StepResult Th) := do
  let m ← mem
  match c.instrs with
  | [] => pure .done
  | i :: rest =>
  match i with
  | .top req =>
    if !c.connected then
      note s!"conn {c.cid}: not connected: handle-client returns (its socket stays open)"
      setMem { m with connEnded := m.connEnded ++ [c.cid] }
      return .done
    match req with
    | some r => pure (setConn c (.dispatch r :: .readMsg :: rest))
    | none => pure (setConn c (.readMsg :: rest))
  | .readMsg =>
    match parse m.cfg.plat c.remainder with
    | .value v r => pure (.ran (.conn { c with remainder := r, instrs := .top (some v) :: rest }))
    | .crash =>
      setMem { m with crashed := some s!"stack overflow in bencode parse-recur on connection {c.cid}" }
      note s!"conn {c.cid}: parse-recur overflows the stack: the process dies"
      throw (.violation "the process stays up" s!"bencode parse-recur overflowed the stack on connection {c.cid}")
    | .none =>
      let s := m.socks.getD c.cid {}
      let (chunk, connected) ← do
        if !s.inbox.isEmpty then
          let n ← readLen s.inbox.length
          setMem { m with socks := m.socks.set! c.cid { s with inbox := s.inbox.drop n } }
          pure (some (s.inbox.take n), c.connected)
        else if s.closed then pure (some [], false)
        else if m.cfg.eintr && (← decideRare (σ := Process Mem Th) "net.read.eintr" 1 8) then
          -- server.cpp:37–41: any error, EINTR included, ends the connection.
          pure (some [], false)
        else pure (none, c.connected)
      match chunk with
      | none => pure .blocked
      | some ch =>
        let input := (c.remainder.getD []) ++ ch
        if ch.isEmpty then note s!"conn {c.cid}: read_some → \"\" ({if s.closed then "eof" else "EINTR"}): connected_ = false"
        else note s!"conn {c.cid}: read_some → {ch.length} bytes \"{showBytes ch}\""
        match parse m.cfg.plat (some input) with
        | .value v r => pure (.ran (.conn { c with connected, remainder := r, instrs := .top (some v) :: rest }))
        | .none => pure (.ran (.conn { c with connected, remainder := some input, instrs := .top none :: rest }))
        | .crash =>
          setMem { (← mem) with crashed := some s!"stack overflow in bencode parse-recur on connection {c.cid}" }
          throw (.violation "the process stays up" s!"bencode parse-recur overflowed the stack on connection {c.cid} (input of {input.length} bytes)")
  | .dispatch req =>
    let op := keyword (jget req (JVal.s "op"))
    let opName := match op with | .kw _ n => String.fromUTF8? (ByteArray.mk n.toArray) | _ => none
    note s!"conn {c.cid}: handle-message {opName.getD "nil"} (id {(strField req "id").getD "-"})"
    match opName with
    | some "eval" | some "load-file" =>
      let isEval := opName == some "eval"
      -- `(some-> (get msg "inspect") parse-boolean)`: parse-boolean throws on a non-string.
      let inspect : Except String (Option Bool) :=
        if !isEval then .ok (some false) else
        match jget req (JVal.s "inspect") with
        | .nil => .ok none
        | .str b => .ok (if b == bytes "true" then some true else if b == bytes "false" then some false else none)
        | _ => .error "parse-boolean: Expected string"
      match inspect with
      | .error e => pure (setConn c (.handlerError req e :: rest))
      | .ok insp =>
        let code := if isEval then (strField req "code").getD "" else (strField req "file").getD ""
        -- do-eval (handler/eval.jank:22): `(if (empty? code) {:status [:no-code :done]} ...)`;
        -- `target-ns` is `(if ns (-> ns symbol find-ns) default-ns)`, nil →
        -- `{:status [:namespace-not-found :done]}` (lines 23–29).
        if code.isEmpty then
          pure (setConn c (.writeOut req (responsesFor req (kmap [("status", statusOf ["no-code", "done"])])) :: rest))
        else
        let target := match strField req "ns" with
          | some n => (findNs n).map (·.name)
          | none => some "user"
        match target with
        | none =>
          pure (setConn c (.writeOut req (responsesFor req (kmap [("status", statusOf ["namespace-not-found", "done"])])) :: rest))
        | some target =>
          let ev : EvalRegs := { req, target, inspect := insp, forms := program code }
          pure (.ran (.conn { c with ev, instrs := evalInstrs ++ rest }))
    | _ =>
      let (resp, m') := match opName with
        | some "clone" =>
          ((kmap [("new-session", JVal.s s!"uuid-{m.nextUuid}"), ("status", statusOf ["done"])]),
           { m with nextUuid := m.nextUuid + 1 })
        | some "close" => (kmap [("status", statusOf ["session-closed", "done"])], m)
        | some "describe" => (describeReply, m)
        | some "completions" | some "complete" => (completionsReply req, m)
        | some "lookup" | some "info" => (lookupReply (c.nsStack.headD "user") req, m)
        -- handler.jank:5–8: `{:status [:error :unknown-op :done] :op (get msg "op")}`.
        | _ => (kmap [("status", statusOf ["error", "unknown-op", "done"]), ("op", jget req (JVal.s "op"))], m)
      setMem m'
      pure (setConn c (.writeOut req (responsesFor req resp) :: rest))
  | .writeOut _ [] => pure (setConn c rest)
  | .writeOut req (r :: rs) =>
    match write r with
    | .error e =>
      note s!"conn {c.cid}: bencode/write throws \"{e}\""
      pure (setConn c (.handlerError req e :: rest))
    | .ok b =>
      let s := m.socks.getD c.cid {}
      -- server.cpp:46–55 `boost::asio::write`: every byte, or an error (the peer closed).
      if s.closed then
        note s!"conn {c.cid}: write fails (the peer closed): connected_ = false"
        pure (.ran (.conn { c with connected := false, instrs := .writeOut req rs :: rest }))
      else
        setMem { m with socks := m.socks.set! c.cid { s with outbox := s.outbox ++ b } }
        note s!"conn {c.cid}: write \"{showBytes b}\""
        pure (setConn c (.writeOut req rs :: rest))
  | .handlerError req msg =>
    -- core.jank:96–100: `(write-message client* (response-for req {:status [:error :done] :err
    -- (str "An exception was thrown from the nREPL handler:" (pr-str e))}))`; the rest of this
    -- request's work is abandoned, the loop reads the next message.
    let err := s!"An exception was thrown from the nREPL handler:#error \{:cause \"{msg}\" ...}"
    note s!"conn {c.cid}: handler exception \"{msg}\": answered with status [error done]"
    setMem { m with handlerErrors := m.handlerErrors ++ [(c.cid, msg)] }
    let loopRest := rest.dropWhile fun i => match i with | .readMsg => false | _ => true
    pure (setConn c (.writeOut req (responsesFor req (kmap [("status", statusOf ["error", "done"]), ("err", JVal.s err)])) :: loopRest))
  -- with-capture: start
  | .capDup fd =>
    match m.lowestFree with
    | some n => setMem (m.setFd n (m.fd fd)); pure (.ran (.conn { c with ev := { c.ev with bak := n }, instrs := rest }))
    | none =>
      note s!"conn {c.cid}: dup({fd}) → -1 (EMFILE)"
      pure (.ran (.conn { c with ev := { c.ev with bak := -1 }, instrs := rest }))
  | .capMkstemp fd =>
    match m.lowestFree with
    | some n =>
      let name := s!"/tmp/jank-nrepl-{m.nextTemp}"
      setMem { (m.setFd n (some (.temp name))) with temps := m.temps ++ [(name, [], true)], nextTemp := m.nextTemp + 1 }
      pure (.ran (.conn { c with ev := { c.ev with tempFd := n, tempName := name }, instrs := rest }))
    | none =>
      note s!"conn {c.cid}: mkstemp → -1 (EMFILE) while capturing fd {fd}: the assert throws"
      pure (setConn c (.handlerError c.ev.req "Assert failed: temp file could not be created" :: rest))
  | .capFlush fd => setMem (m.fflush fd); pure (setConn c rest)
  | .capDup2 fd =>
    let m' := if c.ev.tempFd ≥ 0 then m.setFd fd (m.fd c.ev.tempFd.toNat) else m
    setMem m'
    pure (setConn c rest)
  | .capClose fd =>
    let m' := if c.ev.tempFd ≥ 0 then m.setFd c.ev.tempFd.toNat none else m
    setMem m'
    let h : Handle := { fd, bak := c.ev.bak, temp := c.ev.tempName }
    let ev := if fd == 1 then { c.ev with outH := some h } else { c.ev with errH := some h }
    pure (.ran (.conn { c with ev, instrs := rest }))
  | .bind => pure (.ran (.conn { c with nsStack := c.ev.target :: c.nsStack, instrs := rest }))
  | .form =>
    if c.ev.putcNext then
      setMem (m.fwriteOut [10])
      pure (.ran (.conn { c with ev := { c.ev with putcNext := false }, instrs := .form :: rest }))
    else
      match c.ev.forms with
      | [] => pure (setConn c rest)
      | f :: fs =>
        let ev := { c.ev with forms := fs, ran := true }
        match f with
        | .lit v => pure (.ran (.conn { c with ev := { ev with last := v }, instrs := .form :: rest }))
        | .print s =>
          setMem (m.fwriteOut (bytes s))
          pure (.ran (.conn { c with ev := { ev with last := .nil }, instrs := .form :: rest }))
        | .println s =>
          setMem (m.fwriteOut (bytes s))
          pure (.ran (.conn { c with ev := { ev with last := .nil, putcNext := true }, instrs := .form :: rest }))
        | .throw msg =>
          pure (.ran (.conn { c with ev := { ev with thrown := some (.exInfo msg), forms := [] }, instrs := rest }))
  | .finishEval =>
    match c.ev.thrown with
    | some e =>
      pure (.ran (.conn { c with starE := e, ev := { c.ev with success := false }, instrs := rest }))
    | none =>
      if !c.ev.ran then
        if m.cfg.debugBuild then
          setMem { m with crashed := some "jank_debug_assert(set) in option::unwrap: abort()" }
          note s!"conn {c.cid}: eval_string returned none; unwrap() asserts: abort()"
          throw (.violation "the process stays up"
            s!"eval of code with no form: safe_eval's eval_string(...).unwrap() on none aborts the process (debug build)")
        note s!"conn {c.cid}: eval_string returned none; unwrap() reads the zeroed storage: 0.0"
      let value := if c.ev.ran then c.ev.last else .real0
      pure (.ran (.conn { c with star3 := c.star2, star2 := c.star1, star1 := value,
                                 ev := { c.ev with success := true }, instrs := rest }))
  | .unbind =>
    pure (.ran (.conn { c with ev := { c.ev with resNs := c.nsStack.headD "user" },
                               nsStack := c.nsStack.drop 1, instrs := rest }))
  | .endFlush fd => setMem (m.fflush fd); pure (setConn c rest)
  | .endDup2 fd =>
    let h := if fd == 1 then c.ev.outH else c.ev.errH
    let m' := match h with
      | some h => if h.bak ≥ 0 then m.setFd fd (m.fd h.bak.toNat) else m
      | none => m
    setMem m'; pure (setConn c rest)
  | .endClose fd =>
    let h := if fd == 1 then c.ev.outH else c.ev.errH
    let m' := match h with
      | some h => if h.bak ≥ 0 then m.setFd h.bak.toNat none else m
      | none => m
    setMem m'; pure (setConn c rest)
  | .slurp fd =>
    let h := if fd == 1 then c.ev.outH else c.ev.errH
    let content := match h with
      | some h => ((m.temps.find? fun (n, _, l) => n == h.temp && l).map fun (_, b, _) => b).getD []
      | none => []
    let ev := if fd == 1 then { c.ev with stdout := content } else { c.ev with stderr := content }
    pure (.ran (.conn { c with ev, instrs := rest }))
  | .unlink fd =>
    let h := if fd == 1 then c.ev.outH else c.ev.errH
    let m' := match h with
      | some h => { m with temps := m.temps.map fun (n, b, l) => if n == h.temp then (n, b, false) else (n, b, l) }
      | none => m
    setMem m'; pure (setConn c rest)
  | .evalReplies =>
    let ev := c.ev
    let outR := if blank (some ev.stdout) then JVal.nil else kmap [("out", .str ev.stdout)]
    let errR := if blank (some ev.stderr) then JVal.nil else kmap [("err", .str ev.stderr)]
    let resp : JVal :=
      if !ev.success then
        .vec [outR, errR, kmap [("err", JVal.s c.starE.text)],
              kmap [("ex", JVal.s c.starE.text), ("status", statusOf ["done", "eval-error"])]]
      else if ev.inspect == some true then
        kmap [("value", JVal.s (inspectStr c.star1)), ("status", statusOf ["done"])]
      else
        .vec [outR, errR, kmap [("value", JVal.s c.star1.pr), ("ns", JVal.s ev.resNs)],
              kmap [("status", statusOf ["done"])]]
    pure (setConn c (.writeOut ev.req (responsesFor ev.req resp) :: rest))

/-! ## The accept loop -/

def acceptStep (_t : Nat) : SM (StepResult Th) := do
  let m ← mem
  match m.pending with
  | cid :: more =>
    match m.lowestFree with
    | none =>
      setMem { m with acceptDied := some "accept: EMFILE (boost::system::system_error)" }
      note s!"accept loop: accept() fails with EMFILE: system_error leaves -main; the accept loop is over"
      pure .done
    | some fd =>
      setMem { (m.setFd fd (some (.sock cid))) with pending := more, accepted := m.accepted + 1 }
      modify fun p => { p with threads := p.threads.push (some (.conn { cid })) }
      note s!"accept loop: client {cid} on fd {fd}; a future runs handle-client"
      pure (.ran .acceptor)
  | [] => if m.accepted == m.nClients then pure .done else pure .blocked

/-! ## The clients -/

def reqId (cid k : Nat) : String := s!"c{cid}-{k}"

def sessionOf (c : ClientLoc) (n : Nat) : String := c.sessions.getD n "none"

/-- A request's map (string keys) and its session. -/
def reqMap (c : ClientLoc) (id : String) : Req → JVal × Option String
  | .clone => (.map [(JVal.s "op", JVal.s "clone"), (JVal.s "id", JVal.s id)], none)
  | .close s => (.map [(JVal.s "op", JVal.s "close"), (JVal.s "id", JVal.s id),
                       (JVal.s "session", JVal.s (sessionOf c s))], some (sessionOf c s))
  | .describe => (.map [(JVal.s "op", JVal.s "describe"), (JVal.s "id", JVal.s id)], none)
  | .eval s code ns inspect =>
    (.map ([(JVal.s "op", JVal.s "eval"), (JVal.s "id", JVal.s id), (JVal.s "session", JVal.s (sessionOf c s)),
            (JVal.s "code", JVal.s code)] ++ (match ns with | some n => [(JVal.s "ns", JVal.s n)] | none => [])
            ++ (match inspect with | some v => [(JVal.s "inspect", v)] | none => [])), some (sessionOf c s))
  | .loadFile s file =>
    (.map [(JVal.s "op", JVal.s "load-file"), (JVal.s "id", JVal.s id), (JVal.s "session", JVal.s (sessionOf c s)),
           (JVal.s "file", JVal.s file)], some (sessionOf c s))
  | .lookup ns sym =>
    (.map [(JVal.s "op", JVal.s "lookup"), (JVal.s "id", JVal.s id), (JVal.s "ns", JVal.s ns),
           (JVal.s "sym", JVal.s sym)], none)
  | .info ns sym =>
    (.map [(JVal.s "op", JVal.s "info"), (JVal.s "id", JVal.s id), (JVal.s "ns", JVal.s ns),
           (JVal.s "sym", JVal.s sym)], none)
  | .unknown op =>
    (.map ((match op with | some o => [(JVal.s "op", JVal.s o)] | none => []) ++ [(JVal.s "id", JVal.s id)]), none)
  | .completions ns pfx =>
    (.map [(JVal.s "op", JVal.s "completions"), (JVal.s "id", JVal.s id), (JVal.s "ns", JVal.s ns),
           (JVal.s "prefix", JVal.s pfx)], none)
  | .raw _ => (.nil, none)

def isDone (r : JVal) : Bool :=
  match jget r (JVal.s "status") with
  | .vec xs => xs.any (· == JVal.s "done")
  | _ => false

/-- The client reads what arrived and decodes every complete reply (the spec decoder). -/
def clientRead (c : ClientLoc) : SM ClientLoc := do
  let m ← mem
  let s := m.socks.getD c.cid {}
  let mut cursor := c.cursor
  let mut out := m.replies
  for _ in List.range 64 do
    let avail := s.outbox.drop cursor
    if avail.isEmpty then break
    match specDecode avail with
    | .msg v rest =>
      out := out.push (c.cid, v)
      cursor := cursor + (avail.length - rest.length)
    | .incomplete => break
    | .invalid =>
      throw (.violation "replies are well-formed bencode"
        s!"client {c.cid} cannot decode the bytes it received: \"{showBytes avail}\"")
  setMem { m with replies := out }
  pure { c with cursor }

def clientStep (_t : Nat) (c : ClientLoc) : SM (StepResult Th) := do
  let m ← mem
  match c.phase with
  | .connect =>
    if let some j := c.after then
      if !(m.socks.getD j {}).closed then return .blocked
    setMem { m with pending := m.pending ++ [c.cid] }
    note s!"client {c.cid}: connects"
    pure (.ran (.client { c with phase := .send }))
  | .send =>
    match c.script[c.k]? with
    | none => pure (.ran (.client { c with phase := .close }))
    | some (.raw b) =>
      let s := m.socks.getD c.cid {}
      setMem { m with socks := m.socks.set! c.cid { s with inbox := s.inbox ++ b } }
      note s!"client {c.cid}: sends raw \"{showBytes b}\""
      pure (.ran (.client { c with k := c.k + 1 }))
    | some r =>
      let id := reqId c.cid c.k
      let (msg, session) := reqMap c id r
      let b := (specEncode msg).getD []
      let s := m.socks.getD c.cid {}
      setMem { m with socks := m.socks.set! c.cid { s with inbox := s.inbox ++ b },
                      sent := m.sent.push { cid := c.cid, id, req := r, session } }
      note s!"client {c.cid}: sends {id} \"{showBytes b}\""
      pure (.ran (.client { c with phase := .wait id }))
  | .wait id =>
    let c' ← clientRead c
    let m ← mem
    let mine := m.replies.toList.filter fun (cid, r) => cid == c.cid && strField r "id" == some id
    match mine.find? (fun (_, r) => isDone r) with
    | some _ =>
      let sessions := match c.script[c.k]? with
        | some .clone =>
          match (mine.findSome? fun (_, r) => strField r "new-session") with
          | some s => c'.sessions.push s
          | none => c'.sessions
        | _ => c'.sessions
      note s!"client {c.cid}: {id} done"
      pure (.ran (.client { c' with sessions, k := c.k + 1, phase := .send }))
    | none =>
      if c'.cursor != c.cursor then pure (.ran (.client c')) else pure .blocked
  | .close =>
    let s := m.socks.getD c.cid {}
    setMem { m with socks := m.socks.set! c.cid { s with closed := true } }
    note s!"client {c.cid}: closes"
    pure .done

def step (t : Nat) : Th → SM (StepResult Th)
  | .acceptor => acceptStep t
  | .conn c => connStep t c
  | .client c => clientStep t c

def prog : Program Mem Th := { step }

/-- The world before the clients: fds 0–2 the terminal, 3 the listener, then `baseFds - 4` other
descriptors the runtime holds; the banner printed (core.jank:110). -/
def initial (cfg : Config) (scripts : List (List Req)) (sequential : Bool := false) : Process Mem Th :=
  let fds := (Array.range cfg.fdLimit).map fun i =>
    if i < 3 then some Desc.terminal else if i == 3 then some Desc.listener
    else if i < cfg.baseFds then some (Desc.held i) else none
  let m : Mem := { cfg, fds, socks := Array.replicate scripts.length {}, nClients := scripts.length,
                   terminal := bytes "nREPL server started on port 5555 on host 127.0.0.1 - nrepl://127.0.0.1:5555\n" }
  let clients := scripts.zipIdx.map fun (s, i) =>
    some (Th.client { cid := i, script := s.toArray, after := if sequential && i > 0 then some (i - 1) else none })
  { memory := m, threads := (#[some Th.acceptor] ++ clients.toArray) }

end Jank.NreplServer
