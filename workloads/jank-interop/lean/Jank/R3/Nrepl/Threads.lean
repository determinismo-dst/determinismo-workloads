import Jank.R3.Nrepl.World

/-!
# Round 3, nREPL: World T — connections interleaved on one jank process

Round 2's server world (`Jank.Nrepl.Server`: accept loop, a thread per connection, the fd table,
`FILE* stdout` with its buffer, `with-capture`'s `dup`/`mkstemp`/`dup2`/`close`/`slurp`/`unlink`,
scripted clients decoding replies with the spec decoder) with its abstract evaluator replaced by the
wired one: an eval's thread steps through `EvRun` (read a form, analyze it, evaluate it, each
`fwrite`/`putc` it made), `safe_eval`'s bookkeeping on the thread's own binding boxes, the binding
frame `do-eval` pushes, and `do-eval`'s replies (`pr-str` of `*1` after the capture). Namespaces,
vars, the heap and the analyzer's arena are the process's, shared by the threads (each step atomic).

Granularity (assumption NA4): a form's analysis and its evaluation are one step each; the output
events of an evaluation are applied one per step after it (so another thread can run between two
`fwrite`s of one form, but not between a form's evaluation and the global effects it had).

Properties: no deadlock, no process death; every request gets replies with its id and session,
ending in done; replies decode; each eval's `:out` is what that eval printed; each eval's values and
`eval-error` are those of the client's script run alone by the spec (the clients' code touches
disjoint names, so any interleaving gives each client its own results).
-/

namespace Jank.R3.Nrepl

open Jank.Analyzer Determinismo
open Jank.NreplServer (JVal kmap statusOf strField Desc Sock bytes showBytes specEncode specDecode)

structure TConfig where
  debug : Bool := false
  partialReads : Bool := true
  eintr : Bool := false
  fdLimit : Nat := 40
  baseFds : Nat := 4
  lineBuffered : Bool := true
  maxSteps : Nat := 6000
  /-- Set-aside of R125: `with-capture` (start … end, readback) runs under a process-wide lock. -/
  fixCapture : Bool := false
  /-- The `*ns*` the accept loop's thread conveys to each connection (assumption NA3). -/
  connNs : String := "user"
  deriving Repr, Inhabited

inductive TReq where
  | clone
  | close
  | describe
  | eval (code : String) (ns : Option String := some "user")
  | lookup (ns sym : String)
  | completions (ns pfx : String)
  | raw (b : List UInt8)
  deriving Repr, Inhabited

structure TSent where
  cid : Nat
  id : String
  req : TReq
  session : Option String
  deriving Inhabited

/-- What one eval did on its thread (for the properties). -/
structure EvalRec where
  cid : Nat
  id : String
  /-- The bytes its evaluation wrote to stdout. -/
  own : List UInt8
  deriving Inhabited

structure TMem where
  cfg : TConfig
  jw : JW
  fds : Array (Option Desc)
  temps : List (String × List UInt8 × Bool) := []
  nextTemp : Nat := 0
  terminal : List UInt8 := []
  outBuf : List UInt8 := []
  socks : Array Sock
  pending : List Nat := []
  nClients : Nat
  accepted : Nat := 0
  nextUuid : Nat := 0
  replies : Array (Nat × JVal) := #[]
  sent : Array TSent := #[]
  crashed : Option String := none
  acceptDied : Option String := none
  handlerErrors : List (Nat × String) := []
  connEnded : List Nat := []
  evals : Array EvalRec := #[]
  /-- `fixCapture`: the connection holding the capture lock. -/
  capLock : Option Nat := none
  /-- A thread that never returns (R1). -/
  hung : List (Nat × String) := []
  deriving Inhabited

def TMem.fd (m : TMem) (i : Nat) : Option Desc := m.fds.getD i none
def TMem.lowestFree (m : TMem) : Option Nat := (List.range m.cfg.fdLimit).find? fun i => (m.fd i).isNone
def TMem.setFd (m : TMem) (i : Nat) (d : Option Desc) : TMem :=
  if i < m.fds.size then { m with fds := m.fds.set! i d } else m
def TMem.writeFd (m : TMem) (fd : Nat) (b : List UInt8) : TMem :=
  match m.fd fd with
  | some .terminal => { m with terminal := m.terminal ++ b }
  | some (.temp n) =>
    { m with temps := m.temps.map fun (n', c, l) => if n' == n then (n', c ++ b, l) else (n', c, l) }
  | _ => m
/-- `fwrite`/`putc` on `stdout`: buffered; a terminal's line buffering writes at a newline. -/
def TMem.fwriteOut (m : TMem) (b : List UInt8) : TMem :=
  let buf := m.outBuf ++ b
  if m.cfg.lineBuffered && b.contains 10 then { m.writeFd 1 buf with outBuf := [] }
  else { m with outBuf := buf }
def TMem.fflush (m : TMem) (fd : Nat) : TMem :=
  if fd == 1 then { m.writeFd 1 m.outBuf with outBuf := [] } else m

structure Handle where
  fd : Nat
  bak : Int
  temp : String
  deriving Inhabited

structure TEval where
  req : JVal := .nil
  q : EvalReq := { code := "" }
  bak : Int := -1
  tempFd : Int := -1
  tempName : String := ""
  outH : Option Handle := none
  errH : Option Handle := none
  run : EvRun := default
  own : Array UInt8 := #[]
  ending : EvalEnd := .unsupported "not run"
  success : Bool := false
  resNs : String := "user"
  stdout : List UInt8 := []
  stderr : List UInt8 := []
  deriving Inhabited

inductive TCI where
  | top (req : Option JVal)
  | readMsg
  | dispatch (req : JVal)
  | writeOut (req : JVal) (resps : List JVal)
  | capLock
  | capDup (fd : Nat)
  | capMkstemp (fd : Nat)
  | capFlush (fd : Nat)
  | capDup2 (fd : Nat)
  | capClose (fd : Nat)
  | bind
  | form
  | finishEval
  | unbind
  | endFlush (fd : Nat)
  | endDup2 (fd : Nat)
  | endClose (fd : Nat)
  | slurp (fd : Nat)
  | unlink (fd : Nat)
  | capUnlock
  | evalReplies
  | handlerError (req : JVal) (msg : String)
  deriving Inhabited

structure TConn where
  cid : Nat
  connected : Bool := true
  remainder : Option (List UInt8) := none
  instrs : List TCI := [.top none]
  ev : TEval := {}
  tb : TB := {}
  deriving Inhabited

inductive TPhase where
  | connect
  | send
  | wait (id : String)
  | close
  deriving Repr, BEq, Inhabited

structure TClient where
  cid : Nat
  script : Array TReq
  k : Nat := 0
  phase : TPhase := .connect
  cursor : Nat := 0
  sessions : Array String := #[]
  deriving Inhabited

inductive TTh where
  | acceptor
  | conn (c : TConn)
  | client (c : TClient)
  deriving Inhabited

abbrev TM := ProcessM TMem TTh

def tmem : TM TMem := do pure (← get).memory
def tset (m : TMem) : TM Unit := modify fun p => { p with memory := m }
def tnote (s : String) : TM Unit := Process.note (M := TMem) (L := TTh) s

def tsetConn (c : TConn) (instrs : List TCI) : StepResult TTh := .ran (.conn { c with instrs })

def tReadLen (avail : Nat) : TM Nat := do
  let m ← tmem
  if !m.cfg.partialReads || avail ≤ 1 then return avail
  if (← decideWeighted (σ := Process TMem TTh) "net.read.split" [6, 1]) == 0 then return avail
  pure (1 + (← decide (σ := Process TMem TTh) "net.read.len" (avail - 1)))

def tEvalInstrs (fix : Bool) : List TCI :=
  (if fix then [.capLock] else []) ++
  [.capDup 1, .capMkstemp 1, .capFlush 1, .capDup2 1, .capClose 1,
   .capDup 2, .capMkstemp 2, .capFlush 2, .capDup2 2, .capClose 2,
   .bind, .form, .finishEval, .unbind,
   .endFlush 1, .endDup2 1, .endClose 1, .endFlush 2, .endDup2 2, .endClose 2,
   .slurp 1, .unlink 1, .slurp 2, .unlink 2] ++ (if fix then [.capUnlock] else []) ++ [.evalReplies]

/-- The process state an evaluation step sees: the shared state and this thread's bindings. -/
def esOf (m : TMem) (c : TConn) : ES := { w := m.jw, tb := c.tb }

def tDescribe : JVal :=
  kmap [("aux", .map []),
        ("ops", kmap (Jank.NreplServer.describedOps.map fun o => (o, .map []))),
        ("versions", kmap [("jank", kmap [("version-string", JVal.s "jank-version")])]),
        ("status", statusOf ["done"])]

def tConnStep (_t : Nat) (c : TConn) : TM (StepResult TTh) := do
  let m ← tmem
  match c.instrs with
  | [] => pure .done
  | i :: rest =>
  match i with
  | .top req =>
    if !c.connected then
      tnote s!"conn {c.cid}: not connected: handle-client returns (its socket stays open)"
      tset { m with connEnded := m.connEnded ++ [c.cid] }
      return .done
    match req with
    | some r => pure (tsetConn c (.dispatch r :: .readMsg :: rest))
    | none => pure (tsetConn c (.readMsg :: rest))
  | .readMsg =>
    let plat : Jank.NreplServer.Platform := {}
    match Jank.NreplServer.parse plat c.remainder with
    | .value v r => pure (.ran (.conn { c with remainder := r, instrs := .top (some v) :: rest }))
    | .crash =>
      tset { m with crashed := some s!"stack overflow in bencode parse-recur on connection {c.cid}" }
      throw (.violation "the process stays up" s!"bencode parse-recur overflowed the stack on connection {c.cid}")
    | .none =>
      let s := m.socks.getD c.cid {}
      let (chunk, connected) ← do
        if !s.inbox.isEmpty then
          let n ← tReadLen s.inbox.length
          tset { m with socks := m.socks.set! c.cid { s with inbox := s.inbox.drop n } }
          pure (some (s.inbox.take n), c.connected)
        else if s.closed then pure (some [], false)
        else if m.cfg.eintr && (← decideRare (σ := Process TMem TTh) "net.read.eintr" 1 8) then
          pure (some [], false)
        else pure (none, c.connected)
      match chunk with
      | none => pure .blocked
      | some ch =>
        let input := (c.remainder.getD []) ++ ch
        if ch.isEmpty then tnote s!"conn {c.cid}: read_some → \"\" ({if s.closed then "eof" else "EINTR"}): connected_ = false"
        else tnote s!"conn {c.cid}: read_some → {ch.length} bytes \"{showBytes ch}\""
        match Jank.NreplServer.parse plat (some input) with
        | .value v r => pure (.ran (.conn { c with connected, remainder := r, instrs := .top (some v) :: rest }))
        | .none => pure (.ran (.conn { c with connected, remainder := some input, instrs := .top none :: rest }))
        | .crash =>
          tset { (← tmem) with crashed := some s!"stack overflow in bencode parse-recur on connection {c.cid}" }
          throw (.violation "the process stays up" s!"bencode parse-recur overflowed the stack on connection {c.cid}")
  | .dispatch req =>
    let op := strField req "op"
    tnote s!"conn {c.cid}: handle-message {op.getD "nil"} (id {(strField req "id").getD "-"})"
    match op with
    | some "eval" | some "load-file" =>
      let isEval := op == some "eval"
      let code := if isEval then (strField req "code").getD "" else (strField req "file").getD ""
      let q : EvalReq := { ns := strField req "ns", code, file := (strField req (if isEval then "file" else "file-path")).getD "NO_SOURCE_PATH",
                           inspect := if isEval then none else some false }
      match doEvalPre m.jw q with
      | .reply r => pure (tsetConn c (.writeOut req (Jank.NreplServer.responsesFor req r) :: rest))
      | .run target =>
        let ev : TEval := { req, q := { q with ns := some target } }
        pure (.ran (.conn { c with ev, instrs := tEvalInstrs m.cfg.fixCapture ++ rest }))
    | _ =>
      let (resp, m') := match op with
        | some "clone" =>
          ((kmap [("new-session", JVal.s s!"uuid-{m.nextUuid}"), ("status", statusOf ["done"])]), { m with nextUuid := m.nextUuid + 1 })
        | some "close" => (kmap [("status", statusOf ["session-closed", "done"])], m)
        | some "describe" => (tDescribe, m)
        | some "completions" | some "complete" => (completionsReply m.jw req, m)
        | some "lookup" | some "info" => (lookupReply m.jw (curNsName (esOf m c)) req, m)
        | _ => (kmap [("status", statusOf ["error", "unknown-op", "done"]), ("op", Jank.NreplServer.jget req (JVal.s "op"))], m)
      tset m'
      pure (tsetConn c (.writeOut req (Jank.NreplServer.responsesFor req resp) :: rest))
  | .writeOut _ [] => pure (tsetConn c rest)
  | .writeOut req (r :: rs) =>
    match Jank.NreplServer.write r with
    | .error e =>
      tnote s!"conn {c.cid}: bencode/write throws \"{e}\""
      pure (tsetConn c (.handlerError req e :: rest))
    | .ok b =>
      let s := m.socks.getD c.cid {}
      if s.closed then
        tnote s!"conn {c.cid}: write fails (the peer closed): connected_ = false"
        pure (.ran (.conn { c with connected := false, instrs := .writeOut req rs :: rest }))
      else
        tset { m with socks := m.socks.set! c.cid { s with outbox := s.outbox ++ b } }
        tnote s!"conn {c.cid}: write \"{showBytes b}\""
        pure (tsetConn c (.writeOut req rs :: rest))
  | .handlerError req msg =>
    let err := s!"An exception was thrown from the nREPL handler:{msg}"
    tnote s!"conn {c.cid}: handler exception \"{msg}\": answered with status [error done]"
    tset { m with handlerErrors := m.handlerErrors ++ [(c.cid, msg)] }
    let loopRest := rest.dropWhile fun i => match i with | .readMsg => false | _ => true
    pure (tsetConn c (.writeOut req (Jank.NreplServer.responsesFor req (kmap [("status", statusOf ["error", "done"]), ("err", JVal.s err)])) :: loopRest))
  | .capLock =>
    match m.capLock with
    | some _ => pure .blocked
    | none => tset { m with capLock := some c.cid }; pure (tsetConn c rest)
  | .capUnlock => tset { m with capLock := none }; pure (tsetConn c rest)
  | .capDup fd =>
    match m.lowestFree with
    | some n => tset (m.setFd n (m.fd fd)); pure (.ran (.conn { c with ev := { c.ev with bak := n }, instrs := rest }))
    | none =>
      tnote s!"conn {c.cid}: dup({fd}) → -1 (EMFILE)"
      pure (.ran (.conn { c with ev := { c.ev with bak := -1 }, instrs := rest }))
  | .capMkstemp fd =>
    match m.lowestFree with
    | some n =>
      let name := s!"/tmp/jank-nrepl-{m.nextTemp}"
      tset { (m.setFd n (some (.temp name))) with temps := m.temps ++ [(name, [], true)], nextTemp := m.nextTemp + 1 }
      pure (.ran (.conn { c with ev := { c.ev with tempFd := n, tempName := name }, instrs := rest }))
    | none =>
      tnote s!"conn {c.cid}: mkstemp → -1 (EMFILE) while capturing fd {fd}: the assert throws"
      pure (tsetConn c (.handlerError c.ev.req "Assert failed: temp file could not be created" :: rest))
  | .capFlush fd => tset (m.fflush fd); pure (tsetConn c rest)
  | .capDup2 fd =>
    tset (if c.ev.tempFd ≥ 0 then m.setFd fd (m.fd c.ev.tempFd.toNat) else m)
    pure (tsetConn c rest)
  | .capClose fd =>
    tset (if c.ev.tempFd ≥ 0 then m.setFd c.ev.tempFd.toNat none else m)
    let h : Handle := { fd, bak := c.ev.bak, temp := c.ev.tempName }
    let ev := if fd == 1 then { c.ev with outH := some h } else { c.ev with errH := some h }
    pure (.ran (.conn { c with ev, instrs := rest }))
  | .bind =>
    -- `(binding [*ns* target-ns *file* file-path] ...)`
    let target := c.ev.q.ns.getD "user"
    let (h, nso) := m.jw.heap.nsObj target
    tset { m with jw := { m.jw with heap := h } }
    let tb := c.tb.push [(vNs, nso), (vFile, str c.ev.q.file)]
    pure (.ran (.conn { c with tb, ev := { c.ev with run := EvRun.start c.ev.q.code.toUTF8.toList }, instrs := rest }))
  | .form =>
    if c.ev.run.isDone then return tsetConn c rest
    let (r', s', evt) := c.ev.run.step (esOf m c) c.ev.q.file
    -- R1: a reader that never returns: the thread blocks for good.
    match r'.phase with
    | .done (.error (.unsupported w)) =>
      if w.startsWith "HANG" then
        let m0 ← tmem
        if !(m0.hung.any (·.1 == c.cid)) then
          tnote s!"conn {c.cid}: the reader never returns ({w}); fd 1 and 2 stay on this eval's temp files"
          tset { m0 with hung := m0.hung ++ [(c.cid, w)] }
        return .blocked
      if w.startsWith "CRASH" then
        tset { (← tmem) with crashed := some w }
        throw (.violation "the process stays up" s!"conn {c.cid}: {w}")
      pure ()
    | _ => pure ()
    let m := { m with jw := s'.w }
    let (m, own) := match evt with
      | some (.out b) => (m.fwriteOut b, c.ev.own ++ b.toArray)
      | some (.err b) => (m.writeFd 2 b, c.ev.own)
      | none => (m, c.ev.own)
    tset m
    match r'.phase with
    | .analyze f => tnote s!"conn {c.cid}: read {prObj .jank m.jw.heap f}"
    | _ => pure ()
    if let some (.out b) := evt then tnote s!"conn {c.cid}: fwrite \"{showBytes b}\" to stdout (fd 1 is {reprStr (m.fd 1)})"
    pure (.ran (.conn { c with tb := s'.tb, ev := { c.ev with run := r', own }, instrs := .form :: rest }))
  | .finishEval =>
    match c.ev.run.phase with
    | .done res =>
      let (s', e) := finishSafeEval (esOf m c) res m.cfg.debug
      tset { m with jw := s'.w }
      match e with
      | .crash w =>
        tset { (← tmem) with crashed := some w }
        throw (.violation "the process stays up" s!"conn {c.cid}: {w}")
      | .unsupported w =>
        throw .limit
      | _ =>
        let success := match e with | .ok _ => true | _ => false
        pure (.ran (.conn { c with tb := s'.tb, ev := { c.ev with ending := e, success }, instrs := rest }))
    | _ => pure (tsetConn c rest)
  | .unbind =>
    let resNs := curNsName (esOf m c)
    pure (.ran (.conn { c with tb := c.tb.pop, ev := { c.ev with resNs }, instrs := rest }))
  | .endFlush fd => tset (m.fflush fd); pure (tsetConn c rest)
  | .endDup2 fd =>
    let h := if fd == 1 then c.ev.outH else c.ev.errH
    tset (match h with
      | some h => if h.bak ≥ 0 then m.setFd fd (m.fd h.bak.toNat) else m
      | none => m)
    pure (tsetConn c rest)
  | .endClose fd =>
    let h := if fd == 1 then c.ev.outH else c.ev.errH
    tset (match h with
      | some h => if h.bak ≥ 0 then m.setFd h.bak.toNat none else m
      | none => m)
    pure (tsetConn c rest)
  | .slurp fd =>
    let h := if fd == 1 then c.ev.outH else c.ev.errH
    let content := match h with
      | some h => ((m.temps.find? fun (n, _, l) => n == h.temp && l).map fun (_, b, _) => b).getD []
      | none => []
    let ev := if fd == 1 then { c.ev with stdout := content } else { c.ev with stderr := content }
    pure (.ran (.conn { c with ev, instrs := rest }))
  | .unlink fd =>
    let h := if fd == 1 then c.ev.outH else c.ev.errH
    tset (match h with
      | some h => { m with temps := m.temps.map fun (n, b, l) => if n == h.temp then (n, b, false) else (n, b, l) }
      | none => m)
    pure (tsetConn c rest)
  | .evalReplies =>
    let ev := c.ev
    tset { m with evals := m.evals.push { cid := c.cid, id := (strField ev.req "id").getD "", own := ev.own.toList } }
    let (s', r, printed) := doEvalRepliesOut (esOf (← tmem) c) ev.success ev.resNs ev.stdout ev.stderr ev.q.inspect
    -- what realizing `*1` printed goes to the process's stdout, wherever fd 1 points now
    let m1 := printed.foldl (fun m e => match e with
      | .out b => m.fwriteOut b
      | .err b => m.writeFd 2 b) { (← tmem) with jw := s'.w }
    if !printed.isEmpty then
      tnote s!"conn {c.cid}: (pr-str *1) prints \"{showBytes (outBytes printed)}\" after the capture (fd 1 is {reprStr (m1.fd 1)})"
    tset m1
    match r with
    | .ok resp => pure (.ran (.conn { c with tb := s'.tb, instrs := .writeOut ev.req (Jank.NreplServer.responsesFor ev.req resp) :: rest }))
    | .error msg => pure (.ran (.conn { c with tb := s'.tb, instrs := .handlerError ev.req msg :: rest }))

def tAcceptStep (_t : Nat) : TM (StepResult TTh) := do
  let m ← tmem
  match m.pending with
  | cid :: more =>
    match m.lowestFree with
    | none =>
      tset { m with acceptDied := some "accept: EMFILE (boost::system::system_error)" }
      tnote "accept loop: accept() fails with EMFILE: the accept loop is over"
      pure .done
    | some fd =>
      let (h, tb) := connTB m.jw.heap m.cfg.connNs
      tset { (m.setFd fd (some (.sock cid))) with pending := more, accepted := m.accepted + 1, jw := { m.jw with heap := h } }
      modify fun p => { p with threads := p.threads.push (some (.conn { cid, tb })) }
      tnote s!"accept loop: client {cid} on fd {fd}; a future runs handle-client"
      pure (.ran .acceptor)
  | [] => if m.accepted == m.nClients then pure .done else pure .blocked

def tReqId (cid k : Nat) : String := s!"c{cid}-{k}"

def tReqMap (c : TClient) (id : String) : TReq → JVal × Option String
  | .clone => (.map [(JVal.s "op", JVal.s "clone"), (JVal.s "id", JVal.s id)], none)
  | .close => (.map [(JVal.s "op", JVal.s "close"), (JVal.s "id", JVal.s id), (JVal.s "session", JVal.s (c.sessions.getD 0 "none"))], some (c.sessions.getD 0 "none"))
  | .describe => (.map [(JVal.s "op", JVal.s "describe"), (JVal.s "id", JVal.s id)], none)
  | .eval code ns =>
    let sess := c.sessions.getD 0 "none"
    (.map ([(JVal.s "op", JVal.s "eval"), (JVal.s "id", JVal.s id), (JVal.s "session", JVal.s sess), (JVal.s "code", JVal.s code)]
      ++ (match ns with | some n => [(JVal.s "ns", JVal.s n)] | none => [])), some sess)
  | .lookup ns sym => (.map [(JVal.s "op", JVal.s "lookup"), (JVal.s "id", JVal.s id), (JVal.s "ns", JVal.s ns), (JVal.s "sym", JVal.s sym)], none)
  | .completions ns pfx => (.map [(JVal.s "op", JVal.s "completions"), (JVal.s "id", JVal.s id), (JVal.s "ns", JVal.s ns), (JVal.s "prefix", JVal.s pfx)], none)
  | .raw _ => (.nil, none)

def tIsDone (r : JVal) : Bool := hasStatus r "done"

def tClientRead (c : TClient) : TM TClient := do
  let m ← tmem
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
      throw (.violation "replies are well-formed bencode" s!"client {c.cid} cannot decode \"{showBytes avail}\"")
  tset { m with replies := out }
  pure { c with cursor }

def tClientStep (_t : Nat) (c : TClient) : TM (StepResult TTh) := do
  let m ← tmem
  match c.phase with
  | .connect =>
    tset { m with pending := m.pending ++ [c.cid] }
    tnote s!"client {c.cid}: connects"
    pure (.ran (.client { c with phase := .send }))
  | .send =>
    match c.script[c.k]? with
    | none => pure (.ran (.client { c with phase := .close }))
    | some (.raw b) =>
      let s := m.socks.getD c.cid {}
      tset { m with socks := m.socks.set! c.cid { s with inbox := s.inbox ++ b } }
      tnote s!"client {c.cid}: sends raw \"{showBytes b}\""
      pure (.ran (.client { c with k := c.k + 1 }))
    | some r =>
      let id := tReqId c.cid c.k
      let (msg, session) := tReqMap c id r
      let b := (specEncode msg).getD []
      let s := m.socks.getD c.cid {}
      tset { m with socks := m.socks.set! c.cid { s with inbox := s.inbox ++ b }, sent := m.sent.push { cid := c.cid, id, req := r, session } }
      tnote s!"client {c.cid}: sends {id} \"{showBytes b}\""
      pure (.ran (.client { c with phase := .wait id }))
  | .wait id =>
    let c' ← tClientRead c
    let m ← tmem
    let mine := m.replies.toList.filter fun (cid, r) => cid == c.cid && strField r "id" == some id
    match mine.find? (fun (_, r) => tIsDone r) with
    | some _ =>
      let sessions := match c.script[c.k]? with
        | some .clone =>
          match mine.findSome? fun (_, r) => strField r "new-session" with
          | some s => c'.sessions.push s
          | none => c'.sessions
        | _ => c'.sessions
      tnote s!"client {c.cid}: {id} done"
      pure (.ran (.client { c' with sessions, k := c.k + 1, phase := .send }))
    | none => if c'.cursor != c.cursor then pure (.ran (.client c')) else pure .blocked
  | .close =>
    let s := m.socks.getD c.cid {}
    tset { m with socks := m.socks.set! c.cid { s with closed := true } }
    tnote s!"client {c.cid}: closes"
    pure .done

def tStep (t : Nat) : TTh → TM (StepResult TTh)
  | .acceptor => tAcceptStep t
  | .conn c => tConnStep t c
  | .client c => tClientStep t c

def tProg : Program TMem TTh := { step := tStep }

def tInitial (cfg : TConfig) (scripts : List (List TReq)) : Process TMem TTh :=
  let fds := (Array.range cfg.fdLimit).map fun i =>
    if i < 3 then some Desc.terminal else if i == 3 then some Desc.listener
    else if i < cfg.baseFds then some (Desc.held i) else none
  let m : TMem := { cfg, jw := jankBase, fds, socks := Array.replicate scripts.length {}, nClients := scripts.length }
  let clients := scripts.zipIdx.map fun (s, i) => some (TTh.client { cid := i, script := s.toArray })
  { memory := m, threads := (#[some TTh.acceptor] ++ clients.toArray) }

/-! ## The judge -/

def tRepliesOf (m : TMem) (s : TSent) : List JVal :=
  (m.replies.toList.filter fun (cid, r) => cid == s.cid && strField r "id" == some s.id).map (·.2)

/-- Each client's script run alone by the spec (load-string mode with the given variants):
the expected items of each eval, by request id. -/
def tSpecOf (variant : Variant) (cid : Nat) (script : List TReq) : List (String × SpecEvalOut) := Id.run do
  let mut sw : SW := cljBase
  let mut sess : Session := {}
  let mut out := []
  let mut k := 0
  for r in script do
    let id := tReqId cid k
    k := k + 1
    match r with
    | .eval code ns =>
      if code.isEmpty then continue
      let (sw', sess', o) := specEval sw sess code (some (ns.getD "user")) .loadString variant
      sw := sw'
      sess := sess'
      out := out ++ [(id, o)]
    | _ => pure ()
  return out

def tJudge (aside : Aside) (scripts : List (List TReq)) (m : TMem) : Option (String × String) := Id.run do
  if let some c := m.crashed then return some ("the process stays up", c)
  let specs := scripts.zipIdx.flatMap fun (sc, cid) => tSpecOf aside.variant cid sc
  for s in m.sent do
    let rs := tRepliesOf m s
    if let some sess := s.session then
      for r in rs do
        if strField r "session" != some sess then
          return some ("every reply carries the request's id and session", s!"{s.id}: {JVal.render r} lacks session {sess}")
    match rs.findIdx? tIsDone with
    | none => return some ("a request's replies end with done", s!"{s.id}: no done among {rs.length} replies")
    | some i => if i + 1 != rs.length then return some ("a request's replies end with done", s!"{s.id}: replies after done")
    match s.req with
    | .eval code _ =>
      let out := rs.flatMap fun r => match Jank.NreplServer.jget r (JVal.s "out") with
        | .str b => b
        | _ => []
      match m.evals.toList.find? fun e => e.cid == s.cid && e.id == s.id with
      | some e =>
        let own := if aside.blankOut && e.own.all Jank.NreplServer.cIsspace then [] else e.own
        let got := if aside.blankOut && out.all Jank.NreplServer.cIsspace then [] else out
        if got != own then
          return some ("eval output reaches its client", s!"{s.id} eval {repr code}: :out \"{showBytes out}\", the eval printed \"{showBytes e.own}\"")
      | none => pure ()
      match specs.lookup s.id with
      | some sp =>
        let q : SReq := .eval code (some "user")
        let ans : JankAns := { replies := rs, handlerError := (m.handlerErrors.find? (·.1 == s.cid)).map (·.2) }
        -- output is judged above against the eval's own bytes
        match judgeEval .loadString { aside with blankOut := true } q { ans with handlerError := none } { sp with out := (rs.flatMap fun r => match Jank.NreplServer.jget r (JVal.s "out") with | .str b => b | _ => []) } with
        | some (p, d) => return some (p, s!"{s.id}: {d}")
        | none => pure ()
      | none => pure ()
    | _ => pure ()
  return none

def tStuck (p : Process TMem TTh) : Option String :=
  let m := p.memory
  let waits := p.threads.toList.filterMap fun t => match t with
    | some (.client c) => match c.phase with
      | .wait id => some s!"client {c.cid} waits for the done of {id}"
      | _ => none
    | _ => none
  let hung := m.hung.map fun (c, w) => s!"conn {c} never returns from the reader ({w})"
  let fd1 := match m.fd 1 with
    | some .terminal => []
    | d => [s!"fd 1 (stdout) is left on {reprStr d}"]
  let ended := m.connEnded.filterMap fun c =>
    if (m.socks.getD c {}).closed then none else some s!"conn {c}'s loop ended while its client is connected"
  some ("; ".intercalate (waits ++ hung ++ ended ++ fd1))

def runT (cfg : TConfig) (aside : Aside) (scripts : List (List TReq)) (source : Source) : Ended × Process TMem TTh :=
  let body : TM Unit := do
    interleave tProg cfg.maxSteps tStuck
    let p ← get
    let live := p.threads.toList.any Option.isSome
    if !live then
      if let some (prop, d) := tJudge aside scripts p.memory then throw (.violation prop d)
      -- after every connection: stdout is the terminal again
      match p.memory.fd 1 with
      | some .terminal => pure ()
      | d => throw (.violation "stdout is restored after every eval" s!"fd 1 is left on {reprStr d}")
    else
      throw (.violation "the timeline ends within the step bound (model bound)" s!"{(p.threads.toList.filter Option.isSome).length} threads live after {cfg.maxSteps} rounds")
  match runProcess (tInitial cfg scripts) body source 100000 with
  | (.ok _, p) => ({ taken := p.decisions.taken, violation := none }, p)
  | (.error (.violation "deadlock" d), p) => ({ taken := p.decisions.taken, violation := some ("every request gets a done reply (no hang)", d) }, p)
  | (.error (.violation prop d), p) => ({ taken := p.decisions.taken, violation := some (prop, d) }, p)
  | (.error .limit, p) => ({ taken := p.decisions.taken, violation := none }, p)
  | (.error (.nodeDown _), p) => ({ taken := p.decisions.taken, violation := none }, p)

end Jank.R3.Nrepl
