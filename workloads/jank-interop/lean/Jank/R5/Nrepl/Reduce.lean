import Jank.R3.Nrepl.ThreadSearch
import Jank.R4.Nrepl.Seg
import Jank.R5.Nrepl.Chunk

/-!
# Round 5, nREPL: T7 reduced to whole-message reads (part 2)

Round 3's T7 (`tScenarios` 7th: one client, partial reads, clone/eval/lookup/completions/
describe/close) has ≈3.2·10¹¹ timelines at ≤1 preemption (round 4's Knuth estimate). Almost all of
its branching is the chunking: each `read_some` of a request draws `net.read.split` and
`net.read.len`, and every extra read is one more place a preemption can go.

The reduction (stuttering bisimulation). Let α map a World T state to the same state with each
connection's unread bytes `remainder ++ inbox` put back in its socket's inbox (remainder `none`),
and a connection's `.top none` (just after an incomplete read) shown as `.readMsg`.
1. A partial read that leaves the request incomplete, and the `.top none` step after it, change only
   that connection's `remainder`/`instrs` and its socket's `inbox`, and keep α: they are stutter
   steps. (Threads.lean `tConnStep` `.readMsg` and `.top` arms; checked below at every reachable
   pre-read state of the reduced world, every split point and every chunk length: `stutterCheck`.)
2. The read that completes the request parses `remainder ++ rest`, which is the whole request
   (`Chunk.lean`: every proper prefix of T7's requests parses to nil, ★ `t7_chunking_independent`),
   so it leaves the state a whole read leaves (checked by `stutterCheck` too).
3. No other step reads a connection's `remainder` or its socket's `inbox`: the client appends to the
   inbox only in `.send`, which it reaches only after the previous request's `done`, so after that
   request was read whole (`tClientStep`); the acceptor touches neither (`tAcceptStep`). So stutter
   steps commute with every other thread's steps, and every other step's effect depends only on α of
   the state (code reading of Threads.lean 212–600).
4. The judge (`tJudge`) and the deadlock detail (`tStuck`) read replies, sent requests, evals,
   handler errors, crashes, fd 1, hung threads, ended connections and closed sockets: all α-invariant.
5. Schedules. Deleting a chunked timeline's stutter steps (and the client's blocked steps that
   follow them, which change nothing: `tClientRead` finds no new reply, so the step is `.blocked`)
   gives a schedule of the whole-read world. Its preemptions are no more: a switch that survives the
   deletion is a preemption in both worlds iff the thread switched from was ready, and readiness is a
   function of α (a stutter step's `blocked := []` only re-enables a client whose next step is a
   no-op, which is deleted).

So the final α-states (hence every verdict) of T7 at ≤ b preemptions are those of the whole-read world
at ≤ b, and a complete walk of the whole-read world decides T7. Items 1–2 are proved (`Chunk.lean`)
and checked by execution of the replica's own step function at every reachable state; items 3–5 are
the argument above, from the code, not mechanized.

Beyond the bound: `wholeCensus` also collects every timeline's final state fingerprint (`fpMem`). One
fingerprint for every budget run says the one-client world is confluent there: every schedule gives
the same final state.
-/

namespace Jank.R5.Nrepl

open Determinismo Jank.R3.Nrepl Jank.NreplServer Jank.Analyzer

/-- T7 as round 3 ran it. -/
def t7 : TScenario := tScenarios.getD 6 default

/-- T7 with whole-message reads: the reduced world. -/
def t7Whole : TScenario := { t7 with cfg := { t7.cfg with partialReads := false } }

/-! ## Fingerprints -/

def tciTag : TCI → String
  | .top none => "top"
  | .top (some v) => s!"top {v.render}"
  | .readMsg => "readMsg"
  | .dispatch r => s!"dispatch {r.render}"
  | .writeOut r rs => s!"writeOut {r.render} {rs.map JVal.render}"
  | .capLock => "capLock"
  | .capDup fd => s!"capDup {fd}"
  | .capMkstemp fd => s!"capMkstemp {fd}"
  | .capFlush fd => s!"capFlush {fd}"
  | .capDup2 fd => s!"capDup2 {fd}"
  | .capClose fd => s!"capClose {fd}"
  | .bind => "bind"
  | .form => "form"
  | .finishEval => "finishEval"
  | .unbind => "unbind"
  | .endFlush fd => s!"endFlush {fd}"
  | .endDup2 fd => s!"endDup2 {fd}"
  | .endClose fd => s!"endClose {fd}"
  | .slurp fd => s!"slurp {fd}"
  | .unlink fd => s!"unlink {fd}"
  | .capUnlock => "capUnlock"
  | .evalReplies => "evalReplies"
  | .handlerError r msg => s!"handlerError {r.render} {msg}"

def fpEv (e : TEval) : String :=
  s!"{e.req.render}|{e.q.code}|{e.q.ns}|{e.bak}|{e.tempFd}|{e.tempName}|{showBytes e.own.toList}|{e.success}|{e.resNs}|{showBytes e.stdout}|{showBytes e.stderr}|{e.outH.map (·.fd)}|{e.errH.map (·.fd)}"

def fpConn (c : TConn) : String :=
  s!"conn {c.cid} {c.connected} {c.remainder.map showBytes} {c.instrs.map tciTag} ev:{fpEv c.ev} tb:{c.tb.boxes.size},{c.tb.frames.map List.length}"

def fpJw (w : JW) : String :=
  s!"nss {w.nss.map fun n => (n.name, n.mappings.length, n.aliases.length)} exs {w.heap.exs.size} nsObjs {w.heap.nsObjs} atoms {w.heap.atoms.size} lazies {w.heap.lazies.size} closures {w.closures.size} gensym {w.gensym} exprs {w.arena.exprs.size}"

/-- Everything of the shared memory the judge, the deadlock detail and later steps can read. -/
def fpMem (m : TMem) : String :=
  let socks := m.socks.toList.map fun s => (showBytes s.inbox, showBytes s.outbox, s.closed)
  let temps := m.temps.map fun (n, b, l) => (n, showBytes b, l)
  let replies := m.replies.toList.map fun (c, r) => (c, r.render)
  let evals := m.evals.toList.map fun e => (e.cid, e.id, showBytes e.own)
  s!"fds {m.fds.toList.map reprStr} temps {temps} nextTemp {m.nextTemp} terminal {showBytes m.terminal} outBuf {showBytes m.outBuf} socks {socks} pending {m.pending} accepted {m.accepted} uuid {m.nextUuid} replies {replies} sent {m.sent.toList.map fun s => (s.cid, s.id)} crashed {m.crashed} acceptDied {m.acceptDied} handlerErrors {m.handlerErrors} connEnded {m.connEnded} evals {evals} capLock {m.capLock} hung {m.hung} jw {fpJw m.jw}"

/-- The same with a connection's unread bytes put back in its socket (α). -/
def alphaMem (m : TMem) (cid : Nat) (rem : Option Bytes) : TMem :=
  match rem with
  | none => m
  | some r =>
    let s := m.socks.getD cid {}
    { m with socks := m.socks.set! cid { s with inbox := r ++ s.inbox } }

/-! ## Step 1–2 checks: every chunked read from a reachable pre-read state -/

/-- One step of thread `t` (a connection) from process `p`, its decisions taken from `path`. -/
def connStepFrom (t : Nat) (c : TConn) (p : Process TMem TTh) (path : Array Nat) :
    Except String (StepResult TTh × Process TMem TTh) :=
  let p' := { p with decisions := { source := Source.path path, limit := 100000 } }
  match (tConnStep t c).run p' with
  | .ok r q => .ok (r, q)
  | .error _ _ => .error "the step stopped (violation or limit)"

def fpResult : StepResult TTh → String
  | .ran (.conn c) => s!"ran {fpConn c}"
  | .ran _ => "ran other"
  | .blocked => "blocked"
  | .done => "done"

/-- Is `c` (thread `t`) about to read a chunk: `.readMsg` next, its buffer incomplete, bytes in its
socket's inbox? -/
def preRead (p : Process TMem TTh) (c : TConn) : Bool :=
  match c.instrs with
  | .readMsg :: _ =>
    c.connected && (parse {} c.remainder == .none) && !((p.memory.socks.getD c.cid {}).inbox.isEmpty)
  | _ => false

/-- Checks items 1 and 2 at one state: for every way the chunked world can have split the bytes so
far (`j` bytes already in the buffer) and every next chunk length `n`, the incomplete read and the
`.top none` after it are stutter steps, and the completing read gives the whole read's result.
Returns the number of step runs, or the first failure. -/
def stutterCheck (t : Nat) (c : TConn) (p : Process TMem TTh) : Except String Nat := do
  let m := p.memory
  let s := m.socks.getD c.cid {}
  let full := c.remainder.getD [] ++ s.inbox
  let len := full.length
  let mWhole := { m with cfg := { m.cfg with partialReads := false } }
  let (r0, q0) ← connStepFrom t c { p with memory := mWhole } #[]
  let ref := (fpResult r0, fpMem { q0.memory with cfg := { q0.memory.cfg with partialReads := true } })
  let mut runs := 1
  for j in [0:len] do
    let rem : Option Bytes := if j == 0 then c.remainder else some (full.take j)
    let mj := { m with cfg := { m.cfg with partialReads := true },
                       socks := m.socks.set! c.cid { s with inbox := full.drop j } }
    let cj := { c with remainder := rem }
    let pj := { p with memory := mj }
    -- the completing read (split 0: the whole inbox)
    let path := if len - j ≤ 1 then #[] else #[0]
    let (r1, q1) ← connStepFrom t cj pj path
    runs := runs + 1
    if (fpResult r1, fpMem q1.memory) != ref then
      throw s!"completing read after {j} buffered bytes differs from a whole read"
    -- every incomplete read of n bytes
    for n in [1:len - j] do
      let (r2, q2) ← connStepFrom t cj pj #[1, n - 1]
      runs := runs + 1
      let expectMem := { mj with socks := mj.socks.set! c.cid { s with inbox := full.drop (j + n) } }
      match r2 with
      | .ran (.conn c2) =>
        let expectConn := { cj with remainder := some (full.take (j + n)), instrs := .top none :: c.instrs.drop 1 }
        if fpConn c2 != fpConn expectConn then
          throw s!"incomplete read of {n} after {j}: connection {fpConn c2}"
        if fpMem q2.memory != fpMem expectMem then
          throw s!"incomplete read of {n} after {j}: memory changed beyond the inbox"
        -- `.top none`: back to `.readMsg`, nothing else
        let (r3, q3) ← connStepFrom t c2 q2 #[]
        runs := runs + 1
        match r3 with
        | .ran (.conn c3) =>
          if fpConn c3 != fpConn { c2 with instrs := c.instrs } then
            throw s!"`.top none` after {j}+{n}: connection {fpConn c3}"
          if fpMem q3.memory != fpMem q2.memory then
            throw s!"`.top none` after {j}+{n}: memory changed"
        | _ => throw s!"`.top none` after {j}+{n}: {fpResult r3}"
      | _ => throw s!"incomplete read of {n} after {j}: {fpResult r2}"
  return runs

/-! ## Scheduling with observation -/

/-- `interleavePB` (round 3, ThreadSearch.lean) with an observer called on the process before every
step: the snapshots it returns are collected. -/
def interleavePBObs {M L α : Type} (prog : Program M L) (maxSteps budget : Nat)
    (stuck : Process M L → Option String) (obs : Process M L → List α) :
    StateT (Array α) (ProcessM M L) Unit := do
  let mut blocked : List Nat := []
  let mut cur : Option Nat := none
  let mut left := budget
  for _ in List.range maxSteps do
    let p ← (get : ProcessM M L (Process M L))
    let live := (List.range p.threads.size).filter fun i => (p.threads.getD i none).isSome
    if live.isEmpty then return
    let ready := live.filter (!blocked.contains ·)
    if ready.isEmpty then
      if let some detail := stuck p then
        throw (.violation "deadlock" detail)
      return
    let t ← match cur with
      | some c =>
        if ready.contains c then
          let others := ready.filter (· != c)
          if left > 0 && !others.isEmpty then do
            let k ← (decide (σ := Process M L) "thread.preempt" (others.length + 1) : ProcessM M L Nat)
            if k == 0 then pure c else do
              left := left - 1
              pure (others.getD (k - 1) c)
          else pure c
        else
          pure ((ready.find? (· > c)).getD (ready.headD 0))
      | none => pure (ready.headD 0)
    let some locals := p.threads.getD t none | return
    modify (· ++ (obs p).toArray)
    match ← (prog.step t locals : ProcessM M L (StepResult L)) with
    | .ran locals' =>
      (modify fun p => { p with threads := p.threads.set! t (some locals'), steps := p.steps + 1 } : ProcessM M L Unit)
      blocked := []
      cur := some t
    | .blocked =>
      blocked := t :: blocked
      cur := some t
    | .done =>
      (modify fun p => { p with threads := p.threads.set! t none, steps := p.steps + 1 } : ProcessM M L Unit)
      blocked := []
      cur := some t

abbrev Snap := Nat × TConn × Process TMem TTh

/-- The pre-read snapshots of a process: every connection about to read a chunk. -/
def preReadSnaps (p : Process TMem TTh) : List Snap :=
  (List.range p.threads.size).filterMap fun i =>
    match p.threads.getD i none with
    | some (.conn c) => if preRead p c then some (i, c, p) else none
    | _ => none

/-- `runTWith` (round 4's copy of round 3's World T runner, preemption-bounded) with the snapshots. -/
def runTObs (budget : Nat) (s : TScenario) (source : Source) :
    Ended × Process TMem TTh × Array Snap :=
  let body : StateT (Array Snap) (ProcessM TMem TTh) Unit := do
    interleavePBObs tProg s.cfg.maxSteps budget tStuck preReadSnaps
    let p ← (get : ProcessM TMem TTh (Process TMem TTh))
    let live := p.threads.toList.any Option.isSome
    if !live then
      if let some (prop, d) := tJudge s.aside s.scripts p.memory then
        throw (.violation prop d)
    else
      throw (.violation "the timeline ends within the step bound (model bound)" "threads live")
  let p0 := { tInitial s.cfg s.scripts with decisions := { source, limit := 100000 } }
  match (body.run #[]).run p0 with
  | .ok ((), snaps) p => ({ taken := p.decisions.taken, violation := none }, p, snaps)
  | .error (.violation "deadlock" d) p =>
    ({ taken := p.decisions.taken, violation := some ("every request gets a done reply (no hang)", d) }, p, #[])
  | .error (.violation prop d) p => ({ taken := p.decisions.taken, violation := some (prop, d) }, p, #[])
  | .error _ p => ({ taken := p.decisions.taken, violation := none }, p, #[])

/-- A World T run (round 3's scheduler) with its final process. -/
def runT (budget : Nat) (s : TScenario) (source : Source) : Ended × Process TMem TTh :=
  runTWith (some budget) s.cfg s.aside s.scripts source

/-! ## Walks -/

/-- A walk's tallies. -/
structure Walk where
  runs : Nat := 0
  complete : Bool := false
  next : Option (Array Nat) := none
  counts : List (String × Nat) := []
  examples : List (String × String) := []
  tapes : List (String × Array Nat) := []
  /-- Distinct final-state fingerprints, with how many timelines ended in each. -/
  finals : List (String × Nat) := []
  deriving Inhabited

def Walk.record (w : Walk) (o : Ended) (fp : String) : Walk := Id.run do
  let mut w := w
  if let some (p, d) := o.violation then
    let counts := match w.counts.lookup p with
      | some n => (p, n + 1) :: w.counts.filter (·.1 != p)
      | none => (p, 1) :: w.counts
    let examples := if (w.examples.lookup p).isSome then w.examples else w.examples ++ [(p, d)]
    let tapes := if (w.tapes.lookup p).isSome then w.tapes else w.tapes ++ [(p, o.taken.map (·.value))]
    w := { w with counts, examples, tapes }
  let finals := match w.finals.lookup fp with
    | some n => (fp, n + 1) :: w.finals.filter (·.1 != fp)
    | none => (fp, 1) :: w.finals
  pure { w with finals }

/-- The number of decisions named `name` taken with a nonzero value. -/
def nonzero (name : String) (taken : Array Taken) : Nat :=
  taken.foldl (fun n t => if t.name == name && t.value != 0 then n + 1 else n) 0

/-- The first index at which more than `cuts` decisions `net.read.split` took 1 (a partial read). -/
def overCut (cuts : Nat) (taken : Array Taken) : Option Nat := Id.run do
  let mut n := 0
  for i in [0:taken.size] do
    let t := taken[i]!
    if t.name == "net.read.split" && t.value != 0 then
      n := n + 1
      if n > cuts then return some i
  return none

end Jank.R5.Nrepl
