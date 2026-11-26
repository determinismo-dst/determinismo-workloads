import Jank.R8.Nrepl.Exact

/-!
# Round 8, nREPL: diverging evals, interrupt and stdin inside World T

Round 3's World T ends a timeline at `.limit` when an evaluation runs out of fuel (Handler.lean
`finishSafeEval` 81, Threads.lean `.finishEval` 385–386), so an eval that never returns was outside
it, and round 5's interrupt study (World I) resolved races by hand. World T8 is World T with three
additions, everything else round 3's code:

1. A diverging eval. jank evaluates a form in the connection's own thread (core.jank `handle-client`
   79–106 → handler/eval.jank `do-eval` 22–64 → eval.jank `safe-eval` → evaluate.cpp `safe_eval`);
   a `loop`/`fn` body is JIT-compiled under the interpreter lock and then called outside it
   (evaluate.cpp `eval(expr::function_ref)` 522–553 → jit/processor_dynamic.cpp `processor::eval`
   444–459 → `eval_string` 590–608, which holds `interpreter.lock()` only for `ParseAndExecute` of the
   declaration; the body runs at `.call()`). So the thread spins in the body, holding no lock, with
   fd 1 and fd 2 on its eval's temp files (capture.jank `start` 18–37 ran before `f`). `t8Step`: when
   a form's evaluation exhausts the model's fuel without output (evaluate's `.fail .fuel`, the
   evaluator's bound of 4,000 steps), the thread's step leaves the process as it is and runs again
   (a progress self-loop: it is always ready, never done). Assumption nREPLA8-1: such an evaluation
   is one that never returns (the scenarios' only one is `(loop [] (recur))`).
2. Requests sent without waiting (`TReq.raw` with a bencoded map): the interrupt and stdin ops, and
   an eval pipelined before other requests. jank has neither op (handler.jank 3–8 `:default`:
   `{:status [:error :unknown-op :done] :op …}`; describe.jank 5–17 lists neither), which round 3's
   dispatch already answers (Threads.lean 288).
3. The judge at quiescent states. A state is quiescent when no thread can make a step other than
   the spinning one's (every live thread's every branch blocks, or is that self-loop); a fair
   scheduler reaches one, and nothing changes after it. Each client's socket outbox is decoded
   whole (the spec decoder, as `tClientRead` does), so the replies to requests sent without waiting
   are seen too. The census lists, for every quiescent or final state, each request id's replies.
-/

namespace Jank.R8.Nrepl

open Determinismo Jank.R3.Nrepl Jank.R6.Nrepl Jank.NreplServer Jank.Analyzer

/-- World T8's step: round 3's, except that an evaluation exhausting the model's fuel spins. -/
def t8Step (t : Nat) (th : TTh) : TM (StepResult TTh) :=
  match th with
  | .conn c =>
    match c.instrs with
    | .form :: _ =>
      match c.ev.run.phase with
      | .eval _ => do
        let m ← tmem
        let (r', _, _) := c.ev.run.step (esOf m c) c.ev.q.file
        match r'.phase with
        | .emit [] (.fail .fuel) => pure (.ran (.conn c))
        | _ => tConnStep t c
      | _ => tConnStep t c
    | _ => tConnStep t c
  | other => tStep t other

/-- The same, with the spinning step reported as blocked: the state is unchanged either way, and
under `interleavePB` the other threads then run without spending budget (the fair schedules), so a
state where only the spinning thread could move is a deadlock leaf: the quiescent states of the
bounded exploration (Run/R8/Nrepl.lean `divb`). -/
def t8StepB (t : Nat) (th : TTh) : TM (StepResult TTh) :=
  match th with
  | .conn c =>
    match c.instrs with
    | .form :: _ =>
      match c.ev.run.phase with
      | .eval _ => do
        let m ← tmem
        let (r', _, _) := c.ev.run.step (esOf m c) c.ev.q.file
        match r'.phase with
        | .emit [] (.fail .fuel) => pure .blocked
        | _ => tConnStep t c
      | _ => tConnStep t c
    | _ => tConnStep t c
  | other => tStep t other

/-- A request sent as bytes, without waiting for its replies. -/
def rawReq (kvs : List (String × String)) : TReq :=
  .raw ((specEncode (.map (kvs.map fun (k, v) => (JVal.s k, JVal.s v)))).getD [])

def evalRaw (id code : String) : TReq :=
  rawReq [("op", "eval"), ("id", id), ("session", "S"), ("code", code), ("ns", "user")]

def interruptRaw (id target : String) : TReq :=
  rawReq [("op", "interrupt"), ("id", id), ("session", "S"), ("interrupt-id", target)]

def stdinRaw (id text : String) : TReq :=
  rawReq [("op", "stdin"), ("id", id), ("session", "S"), ("stdin", text)]

def dScenarios : List TScenario := [
  { name := "D1 one connection: a diverging eval, then interrupt (its id) and describe pipelined after it"
    cfg := { partialReads := false }
    aside := allAside
    scripts := [[.clone, evalRaw "e" "(loop [] (recur))", interruptRaw "i" "e", .describe]] },
  { name := "D2 connection 0 runs a diverging eval; connection 1 prints, interrupts it, describes (jank's capture)"
    cfg := { partialReads := false }
    aside := allAside
    scripts := [[.clone, evalRaw "e" "(loop [] (recur))", .describe],
                [.clone, .eval "(println \"x\")", interruptRaw "i" "e", .describe]] },
  { name := "D2L D2 under round 3's capture lock (the set-aside of R125)"
    cfg := { partialReads := false, fixCapture := true }
    aside := allAside
    scripts := [[.clone, evalRaw "e" "(loop [] (recur))", .describe],
                [.clone, .eval "(println \"x\")", interruptRaw "i" "e", .describe]] },
  { name := "D3 stdin: an eval reading a line (read-line as core.jank 5966-5972 defines it), then the stdin op"
    cfg := { partialReads := false }
    aside := allAside
    scripts := [[.clone, .eval "(defn read-line [] (throw (ex-info \"TODO: port read-line\" {})))",
                 .eval "(read-line)", stdinRaw "s" "hi\n", .describe]] },
  { name := "D4 two connections: connection 0 diverges, connection 1 sends stdin and an eval (jank's capture)"
    cfg := { partialReads := false }
    aside := allAside
    scripts := [[.clone, evalRaw "e" "(loop [] (recur))", .describe],
                [.clone, stdinRaw "s" "hi\n", .eval "(def z 1) z"]] } ]

/-- Every reply in a socket's outbox (the spec decoder, as `tClientRead`). -/
def outboxReplies (s : Sock) : List JVal := Id.run do
  let mut rest := s.outbox
  let mut out := #[]
  for _ in [0:200] do
    if rest.isEmpty then break
    match specDecode rest with
    | .msg v r => out := out.push v; rest := r
    | _ => break
  return out.toList

def statusText (r : JVal) : String :=
  match jget r (JVal.s "status") with
  | .nil => ""
  | v => JVal.render v

def replyText (r : JVal) : String :=
  let f (k : String) : String := match strField r k with
    | some v => s!" {k}={String.ofList ((v.toList.take 40).map (fun c => if c == '\n' then '|' else c))}"
    | none => ""
  s!"[{statusText r}{f "value"}{f "out"}{f "err"}{f "op"}]"

/-- One line per client: each request id's replies, in order. -/
def census (m : TMem) : String := Id.run do
  let mut lines := #[]
  for cid in [0:m.socks.size] do
    let rs := outboxReplies (m.socks.getD cid {})
    let ids := (rs.filterMap fun r => strField r "id").eraseDups
    let parts := ids.map fun id =>
      let mine := rs.filter fun r => strField r "id" == some id
      s!"{id}:{String.intercalate "" (mine.map replyText)}"
    lines := lines.push s!"client {cid}: {String.intercalate " " parts}"
  let fd1 := reprStr (m.fd 1)
  let outOk := m.evals.toList.map fun e =>
    let rs := outboxReplies (m.socks.getD e.cid {})
    let out := rs.flatMap fun r => if strField r "id" == some e.id then
      (match jget r (JVal.s "out") with | .str b => b | _ => []) else []
    s!"{e.id} printed \"{showBytes e.own}\" got \"{showBytes out}\""
  lines := lines.push s!"fd 1: {fd1}; evals: {String.intercalate ", " outOk}"
  return String.intercalate " / " lines.toList

/-- Quiescent states (not final, every edge blocked or a progress self-loop) and final states. -/
def EG.quiet (g : EG) (i : Nat) : Bool := Id.run do
  let a := g.eoff.getD i 0
  let b := g.eoff.getD (i + 1) g.edges.size
  if a == b then return true
  for k in [a:b] do
    let e := g.edges[k]!
    let kd := eKind e
    if kd == 1 then continue
    if (kd == 0 || kd == 2) && eSucc e == i then continue
    return false
  return true

end Jank.R8.Nrepl
