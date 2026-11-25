import Jank.R3.Nrepl.ThreadSearch

/-!
# Round 5, nREPL: World I, the `interrupt` op

**jank (94d32623).** `handle-message` (nrepl/server/handler.jank 3–8) is a multimethod on
`(keyword (get msg "op"))`; no method is defined for `:interrupt` (the handler namespaces
clone/close/completions/describe/eval/lookup, core.jank 7–12), so `:default` answers
`{:status [:error :unknown-op :done] :op "interrupt"}`, and `responses-for` (core.jank 33–45) copies
the request's `id` and `session`. `describe` (handler/describe.jank 5–17) does not list `interrupt`.
A connection is one loop (`handle-client`, core.jank 79–106): it reads a request, runs its handler
to the end, writes the replies, then reads the next. So an interrupt sent on the connection of a
running eval is read only after that eval returns, and never if it does not; an interrupt on
another connection is answered at once and touches nothing (sessions are not kept: `clone` returns
a fresh uuid, handler/clone.jank 5–7, R127).

**nREPL (the protocol's reference implementation, 1.8.0: session.clj `session` 311–384,
`interrupt-session` 277–296, `session-exec` 181–265; server.clj `handle` 39–48; interruptible_eval.clj
181–204).**
Every request is handled on a pool thread as it arrives (`handle`), evals of a session run one at
a time on the session's thread, and `interrupt` answers from the session's state when it is
handled:
- no `session`: an ephemeral session, `#{:error :session-ephemeral :done}`;
- an unknown session: `#{:error :unknown-session :done}`;
- nothing running: `#{:session-idle :done}`;
- running, with an `interrupt-id` other than the running request's: `#{:error :interrupt-id-mismatch
  :done}`;
- running, `interrupt-id` absent or equal: the eval's thread is interrupted (stopped where the JVM
  allows), `#{:interrupted :done}` is sent for the eval's id on the interrupt's own connection, its
  session loop skips the eval's own `done`, and the interrupt gets `#{:done}`.
Sessions are global, so an interrupt sent on another connection reaches the eval. Which state the
interrupt sees is a race (`world.interrupt.sees`): before the eval starts, while it runs, after it
ends (only if it ends). `results/r5-nrepl-interrupt-jvm.txt` measures these replies on nREPL 1.8.0.

**World I.** Cases: the eval's code (ends after printing, or never returns), where the interrupt is
sent (right after the eval on its connection; after the eval's done; on a second connection; with no
eval), its `session` (the eval's, absent, unknown) and its `interrupt-id` (absent, the eval's,
another). Property: what jank's client sees for each request (its replies' shape, or never done) is
one of the outcomes nREPL can give. jank's side is computed twice: from the code above
(`jankOutcome`), and, for evals that end, by round 3's World T conn replica with the requests sent as
raw bytes (`worldT`), every schedule within 2 preemptions.
-/

namespace Jank.R5.Nrepl.Interrupt

open Determinismo Jank.NreplServer Jank.R3.Nrepl

inductive Code where
  | ends
  | diverges
  deriving Repr, BEq, DecidableEq, Inhabited

inductive Place where
  /-- On the eval's connection, right after the eval, without waiting. -/
  | pipelined
  /-- On the eval's connection, after the eval's `done`. -/
  | afterDone
  /-- On a second connection, after the eval was sent on the first. -/
  | otherConn
  /-- No eval at all. -/
  | idle
  deriving Repr, BEq, DecidableEq, Inhabited

inductive Sess where
  | evalSession
  | absent
  | unknown
  deriving Repr, BEq, DecidableEq, Inhabited

inductive IId where
  | absent
  | evalId
  | other
  deriving Repr, BEq, DecidableEq, Inhabited

structure Case where
  code : Code
  place : Place
  sess : Sess
  iid : IId
  deriving Repr, BEq, Inhabited

/-- What the eval request gets. -/
inductive EShape where
  /-- its output, its value, `done` -/
  | normal
  /-- `#{:interrupted :done}` -/
  | interrupted
  /-- never a `done` -/
  | never
  /-- not sent -/
  | none
  deriving Repr, BEq, DecidableEq, Inhabited

/-- What the interrupt request gets. -/
inductive IShape where
  | status (xs : List String)
  | never
  | notSent
  deriving Repr, BEq, DecidableEq, Inhabited

structure Outcome where
  e : EShape
  i : IShape
  deriving Repr, BEq, DecidableEq, Inhabited

def sortS (xs : List String) : List String := xs.mergeSort (fun a b => decide (a ≤ b))

def st (xs : List String) : IShape := .status (sortS xs)

/-! ## jank -/

def unknownOp : IShape := st ["error", "unknown-op", "done"]

/-- jank's outcome, from handler.jank and core.jank's `handle-client`. -/
def jankOutcome (c : Case) : Outcome :=
  let e : EShape := match c.place with
    | .idle => .none
    | _ => if c.code == .ends then .normal else .never
  let i : IShape := match c.place with
    | .pipelined => if c.code == .ends then unknownOp else .never
    | .afterDone => if c.code == .ends then unknownOp else .notSent
    | .otherConn => unknownOp
    | .idle => unknownOp
  { e := e, i := i }

/-! ## nREPL -/

/-- What the interrupt sees when it is handled. -/
inductive Sees where
  | before
  | running
  | after
  deriving Repr, BEq, DecidableEq, Inhabited

/-- nREPL's outcome for one race resolution. -/
def nreplFor (c : Case) (s : Sees) : Outcome :=
  let eAlone : EShape := match c.place with
    | .idle => .none
    | _ => if c.code == .ends then .normal else .never
  match c.sess with
  | .absent => { e := eAlone, i := (if c.place == .afterDone && c.code == .diverges then .notSent else st ["error", "session-ephemeral", "done"]) }
  | .unknown => { e := eAlone, i := (if c.place == .afterDone && c.code == .diverges then .notSent else st ["error", "unknown-session", "done"]) }
  | .evalSession =>
    match c.place with
    | .idle => { e := .none, i := st ["session-idle", "done"] }
    | .afterDone =>
      if c.code == .ends then { e := .normal, i := st ["session-idle", "done"] }
      else { e := .never, i := .notSent }
    | .pipelined | .otherConn =>
      match s with
      | .before | .after => { e := eAlone, i := st ["session-idle", "done"] }
      | .running =>
        if c.iid == .other then { e := eAlone, i := st ["error", "interrupt-id-mismatch", "done"] }
        -- `interrupt-session` sends the eval's `#{:interrupted :done}` on the interrupt's transport
        -- (session.clj 293–295): from another connection, the eval's own connection never gets a
        -- done (measured: results/r5-nrepl-interrupt-jvm.txt)
        else if c.place == .otherConn then { e := .never, i := st ["done"] }
        else { e := .interrupted, i := st ["done"] }

/-- Every outcome nREPL can give: the race resolutions possible for the case (after only when the
eval ends; one resolution when the interrupt is not racing an eval). -/
def nreplOutcomes (c : Case) : List Outcome :=
  let races : List Sees := match c.place with
    | .pipelined | .otherConn => if c.code == .ends then [.before, .running, .after] else [.before, .running]
    | _ => [.after]
  (races.map (nreplFor c)).eraseDups

/-! ## The census -/

def allCases : List Case := Id.run do
  let mut out := []
  for code in [Code.ends, .diverges] do
    for place in [Place.pipelined, .afterDone, .otherConn, .idle] do
      for sess in [Sess.evalSession, .absent, .unknown] do
        for iid in [IId.absent, .evalId, .other] do
          out := out ++ [{ code := code, place := place, sess := sess, iid := iid }]
  return out

/-- The class of a disagreement, for the tally. -/
def classify (j : Outcome) (ns : List Outcome) : String :=
  if ns.contains j then "agrees"
  else if j.i == .never && ns.all (fun n => n.i != .never) then
    "the interrupt is never answered (nREPL answers it in every race)"
  else if j.i == unknownOp then
    if ns.any (fun n => n.e == j.e) then "unknown-op where nREPL gives its interrupt status (the eval's own replies agree)"
    else "unknown-op, and the eval's replies are none of nREPL's"
  else "other"

/-! ## jank's side through World T (round 3's conn replica), for evals that end -/

def evalCode : String := "(do (print \"a\") 3)"

def mapOf (kvs : List (String × String)) : JVal := .map (kvs.map fun (k, v) => (JVal.s k, JVal.s v))

def enc (kvs : List (String × String)) : List UInt8 := (specEncode (mapOf kvs)).getD []

def interruptMsg (c : Case) (session : String) (evalId : String) : List UInt8 :=
  enc ([("op", "interrupt"), ("id", "i")] ++
    (match c.sess with
     | .evalSession => [("session", session)]
     | .absent => []
     | .unknown => [("session", "no-such-session")]) ++
    (match c.iid with
     | .absent => []
     | .evalId => [("interrupt-id", evalId)]
     | .other => [("interrupt-id", "zz")]))

/-- The scripts: the first clone gets `uuid-0`; the eval is `c0-1` when sent as a request (waiting for
its done), `e` when sent raw (pipelined); a final `describe` makes the client wait for every reply. -/
def scriptsOf (c : Case) : List (List TReq) :=
  match c.place with
  | .pipelined =>
    [[.clone, .raw (enc [("op", "eval"), ("id", "e"), ("session", "uuid-0"), ("code", evalCode), ("ns", "user")]),
      .raw (interruptMsg c "uuid-0" "e"), .describe]]
  | .afterDone => [[.clone, .eval evalCode, .raw (interruptMsg c "uuid-0" "c0-1"), .describe]]
  | .otherConn => [[.clone, .eval evalCode], [.raw (interruptMsg c "uuid-0" "c0-1"), .describe]]
  | .idle => [[.clone, .raw (interruptMsg c "uuid-0" "e"), .describe]]

def statusesOf (r : JVal) : List String :=
  match jget r (JVal.s "status") with
  | .vec xs | .list xs => xs.filterMap fun x => match x with
    | .str b => String.fromUTF8? (ByteArray.mk b.toArray)
    | _ => none
  | _ => []

/-- The shapes jank's clients ended with in a World T run. -/
def shapesOf (c : Case) (m : TMem) : Outcome :=
  let evalId := if c.place == .pipelined then "e" else "c0-1"
  let rs (id : String) := (m.replies.toList.filter fun (_, r) => strField r "id" == some id).map (·.2)
  let es := rs evalId
  let e : EShape :=
    if c.place == .idle then .none
    else if es.any fun r => (statusesOf r).contains "done" then
      (if es.any fun r => (jget r (JVal.s "value")) != .nil then .normal else .interrupted)
    else .never
  let is := rs "i"
  let i : IShape := match is.find? fun r => (statusesOf r).contains "done" with
    | some r => .status (sortS (statusesOf r))
    | none => .never
  { e := e, i := i }

def tCfg : TConfig := { partialReads := false }

/-- Every World T schedule within `budget` preemptions: the distinct outcomes jank's clients see,
and the violations of World T's own properties (replies end with done, carry id/session). -/
def worldT (c : Case) (budget : Nat) (maxRuns : Nat := 200000) : List Outcome × Nat × List String := Id.run do
  let scripts := scriptsOf c
  let mut path : Array Nat := #[]
  let mut outs : List Outcome := []
  let mut runs := 0
  let mut viol : List String := []
  for _ in [0:maxRuns] do
    let (o, p) := runTWith (some budget) tCfg {} scripts (Source.path path)
    runs := runs + 1
    if let some (prop, d) := o.violation then
      if !viol.contains prop then viol := viol ++ [s!"{prop}: {d}"]
    let sh := shapesOf c p.memory
    if !outs.contains sh then outs := outs ++ [sh]
    match nextPath o.taken with
    | none => break
    | some q => path := q
  return (outs, runs, viol)

def showOutcome (o : Outcome) : String :=
  let e := match o.e with
    | .normal => "eval: out, value, done"
    | .interrupted => "eval: interrupted done"
    | .never => "eval: never done"
    | .none => "no eval"
  let i := match o.i with
    | .status xs => s!"interrupt: {xs}"
    | .never => "interrupt: never answered"
    | .notSent => "interrupt: not sent"
  s!"{e}; {i}"

def main (args : List String) : IO Unit := do
  let budget := (args.headD "2").toNat!
  IO.println s!"== World I: the interrupt op, {allCases.length} cases; jank's side also run through World T (≤ {budget} preemptions) where the eval ends"
  let mut tally : List (String × Nat) := []
  let mut tRuns := 0
  for c in allCases do
    let j := jankOutcome c
    let ns := nreplOutcomes c
    let cls := classify j ns
    tally := match tally.lookup cls with
      | some n => (cls, n + 1) :: tally.filter (·.1 != cls)
      | none => tally ++ [(cls, 1)]
    let tline ← if c.code == .ends then do
        let (outs, runs, viol) := worldT c budget
        tRuns := tRuns + runs
        let agree := outs == [j]
        pure s!"   World T: {runs} schedules, outcomes {outs.map showOutcome}{if viol.isEmpty then "" else s!", World T violations {viol}"} — {if agree then "= jankOutcome" else "DIFFERS from jankOutcome"}"
      else pure "   World T: not run (an eval that never returns is outside its evaluator)"
    IO.println s!"- {reprStr c.code} {reprStr c.place} session {reprStr c.sess} interrupt-id {reprStr c.iid}: {cls}"
    IO.println s!"   jank: {showOutcome j}"
    IO.println s!"   nREPL: {ns.map showOutcome}"
    IO.println tline
  IO.println s!"== tally ({tRuns} World T schedules in all)"
  for (k, n) in tally do IO.println s!"  {k}: {n}"
  (← IO.getStdout).flush

end Jank.R5.Nrepl.Interrupt
