import Jank.R9.Nrepl.Fix

/-!
# Round 9, nREPL: World TQ's scenarios and the checks at every final and quiescent state

`fixRun` builds a scenario's every-schedule graph (round 8's `exactGraph`, compact codec, logs
ordered by client) on World TQ's step, then reads every final and quiescent state: round 3's judge
(`judgeEnd`, as round 8), the protocol property for every request including raw ones
(`protocolAt`), the replies holding only an id and a session (`emptyReplies`), and each outcome's
replies (round 8's `census`).
-/

namespace Jank.R9.Nrepl

open Determinismo Jank.R3.Nrepl Jank.R6.Nrepl Jank.R8.Nrepl Jank.NreplServer Jank.Analyzer

def stdinS (id text : String) (sess : Option String := some "none") : TReq :=
  rawReq ([("op", "stdin"), ("id", id), ("stdin", text)] ++ (match sess with | some s => [("session", s)] | none => []))

def evalRawS (id code : String) : TReq :=
  rawReq [("op", "eval"), ("id", id), ("session", "none"), ("code", code), ("ns", "user")]

def interruptS (id : String) (sess : Option String) : TReq :=
  rawReq ([("op", "interrupt"), ("id", id), ("interrupt-id", "e")] ++ (match sess with | some s => [("session", s)] | none => []))

/-- World TQ's scenarios. The ones without a clone use the session id "none" for every request,
which is what round 3's clients send before a clone (Threads.lean `tReqMap`), so raw stdin ops and
the evals share one session. -/
def qScenarios : List (String × TScenario × Bool) := [
  ("T9", tScenarios.getD 8 default, false),
  ("T3", tScenarios.getD 2 default, false),
  ("D3q", { name := "D3 with the fix: an eval of (read-line) with nothing sent, then the stdin op, then describe"
            cfg := { partialReads := false }, aside := allAside
            scripts := [[.eval "(read-line)", stdinS "s" "hi\n", .describe]] }, false),
  ("D3b", { name := "type-ahead: stdin \"hi\\n\" sent before two evals of (read-line), then describe"
            cfg := { partialReads := false }, aside := allAside
            scripts := [[stdinS "s" "hi\n", .eval "(read-line)", .eval "(read-line)", .describe]] }, false),
  ("D3c", { name := "stdin \"a\\r\", \"\\nb\", an end of input, then four evals of (read-line)"
            cfg := { partialReads := false }, aside := allAside
            scripts := [[stdinS "s" "a\r", stdinS "t" "\nb", stdinS "u" "", .eval "(read-line)", .eval "(read-line)",
                         .eval "(read-line)", .eval "(read-line)"]] }, false),
  ("D3d", { name := "two connections, one session: connection 0 sends stdin then describes, connection 1 evaluates (read-line) twice"
            cfg := { partialReads := false }, aside := allAside
            scripts := [[stdinS "s" "x\n", .describe], [.eval "(read-line)", .eval "(read-line)"]] }, false),
  ("D3n", { name := "need-input: (read-line) sent without waiting, then stdin \"hi\\n\", then describe"
            cfg := { partialReads := false }, aside := allAside
            scripts := [[evalRawS "e" "(read-line)", stdinS "s" "hi\n", .describe]] }, false),
  ("D3e", { name := "need-input, then the end of input (an empty stdin), then describe"
            cfg := { partialReads := false }, aside := allAside
            scripts := [[evalRawS "e" "(read-line)", stdinS "s" "", .describe]] }, false),
  ("D3w", { name := "need-input, describe answered while the eval waits, then the client leaves"
            cfg := { partialReads := false }, aside := allAside
            scripts := [[evalRawS "e" "(read-line)", .describe]] }, false),
  ("D3p", { name := "a partial line: need-input, stdin \"ab\", need-input again, stdin \"c\\n\", describe"
            cfg := { partialReads := false }, aside := allAside
            scripts := [[evalRawS "e" "(read-line)", stdinS "s" "ab", stdinS "t" "c\n", .describe]] }, false),
  ("D3t", { name := "two connections, one session: connection 0's (read-line) waits, then describes; connection 1 sends stdin and describes"
            cfg := { partialReads := false }, aside := allAside
            scripts := [[evalRawS "e" "(read-line)", .describe], [stdinS "s" "x\n", .describe]] }, false),
  ("I1", { name := "V37i: interrupt with a session, without one, then describe"
           cfg := { partialReads := false }, aside := allAside
           scripts := [[interruptS "i" (some "none"), interruptS "j" none, .describe]] }, false),
  ("D1q", { name := "D1 with the fixes: a diverging eval, then interrupt and describe pipelined (World T8's step)"
            cfg := { partialReads := false }, aside := allAside
            scripts := [[.clone, evalRaw "e" "(loop [] (recur))", interruptRaw "i" "e", .describe]] }, true) ]

def fmtN (n : Nat) : String :=
  let s := (toString n).toList
  let len := s.length
  String.ofList (s.zipIdx.foldr (fun (c, i) acc =>
    if i > 0 && (len - i) % 3 == 0 then ',' :: c :: acc else c :: acc) [])

def flushOut : IO Unit := do (← IO.getStdout).flush

/-- Every schedule of one scenario on World TQ (`fx`) or round 3's World T (`stock`). -/
def fixRun (name : String) (fx : QFix) (stock : Bool) (maxStates secs : Nat) : IO Unit := do
  let some (_, s, div) := qScenarios.find? (·.1 == name) | IO.println s!"unknown scenario {name}"
  let step : StepFn := if stock then (if div then t8Step else tStep) else (if div then qStep8 fx else qStep fx)
  IO.println s!"== {name}: {s.name}"
  IO.println s!"  step: {if stock then "round 3's (stock jank)" else s!"World TQ (fixes {repr fx})"}{if div then ", diverging evals spin (World T8)" else ""}; cfg fixCapture {s.cfg.fixCapture}; every schedule, exact, logs ordered by client"
  flushOut
  let t0 ← IO.monoMsNow
  let (g, T, complete) ← exactGraph s true false true maxStates (secs * 1000) (fun i n => do
    IO.println s!"    … {fmtN i} expanded, {fmtN n} found ({(← IO.monoMsNow) - t0} ms)"; flushOut) step
  IO.println s!"  graph: {fmtN g.size} states, {fmtN g.runs} step runs, {if complete then "COMPLETE" else "STOPPED"} ({(← IO.monoMsNow) - t0} ms)"
  IO.println s!"  final states: {g.finals.size} ({g.finalViol.size} with a violation of round 3's judge); step violations: {g.stepViol.size}; states where every thread only blocks: {g.deadlocks.size}; progress self-loops: {g.progressSelf}; blocked steps that moved: {g.blockedMoves}"
  for (i, p, d) in g.finalViol.toList.take 3 do IO.println s!"    final {i}: {p}: {d.take 300}"
  for (i, p, d) in g.stepViol.toList.take 3 do IO.println s!"    step at {i}: {p}: {d.take 300}"
  flushOut
  if !complete then return
  let (longest, acyclic) := g.longest
  IO.println s!"  acyclic (progress steps): {acyclic}; longest progress path: {longest} steps"
  let mut seen : Std.HashMap String Nat := {}
  let mut quiet := 0
  let mut withEmpty := 0
  let mut emptyTotal := 0
  let mut protoBad := 0
  let mut protoEx : Option String := none
  for i in [0:g.size] do
    if g.quiet i then
      quiet := quiet + 1
      if let some k := g.decode T i then
        let final := (g.eoff.getD i 0) == (g.eoff.getD (i + 1) g.edges.size)
        let es := emptyReplies k.mem
        if !es.isEmpty then
          withEmpty := withEmpty + 1
          emptyTotal := emptyTotal + es.length
        if let some d := protocolAt s.scripts k.mem final then
          protoBad := protoBad + 1
          if protoEx.isNone then protoEx := some d
        let line := (if final then "FINAL " else if g.deadlocks.contains i then "STUCK " else "QUIESCENT ") ++ census k.mem
        seen := seen.insert line (seen.getD line 0 + 1)
  IO.println s!"  final or quiescent states: {quiet}; with a reply holding only id and session: {withEmpty} ({emptyTotal} such replies in all); protocol (every request, raw ones too: id, one done, last; every request answered at final states) broken: {protoBad}{match protoEx with | some d => s!" (e.g. {d})" | none => ""}"
  IO.println s!"  distinct outcomes: {seen.size}"
  for (l, n) in seen.toList.take 8 do IO.println s!"    {n} × {l.take 700}"
  flushOut

/-- World T8's D4 with the fixes: connection 0 diverges (silently), connection 1 sends stdin and
evaluates (read-line) (session "none"), then describes. -/
def d4q : TScenario :=
  { name := "D4q: connection 0 runs a diverging eval; connection 1 sends stdin \"hi\\n\", evaluates (read-line), describes (jank's capture)"
    cfg := { partialReads := false }, aside := allAside
    scripts := [[.clone, evalRaw "e" "(loop [] (recur))", .describe], [stdinS "s" "hi\n", .eval "(read-line)", .describe]] }

/-- World TQ8 at one budget, states expanded on demand, the spinning eval's step blocked (round 8's
`divbCmd` with `qStep8B`): every quiescent state the schedules with at most `b` preemptions reach. -/
def divqRun (fx : QFix) (stock : Bool) (b maxStates maxCombos secs : Nat) : IO Unit := do
  let s := d4q
  let step : StepFn := if stock then t8StepB else qStep8B fx
  IO.println s!"== {s.name} ({if stock then "stock" else "fixes"})"
  IO.println s!"  ≤{b} preemptions, states expanded on demand, the spinning eval's step reported as blocked"
  flushOut
  let t0 ← IO.monoMsNow
  let (o, lb, nc, complete) ← countBounded s b true false true maxStates maxCombos (t0 + secs * 1000) step
  IO.println s!"  {if complete then "COMPLETE" else "STOPPED"}: {fmtN lb.g.size} states, {fmtN lb.g.runs} step runs, {fmtN nc} scheduler states; timelines {fmtN o.n}; step violations {lb.g.stepViol.size} ({(← IO.monoMsNow) - t0} ms)"
  let mut seen : Std.HashMap String Nat := {}
  let mut withEmpty := 0
  for i in lb.g.deadlocks.toList ++ lb.g.finals.toList do
    if let some k := lb.g.decode lb.T i then
      if !(emptyReplies k.mem).isEmpty then withEmpty := withEmpty + 1
      let line := (if lb.g.finals.contains i then "FINAL " else "QUIESCENT ") ++ census k.mem
      seen := seen.insert line (seen.getD line 0 + 1)
  IO.println s!"  quiescent or final states: {lb.g.deadlocks.size + lb.g.finals.size}; with a reply holding only id and session: {withEmpty}; distinct outcomes: {seen.size}"
  for (l, n) in seen.toList.take 10 do IO.println s!"    {n} × {l.take 700}"
  flushOut

end Jank.R9.Nrepl
