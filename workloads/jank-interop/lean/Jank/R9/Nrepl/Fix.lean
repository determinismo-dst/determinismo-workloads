import Jank.R8.Nrepl.Diverge

/-!
# Round 9, nREPL: fixes Q1, Q2 and V37i inside World T (World TQ)

World TQ is round 3's World T (Threads.lean `tConnStep`, unchanged for everything else) with the
three fixes of this round, each a switch (`QFix`):

- Q2 (fixes/Q2.diff, handler/eval.jank `do-eval`): `(filterv some? [...])` around both reply vectors,
  so a blank `:out`/`:err` (the `nil` of `(when-not (blank? stdout) ...)`) sends no message.
  `qEvalReplies` is `tConnStep`'s `.evalReplies` arm (Threads.lean 420-433) with `dropNils` applied
  to the handler's vector before core.jank's `responses-for`.
- Q1 (fixes/Q1.diff): a per-session input (handler/eval.jank `session-inputs`, `add-input`,
  `take-line`, `skip-eol` after every eval, `session-reader`), the `:stdin` method, `:stdin` in describe's ops, and core.jank's
  `read-line` calling a function bound to `*in*`. The session inputs live in `TMem.temps` under names
  no temp file has (`sinName`; nothing in World T iterates `temps` except by name). An eval whose
  code is exactly `(read-line)` runs `do-eval`'s capture (the same instructions as any eval) and,
  in place of the evaluator's steps (`.bind .form .finishEval .unbind`), one atomic step that takes a
  line from the request's session input (`take-line`, the compare-and-set loop of `session-reader`
  being one atomic update), or, with nothing to read, sends need-input and runs core.jank's
  `wait-input` loop (round 3's `.readMsg` and dispatch for each request read meanwhile, until the
  session's input changes; a nested eval is outside the model: `.limit`), or fails with need-input
  when the request has no session or the client is gone (assumption nREPLA9-2: `*1`/`*e` are not
  updated by this step; no scenario reads them after a read-line eval).
- V37i (fixes/V37i.diff, handler/clone.jank): `:interrupt` answered `[:session-idle :done]` with a
  session and `[:error :session-ephemeral :done]` without one.

Encoding (model only): the read-line step is the instruction `.handlerError req readLineMark`, which
`qConnStep` intercepts before round 3's step can see it; its outcome is kept in the eval's
`q.file` (`valueMark`/`needMark`), read back by `qEvalReplies`. Nothing else uses those values.
-/

namespace Jank.R9.Nrepl

open Determinismo Jank.R3.Nrepl Jank.R6.Nrepl Jank.R8.Nrepl Jank.NreplServer Jank.Analyzer

structure QFix where
  q1 : Bool := true
  q2 : Bool := true
  v37i : Bool := true
  deriving Repr, Inhabited

/-! ## Q1's session input (handler/eval.jank in fixes/Q1.diff) -/

/-- One session's `*in*`: the text not read yet, an end of input sent (an empty stdin), and a `\r`
that ended the last line at the end of the text (a `\n` sent next completes that `\r\n`). -/
structure SIn where
  text : List UInt8 := []
  eof : Bool := false
  skipLf : Bool := false
  deriving BEq, Repr, Inhabited

/-- `add-input`. -/
def addInput (i : SIn) (t : List UInt8) : SIn :=
  if t.isEmpty then { i with eof := true }
  else
    let t := if i.skipLf && t.head? == some 10 then t.drop 1 else t
    { i with text := i.text ++ t, skipLf := false }

/-- The first terminator's index (`(min n r)` of `take-line`). -/
def termIdx (text : List UInt8) : Option Nat :=
  match text.findIdx? (· == 10), text.findIdx? (· == 13) with
  | some a, some b => some (min a b)
  | some a, none => some a
  | none, some b => some b
  | none, none => none

/-- `take-line`: `some (line, in')`, the line `none` at an end of input with no text left, or `none`
when no line is complete and the input has not ended. -/
def takeLine (i : SIn) : Option (Option (List UInt8) × SIn) :=
  match termIdx i.text with
  | some k =>
    let isR := i.text.findIdx? (· == 13) == some k
    let crlf := isR && i.text.findIdx? (· == 10) == some (k + 1)
    let e := if crlf then k + 2 else k + 1
    some (some (i.text.take k), { i with text := i.text.drop e, skipLf := isR && !crlf && e == i.text.length })
  | none =>
    if i.eof then some ((if i.text.isEmpty then none else some i.text), { i with text := [], eof := false })
    else none

/-- `skip-eol`: one end of line left on the input is dropped after every eval of the session. -/
def skipEol (i : SIn) : SIn :=
  match i.text with
  | 13 :: 10 :: r => { i with text := r }
  | [13] => { i with text := [], skipLf := true }
  | 10 :: r => { i with text := r }
  | 13 :: r => { i with text := r }
  | _ => i

def sinName (s : String) : String := s!"\u0000stdin:{s}"
def lfName (s : String) : String := s!"\u0000stdin-lf:{s}"

def sinOf (m : TMem) (s : String) : SIn :=
  match m.temps.find? (·.1 == sinName s), m.temps.find? (·.1 == lfName s) with
  | some (_, b, e), some (_, _, l) => { text := b, eof := e, skipLf := l }
  | some (_, b, e), none => { text := b, eof := e }
  | _, _ => {}

def setEntry (xs : List (String × List UInt8 × Bool)) (n : String) (b : List UInt8) (l : Bool) :
    List (String × List UInt8 × Bool) :=
  if xs.any (·.1 == n) then xs.map fun (n', b', l') => if n' == n then (n, b, l) else (n', b', l')
  else xs ++ [(n, b, l)]

def setSin (m : TMem) (s : String) (i : SIn) : TMem :=
  { m with temps := setEntry (setEntry m.temps (sinName s) i.text i.eof) (lfName s) [] i.skipLf }

/-! ## The fixed handlers -/

def qDescribe (fx : QFix) : JVal :=
  kmap [("aux", .map []),
        ("ops", kmap ((describedOps ++ (if fx.q1 then ["stdin"] else [])).map fun o => (o, .map []))),
        ("versions", kmap [("jank", kmap [("version-string", JVal.s "jank-version")])]),
        ("status", statusOf ["done"])]

/-- Q2: `(filterv some? v)` on a reply vector. -/
def dropNils : JVal → JVal
  | .vec xs => .vec (xs.filter fun x => match x with | .nil => false | _ => true)
  | x => x

def readLineMark : String := "\u0000read-line"
def needMark : String := "\u0000need-input"
def valueMark : String := "\u0000value:"

def needText : String := "need-input: nothing to read on *in*"
def waitMark : String := "\u0000wait:"
def nestedReadMark : String := "\u0000nested-read"

/-- `pr-str` of a string with no line terminator (the lines `take-line` returns). -/
def prStrBytes (b : List UInt8) : String :=
  let esc := b.flatMap fun c => if c == 34 then [92, 34] else if c == 92 then [92, 92] else if c == 9 then [92, 116] else [c]
  "\"" ++ (String.fromUTF8? (ByteArray.mk esc.toArray)).getD "?" ++ "\""

/-- `tEvalInstrs` with the evaluator's four steps replaced by the read-line step. -/
def readLineInstrs (fix : Bool) (req : JVal) : List TCI :=
  (tEvalInstrs fix).flatMap fun i => match i with
    | .bind => [.handlerError req readLineMark]
    | .form | .finishEval | .unbind => []
    | x => [x]

def isReadLineEval (fx : QFix) (ev : TEval) : Bool :=
  fx.q1 && ev.q.code == "(read-line)" && strField ev.req "op" == some "eval"

/-- `tConnStep`'s `.evalReplies` arm with the fixes: Q2 drops the nils, a read-line eval answers
from the read step's outcome. -/
def qEvalReplies (fx : QFix) (c : TConn) (rest : List TCI) : TM (StepResult TTh) := do
  let ev := c.ev
  let m0 ← tmem
  -- do-eval's `(swap! session-inputs ... skip-eol)` after the capture (an entry only if one exists)
  let m0 := match strField ev.req "session" with
    | some s => if fx.q1 && m0.temps.any (·.1 == sinName s) then setSin m0 s (skipEol (sinOf m0 s)) else m0
    | none => m0
  tset { m0 with evals := m0.evals.push { cid := c.cid, id := (strField ev.req "id").getD "", own := ev.own.toList } }
  if isReadLineEval fx ev then
    let outR := outReply ev.stdout
    let errR := errReply ev.stderr
    let v : JVal :=
      if ev.success then
        .vec [outR, errR, kmap [("value", JVal.s ((ev.q.file.drop valueMark.length).toString)), ("ns", JVal.s "user")],
              kmap [("status", statusOf ["done"])]]
      else
        .vec [outR, errR, kmap [("err", JVal.s needText)],
              kmap [("ex", JVal.s needText), ("status", statusOf ["done", "eval-error"])]]
    let v := if fx.q2 then dropNils v else v
    return .ran (.conn { c with instrs := .writeOut ev.req (responsesFor ev.req v) :: rest })
  let (s', r, printed) := doEvalRepliesOut (esOf (← tmem) c) ev.success ev.resNs ev.stdout ev.stderr ev.q.inspect
  let m1 := printed.foldl (fun m e => match e with
    | .out b => m.fwriteOut b
    | .err b => m.writeFd 2 b) { (← tmem) with jw := s'.w }
  tset m1
  match r with
  | .ok resp =>
    let resp := if fx.q2 then dropNils resp else resp
    pure (.ran (.conn { c with tb := s'.tb, instrs := .writeOut ev.req (responsesFor ev.req resp) :: rest }))
  | .error msg => pure (.ran (.conn { c with tb := s'.tb, instrs := .handlerError ev.req msg :: rest }))

/-- World TQ's connection step. -/
def qConnStep (fx : QFix) (t : Nat) (c : TConn) : TM (StepResult TTh) := do
  match c.instrs with
  | .dispatch req :: rest =>
    let reply (r : JVal) : TM (StepResult TTh) := pure (tsetConn c (.writeOut req (responsesFor req r) :: rest))
    match strField req "op" with
    | some "stdin" =>
      if !fx.q1 then tConnStep t c else
      let m ← tmem
      if let some s := strField req "session" then
        let text := match jget req (JVal.s "stdin") with
          | .str b => b
          | _ => []
        tset (setSin m s (addInput (sinOf m s) text))
      reply (kmap [("status", statusOf ["done"])])
    | some "describe" => if fx.q1 then reply (qDescribe fx) else tConnStep t c
    | some "interrupt" =>
      if !fx.v37i then tConnStep t c else
      if (strField req "session").isSome then reply (kmap [("status", statusOf ["session-idle", "done"])])
      else reply (kmap [("status", statusOf ["error", "session-ephemeral", "done"])])
    | some "eval" =>
      if fx.q1 && strField req "code" == some "(read-line)" then
        let m ← tmem
        let q : EvalReq := { ns := strField req "ns", code := "(read-line)", file := (strField req "file").getD "NO_SOURCE_PATH" }
        match doEvalPre m.jw q with
        | .reply r => reply r
        | .run target =>
          let ev : TEval := { req, q := { q with ns := some target } }
          pure (.ran (.conn { c with ev, instrs := readLineInstrs m.cfg.fixCapture req ++ rest }))
      else tConnStep t c
    | _ => tConnStep t c
  | .handlerError req mark :: rest =>
    let fail : TM (StepResult TTh) :=
      pure (.ran (.conn { c with ev := { c.ev with success := false, q := { c.ev.q with file := needMark } }, instrs := rest }))
    if mark.startsWith waitMark then
      -- core.jank `wait-input`'s loop: the input changed (back to the read), the client gone
      -- (the read fails), else read and handle the next request on this connection
      let m ← tmem
      let s := (strField c.ev.req "session").getD ""
      if toString (repr (sinOf m s)) != (mark.drop waitMark.length).toString then
        return tsetConn c (.handlerError req readLineMark :: rest)
      if !c.connected then return (← fail)
      return tsetConn c (.handlerError req nestedReadMark :: .handlerError req mark :: rest)
    if mark == nestedReadMark then
      -- `next-request`: round 3's `.readMsg`, then the request dispatched with this wait after it
      match ← tConnStep t { c with instrs := [.readMsg] } with
      | .ran (.conn c') =>
        match c'.instrs with
        | [.top (some v)] =>
          match strField v "op" with
          | some "eval" | some "load-file" =>
            tnote "an eval while another eval of this connection waits for input: outside World TQ (one eval slot per connection)"
            throw .limit
          | _ => return .ran (.conn { c' with instrs := .dispatch v :: rest })
        | [.top none] => return .ran (.conn { c' with instrs := rest })
        | _ => return .ran (.conn { c' with instrs := c'.instrs ++ rest })
      | r => return r
    if mark != readLineMark then tConnStep t c else
    let m ← tmem
    match strField c.ev.req "session" with
    | none => fail
    | some s =>
      match takeLine (sinOf m s) with
      | none =>
        -- `session-reader` calls `*wait-input*`: need-input, then the wait (from what the input is now)
        let need := responsesFor req (kmap [("status", statusOf ["need-input"])])
        pure (tsetConn c (.writeOut req need :: .handlerError req (waitMark ++ toString (repr (sinOf m s))) :: rest))
      | some (line, i') =>
        tset (setSin m s i')
        let v := match line with
          | some l => prStrBytes l
          | none => "nil"
        pure (.ran (.conn { c with ev := { c.ev with success := true, q := { c.ev.q with file := valueMark ++ v } }, instrs := rest }))
  | .evalReplies :: rest => if fx.q1 || fx.q2 then qEvalReplies fx c rest else tConnStep t c
  | _ => tConnStep t c

/-- World TQ's step (round 3's for the acceptor and the clients). -/
def qStep (fx : QFix) (t : Nat) : TTh → TM (StepResult TTh)
  | .conn c => qConnStep fx t c
  | other => tStep t other

/-- World TQ's step with World T8's diverging evals (Diverge.lean `t8Step`, the same rule). -/
def qStep8 (fx : QFix) (t : Nat) (th : TTh) : TM (StepResult TTh) :=
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
        | _ => qConnStep fx t c
      | _ => qConnStep fx t c
    | _ => qConnStep fx t c
  | other => tStep t other

/-- The same with the spinning step reported as blocked (Diverge.lean `t8StepB`'s rule): the
quiescent states of a bounded exploration. -/
def qStep8B (fx : QFix) (t : Nat) (th : TTh) : TM (StepResult TTh) :=
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
        | _ => qConnStep fx t c
      | _ => qConnStep fx t c
    | _ => qConnStep fx t c
  | other => tStep t other

/-! ## The properties at a state: every reply has content; every request's replies end in one done -/

def replyKeys (r : JVal) : List String :=
  match r with
  | .map kvs => kvs.filterMap fun (k, _) => match k with
      | .str b => String.fromUTF8? (ByteArray.mk b.toArray)
      | _ => none
  | _ => []

/-- A reply holding nothing but the id and session (Q2's message). -/
def emptyReply (r : JVal) : Bool := (replyKeys r).all fun k => k == "id" || k == "session"

/-- Every reply any client's socket carries that holds only the id and session. -/
def emptyReplies (m : TMem) : List (Nat × String) := Id.run do
  let mut out := []
  for cid in [0:m.socks.size] do
    for r in outboxReplies (m.socks.getD cid {}) do
      if emptyReply r then out := out ++ [(cid, (strField r "id").getD "-")]
  return out

/-- The request ids of a client's script: `tReqId` for a request it waits on, the bencoded `id` of a
raw one. -/
def scriptIds (cid : Nat) (script : List TReq) : List String :=
  script.zipIdx.filterMap fun (r, k) => match r with
    | .raw b => match specDecode b with
      | .msg v _ => strField v "id"
      | _ => none
    | _ => some (tReqId cid k)

/-- Round 3's protocol property for every request, raw ones included, read from the sockets: its
replies carry its id (and session when it sent one) and contain exactly one done, the last. `none`
when it holds; for a request with no reply, "unanswered". -/
def protocolAt (scripts : List (List TReq)) (m : TMem) (needAll : Bool) : Option String := Id.run do
  for (sc, cid) in scripts.zipIdx do
    let rs := outboxReplies (m.socks.getD cid {})
    for id in scriptIds cid sc do
      let mine := rs.filter fun r => strField r "id" == some id
      if mine.isEmpty then
        if needAll then return some s!"client {cid} {id}: unanswered"
        continue
      let dones := mine.filter (hasStatus · "done")
      if dones.length != 1 then return some s!"client {cid} {id}: {dones.length} done replies"
      if !(hasStatus mine.getLast! "done") then return some s!"client {cid} {id}: a reply after done"
  return none

end Jank.R9.Nrepl
