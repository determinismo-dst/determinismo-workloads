import Jank.R3.Nrepl.Handler
import Jank.R3.Nrepl.CljEval

/-!
# Round 3, nREPL: World S — one connection, requests from a grammar, jank beside the spec

A timeline is a script of requests drawn from a grammar (decisions `req.*`). Each request is
handled by jank's handlers on the wired evaluator (the same functions World T steps through), with
no other thread: `with-capture` then captures exactly what the evaluation wrote. The spec handles
the same request in its own process (Clojure's namespaces and vars, the nREPL session's bindings).

Properties (each mismatch is named by its class, so a census counts them):

- `no hang` — an eval returns (REPORT-2 R1: a NUL byte);
- `the process stays up` — no stack overflow, no abort;
- `replies are written` — `bencode/write` succeeds on every reply (else core.jank's handler error);
- `eval value` — the `:value`s are the spec's (REPL: one per form; load-string: the last), the
  `:ns` beside the last is the spec's `*ns*`, `eval-error` iff the spec saw an exception;
- `eval output` — `:out` is exactly what the evaluation printed;
- `lookup finds what ns-resolve finds` — on jank's own namespaces (Clojure's `ns-resolve`:
  aliases of the given namespace);
- `completions` — every `ns-map` key with the prefix is a candidate.
-/

namespace Jank.R3.Nrepl

open Jank.Analyzer Determinismo
open Jank.NreplServer (JVal kmap statusOf strField)

/-! ## Requests -/

inductive SReq where
  /-- `eval` in session `sess` (the client's `sess`-th clone), with an optional `ns` and `file`. -/
  | eval (code : String) (ns : Option String) (sess : Nat := 0) (file : Option String := none)
  | loadFile (content : String) (ns : Option String) (sess : Nat := 0)
  | lookup (ns sym : String)
  | info (ns sym : String)
  | completions (ns pfx : String)
  deriving Repr, Inhabited, BEq

def SReq.show : SReq → String
  | .eval c ns sess file => s!"eval {repr c}{match ns with | some n => " ns=" ++ n | none => ""}{if sess != 0 then s!" session={sess}" else ""}{match file with | some f => " file=" ++ f | none => ""}"
  | .loadFile c ns _ => s!"load-file {repr c}{match ns with | some n => " ns=" ++ n | none => ""}"
  | .lookup n s => s!"lookup ns={n} sym={s}"
  | .info n s => s!"info ns={n} sym={s}"
  | .completions n p => s!"completions ns={n} prefix={p}"

def SReq.session : SReq → Option Nat
  | .eval _ _ s _ | .loadFile _ _ s => some s
  | _ => none

def sessName (k : Nat) : String := s!"s{k}"

/-- The request map a client sends. -/
def SReq.toJVal (id : String) : SReq → JVal
  | .eval code ns sess file => .map ([(JVal.s "op", JVal.s "eval"), (JVal.s "id", JVal.s id), (JVal.s "session", JVal.s (sessName sess)),
      (JVal.s "code", JVal.s code)] ++ (match ns with | some n => [(JVal.s "ns", JVal.s n)] | none => [])
      ++ (match file with | some f => [(JVal.s "file", JVal.s f)] | none => []))
  | .loadFile c ns sess => .map ([(JVal.s "op", JVal.s "load-file"), (JVal.s "id", JVal.s id), (JVal.s "session", JVal.s (sessName sess)),
      (JVal.s "file", JVal.s c)] ++ (match ns with | some n => [(JVal.s "ns", JVal.s n)] | none => []))
  | .lookup n s => .map [(JVal.s "op", JVal.s "lookup"), (JVal.s "id", JVal.s id), (JVal.s "session", JVal.s (sessName 0)),
      (JVal.s "ns", JVal.s n), (JVal.s "sym", JVal.s s)]
  | .info n s => .map [(JVal.s "op", JVal.s "info"), (JVal.s "id", JVal.s id), (JVal.s "session", JVal.s (sessName 0)),
      (JVal.s "ns", JVal.s n), (JVal.s "sym", JVal.s s)]
  | .completions n p => .map [(JVal.s "op", JVal.s "completions"), (JVal.s "id", JVal.s id), (JVal.s "session", JVal.s (sessName 0)),
      (JVal.s "ns", JVal.s n), (JVal.s "prefix", JVal.s p)]

/-! ## jank's side of one request (no other thread) -/

/-- What jank answered: the replies a client decodes, and how the eval ended. -/
structure JankAns where
  replies : List JVal
  /-- The thread never returned. -/
  hang : Option String := none
  crash : Option String := none
  unsupported : Option String := none
  /-- `do-eval`'s `pr-str`, or `bencode/write`, threw: core.jank's handler error. -/
  handlerError : Option String := none
  /-- A reply the client cannot decode. -/
  badBytes : Option String := none
  deriving Inhabited

/-- core.jank `handle-client`'s writing (79–106): `responses-for`, then each reply through
`bencode/write`; an exception (a reply that cannot be written) is answered `{:status [:error
:done] :err ...}` and the rest of the request's replies are dropped. The client decodes every reply
with the spec decoder (string keys); bytes it cannot decode are reported in the second result. -/
def writeReplies (req : JVal) (resp : JVal) : List JVal × Option String × Option String := Id.run do
  let mut out : Array JVal := #[]
  let decode (b : List UInt8) : Option JVal := match Jank.NreplServer.specDecode b with
    | .msg v [] => some v
    | _ => none
  for r in Jank.NreplServer.responsesFor req resp do
    match Jank.NreplServer.write r with
    | .ok b =>
      match decode b with
      | some v => out := out.push v
      | none => return (out.toList, none, some s!"cannot decode \"{Jank.NreplServer.showBytes b}\"")
    | .error e =>
      let he := Jank.NreplServer.responseFor req (kmap [("status", statusOf ["error", "done"]),
        ("err", JVal.s s!"An exception was thrown from the nREPL handler:{e}")])
      match (Jank.NreplServer.write he).toOption.bind decode with
      | some v => out := out.push v
      | none => pure ()
      return (out.toList, some e, none)
  return (out.toList, none, none)

/-- jank's state for World S: the process and its one connection thread. -/
structure JConn where
  s : ES
  debug : Bool := false
  deriving Inhabited

def JConn.start (connNs : String := "user") : JConn :=
  let w := jankBase
  let (h, tb) := connTB w.heap connNs
  { s := { w := { w with heap := h }, tb } }

/-- `do-eval` (handler/eval.jank:22) run to its end. -/
def jankDoEval (c : JConn) (req : JVal) (q : EvalReq) : JConn × JankAns :=
  match doEvalPre c.s.w q with
  | .reply r =>
    let (rs, he, bad) := writeReplies req r
    (c, { replies := rs, handlerError := he, badBytes := bad })
  | .run target =>
    let s := c.s
    let (h, nso) := s.w.heap.nsObj target
    let s := { s with w := { s.w with heap := h }, tb := s.tb.push [(vNs, nso), (vFile, str q.file)] }
    let (s, e, out, _) := runSafeEval s q.code.toUTF8.toList q.file c.debug
    match e with
    | .hang w => ({ c with s }, { replies := [], hang := some w })
    | .crash w => ({ c with s }, { replies := [], crash := some w })
    | .unsupported w => ({ c with s }, { replies := [], unsupported := some w })
    | _ =>
      let success := match e with | .ok _ => true | _ => false
      let resNs := curNsName s
      let s := { s with tb := s.tb.pop }
      let errs := out.flatMap fun ev => match ev with | .err b => b | _ => []
      let (s, r) := doEvalReplies s success resNs (outBytes out) errs q.inspect
      match r with
      | .ok resp =>
        let (rs, he, bad) := writeReplies req resp
        ({ c with s }, { replies := rs, handlerError := he, badBytes := bad })
      | .error m =>
        let (rs, _, bad) := writeReplies req (kmap [("status", statusOf ["error", "done"]),
          ("err", JVal.s s!"An exception was thrown from the nREPL handler:{m}")])
        ({ c with s }, { replies := rs, handlerError := some m, badBytes := bad })

def jankHandle (c : JConn) (id : String) (q : SReq) : JConn × JankAns :=
  let req := q.toJVal id
  match q with
  | .eval code ns _ file => jankDoEval c req { ns, code, file := file.getD "NO_SOURCE_PATH" }
  | .loadFile content ns _ => jankDoEval c req { ns, code := content, inspect := some false }
  | .lookup .. | .info .. =>
    let cur := curNsName c.s
    let (rs, he, bad) := writeReplies req (lookupReply c.s.w cur req)
    (c, { replies := rs, handlerError := he, badBytes := bad })
  | .completions .. =>
    let (rs, he, bad) := writeReplies req (completionsReply c.s.w req)
    (c, { replies := rs, handlerError := he, badBytes := bad })

/-! ## The spec's side -/

structure SConn where
  w : SW := cljBase
  /-- The client's sessions (nREPL keeps each one's bindings). -/
  sessions : Array Session := #[{}, {}]
  /-- A second spec process run as jank runs the requests (one session, `user` without an `ns`
  field): the R127 label. -/
  jw : SW := cljBase
  jsess : Session := {}
  deriving Inhabited

/-! ## The judge -/

def fieldStrs (rs : List JVal) (k : String) : List String := rs.filterMap (strField · k)

def hasStatus (r : JVal) (x : String) : Bool :=
  match Jank.NreplServer.jget r (JVal.s "status") with
  | .vec xs => xs.any (· == JVal.s x)
  | _ => false

/-- The protocol: replies decode, carry the request's id and session, and end with exactly one
`done` (the last). -/
def judgeProtocol (q : SReq) (id : String) (j : JankAns) : Option (String × String) := Id.run do
  if let some b := j.badBytes then return some ("replies are well-formed bencode", s!"{q.show}: {b}")
  let sess := sessName (q.session.getD 0)
  for r in j.replies do
    if strField r "id" != some id || strField r "session" != some sess then
      return some ("every reply carries the request's id and session", s!"{q.show}: {JVal.render r}")
  match j.replies.findIdx? (hasStatus · "done") with
  | none => return some ("a request's replies end with done", s!"{q.show}: no done in {j.replies.map JVal.render}")
  | some i =>
    if i + 1 != j.replies.length then
      return some ("a request's replies end with done", s!"{q.show}: replies after done")
  return none

def bytesShow (b : List UInt8) : String := Jank.NreplServer.showBytes b

/-- Normalizations that set a known class aside (residual searches). -/
structure Aside where
  /-- R136: whitespace-only output dropped: compare `:out` only when the spec's is not blank. -/
  blankOut : Bool := false
  /-- R127: the spec runs every eval in session 0, in `user` when the request names no `ns`. -/
  sessions : Bool := false
  /-- The spec's variants turned on. -/
  variant : Variant := {}
  /-- Lookups that fail with a round-2 signature (R111 alias, R131 nil arglists, R138 no
  `:module`) are not counted. -/
  lookupKnown : Bool := false
  /-- N2: a lookup in a namespace that does not exist answers for `user`. -/
  lookupFallback : Bool := false
  /-- A load-file's `:ns` names the namespace the file switched to (Compiler.load restores it). -/
  loadNs : Bool := false
  deriving Repr, Inhabited

/-- The first property a request's answer breaks, with its class (`[Rn]` when it is the signature
of a round-2 entry). -/
def judgeEval (mode : SpecMode) (aside : Aside) (q : SReq) (j : JankAns) (sp : SpecEvalOut) :
    Option (String × String) := Id.run do
  let rs := j.replies
  let values := fieldStrs rs "value"
  let nss := fieldStrs rs "ns"
  let out := rs.flatMap fun r => match Jank.NreplServer.jget r (JVal.s "out") with
    | .str b => b
    | _ => []
  let jErr := rs.any (hasStatus · "eval-error")
  let spValues := sp.items.filterMap fun i => match i with | .value v _ => some v | _ => none
  let spErr := sp.items.any (· == .error)
  let spLastNs := (sp.items.filterMap fun i => match i with | .value _ n => some n | _ => none).getLast?
  if let some he := j.handlerError then
    let cls := if (he.splitOn "cannot write").length > 1 || (he.splitOn "Unexpected data type").length > 1
      then "eval value: handler error (bencode write)" else "eval value: handler error from pr-str [R126]"
    return some (cls, s!"{q.show}: jank answers a handler error ({he}); spec {repr sp.items}")
  if sp.items.isEmpty && values == ["0.0"] then
    return some ("eval value: no form gives 0.0 [R132]", s!"{q.show}: jank values {values}, spec none")
  if jErr != spErr then
    return some ("eval value: error", s!"{q.show}: jank eval-error {jErr}, spec {repr sp.items} ({repr mode})")
  if values != spValues then
    let cls := if values.length != spValues.length then "eval value: count" else "eval value: text"
    return some (cls, s!"{q.show}: jank values {values}, spec {spValues} ({repr mode})")
  let isLoad := match q with | .loadFile .. => true | _ => false
  if !values.isEmpty && nss.getLast? != spLastNs && !(isLoad && aside.loadNs) then
    let cls := if isLoad then "eval value: ns (load-file: the file's ns switch is not undone)" else "eval value: ns"
    return some (cls, s!"{q.show}: jank :ns {nss}, spec {spLastNs}")
  let blankSpec := sp.out.all Jank.NreplServer.cIsspace
  if out != sp.out && !(aside.blankOut && blankSpec) then
    let cls := if out.isEmpty && blankSpec then "eval output: whitespace dropped [R136]" else "eval output"
    return some (cls, s!"{q.show}: jank :out \"{bytesShow out}\", spec \"{bytesShow sp.out}\"")
  return none

/-- Clojure's `ns-resolve` of `sym` in namespace `ns` of jank's own namespaces. -/
def expectLookup (w : JW) (ns sym : String) : Option VarRef :=
  (w.nss.find? (·.name == ns)).bind fun n => cljNsResolve w.nss n (Jank.NreplServer.splitSym sym)

def judgeLookup (aside : Aside) (w : JW) (q : SReq) (j : JankAns) : Option (String × String) :=
  match q with
  | .lookup ns sym | .info ns sym =>
    let isInfo := match q with | .info .. => true | _ => false
    let expected := expectLookup w ns sym
    let got := j.replies.any fun r =>
      if isInfo then Jank.NreplServer.jget r (JVal.s "name") != .nil else Jank.NreplServer.jget r (JVal.s "info") != .nil
    if expected.isSome != got then
      let label := match expected with
        | some r =>
          if r == ({ ns := "clojure.core", name := "iteration" } : VarRef) then some "R131 arglists hold nil"
          else if !Jank.NreplServer.coreModules.contains r.ns && j.handlerError.isSome then some "R138 no :module outside core modules"
          else if (Jank.NreplServer.splitSym sym).1.isSome then some "R111 alias resolved in *ns*"
          else none
        | none =>
          if (w.nss.find? (·.name == ns)).isNone then some "N2 unknown ns falls back to user" else none
      if aside.lookupKnown && label.isSome && label != some "N2 unknown ns falls back to user" then none else
      if aside.lookupFallback && label == some "N2 unknown ns falls back to user" then none else
      let cls := (if j.handlerError.isSome then "lookup: handler error" else "lookup: info")
        ++ (match label with | some l => s!" [{l}]" | none => "")
      some (cls, s!"{q.show}: ns-resolve gives {(expected.map fun r => r.ns ++ "/" ++ r.name).getD "nil"}, the replies {(j.replies.map JVal.render)}")
    else none
  | .completions ns pfx =>
    match w.nss.find? (·.name == ns) with
    | none => none
    | some n =>
      let want := (n.mappings.map (·.1)).filter (·.startsWith pfx)
      let got := j.replies.flatMap fun r => match Jank.NreplServer.jget r (JVal.s "completions") with
        | .vec cs => cs.filterMap (strField · "candidate")
        | _ => []
      let missing := want.filter (!got.contains ·)
      if !missing.isEmpty then some ("completions", s!"{q.show}: missing {missing}") else none
  | _ => none

/-! ## The grammar -/

/-- Code fragments: one form each (or a reader error, or no form). -/
structure Grammar where
  name : String
  forms : List String
  /-- Code strings are 1 or 2 fragments joined by a space. -/
  pairs : Bool := true
  /-- `ns` fields drawn for evals. -/
  nsFields : List (Option String) := [some "user", none]
  /-- Sessions drawn for evals (the client cloned two). -/
  sessions : Nat := 1
  /-- `file` fields drawn for evals. -/
  files : List (Option String) := [none]
  /-- lookup/completions/info requests drawn beside evals. -/
  queries : List SReq := []
  /-- load-file contents drawn beside evals. -/
  loadFiles : List String := []
  /-- Requests per timeline. -/
  len : Nat := 3
  deriving Inhabited

structure SWorld where
  decisions : Decisions := {}
  /-- The requests so far (labels replay them on a variant of the spec). -/
  history : Array SReq := #[]
  j : JConn
  sp : SConn
  log : Array String := #[]
  /-- Timelines cut because the model left its grammar. -/
  outside : Option String := none

instance : Chaotic SWorld where
  decisions w := w.decisions
  setDecisions w d := { w with decisions := d }

abbrev SWM := EStateM Stop SWorld

def drawCode (g : Grammar) : SWM String := do
  let n := g.forms.length
  let a ← decide (σ := SWorld) "req.form" n
  let first := g.forms.getD a ""
  if !g.pairs then return first
  let two ← decide (σ := SWorld) "req.more" 2
  if two == 0 then return first
  let b ← decide (σ := SWorld) "req.form2" n
  return first ++ " " ++ g.forms.getD b ""

def drawSReq (g : Grammar) : SWM SReq := do
  let kinds := 1 + (if g.queries.isEmpty then 0 else 1) + (if g.loadFiles.isEmpty then 0 else 1)
  let k ← decide (σ := SWorld) "req.kind" kinds
  if k == 1 && !g.queries.isEmpty then
    let i ← decide (σ := SWorld) "req.query" g.queries.length
    return g.queries.getD i default
  if k ≥ 1 then
    let i ← decide (σ := SWorld) "req.load" g.loadFiles.length
    let nsi ← decide (σ := SWorld) "req.ns" g.nsFields.length
    return .loadFile (g.loadFiles.getD i "") (g.nsFields.getD nsi none)
  let code ← drawCode g
  let nsi ← decide (σ := SWorld) "req.ns" g.nsFields.length
  let sess ← decide (σ := SWorld) "req.session" g.sessions
  let fi ← decide (σ := SWorld) "req.file" g.files.length
  return .eval code (g.nsFields.getD nsi none) sess (g.files.getD fi none)

/-- One timeline of World S. -/
def sBody (g : Grammar) (mode : SpecMode) (aside : Aside) : SWM Unit := do
  for k in [0:g.len] do
    let q ← drawSReq g
    let w ← get
    let id := s!"r{k}"
    let (j', ans) := jankHandle w.j id q
    modify fun w => { w with j := j', log := w.log.push s!"{id} {q.show} → jank {(ans.replies.map JVal.render)}" }
    let w ← get
    modify fun w => { w with history := w.history.push q }
    if let some h := ans.hang then
      throw (.violation "no hang" s!"{q.show}: the connection thread never returns ({h})")
    if let some c := ans.crash then
      throw (.violation "the process stays up" s!"{q.show}: {c}")
    if let some u := ans.unsupported then
      modify fun w => { w with outside := some u }
      throw .limit
    if let some (p, d) := judgeProtocol q id ans then throw (.violation p d)
    match q with
    | .eval code ns sess _ | .loadFile code ns sess =>
      let sess := if aside.sessions then 0 else sess
      let ses := w.sp.sessions.getD sess {}
      let nsO := if aside.sessions then some (ns.getD "user") else ns
      let lsMode := match q with | .loadFile .. => SpecMode.loadString | _ => mode
      -- do-eval's checks: no code, unknown namespace (jank's own replies; checked by the protocol)
      if code.isEmpty then continue
      if let some n := nsO then
        if (w.sp.w.nss.find? (·.name == n)).isNone then
          if ans.replies.any (hasStatus · "namespace-not-found") then continue
      let isLoad := match q with | .loadFile .. => true | _ => false
      let (sw, ses', o) := specEval w.sp.w ses code nsO lsMode aside.variant isLoad
      let (jw', jsess', oj) := specEval w.sp.jw w.sp.jsess code (some (ns.getD "user")) lsMode aside.variant isLoad
      modify fun w => { w with sp := { w.sp with w := sw, sessions := w.sp.sessions.set! sess ses', jw := jw', jsess := jsess' }
                               log := w.log.push s!"   spec {repr o.items} out \"{bytesShow o.out}\"" }
      if let some u := o.unsupported then
        modify fun w => { w with outside := some s!"spec: {u}" }
        throw .limit
      if let some (p, d) := judgeEval lsMode aside q ans o then
        -- Label: a variant of the spec (adopting one known jank behavior, from the start of the
        -- timeline) under which this request does not break this property.
        let explains (o' : SpecEvalOut) : Bool := match judgeEval lsMode aside q ans o' with
          | none => true
          | some (p', _) => p' != p
        let hist := w.history
        let replay (v : Variant) (asJank : Bool) (m : SpecMode) : SpecEvalOut := Id.run do
          let mut sc : SConn := {}
          for h in hist do
            match h with
            | .eval c n se _ | .loadFile c n se =>
              if c.isEmpty then continue
              let il := match h with | .loadFile .. => true | _ => false
              let se := if asJank || aside.sessions then 0 else se
              let n := if asJank || aside.sessions then some (n.getD "user") else n
              if let some nn := n then
                if (sc.w.nss.find? (·.name == nn)).isNone then continue
              let (sw, ss, _) := specEval sc.w (sc.sessions.getD se {}) c n (if il then .loadString else m) v il
              sc := { sc with w := sw, sessions := sc.sessions.set! se ss }
            | _ => pure ()
          let se := if asJank || aside.sessions then 0 else sess
          let n := if asJank || aside.sessions then some (ns.getD "user") else nsO
          let (_, _, o') := specEval sc.w (sc.sessions.getD se {}) code n (if isLoad then .loadString else m) v isLoad
          return o'
        let label := Variant.all.findSome? fun (name, v) =>
          if aside.variant.join v == aside.variant then none else
          if explains (replay (aside.variant.join v) false lsMode) then some name else none
        -- R31: a macro's expansion carries `:jank/macro-expansion` at run time (with a file).
        let label := label <|> (if ((d.splitOn "jank/macro-expansion").length > 1) then some "R31 macro-expansion meta (the request has a file)" else none)
        -- NA1: REPL (a value per form, *1 per form, the loop going on after an exception) against
        -- load-string (jank's design: one value, the first exception ends it).
        let label := label <|> (if lsMode != .repl then none else
          if explains (replay aside.variant false .loadString) then some "NA1 REPL per form vs one value per eval" else none)
        -- R127: the session's own state (another session's *1, the *ns* a previous eval left):
        -- the spec run as jank runs the requests (one session, `user` without an ns field).
        let label := label <|> (if aside.sessions then none else
          if explains (replay aside.variant true lsMode) then some "R127 sessions keep no state" else none)
        let p := match label with
          | some l => p ++ s!" [{l}]"
          | none => p
        throw (.violation p d)
    | _ =>
      if let some (p, d) := judgeLookup aside (← get).j.s.w q ans then throw (.violation p d)

def runS (g : Grammar) (mode : SpecMode) (aside : Aside) (source : Source) : Ended × SWorld :=
  let w0 : SWorld := { decisions := { source, limit := 10000 }, j := JConn.start, sp := {} }
  match (sBody g mode aside).run w0 with
  | .ok _ w => ({ taken := w.decisions.taken, violation := none }, w)
  | .error (.violation p d) w => ({ taken := w.decisions.taken, violation := some (p, d) }, w)
  | .error .limit w => ({ taken := w.decisions.taken, violation := none }, w)
  | .error (.nodeDown _) w => ({ taken := w.decisions.taken, violation := none }, w)

/-- Census over every timeline (all classes counted; a cut timeline counts as `outside`). -/
structure Census where
  runs : Nat := 0
  complete : Bool := false
  counts : List (String × Nat) := []
  examples : List (String × String) := []
  /-- The decisions of each class's first example. -/
  tapes : List (String × Array Nat) := []
  outside : Nat := 0
  outsideEx : List String := []
  deriving Inhabited

def censusS (g : Grammar) (mode : SpecMode) (aside : Aside) (maxRuns : Nat) (pre : Array Nat := #[]) : Census := Id.run do
  let mut path : Array Nat := pre
  let mut c : Census := {}
  for i in List.range maxRuns do
    let (o, w) := runS g mode aside (Source.path path)
    c := { c with runs := i + 1 }
    if let some u := w.outside then
      c := { c with outside := c.outside + 1, outsideEx := if c.outsideEx.length < 3 && !c.outsideEx.contains u then c.outsideEx ++ [u] else c.outsideEx }
    if let some (p, d) := o.violation then
      let counts := match c.counts.lookup p with
        | some n => (p, n + 1) :: c.counts.filter (·.1 != p)
        | none => (p, 1) :: c.counts
      let examples := if (c.examples.lookup p).isSome then c.examples else c.examples ++ [(p, d)]
      let tapes := if (c.tapes.lookup p).isSome then c.tapes else c.tapes ++ [(p, o.taken.map (·.value))]
      c := { c with counts, examples, tapes }
    -- stay under the prefix
    let next := nextPath o.taken
    match next with
    | none => return { c with complete := true }
    | some q =>
      if q.size < pre.size || (q.extract 0 pre.size) != pre then return { c with complete := true }
      path := q
  return c

end Jank.R3.Nrepl
