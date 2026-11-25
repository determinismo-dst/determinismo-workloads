import Jank.Nrepl.Server

/-!
# The spec, the properties, the searches

## The spec (assumption A1)

The nREPL protocol as jank's own sources and book describe it (the nREPL documentation is not on
the allowed list): requests are bencode dicts with `op`, `id`, `session`; every reply carries the
request's `id` and `session`; a request's replies end with one whose `status` holds `done`;
`describe` lists the ops the server handles; `eval` sends `out`/`err` for what the evaluation
printed, a `value` (with `ns`) per evaluated form, then `done`, or `ex` with `eval-error`;
`lookup` gives `info` for a symbol that resolves in the given namespace (Clojure's `ns-resolve`),
else `error`. Clojure's semantics for evaluation: code with no form evaluates nothing (no value;
`load-string` of it is nil); output is what `print`/`println` wrote, newlines included.

## Properties (judged at the end of each timeline; a hang is a deadlock of the threads)

- `the process stays up`
- `every request gets a done reply (no hang)`
- `replies are well-formed bencode` (the client decodes them with the spec decoder)
- `every reply carries the request's id and session`
- `a request's replies end with done`
- `eval output reaches its client` (exact bytes)
- `eval value` (an eval with forms: one value, the last form's; with none: no value or nil)
- `describe lists the ops the server handles`
- `lookup finds what ns-resolve finds in that namespace`
- `clone gives a new session id` (the session table: distinct ids; linearizable as a set of
  fresh ids)
-/

namespace Jank.NreplServer

open Determinismo

/-! ## Spec of an eval -/

structure SpecEval where
  out : Bytes
  value : Option String
  error : Bool
  deriving Repr, Inhabited

/-- Clojure: the forms run in order; `print`/`println` write to the eval's `*out*`; a throw ends
it; the value is the last form's; no form, no value. -/
def specEval (code : String) : SpecEval := Id.run do
  let mut out : Bytes := []
  let mut last : Option RVal := none
  for f in program code do
    match f with
    | .lit v => last := some v
    | .print s => out := out ++ bytes s; last := some .nil
    | .println s => out := out ++ bytes s ++ [10]; last := some .nil
    | .throw _ => return { out, value := none, error := true }
  return { out, value := last.map RVal.pr, error := false }

/-! ## The judgment -/

def repliesOf (m : Mem) (s : Sent) : List JVal :=
  (m.replies.toList.filter fun (cid, r) => cid == s.cid && strField r "id" == some s.id).map (·.2)

def fieldBytes (r : JVal) (k : String) : Bytes :=
  match jget r (JVal.s k) with
  | .str b => b
  | _ => []

def statusHas (r : JVal) (x : String) : Bool :=
  match jget r (JVal.s "status") with
  | .vec xs => xs.any (· == JVal.s x)
  | _ => false

def mapKeys (r : JVal) : List String :=
  match r with
  | .map kvs => kvs.filterMap fun (k, _) => match k with
    | .str b => String.fromUTF8? (ByteArray.mk b.toArray)
    | _ => none
  | _ => []

/-- The first property a finished timeline breaks. -/
def judge (m : Mem) : Option (String × String) := Id.run do
  if let some c := m.crashed then return some ("the process stays up", c)
  for s in m.sent do
    let rs := repliesOf m s
    -- ids and sessions
    if let some sess := s.session then
      for r in rs do
        if strField r "session" != some sess then
          return some ("every reply carries the request's id and session",
            s!"{s.id}: a reply {JVal.render r} lacks session {sess}")
    match rs.findIdx? isDone with
    | none => return some ("a request's replies end with done", s!"{s.id}: no done among {rs.length} replies")
    | some i =>
      if i + 1 != rs.length then
        return some ("a request's replies end with done", s!"{s.id}: {rs.length - i - 1} replies after done")
    match s.req with
    | .eval _ code _ inspect =>
      let sp := specEval code
      let out := rs.flatMap (fieldBytes · "out")
      if out != sp.out then
        return some ("eval output reaches its client",
          s!"{s.id} eval {repr code}{if inspect.isSome then " (inspect)" else ""}: :out \"{showBytes out}\", Clojure \"{showBytes sp.out}\"")
      let values := rs.filterMap (strField · "value")
      if sp.error then
        if !rs.any (statusHas · "eval-error") then
          return some ("eval value", s!"{s.id} eval {repr code}: no eval-error")
      else if inspect.isNone then
        match sp.value with
        | some v =>
          if values != [v] then
            return some ("eval value", s!"{s.id} eval {repr code}: values {values}, Clojure [{v}]")
        | none =>
          if !(values.all (· == "nil")) then
            return some ("eval value",
              s!"{s.id} eval {repr code} (no form): values {values}, Clojure none (load-string: nil)")
    | .loadFile _ file =>
      let sp := specEval file
      let values := rs.filterMap (strField · "value")
      if sp.value.isNone && !(values.all (· == "nil")) then
        return some ("eval value",
          s!"{s.id} load-file {repr file} (no form): values {values}, Clojure nil")
    | .describe =>
      for r in rs do
        let ops := mapKeys (jget r (JVal.s "ops"))
        if !rs.isEmpty && (jget r (JVal.s "ops")) != .nil then
          let missing := implementedOps.filter (!ops.contains ·)
          if !missing.isEmpty then
            return some ("describe lists the ops the server handles",
              s!"{s.id}: describe lists {ops}; handled but not listed: {missing}")
    | .lookup ns sym | .info ns sym =>
      let expected := (findNs ns).bind fun n => cljNsResolve n (splitSym sym)
      let isInfo := match s.req with | .info _ _ => true | _ => false
      let gotInfo := rs.any fun r =>
        if isInfo then jget r (JVal.s "name") != .nil else jget r (JVal.s "info") != .nil
      if expected.isSome != gotInfo then
        return some ("lookup finds what ns-resolve finds in that namespace",
          s!"{s.id} {if isInfo then "info" else "lookup"} {ns} {sym}: Clojure's ns-resolve gives {(expected.map fun v => v.ns ++ "/" ++ v.name).getD "nil"}, the reply {if gotInfo then "has info" else "is " ++ (rs.map JVal.render).toString}")
    | .unknown op =>
      if !rs.any (statusHas · "unknown-op") then
        return some ("an unknown op is answered unknown-op",
          s!"{s.id} op {op}: the reply is {(rs.map JVal.render).toString}")
    | _ => pure ()
  -- the session table: clone ids are fresh
  let ids := m.sent.toList.filterMap fun s => match s.req with
    | .clone => (repliesOf m s).findSome? (strField · "new-session")
    | _ => none
  if ids.eraseDups.length != ids.length then
    return some ("clone gives a new session id", s!"ids {ids}")
  return none

/-- What a deadlock (every live thread blocked) means here. -/
def stuckDetail (p : Process Mem Th) : Option String :=
  let m := p.memory
  let waits := p.threads.toList.filterMap fun t => match t with
    | some (.client c) => match c.phase with
      | .wait id => some s!"client {c.cid} waits for the done of {id}"
      | .connect => some s!"client {c.cid} waits to connect"
      | _ => none
    | _ => none
  let conns := p.threads.toList.filterMap fun t => match t with
    | some (.conn c) => some s!"conn {c.cid} blocked in read_some with {(c.remainder.getD []).length} buffered bytes \"{showBytes (c.remainder.getD [])}\""
    | _ => none
  let died := m.handlerErrors.map fun (c, e) => s!"conn {c} answered a handler exception: {e}"
  let ended := m.connEnded.filterMap fun c =>
    if (m.socks.getD c {}).closed then none
    else some s!"conn {c}'s loop ended (connected_ false) while its client is still connected; the socket stays open"
  let acc := match m.acceptDied with | some e => [s!"accept loop over: {e}"] | none => []
  let fd1 := match m.fd 1 with
    | some .terminal => []
    | d => [s!"fd 1 (stdout) is left on {reprStr d}"]
  some ("; ".intercalate (waits ++ conns ++ died ++ ended ++ acc ++ fd1))

def runWorld (cfg : Config) (scripts : List (List Req)) (sequential : Bool) (source : Source) :
    Ended × Process Mem Th :=
  let body : SM Unit := do
    interleave prog cfg.maxSteps stuckDetail
    let p ← get
    let live := p.threads.toList.any Option.isSome
    if !live then
      if let some (prop, d) := judge p.memory then throw (.violation prop d)
    else if cfg.requireFinish then
      throw (.violation "the timeline ends within the step bound (model bound)"
        s!"{(p.threads.toList.filter Option.isSome).length} threads still live after {cfg.maxSteps} scheduler rounds")
  match runProcess (initial cfg scripts sequential) body source 100000 with
  | (.ok _, p) => ({ taken := p.decisions.taken, violation := none }, p)
  | (.error (.violation "deadlock" d), p) =>
    ({ taken := p.decisions.taken, violation := some ("every request gets a done reply (no hang)", d) }, p)
  | (.error (.violation prop d), p) => ({ taken := p.decisions.taken, violation := some (prop, d) }, p)
  | (.error .limit, p) => ({ taken := p.decisions.taken, violation := none }, p)
  | (.error (.nodeDown _), p) => ({ taken := p.decisions.taken, violation := none }, p)

/-- A scenario: clients' scripts and the world's configuration. -/
structure Scenario where
  name : String
  cfg : Config := {}
  scripts : List (List Req)
  sequential : Bool := false
  seeds : Nat := 300
  exhaustRuns : Nat := 100000

def Scenario.run (s : Scenario) (source : Source) : Ended := (runWorld s.cfg s.scripts s.sequential source).1
def Scenario.story (s : Scenario) (source : Source) : Array String := (runWorld s.cfg s.scripts s.sequential source).2.log

/-! ## Scenarios -/

def scenarios : List Scenario := [
  { name := "N1: lookup of clojure.core/iteration (its :arglists hold nil)",
    scripts := [[.lookup "clojure.core" "iteration", .describe]] },
  { name := "N1: lookup of user/f, whose :arglists hold false",
    scripts := [[.lookup "user" "f"]] },
  { name := "N1: lookup of user/g, whose :arglists hold a double",
    scripts := [[.lookup "user" "g"]] },
  { name := "N2: lookup through the namespace's alias (str/join in my.app)",
    scripts := [[.lookup "my.app" "str/join"]] },
  { name := "N11: lookup and info of a var of a project namespace (my.app/h)",
    scripts := [[.lookup "my.app" "h", .info "my.app" "h"]] },
  { name := "lookup and info in core modules (control)",
    scripts := [[.lookup "user" "clojure.string/join", .lookup "user" "map", .info "clojure.core" "map"]],
    exhaustRuns := 20000 },
  { name := "eval of the empty string (control: no-code since 7135b7708)",
    scripts := [[.clone, .eval 0 ""]], exhaustRuns := 20000 },
  { name := "N3: eval of a comment only (release build)",
    scripts := [[.clone, .eval 0 ";; nothing here"]] },
  { name := "N3: load-file of a comment-only file (release build)",
    scripts := [[.clone, .loadFile 0 ";; nothing here"]] },
  { name := "N3: eval of a #_ discard only (debug build)",
    cfg := { debugBuild := true },
    scripts := [[.clone, .eval 0 "#_(foo)"]] },
  { name := "N8: eval printing only a newline",
    scripts := [[.clone, .eval 0 "(println)"]] },
  { name := "N8: eval printing only spaces",
    scripts := [[.clone, .eval 0 "(print \"  \")"]] },
  { name := "N10: eval with inspect=\"true\" that prints",
    scripts := [[.clone, .eval 0 "(println \"hi\")" (some "user") (some (JVal.s "true"))]] },
  { name := "eval with inspect sent as an integer (control: answered with an error since 7135b7708)",
    scripts := [[.clone, .eval 0 "1" (some "user") (some (.int 1)), .eval 0 "2"]], exhaustRuns := 20000 },
  { name := "describe (control: lists every handled op since 7135b7708)",
    scripts := [[.describe]], exhaustRuns := 20000 },
  { name := "N13: a request without an op",
    scripts := [[.unknown none]] },
  { name := "an unknown op, interrupt (control)",
    scripts := [[.unknown (some "interrupt")]], exhaustRuns := 20000 },
  { name := "N5: a stray newline after a request",
    scripts := [[.raw (bytes "d2:op8:describe2:id1:xe\n"), .describe]] },
  { name := "N6: deeply nested bencode (stack of 64 frames)",
    cfg := { plat := { maxDepth := 64 } },
    scripts := [[.raw (List.replicate 65 108)]] },
  { name := "N12: EINTR on a blocked read_some, one client",
    cfg := { partialReads := true, eintr := true },
    scripts := [[.clone, .eval 0 "(do (print \"a\") 3)", .lookup "user" "map", .completions "user" "ma", .close 0]],
    seeds := 500, exhaustRuns := 20000 },
  { name := "partial reads, one client, every op (control)",
    cfg := { partialReads := true },
    scripts := [[.clone, .eval 0 "(do (print \"a\") 3)", .lookup "user" "map", .completions "user" "ma", .describe, .close 0]],
    seeds := 500, exhaustRuns := 20000 },
  { name := "two connections: clone, lookup, completions, close concurrently (control)",
    cfg := { partialReads := true },
    scripts := [[.clone, .lookup "user" "map", .completions "user" "wh"],
                [.clone, .lookup "clojure.string" "join", .close 0]],
    seeds := 500, exhaustRuns := 20000 },
  { name := "two connections, one evaluating, partial reads (control)",
    cfg := { partialReads := true },
    scripts := [[.clone, .eval 0 "(do (print \"a\") 3)", .eval 0 "(throw (ex-info \"boom\" {}))"],
                [.clone, .completions "user" "ma"]],
    seeds := 500, exhaustRuns := 20000 },
  { name := "N7: connections one after the other, each evaluating: RLIMIT_NOFILE = 12, 4 held before",
    cfg := { fdLimit := 12, partialReads := false },
    scripts := List.replicate 7 [.clone, .eval 0 "1"],
    sequential := true, seeds := 20, exhaustRuns := 2000 },
  { name := "N7: connections one after the other, each only cloning: RLIMIT_NOFILE = 10, 4 held before",
    cfg := { fdLimit := 10, partialReads := false },
    scripts := List.replicate 7 [.clone],
    sequential := true, seeds := 20, exhaustRuns := 2000 } ]

/-! ## Pure searches: bencode -/

/-- Values of the bencode universe (longs, strings, vectors, string-keyed maps) up to a size. -/
def valueUniverse : Nat → List JVal
  | 0 => [.int 0, .int (-7), .int 42, JVal.s "", JVal.s "e", JVal.s "a:b", .str [0xC3, 0xA9], .str [0, 10]]
  | n + 1 =>
    let small := valueUniverse n
    let atoms := valueUniverse 0
    small ++ [.vec []] ++ (atoms.map fun a => .vec [a]) ++ (atoms.flatMap fun a => (atoms.take 3).map fun b => .vec [a, b])
      ++ [.map []] ++ (atoms.map fun a => .map [(JVal.s "op", a)])
      ++ ((small.take 12).map fun a => .map [(JVal.s "k", a), (JVal.s "id", JVal.s "1")])
      ++ ((small.take 12).map fun a => .vec [a, .vec [a]])

/-- `parse (write v)` gives back `v` and nothing left (vectors, strings, longs, maps). -/
def roundTrip (p : Platform) (v : JVal) : Bool :=
  match write v with
  | .ok b => match parse p (some b) with
    | .value v' none => JVal.same v v'
    | _ => false
  | .error _ => false

/-- How jank's `parse` and the spec decoder classify one buffer. -/
inductive Class where
  | agree
  /-- spec: a message; jank: a different one or none -/
  | wrongMessage
  /-- spec: invalid; jank: waits for more (nil), forever -/
  | stall
  /-- spec: invalid; jank: a message -/
  | lenient
  | crash
  deriving Repr, BEq, Inhabited

def classify (p : Platform) (b : Bytes) : Class :=
  match specDecode b, parse p (some b) with
  | _, .crash => .crash
  | .msg v rest, .value v' r => if JVal.same v v' && (notEmpty rest) == r then .agree else .wrongMessage
  | .msg _ _, _ => .wrongMessage
  | .incomplete, .none => .agree
  | .incomplete, _ => .wrongMessage
  | .invalid, .none => .stall
  | .invalid, .value _ _ => .lenient

/-- Every byte string of length ≤ n over an alphabet. -/
def allStrings (alphabet : List UInt8) : Nat → List Bytes
  | 0 => [[]]
  | n + 1 =>
    let shorter := allStrings alphabet n
    shorter ++ ((shorter.filter (·.length == n)).flatMap fun s => alphabet.map fun c => s ++ [c])

def alphabet : List UInt8 := bytes "dlie012:-+ x" ++ [10]

/-- `handle-client`'s reading on a stream cut into chunks (`read-message` replicated, core.jank:58,
with `read_some` returning the chunks, then eof): the messages it hands to `handle-message`. -/
def readAll (p : Platform) (chunks : List Bytes) : Except String (List JVal × Bytes) := Id.run do
  let mut remainder : Option Bytes := none
  let mut connected := true
  let mut out : List JVal := []
  let mut queue := chunks
  for _ in List.range (4 * chunks.length + 64) do
    if !connected then break
    match parse p remainder with
    | .value v r => out := out ++ [v]; remainder := r
    | .crash => return .error "crash"
    | .none =>
      let (chunk, q) := match queue with
        | c :: rest => (c, rest)
        | [] => ([], [])
      if queue.isEmpty then connected := false
      queue := q
      let input := (remainder.getD []) ++ chunk
      match parse p (some input) with
      | .value v r => out := out ++ [v]; remainder := r
      | .none => remainder := some input
      | .crash => return .error "crash"
  return .ok (out, remainder.getD [])

/-- The spec: every message of the stream, in order. -/
def specAll (b : Bytes) : List JVal := Id.run do
  let mut rest := b
  let mut out := []
  for _ in List.range (b.length + 1) do
    match specDecode rest with
    | .msg v r => out := out ++ [v]; rest := r
    | _ => break
  return out

/-- A world of chunkings: the stream cut at decided points (`net.read.cut`). -/
structure ChunkWorld where
  decisions : Decisions := {}

instance : Chaotic ChunkWorld where
  decisions w := w.decisions
  setDecisions w d := { w with decisions := d }

def chunkRun (p : Platform) (stream : Bytes) (maxCuts : Nat) (source : Source) : Ended :=
  let body : EStateM Stop ChunkWorld Unit := do
    let mut chunks : List Bytes := []
    let mut rest := stream
    for _ in List.range maxCuts do
      if rest.isEmpty then break
      let n := 1 + (← decide (σ := ChunkWorld) "net.read.len" rest.length)
      chunks := chunks ++ [rest.take n]
      rest := rest.drop n
    if !rest.isEmpty then chunks := chunks ++ [rest]
    let got := readAll p chunks
    let want := specAll stream
    match got with
    | .ok (vs, left) =>
      if vs.length != want.length || !(vs.zip want).all (fun (a, b) => JVal.same a b) then
        throw (.violation "a message split across reads decodes the same"
          s!"chunks {chunks.map showBytes}: handled {vs.map JVal.render}, spec {want.map JVal.render}")
      if specDecode left == .invalid then
        throw (.violation "invalid bytes give an error, never a wait"
          s!"chunks {chunks.map showBytes}: after {vs.length} messages the server holds \"{showBytes left}\" and waits for more; no continuation can make it a message")
    | .error e => throw (.violation "a message split across reads decodes the same" s!"chunks {chunks.map showBytes}: {e}")
  match body.run { decisions := { source } } with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation prop d) w => { taken := w.decisions.taken, violation := some (prop, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }
  | .error (.nodeDown _) w => { taken := w.decisions.taken, violation := none }

/-! ## Theorems -/

/-- A map whose sorted entries hold a value that cannot be written cannot be written, wherever
that entry sorts (`reduce-kv` reaches every entry; the first failure ends it). With `write_nil`:
`iteration`'s `:or {... initk nil}` makes its arglists, and every reply holding them, unwritable. -/
theorem joinSorted_error_of_mem (l : List (Bytes × Except String Bytes)) (k : Bytes) (e : String)
    (h : (k, .error e) ∈ l) : ∃ e', joinSorted l = .error e' := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    obtain ⟨k0, r0⟩ := x
    cases r0 with
    | error e0 => exact ⟨e0, by simp [joinSorted, bind, Except.bind]⟩
    | ok b =>
      have hx : (k, Except.error e) ∈ xs := by
        rcases List.mem_cons.mp h with h1 | h1
        · simp at h1
        · exact h1
      obtain ⟨e', he⟩ := ih hx
      exact ⟨e', by simp [joinSorted, bind, Except.bind, he]⟩

/-- Since 7135b7708 `describe` lists every op `handle-message` handles. -/
theorem describe_lists_handled_ops : ∀ o ∈ implementedOps, o ∈ describedOps := by
  simp [implementedOps, describedOps]

/-- `ns-resolve` of `str/join` in `my.app` (which aliases `str` to clojure.string): jank resolves
the alias in the calling thread's `*ns*` (`user`), Clojure in `my.app`. -/
theorem alias_resolution :
    (jankNsResolve "user" ((findNs "my.app").getD default) (some "str", "join")).isNone = true ∧
    (cljNsResolve ((findNs "my.app").getD default) (some "str", "join")).isSome = true := by
  constructor <;> decide

/-- A buffer that starts with a newline never parses, whatever follows it, for either signedness of
`char` and any stack: `parse` gives nil, which `read-message` takes for "incomplete", so the
connection waits for more bytes forever. -/
theorem parse_newline_any (s : Bool) (d : Nat) (rest : Bytes) :
    parse { signedChar := s, maxDepth := d + 1 } (some (10 :: rest)) = .none := by
  cases s <;> simp [parse, parseRecur, nthByte, charToInt, StateT.run, bind, StateT.bind, get, getThe,
    MonadStateOf.get, StateT.get, pure, StateT.pure, Except.pure, Except.bind]

/-- The same for a space. -/
theorem parse_space_any (s : Bool) (d : Nat) (rest : Bytes) :
    parse { signedChar := s, maxDepth := d + 1 } (some (32 :: rest)) = .none := by
  cases s <;> simp [parse, parseRecur, nthByte, charToInt, StateT.run, bind, StateT.bind, get, getThe,
    MonadStateOf.get, StateT.get, pure, StateT.pure, Except.pure, Except.bind]

end Jank.NreplServer
