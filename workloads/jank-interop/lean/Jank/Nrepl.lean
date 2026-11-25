import Determinismo

/-!
# jank's nREPL server: output capture under concurrency, sessions, failures

Sources (commit 7135b7708; first written against f3d82d654), src/jank/jank/nrepl/server/:

- core.jank `-main` (108): accepts connections in a loop (129–143); each one runs
  `handle-client` in its own `future` (131), a thread. `handle-client` (79) reads a message,
  `handle-message`, writes the responses, loops: one connection's messages are handled one at a
  time; two connections run at once. Since 7135b7708 the handling of a request is inside a `try`
  (85–105): an exception from `handle-message` or `write-message` is answered
  `{:status [:error :done] :err "An exception was thrown from the nREPL handler:..."}` and the
  loop goes on. (At f3d82d654 it left the loop and the connection was never read again.) The
  `native_client` is still never deleted (server.cpp 127–129, "This leaks memory").
- handler/eval.jank `do-eval` (22): empty code is answered `{:status [:no-code :done]}` (23–24);
  `target-ns` is `(if ns (-> ns symbol find-ns) default-ns)`, and a missing namespace is answered
  `{:status [:namespace-not-found :done]}` (27–29); then `(with-capture (fn [] (binding [*ns*
  target-ns *file* …] [(safe-eval code line col) *ns*])))` (31–36), and the response is built
  from `*1`/`*e` with `(pr-str *1)` (59) *outside* `safe-eval`'s handlers. Nothing is kept per
  session.
- handler/clone.jank: `{:new-session (str (random-uuid))}`: no session state exists.
- capture.jank (unchanged) `with-capture` (60): `start` stdout and stderr, `(f)`, `end` both (in a
  `finally`), `readback` both. `start` (18): `bak-fd (dup fd)`, `mkstemp`, `fflush`,
  `dup2 temp-fd fd`, `close temp-fd`. `end` (39): `fflush`, `dup2 bak-fd fd`, `close bak-fd`.
  `readback` (52): `slurp` the temp file, `unlink` it. File descriptor 1 is the process's: every
  thread's `print` (core.cpp `print`/`println` 141–211: `fwrite` to the `FILE*` in `*out*`,
  stdout) goes wherever fd 1 points when the `FILE` buffer is flushed.
- evaluate.cpp `safe_eval` (733): sets `*1`/`*2`/`*3` or `*e` with `var::set` on the calling
  thread's binding (var.cpp 113): one set per connection thread (a future conveys fresh boxes,
  context.cpp 719–744), shared by every session of that connection.
- handler.jank (5–8): an unknown op (`interrupt` included; describe.jank 5–17 lists none)
  answers `{:status [:error :unknown-op :done] :op (get msg "op")}`.

The spec is nREPL's documented semantics (nrepl.org: "Sessions persist dynamic bindings, the
current namespace (*ns*), *1 *2 *3 *e"; "interrupt: attempts to interrupt some executing
request"; eval's "ns": "the namespace in which to perform the evaluation. The supplied namespace
must exist already"; output: `*out*` is bound per session, its text sent as `:out` of the
request that printed it) and Clojure's: an exception while printing a value is reported as an
evaluation error.
-/

namespace Jank.Nrepl

open Determinismo

/-! ## A. Output capture: fd 1 shared by concurrent evaluations (Threads) -/

/-- The process: what fd 1 refers to, the stdio `FILE* stdout` buffer, the open files. -/
structure CapMem where
  /-- The open file fd 1 refers to: 0 is the server's terminal. -/
  fd1 : Nat := 0
  /-- `stdout`'s buffer (one per process; glibc locks it per call). -/
  buf : List String := []
  /-- Each file's content; file 0 is the terminal. -/
  files : Array (List String) := #[[]]
  unlinked : List Nat := []
  /-- What each client's `readback` returned (its `:out`). -/
  captured : Array (Option (List String)) := #[]
  /-- stdout line-buffered (a terminal: `jank repl`): each `println` flushes. -/
  lineBuffered : Bool := false
  deriving Inhabited

/-- A thread: a client's evaluation (`(println "o<t>")` inside `with-capture`) or a printer
outside any capture (the terminal REPL of `jank repl`, or a `future` an earlier evaluation
started). -/
inductive Role where
  | client
  | printer
  deriving BEq, Repr, Inhabited

structure CapLoc where
  role : Role
  pc : Nat := 0
  bak : Nat := 0
  temp : Nat := 0
  deriving Inhabited

abbrev CapM := ProcessM CapMem CapLoc

def setMem (m : CapMem) : CapM Unit := modify fun p => { p with memory := m }

def note (line : String) : CapM Unit := modify fun p => { p with log := p.log.push line }

def flush (m : CapMem) : CapMem :=
  { m with files := m.files.modify m.fd1 (· ++ m.buf), buf := [] }

def fileName (f : Nat) : String := if f == 0 then "the terminal" else s!"temp{f}"

/-- One atomic step of thread `t` (capture.jank `start`, the evaluation's `println`, `end`,
`readback`). -/
def capStep (t : Nat) (l : CapLoc) : CapM (StepResult CapLoc) := do
  let m := (← get).memory
  let tok := s!"o{t}"
  match l.role, l.pc with
  | .client, 0 =>
    -- start: (cpp/dup fd)
    note s!"t{t}: bak-fd = dup(1) → {fileName m.fd1}"
    pure (.ran { l with pc := 1, bak := m.fd1 })
  | .client, 1 =>
    -- start: mkstemp
    let f := m.files.size
    setMem { m with files := m.files.push [] }
    note s!"t{t}: mkstemp → {fileName f}"
    pure (.ran { l with pc := 2, temp := f })
  | .client, 2 =>
    -- start: (cpp/fflush fp)
    setMem (flush m)
    note s!"t{t}: fflush(stdout) → {m.buf} to {fileName m.fd1}"
    pure (.ran { l with pc := 3 })
  | .client, 3 =>
    -- start: (cpp/dup2 temp-fd fd) (cpp/close temp-fd)
    setMem { m with fd1 := l.temp }
    note s!"t{t}: dup2(temp, 1): fd 1 → {fileName l.temp}"
    pure (.ran { l with pc := 4 })
  | .client, 4 =>
    -- (f): the evaluation prints.
    let m := { m with buf := m.buf ++ [tok] }
    setMem (if m.lineBuffered then flush m else m)
    note s!"t{t}: (println \"{tok}\"){if m.lineBuffered then s!" → {fileName m.fd1}" else " (buffered)"}"
    pure (.ran { l with pc := 5 })
  | .client, 5 =>
    -- end: (cpp/fflush fp)
    setMem (flush m)
    note s!"t{t}: fflush(stdout) → {m.buf} to {fileName m.fd1}"
    pure (.ran { l with pc := 6 })
  | .client, 6 =>
    -- end: (cpp/dup2 bak-fd fd) (cpp/close bak-fd)
    setMem { m with fd1 := l.bak }
    note s!"t{t}: dup2(bak-fd, 1): fd 1 → {fileName l.bak}"
    pure (.ran { l with pc := 7 })
  | .client, _ =>
    -- readback: slurp, unlink.
    let out := m.files.getD l.temp []
    setMem { m with captured := m.captured.set! t (some out), unlinked := l.temp :: m.unlinked }
    note s!"t{t}: readback {fileName l.temp} = {out}; unlink"
    pure .done
  | .printer, 0 =>
    let m := { m with buf := m.buf ++ [tok] }
    setMem (if m.lineBuffered then flush m else m)
    note s!"t{t}: (println \"{tok}\") outside any capture{if m.lineBuffered then s!" → {fileName m.fd1}" else " (buffered)"}"
    pure (.ran { l with pc := 1 })
  | .printer, _ =>
    setMem (flush m)
    note s!"t{t}: fflush(stdout) → {m.buf} to {fileName m.fd1}"
    pure .done

/-- The judgment once every thread ended: each client's `:out` is its own output, the printers'
output reached the terminal, fd 1 is the terminal again. -/
def judge (roles : List Role) (m : CapMem) : Option (String × String) :=
  let clients := (List.range roles.length).filter fun i => roles.getD i .client == .client
  let printers := (List.range roles.length).filter fun i => roles.getD i .client == .printer
  let bad := clients.filterMap fun i =>
    let got := (m.captured.getD i none).getD []
    if got != [s!"o{i}"] then some s!"client t{i}'s :out is {got}, expected [o{i}]" else none
  let lost := printers.filterMap fun i =>
    if (m.files.getD 0 []).contains s!"o{i}" then none
    else some s!"t{i}'s output o{i} never reached the terminal"
  if !bad.isEmpty then some ("each evaluation's :out is its own output", "; ".intercalate bad)
  else if !lost.isEmpty then some ("output outside an evaluation stays on the terminal", "; ".intercalate lost)
  else if m.fd1 != 0 then
    some ("fd 1 is the terminal again", s!"fd 1 is left on {fileName m.fd1}{if m.unlinked.contains m.fd1 then " (unlinked)" else ""}: everything the server prints from now on is lost")
  else none

def runCapture (roles : List Role) (lineBuffered : Bool) (source : Source) : Ended × Array String :=
  let start : Process CapMem CapLoc :=
    { memory := { lineBuffered, captured := Array.replicate roles.length none },
      threads := (roles.map fun r => some ({ role := r } : CapLoc)).toArray }
  let prog : CapM Unit := do
    interleave { step := capStep } 200
    let m := (← get).memory
    if let some (p, d) := judge roles m then throw (.violation p d)
  match runProcess start prog source with
  | (.ok _, p) => ({ taken := p.decisions.taken, violation := none }, p.log)
  | (.error (.violation prop d), p) => ({ taken := p.decisions.taken, violation := some (prop, d) }, p.log)
  | (.error .limit, p) => ({ taken := p.decisions.taken, violation := none }, p.log)
  | (.error (.nodeDown _), p) => ({ taken := p.decisions.taken, violation := none }, p.log)

/-- The spec: nREPL binds `*out*` per session, so each evaluation's text is its own and nothing
else moves: modeled as each client writing to its own sink. Every interleaving satisfies the
judgment (checked by `exhaust`). -/
def specStep (t : Nat) (l : CapLoc) : CapM (StepResult CapLoc) := do
  let m := (← get).memory
  match l.role with
  | .client =>
    setMem { m with captured := m.captured.set! t (some [s!"o{t}"]) }
    pure .done
  | .printer =>
    setMem { m with files := m.files.modify 0 (· ++ [s!"o{t}"]) }
    pure .done

def runSpec (roles : List Role) (source : Source) : Ended :=
  let start : Process CapMem CapLoc :=
    { memory := { captured := Array.replicate roles.length none },
      threads := (roles.map fun r => some ({ role := r } : CapLoc)).toArray }
  let prog : CapM Unit := do
    interleave { step := specStep } 200
    if let some (p, d) := judge roles (← get).memory then throw (.violation p d)
  match runProcess start prog source with
  | (.ok _, p) => { taken := p.decisions.taken, violation := none }
  | (.error (.violation prop d), p) => { taken := p.decisions.taken, violation := some (prop, d) }
  | (.error .limit, p) => { taken := p.decisions.taken, violation := none }
  | (.error (.nodeDown _), p) => { taken := p.decisions.taken, violation := none }

/-! ## B. Sessions, *1/*e, ns, printing errors, interrupts (one connection, in order) -/

/-- What a request's code does when evaluated. -/
inductive Code where
  /-- A number literal. -/
  | lit (n : Nat)
  | star1
  | starE
  | inNs
  | curNs
  /-- `(throw (ex-info "e" {}))`. -/
  | throws
  /-- `(map (fn [_] (throw (ex-info "p" {}))) [1])`: evaluates to a lazy seq; printing it throws. -/
  | lazyThrows
  /-- `(loop [] (recur))`. -/
  | forever
  /-- `((fn f [n] (inc (f n))) 0)`: unbounded recursion. -/
  | recurse
  deriving BEq, Repr, Inhabited

def Code.code : Code → String
  | .lit n => toString n
  | .star1 => "*1"
  | .starE => "(ex-message *e)"
  | .inNs => "(in-ns 'foo)"
  | .curNs => "(str *ns*)"
  | .throws => "(throw (ex-info \"e\" {}))"
  | .lazyThrows => "(map (fn [_] (throw (ex-info \"p\" {}))) [1])"
  | .forever => "(loop [] (recur))"
  | .recurse => "((fn f [n] (inc (f n))) 0)"

inductive Msg where
  /-- An eval in session s (1 or 2), with an "ns" field or without. -/
  | eval (s : Nat) (c : Code) (ns : Option String)
  /-- An interrupt of session s's running eval. -/
  | interrupt (s : Nat)
  deriving BEq, Repr, Inhabited

def Msg.code : Msg → String
  | .eval s c ns => s!"\{op eval, session s{s}, code {repr c.code}{match ns with | some n => s!", ns {n}" | none => ""}}"
  | .interrupt s => s!"\{op interrupt, session s{s}}"

/-- A response, as the client sees it. -/
inductive Resp where
  | value (v : String) (ns : String)
  | evalError (ex : String)
  | nsNotFound
  | unknownOp
  | interrupted
  /-- An interrupt with nothing running. -/
  | idle
  /-- `{:status [:error :done] :err "An exception was thrown from the nREPL handler:..."}`:
  handle-client's `catch` (core.jank 96–100), the connection goes on. -/
  | handlerError
  /-- Nothing ever comes back. -/
  | none_
  deriving BEq, Repr, Inhabited

def Resp.code : Resp → String
  | .value v ns => s!"value {v} (ns {ns})"
  | .evalError e => s!"eval-error {e}"
  | .nsNotFound => "namespace-not-found"
  | .unknownOp => "unknown-op"
  | .interrupted => "interrupted"
  | .idle => "session-idle"
  | .handlerError => "error (handler exception)"
  | .none_ => "no response"

/-- A session's (or the connection thread's) state. -/
structure Sess where
  ns : String := "user"
  star1 : String := "nil"
  starE : String := "nil"
  deriving Inhabited, BEq

def nsExists (n : String) (created : Bool) : Bool := n == "user" || (n == "foo" && created)

/-- Evaluating `c` in namespace `ns`: the value printed, the namespace after, or an error. -/
def evalIn (c : Code) (ns : String) (st : Sess) : Except String (String × String) :=
  match c with
  | .lit n => .ok (toString n, ns)
  | .star1 => .ok (st.star1, ns)
  | .starE => .ok (st.starE, ns)
  | .inNs => .ok ("#object[ns foo]", "foo")
  | .curNs => .ok (s!"\"{ns}\"", ns)
  | .throws => .error "e"
  | .lazyThrows => .ok ("<lazy>", ns)
  | .forever => .ok ("<forever>", ns)
  | .recurse => .error "StackOverflowError"

/-- Each jank difference, fixable one at a time: with all four on, jank's model is the spec's
(checked by `exhaust`), so the searches below find each difference on its own. -/
structure Fixes where
  /-- A printing error answered as an eval error (do-eval's `(pr-str *1)` inside the handler). -/
  printError : Bool := false
  /-- An "ns" that does not exist answered `namespace-not-found`: jank does so since 7135b7708
  (handler/eval.jank 27–29), so this toggle no longer changes jank's model. -/
  missingNs : Bool := false
  /-- ns, *1, *e kept per session (not per connection thread). -/
  sessions : Bool := false
  /-- `interrupt` stops a running eval. -/
  interrupt : Bool := false
  /-- A stack overflow is an exception (no guard: the thread runs into its guard page). -/
  stack : Bool := false
  deriving Repr, Inhabited

def Fixes.all : Fixes :=
  { printError := true, missingNs := true, sessions := true, interrupt := true, stack := true }

/-- jank's connection: the connection thread's bindings (slot 0; slots 1 and 2 are used only
when `sessions` is fixed), whether the loop is dead. -/
structure JankConn where
  slots : Array Sess := #[{}, {}, {}]
  fooCreated : Bool := false
  dead : Bool := false
  running : Option Nat := none
  deriving Inhabited

/-- core.jank `handle-client` + handler/eval.jank `do-eval` + evaluate.cpp `safe_eval`, on one
message. -/
def jankStep (fx : Fixes) (c : JankConn) (msg : Msg) : JankConn × Resp :=
  if c.dead then (c, .none_) else
  match msg with
  | .interrupt s =>
    if fx.interrupt then
      if c.running == some s then ({ c with running := none }, .interrupted) else (c, .idle)
    else (c, .unknownOp)                                  -- handler.jank :default
  | .eval s code ns =>
    if fx.interrupt && c.running == some s then (c, .none_) else
    let slot := if fx.sessions then s else 0
    let st := c.slots.getD slot {}
    -- target-ns: (if ns (-> ns symbol find-ns) default-ns); nil → namespace-not-found
    -- (handler/eval.jank 27–29).
    let target? : Option String := match ns with
      | some n => if nsExists n c.fooCreated then some n else none
      | none => some (if fx.sessions then st.ns else "user")
    match target? with
    | none => (c, .nsNotFound)
    | some target =>
    let fooCreated := c.fooCreated || code == .inNs
    if code == .recurse && !fx.stack then
      -- no stack-depth check anywhere in src/ (no sigaltstack, no guard): SIGSEGV on the guard
      -- page; safe_eval's handlers catch C++ exceptions, not signals: the process dies, every
      -- connection and the terminal REPL with it.
      ({ c with dead := true, fooCreated }, .none_)
    else if code == .forever then
      -- the loop never returns; the next message is never read
      if fx.interrupt then ({ c with running := some s, fooCreated }, .none_)
      else ({ c with dead := true, fooCreated }, .none_)
    else
    match evalIn code target st with
    | .error e =>
      -- safe_eval sets *e on the connection thread's binding.
      ({ c with slots := c.slots.set! slot { st with starE := e }, fooCreated }, .evalError e)
    | .ok (v, nsAfter) =>
      -- *1 set by safe_eval; *ns* is only `binding`-bound around the eval: not kept.
      let st' := { st with star1 := v, ns := if fx.sessions then nsAfter else st.ns }
      if code == .lazyThrows then
        if fx.printError then
          ({ c with slots := c.slots.set! slot { st' with starE := "p" }, fooCreated }, .evalError "p")
        else
          -- (pr-str *1) in do-eval (59), outside safe-eval: throws out of handle-message;
          -- handle-client's catch (core.jank 96–100) answers a handler error, the connection
          -- goes on; *1 was set by safe_eval, *e is not set.
          ({ c with slots := c.slots.set! slot st', fooCreated }, .handlerError)
      else ({ c with slots := c.slots.set! slot st', fooCreated }, .value v nsAfter)

/-- nREPL: per-session ns, *1, *e; a missing ns is an error; a printing error is an eval error;
an interrupt stops a running eval. -/
structure SpecConn where
  sessions : Array Sess := #[{}, {}, {}]
  fooCreated : Bool := false
  /-- The session whose eval is running forever (until interrupted). -/
  running : Option Nat := none
  deriving Inhabited

def specStepN (c : SpecConn) (msg : Msg) : SpecConn × Resp :=
  match msg with
  | .interrupt s =>
    if c.running == some s then ({ c with running := none }, .interrupted)
    else (c, .idle)  -- {:status [:done :session-idle]}
  | .eval s code ns =>
    if c.running == some s then (c, .none_) else  -- queued behind the running eval (answered later)
    let st := c.sessions.getD s {}
    let target? : Option String := match ns with
      | some n => if nsExists n c.fooCreated then some n else none
      | none => some st.ns
    match target? with
    | none => (c, .nsNotFound)
    | some target =>
    let fooCreated := c.fooCreated || code == .inNs
    if code == .forever then ({ c with running := some s, fooCreated }, .none_) else
    match evalIn code target st with
    | .error e => ({ c with sessions := c.sessions.set! s { st with starE := e }, fooCreated }, .evalError e)
    | .ok (v, nsAfter) =>
      if code == .lazyThrows then
        -- the printing error is reported; *e is the printing exception
        ({ c with sessions := c.sessions.set! s { st with star1 := v, starE := "p", ns := nsAfter }, fooCreated }, .evalError "p")
      else
        ({ c with sessions := c.sessions.set! s { st with star1 := v, ns := nsAfter }, fooCreated }, .value v nsAfter)

/-- Responses compared on what clients use: a value's printed form, the error, its absence. -/
def Resp.sameAs : Resp → Resp → Bool
  | .value v _, .value w _ => v == w
  | .evalError _, .evalError _ => true
  | a, b => a == b

structure World where
  decisions : Decisions := {}

instance : Chaotic World where
  decisions w := w.decisions
  setDecisions w d := { w with decisions := d }

def codes : List Code := [.lit 1, .lit 2, .star1, .starE, .inNs, .curNs, .throws, .lazyThrows, .forever, .recurse]

def drawMsg (withInterrupt : Bool) : EStateM Stop World Msg := do
  let kind ← decide (σ := World) "nrepl.msg" (if withInterrupt then 2 else 1)
  let s := 1 + (← decide (σ := World) "nrepl.session" 2)
  if kind == 1 then return .interrupt s
  let c := codes.getD (← decide (σ := World) "nrepl.code" codes.length) (.lit 1)
  let ns ← match ← decide (σ := World) "nrepl.ns" 3 with
    | 0 => pure none
    | 1 => pure (some "user")
    | _ => pure (some "foo")
  return .eval s c ns

def sessionsBody (fx : Fixes) (len : Nat) (withInterrupt : Bool) : EStateM Stop World Unit := do
  let mut j : JankConn := {}
  let mut c : SpecConn := {}
  let mut lines : Array String := #[]
  for _ in List.range len do
    let msg ← drawMsg withInterrupt
    let (j', jr) := jankStep fx j msg
    let (c', cr) := specStepN c msg
    j := j'; c := c'
    lines := lines.push msg.code
    if !jr.sameAs cr then
      violate (σ := World) "nREPL responses as nREPL's"
        s!"{" ".intercalate lines.toList}: the last answered by nREPL with {cr.code}, by jank with {jr.code}"

def runSessions (fx : Fixes) (len : Nat) (withInterrupt : Bool) (source : Source) : Ended :=
  match (sessionsBody fx len withInterrupt).run { decisions := { source } } with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }
  | .error (.nodeDown _) w => { taken := w.decisions.taken, violation := none }

/-! ## Theorems -/

/-- Once jank's connection loop is stuck (an eval that never returns, C13) or the process is gone (C14), no later message is answered. (At f3d82d654 a printing error also ended it, C10.) -/
theorem dead_stays_dead (fx : Fixes) (c : JankConn) (h : c.dead = true) (msgs : List Msg) :
    (msgs.foldl (fun (acc : JankConn × List Resp) m =>
      let (c', r) := jankStep fx acc.1 m; (c', acc.2 ++ [r])) (c, [])).2 =
    msgs.map (fun _ => Resp.none_) := by
  suffices ∀ (rs : List Resp), (msgs.foldl (fun (acc : JankConn × List Resp) m =>
      let (c', r) := jankStep fx acc.1 m; (c', acc.2 ++ [r])) (c, rs)).2 =
      rs ++ msgs.map (fun _ => Resp.none_) by simpa using this []
  induction msgs generalizing c with
  | nil => intro rs; simp
  | cons m ms ih =>
    intro rs
    simp only [List.foldl_cons, List.map_cons]
    have hs : jankStep fx c m = (c, .none_) := by simp [jankStep, h]
    rw [hs]
    simpa [List.append_assoc] using ih c h (rs ++ [Resp.none_])

/-- The two-client race, as a fixed schedule: t0 starts, t1 starts, t0 prints and ends, t1
prints and ends. t0's `:out` is empty, t1's holds t0's output, and fd 1 is left on t0's
unlinked temp file. -/
def raceSchedule : Array Nat := #[0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0]

/-! ## C. What each connection and each evaluation keeps alive -/

/-- What the server holds after `conns` connections, each closed after `evals` evaluations:
- per connection: its `native_client` (server.cpp 129: `new native_client(...)`, never deleted:
  "This leaks memory"), whose `impl` holds a value-initialized 1 MiB `rx_buf_` (server.cpp 61,
  zeroed: resident) and the socket (`tcp::socket`, never closed); its `future`'s `std::thread`,
  never joined (nobody derefs it: core.jank 131; future.cpp 20 joins only in `deref`), so its
  stack stays mapped; its thread-binding frame (context.cpp 719: pushed, never popped);
- per evaluation: the wrapper function JIT-compiled for it (evaluate.cpp 149 `wrap_expression`
  → jit/processor_dynamic.cpp 583 `ParseAndExecute`; nothing in jit/ unloads code).
nREPL on the JVM keeps none of these past a connection's close (its socket is closed, its
threads end) and an evaluation's classes are collectable with its class loader. -/
structure Held where
  rxBytes : Nat
  sockets : Nat
  unjoinedThreads : Nat
  bindingFrames : Nat
  jitModules : Nat
  deriving Repr

def jankHeld (conns evals : Nat) : Held :=
  { rxBytes := conns * 1024 * 1024, sockets := conns, unjoinedThreads := conns,
    bindingFrames := conns, jitModules := conns * evals }

def specHeld (_conns _evals : Nat) : Held :=
  { rxBytes := 0, sockets := 0, unjoinedThreads := 0, bindingFrames := 0, jitModules := 0 }

/-- jank's held resources grow without bound in connections and in evaluations. -/
theorem held_unbounded (bound : Nat) :
    ∃ c e, (jankHeld c e).sockets > bound ∧ (jankHeld 1 e).jitModules > bound ∧
      (specHeld c e).sockets = 0 := by
  exact ⟨bound + 1, bound + 1, by simp [jankHeld], by simp [jankHeld], rfl⟩

end Jank.Nrepl
