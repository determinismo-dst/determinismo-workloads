import Jank.R6.Nrepl.Graph

/-!
# Round 6, nREPL: round 5's T7 reduction checked at every reachable state

Round 5 (Reduce.lean) reduced T7 (partial reads) to whole-message reads through the abstraction α:
a connection's buffered bytes put back at the front of its socket's inbox (remainder none), and the
`.top none` right after an incomplete read shown as `.readMsg`. (Made precise here: α applies only to
a NONEMPTY remainder. Applied to every `.top none` it would also rewrite a new connection's first
instruction, and applied to `some []` it would erase what a read of end-of-file leaves; both are the
same in the two worlds and must stay as they are. The first run of the check below found exactly
these two, at 2 states and 4 steps.) Its steps
1–2 (a partial read is a stutter step; the completing read is a whole read) were checked at the 6
pre-read states one schedule reaches; steps 3–5 (no other thread reads those bytes; the judge sees
only α; deleting stutter steps adds no preemption) were argued.

With both worlds' state graphs complete (Graph.lean: every state reachable under every schedule),
the claim can be checked whole: for EVERY reachable state s of T7 and EVERY step s → s' (every
thread, every value of the step's own decisions),
- α(s) is a reachable state of the whole-read world, and
- either α(s') = α(s) (a stutter step), or the whole-read world has the step α(s) → α(s') by the
  same thread with the same result;
and every final state of T7 has α equal to a final state of the whole-read world with the same
verdict. That is a stuttering simulation, checked on the full reachable set (steps 1–4), and step 5
is no longer needed: T7's timelines are counted in T7 itself (Graph.lean `count`).
-/

namespace Jank.R6.Nrepl

open Determinismo Jank.R3.Nrepl Jank.NreplServer

def alphaTh : Option TTh → Option TTh
  | some (.conn c) =>
    match c.remainder with
    | some (_ :: _) =>
      let instrs := match c.instrs with
        | .top none :: rest => .readMsg :: rest
        | is => is
      some (.conn { c with remainder := none, instrs })
    | _ => some (.conn c)
  | t => t

/-- α: every connection's buffered bytes (a nonempty remainder: an incomplete message) back at the
front of its socket's inbox, and the `.top none` after that incomplete read shown as `.readMsg`; the
config's `partialReads` set to the whole-read world's. (An empty remainder `some []`, left by a read
of end-of-file, and the first `.top none` of a new connection are the same in both worlds.) -/
def alpha (k : PKey) : PKey := Id.run do
  let mut m := { k.mem with cfg := { k.mem.cfg with partialReads := false } }
  for t in k.threads do
    if let some (.conn c) := t then
      if let some r@(_ :: _) := c.remainder then
        let s := m.socks.getD c.cid {}
        m := { m with socks := m.socks.set! c.cid { s with inbox := r ++ s.inbox } }
  return { mem := m, threads := k.threads.map alphaTh }

structure SimOut where
  states : Nat := 0
  edges : Nat := 0
  stutters : Nat := 0
  matched : Nat := 0
  /-- α of a reachable state that the whole-read world does not reach. -/
  unreached : Nat := 0
  /-- Edges with no matching whole-read edge. -/
  unmatched : Nat := 0
  finalsOk : Nat := 0
  finalsBad : Nat := 0
  firstBad : Option String := none
  deriving Inhabited

def resTag : Res → String
  | .ran => "ran"
  | .blocked => "blocked"
  | .done => "done"
  | .stop v => s!"stop {v}"

/-- Checks the stuttering simulation of `gc` (T7) by `gw` (T7, whole reads) under α. -/
def simCheck (gc gw : G) : SimOut := Id.run do
  let mut o : SimOut := { states := gc.keys.size }
  let alphas := gc.keys.map alpha
  let idx : Array (Option Nat) := alphas.map fun a => gw.index.get? a
  for i in [0:gc.keys.size] do
    let some wi := idx[i]! | do
      o := { o with unreached := o.unreached + 1 }
      if o.firstBad.isNone then o := { o with firstBad := some s!"α of state {i} is not a whole-read state" }
      continue
    match gc.final.getD i none, gw.final.getD wi none with
    | some v, some w =>
      if v == w then o := { o with finalsOk := o.finalsOk + 1 }
      else
        o := { o with finalsBad := o.finalsBad + 1 }
        if o.firstBad.isNone then o := { o with firstBad := some s!"final state {i}: verdict {v} vs {w}" }
    | some _, none =>
      o := { o with finalsBad := o.finalsBad + 1 }
      if o.firstBad.isNone then o := { o with firstBad := some s!"state {i} is final, its α is not" }
    | _, _ => pure ()
    let wes : Array (Nat × Array Branch) := gw.edges.getD wi #[]
    for (t, bs) in gc.edges.getD i #[] do
      for (b : Branch) in bs do
        o := { o with edges := o.edges + 1 }
        let ai := idx[b.succ]!
        if ai == some wi && (b.res == .ran || b.res == .blocked) then
          o := { o with stutters := o.stutters + 1 }
        else
          let ok := match ai with
            | none => false
            | some aj =>
              match wes.find? (fun (e : Nat × Array Branch) => e.1 == t) with
              | some (_, wbs) => wbs.any fun wb => wb.succ == aj && wb.res == b.res
              | none => false
          if ok then o := { o with matched := o.matched + 1 }
          else
            o := { o with unmatched := o.unmatched + 1 }
            if o.firstBad.isNone then
              o := { o with firstBad := some s!"state {i} thread {t} {resTag b.res} decisions {b.taken.map (fun (x : Taken) => x.value)}: no whole-read step" }
  return o

end Jank.R6.Nrepl

namespace Jank.R6.Nrepl
open Determinismo Jank.R3.Nrepl Jank.NreplServer

/-- Which parts of two keys differ (debugging aid). -/
def diffKeys (a b : PKey) : List String := Id.run do
  let ma := a.mem
  let mb := b.mem
  let mut d := []
  if !(ma.cfg == mb.cfg) then d := d ++ ["cfg"]
  if !(ma.jw == mb.jw) then d := d ++ ["jw"]
  if !(ma.fds == mb.fds) then d := d ++ ["fds"]
  if !(ma.temps == mb.temps) then d := d ++ ["temps"]
  if !(ma.terminal == mb.terminal && ma.outBuf == mb.outBuf) then d := d ++ ["terminal/outBuf"]
  if !(ma.socks == mb.socks) then d := d ++ [s!"socks {ma.socks.toList.map fun s => (s.inbox.length, s.outbox.length, s.closed)} vs {mb.socks.toList.map fun s => (s.inbox.length, s.outbox.length, s.closed)}"]
  if !(ma.pending == mb.pending && ma.accepted == mb.accepted && ma.nextUuid == mb.nextUuid) then d := d ++ ["pending/accepted/uuid"]
  if !(ma.replies == mb.replies) then d := d ++ ["replies"]
  if !(ma.sent == mb.sent) then d := d ++ ["sent"]
  if !(ma.evals == mb.evals) then d := d ++ ["evals"]
  if !(ma.crashed == mb.crashed && ma.handlerErrors == mb.handlerErrors && ma.connEnded == mb.connEnded && ma.hung == mb.hung) then d := d ++ ["errors"]
  if a.threads.size != b.threads.size then d := d ++ [s!"threads {a.threads.size} vs {b.threads.size}"]
  for i in [0:min a.threads.size b.threads.size] do
    let ta := a.threads[i]!
    let tb := b.threads[i]!
    if !(ta == tb) then
      match ta, tb with
      | some (.conn c1), some (.conn c2) =>
        d := d ++ [s!"thread {i}: conn {Jank.R5.Nrepl.fpConn c1} VS {Jank.R5.Nrepl.fpConn c2}"]
      | some (.client c1), some (.client c2) =>
        d := d ++ [s!"thread {i}: client k {c1.k}/{c2.k} cursor {c1.cursor}/{c2.cursor} phase {reprStr c1.phase}/{reprStr c2.phase}"]
      | _, _ => d := d ++ [s!"thread {i}"]
  return d

/-- For the first state whose α is not a whole-read state: the field differences from the
whole-read state α of its predecessor steps to by the same thread. -/
def simDebug (gc gw : G) : List String := Id.run do
  for i in [0:gc.keys.size] do
    let some wi := gw.index.get? (alpha gc.keys[i]!) | continue
    for (t, bs) in gc.edges.getD i #[] do
      for (b : Branch) in bs do
        if (gw.index.get? (alpha gc.keys[b.succ]!)).isNone then
          let wes : Array (Nat × Array Branch) := gw.edges.getD wi #[]
          match wes.find? (fun (e : Nat × Array Branch) => e.1 == t) with
          | some (_, wbs) =>
            return [s!"state {i} -> {b.succ} by thread {t} ({resTag b.res})"] ++
              (wbs.toList.flatMap fun (wb : Branch) => diffKeys (alpha gc.keys[b.succ]!) gw.keys[wb.succ]!)
          | none => return [s!"state {i}: thread {t} has no whole-read step"]
  return []

end Jank.R6.Nrepl
