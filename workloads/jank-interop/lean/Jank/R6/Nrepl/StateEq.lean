import Jank.R5.Nrepl.Reduce
import Std.Data.HashMap

/-!
# Round 6, nREPL: exact equality of World T states

Round 5 (Reduce.lean, section 10 of its report) said World T's states "have no decidable equality",
so it compared states by fingerprint strings (`fpMem`), which summarize the jank world (namespace
names and sizes only) and so can call two different states equal. A stateful search needs the
opposite guarantee: two states merged only when they are the same state.

Every type a World T process holds is plain data: the jank world `JW` (namespaces, var slots, heap,
the analyzer's arena, closures as an expression index with an environment, the gensym counter), the
fd table, sockets, temp files, the reply/sent/eval logs, and each thread's locals (a connection's
instruction list, its eval in progress with the reader's state, its binding frames; a client's
script position). None holds a function: `VarCell`'s macro closures are rebuilt from var metadata
before each analysis (JankEval.lean), not stored. So structural equality is derivable. The
instances below are derived (`deriving instance BEq`), except `NV`, whose `Float` is compared by
its bits (IEEE `==` says `0.0 == -0.0` and `nan != nan`; bit equality is exact identity).

`PKey` is the part of a `Process` that a step, the scheduler and the judge read: the memory and the
threads. Not in it: the decisions (a step draws from them, and the searches enumerate every value),
the step counter and the story log (`Process.note` writes them; no step, judge or deadlock detail of
World T reads them: Threads.lean uses only `tmem`, `tset`, `tnote`, `decide*` and `modify threads`).

Its hash is a cheap summary (sizes and counters). A hash is only a bucket: equal keys are decided
by the derived `BEq`, so a collision costs time, never soundness.
-/

namespace Jank.R6.Nrepl

open Determinismo Jank.R3.Nrepl Jank.NreplServer Jank.Analyzer

/-- `NV` (Eval.lean): a native value; its double compared by IEEE bits (exact identity). -/
def nvEq : NV → NV → Bool
  | .i a, .i b => a == b
  | .d a, .d b => a.toBits == b.toBits
  | .b a, .b b => a == b
  | .cs a, .cs b => a == b
  | _, _ => false

instance : BEq NV := ⟨nvEq⟩

deriving instance BEq for Val
deriving instance BEq for Closure
deriving instance BEq for Arena
deriving instance BEq for NsCell
deriving instance BEq for Slot
deriving instance BEq for ExObj
deriving instance BEq for LazyMap
deriving instance BEq for Heap
deriving instance BEq for JW
deriving instance BEq for TB
deriving instance BEq for Sock
deriving instance BEq for TConfig
deriving instance BEq for TReq
deriving instance BEq for TSent
deriving instance BEq for EvalRec
deriving instance BEq for TMem
deriving instance BEq for Jank.R3.Nrepl.Handle
deriving instance BEq for EvalReq
deriving instance BEq for Fail
deriving instance BEq for EvalEnd
deriving instance BEq for EvAfter

def exceptEq : Except Fail (Option Obj) → Except Fail (Option Obj) → Bool
  | .ok a, .ok b => a == b
  | .error a, .error b => a == b
  | _, _ => false

instance : BEq (Except Fail (Option Obj)) := ⟨exceptEq⟩

deriving instance BEq for EvPhase
deriving instance BEq for Jank.Lex.P
deriving instance BEq for Jank.Read.Shorthand
deriving instance BEq for Jank.Read.S
deriving instance BEq for EvRun
deriving instance BEq for TEval
deriving instance BEq for TCI
deriving instance BEq for TConn
deriving instance BEq for TClient
deriving instance BEq for TTh

/-- The state a step, the scheduler and the judge read. -/
structure PKey where
  mem : TMem
  threads : Array (Option TTh)
  deriving BEq, Inhabited

def mixN (h : UInt64) (n : Nat) : UInt64 := mixHash h (hash n)

def hashTh : Option TTh → UInt64
  | none => 7
  | some .acceptor => 11
  | some (.conn c) =>
    let h := mixN 13 c.cid
    let h := mixN h c.instrs.length
    let h := mixN h ((c.remainder.map List.length).getD 1000003)
    let h := mixN h c.ev.own.size
    let h := mixN h c.ev.run.forms.length
    let h := mixN h c.ev.run.parser.lex.pos
    let h := mixN h c.tb.boxes.size
    mixN h (if c.connected then 1 else 0)
  | some (.client c) =>
    let h := mixN 17 c.cid
    let h := mixN h c.k
    let h := mixN h c.cursor
    let h := mixN h c.sessions.size
    mixHash h (hash (reprStr c.phase))

def hashMem (m : TMem) : UInt64 :=
  let h := mixN 19 m.replies.size
  let h := mixN h m.sent.size
  let h := mixN h m.evals.size
  let h := mixN h m.nextUuid
  let h := mixN h m.nextTemp
  let h := mixN h m.terminal.length
  let h := mixN h m.outBuf.length
  let h := mixN h m.accepted
  let h := mixN h m.pending.length
  let h := mixN h m.jw.arena.exprs.size
  let h := mixN h m.jw.closures.size
  let h := mixN h m.jw.heap.exs.size
  let h := mixN h m.jw.heap.lazies.size
  let h := mixN h m.jw.slots.length
  let h := mixN h m.jw.gensym
  let h := m.socks.foldl (fun h s => mixN (mixN h s.inbox.length) s.outbox.length) h
  let h := m.temps.foldl (fun h (_, b, l) => mixN (mixN h b.length) (if l then 1 else 0)) h
  let h := m.fds.foldl (fun h d => mixHash h (hash (reprStr d))) h
  mixN h (m.capLock.getD 1000)

instance : Hashable PKey where
  hash k := k.threads.foldl (fun h t => mixHash h (hashTh t)) (hashMem k.mem)

def PKey.of (p : Process TMem TTh) : PKey := { mem := p.memory, threads := p.threads }

end Jank.R6.Nrepl
