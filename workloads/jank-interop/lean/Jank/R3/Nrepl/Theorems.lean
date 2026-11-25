import Jank.R3.Nrepl.World

/-!
# Round 3, nREPL: facts about the wired replica, for every input

- thread-binding boxes (`TB`): `var::set` then `var::deref` of the same var gives the value set;
  other vars bound to other boxes are unchanged;
- `safe_eval`'s bookkeeping (evaluate.cpp:733) on the connection thread's boxes: a success shifts
  `*3 ← *2 ← *1 ← v` and leaves `*e`; a failure sets `*e` and leaves `*1`–`*3`; code with no form
  gives 0.0 in a release build (REPORT-2 R132) and aborts in a debug one;
- R127: jank's state after an eval does not depend on the request's session;
- R136: whitespace-only output gives no `:out` reply;
- N1: `eval_string` hands each form the reader returns, a whole top-level `(do ...)` included, to
  one analysis;
- N2: a lookup in a namespace that does not exist searches `user`.
-/

namespace Jank.R3.Nrepl

open Jank.Analyzer
open Jank.NreplServer (JVal kmap statusOf)

/-! ## Thread-binding boxes -/

theorem TB.set_of_bound (tb : TB) (v : VarRef) (o : Obj) (b : Nat) (h : tb.binding? v = some b) :
    tb.set v o = .ok { tb with boxes := tb.boxes.set! b o } := by
  simp [TB.set, h]

theorem TB.binding?_boxes (tb : TB) (bs : Array Obj) (v : VarRef) :
    ({ tb with boxes := bs } : TB).binding? v = tb.binding? v := rfl

theorem TB.deref_of_bound (tb : TB) (slots : Slots) (v : VarRef) (b : Nat) (h : tb.binding? v = some b) :
    tb.deref slots v = tb.boxes[b]? := by
  simp [TB.deref, h]

/-- `var::set` then `var::deref` on the same thread: the value set. -/
theorem TB.deref_set_same (tb : TB) (slots : Slots) (v : VarRef) (o : Obj) (b : Nat)
    (h : tb.binding? v = some b) (hb : b < tb.boxes.size) :
    ((tb.set v o).toOption.getD tb).deref slots v = some o := by
  rw [TB.set_of_bound tb v o b h]
  simp [Except.toOption, TB.deref, TB.binding?_boxes, h, Array.set!, hb]

/-- A var bound to another box is unchanged by `var::set`. -/
theorem TB.deref_set_other (tb : TB) (slots : Slots) (v u : VarRef) (o : Obj) (b c : Nat)
    (h : tb.binding? v = some b) (hu : tb.binding? u = some c) (hbc : b ≠ c) :
    ((tb.set v o).toOption.getD tb).deref slots u = tb.deref slots u := by
  rw [TB.set_of_bound tb v o b h]
  simp [Except.toOption, TB.deref, TB.binding?_boxes, hu, Array.set!, Array.getElem?_setIfInBounds_ne hbc]

/-- The bound boxes of `*1`, `*2`, `*3`, `*e` on a thread: distinct, in range. -/
structure Stars (tb : TB) where
  i1 : Nat
  i2 : Nat
  i3 : Nat
  ie : Nat
  h1 : tb.binding? v1 = some i1
  h2 : tb.binding? v2 = some i2
  h3 : tb.binding? v3 = some i3
  he : tb.binding? vE = some ie
  s1 : i1 < tb.boxes.size
  s2 : i2 < tb.boxes.size
  s3 : i3 < tb.boxes.size
  se : ie < tb.boxes.size
  d12 : i1 ≠ i2
  d13 : i1 ≠ i3
  d23 : i2 ≠ i3
  d1e : i1 ≠ ie
  d2e : i2 ≠ ie
  d3e : i3 ≠ ie

/-! ## `safe_eval` -/

/-- A success shifts `*3 ← *2 ← *1 ← v` (evaluate.cpp:746–748) and leaves `*e`, for every value
and every state of the thread's boxes. -/
theorem safeEval_success (s : ES) (v : Obj) (debug : Bool) (st : Stars s.tb) :
    let r := finishSafeEval s (.ok (some v)) debug
    r.2 = .ok v ∧
    r.1.tb.deref r.1.w.slots v1 = some v ∧
    r.1.tb.deref r.1.w.slots v2 = s.tb.deref s.w.slots v1 ∧
    r.1.tb.deref r.1.w.slots v3 = s.tb.deref s.w.slots v2 ∧
    r.1.tb.deref r.1.w.slots vE = s.tb.deref s.w.slots vE := by
  obtain ⟨i1, i2, i3, ie, h1, h2, h3, he, s1, s2, s3, se, d12, d13, d23, d1e, d2e, d3e⟩ := st
  simp only [finishSafeEval]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  simp [TB.set, TB.deref, TB.binding?_boxes, Except.toOption, h1, h2, h3, he, Array.set!,
    Array.getElem?_setIfInBounds, s1, s2, s3, d12, d13, d23, d1e, d2e, d3e,
    Ne.symm d12, Ne.symm d13, Ne.symm d23, Ne.symm d1e, Ne.symm d2e, Ne.symm d3e]

/-- R132 for every state: code with no form leaves `*1` = the zeroed object (0.0) in a release
build. -/
theorem safeEval_noForm_release (s : ES) (st : Stars s.tb) :
    let r := finishSafeEval s (.ok none) false
    r.2 = .ok real0 ∧ r.1.tb.deref r.1.w.slots v1 = some real0 := by
  obtain ⟨i1, i2, i3, ie, h1, h2, h3, he, s1, s2, s3, se, d12, d13, d23, d1e, d2e, d3e⟩ := st
  simp only [finishSafeEval]
  refine ⟨?_, ?_⟩ <;>
  simp [TB.set, TB.deref, TB.binding?_boxes, Except.toOption, h1, h2, h3, Array.set!,
    Array.getElem?_setIfInBounds, s1, d12, d13]

/-- In a debug build, code with no form aborts the process (option.hpp `unwrap`'s assert). -/
theorem safeEval_noForm_debug (s : ES) :
    (finishSafeEval s (.ok none) true).2 = .crash "jank_debug_assert(set) in option::unwrap: abort()" := rfl

/-- A failure (a thrown object, an `error_ref`, a `std::exception`) sets `*e` and leaves `*1`,
`*2`, `*3`, whatever the thread's boxes held. -/
theorem safeEval_failure (s : ES) (f : Fail) (st : Stars s.tb)
    (hf : f.isUser = true) :
    let r := finishSafeEval s (.error f) false
    (∃ e, r.2 = .failed e ∧ r.1.tb.deref r.1.w.slots vE = some e) ∧
    r.1.tb.deref r.1.w.slots v1 = s.tb.deref s.w.slots v1 ∧
    r.1.tb.deref r.1.w.slots v2 = s.tb.deref s.w.slots v2 ∧
    r.1.tb.deref r.1.w.slots v3 = s.tb.deref s.w.slots v3 := by
  obtain ⟨i1, i2, i3, ie, h1, h2, h3, he, s1, s2, s3, se, d12, d13, d23, d1e, d2e, d3e⟩ := st
  cases f with
  | thrown o =>
    cases o <;> simp [finishSafeEval, failObj, TB.set, TB.deref, TB.binding?_boxes, Except.toOption, h1, h2, h3, he,
      Array.set!, Array.getElem?_setIfInBounds, se, Ne.symm d1e, Ne.symm d2e, Ne.symm d3e] <;>
      (rename_i t _; cases t <;> simp [TB.set, TB.deref, TB.binding?_boxes, Except.toOption, h1, h2, h3, he,
        Array.set!, Array.getElem?_setIfInBounds, se, Ne.symm d1e, Ne.symm d2e, Ne.symm d3e])
  | error k m =>
    simp [finishSafeEval, failObj, TB.set, TB.deref, TB.binding?_boxes, Except.toOption, h1, h2, h3, he,
      Array.set!, Array.getElem?_setIfInBounds, se, Ne.symm d1e, Ne.symm d2e, Ne.symm d3e]
  | stdex m =>
    simp [finishSafeEval, failObj, TB.set, TB.deref, TB.binding?_boxes, Except.toOption, h1, h2, h3, he,
      Array.set!, Array.getElem?_setIfInBounds, se, Ne.symm d1e, Ne.symm d2e, Ne.symm d3e]
  | ub _ => simp [Fail.isUser] at hf
  | unsupported _ => simp [Fail.isUser] at hf
  | fuel => simp [Fail.isUser] at hf

/-! ## R127: the session is not part of jank's state -/

/-- `do-eval`'s effect on the connection does not depend on the request map (only its replies
do): the request's `session` is never read. -/
theorem jankDoEval_state_indep (c : JConn) (r r' : JVal) (q : EvalReq) :
    (jankDoEval c r q).1 = (jankDoEval c r' q).1 := by
  unfold jankDoEval
  split
  · rfl
  · simp only []
    split
    · rfl
    · rfl
    · rfl
    · split <;> rfl

/-- R127 for every eval: two requests that differ only in their session leave jank's process
and connection in the same state, so a session's `*1`, `*ns*` and `*e` are the connection's. -/
theorem jankHandle_eval_session_indep (c : JConn) (id code : String) (ns file : Option String) (s1 s2 : Nat) :
    (jankHandle c id (.eval code ns s1 file)).1 = (jankHandle c id (.eval code ns s2 file)).1 := by
  simp only [jankHandle]
  exact jankDoEval_state_indep _ _ _ _

/-! ## R136: whitespace-only output -/

/-- For every output: `do-eval` sends no `:out` exactly when the output is only C whitespace
(`blank?`, string.jank:201), so `(println)` or `(print " ")` answers no output at all. -/
theorem outReply_nil_iff (out : List UInt8) :
    outReply out = .nil ↔ Jank.NreplServer.blank (some out) = true := by
  unfold outReply
  split
  · simp_all
  · rename_i h; simp [h, kmap]

/-! ## N1: a top-level `do` is analyzed whole -/

/-- Whatever form the reader returns — a whole `(do ...)` included — `eval_string`'s next step
analyzes that form as one unit (context_dynamic.cpp:59–71); Clojure's `Compiler.eval` evaluates a
top-level `do`'s forms one by one (Compiler.java:7685). -/
theorem evalString_analyzes_whole_form (r : EvRun) (s : ES) (file : String) (f : Obj)
    (p' : Jank.Read.S) (hphase : r.phase = .read) (hread : readNext r.parser (curNsName s) file = (.form f, p')) :
    (r.step s file).1.phase = .analyze f := by
  simp [EvRun.step, hphase, hread]

/-! ## N2: a lookup in a namespace that does not exist -/

/-- For every process state and name: when no namespace has that name, `lookup` searches `user`
(handler/lookup.jank:11). -/
theorem lookupTarget_unknown (w : JW) (n : String) (h : w.nss.find? (·.name == n) = none) :
    lookupTarget w (some n) = w.nss.find? (·.name == "user") := by
  simp [lookupTarget, h]

end Jank.R3.Nrepl
