import Jank.R3.Proofs.AtomLin

/-!
# The step of `Jank.Atom.prog` keeps the linearizability invariant (round 3, proofs)

Every instruction of every phase of the fragment (`AtomLin.COp`), whatever the locks, the
platform (`llsc`), the mode (jank or Clojure) and the spurious-failure decision: the invariant
`AtomLin.GInv` holds after it. `stepKeeps` is the case analysis; the theorems are in
`AtomMain`.
-/

namespace Jank.R3.Proofs.AtomLin

open Determinismo Jank.Atom Jank.R3.Proofs Jank.R3.Proofs.Lin

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

/-- The invariant: the platform flags, the linearization invariant and the locks' holders. -/
def InvF (spec : Spec Nat Op Res) (v0 : Nat) (nc llsc clj : Bool) (p : Process Mem Loc) : Prop :=
  p.memory.llsc = llsc ∧ p.memory.clojure = clj ∧
    ∃ lin phs, GInv spec v0 nc p.memory p.threads p.steps lin phs ∧ MInv p.memory phs

structure SpecOK (spec : Spec Nat Op Res) : Prop where
  swap : ∀ v, spec v .swapInc (v + 1) (.val (v + 1))
  deref : ∀ v, spec v .deref v (.val v)
  reset : ∀ v x, spec v (.reset x) x (.val x)
  casT : ∀ v n, spec v (.cas v n) n (.bool true)
  casF : ∀ v o n, v ≠ o → spec v (.cas o n) v (.bool false)

theorem spurious_eq (p : Process Mem Loc) :
    (∃ b d, spurious p = .ok b {p with decisions := d} ∧ (b = true → p.memory.llsc = true ∧ p.memory.clojure = false)) ∨
    (∃ e, spurious p = .error e p) := by
  by_cases hc : (p.memory.llsc && !p.memory.clojure) = true
  · cases h : (Chaotic.decisions p).next "cpu.cas_spurious" [7, 1] with
    | ok vd =>
      obtain ⟨v, d⟩ := vd
      left
      refine ⟨v == 1, d, ?_, ?_⟩
      · simp [spurious, hc, decideWeighted, h, bind, EStateM.bind, mem, get, getThe, MonadStateOf.get, EStateM.get,
          pure, EStateM.pure, set, EStateM.set, Chaotic.setDecisions, Functor.map, EStateM.map]
      · intro _; simpa using hc
    | error e =>
      right; exact ⟨e, by simp [spurious, hc, decideWeighted, h, bind, EStateM.bind, mem, get, getThe,
        MonadStateOf.get, EStateM.get, pure, EStateM.pure, throw, throwThe, MonadExceptOf.throw, EStateM.throw]⟩
  · left
    refine ⟨false, p.decisions, ?_, by simp⟩
    simp only [Bool.not_eq_true] at hc
    simp [spurious, hc, bind, EStateM.bind, mem, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure]

theorem notin_lin_of_fresh {spec : Spec Nat Op Res} {v0 : Nat} {nc : Bool} {m : Mem}
    {threads : Array (Option Loc)} {steps : Nat} {lin : List LE} {phs : Nat → Ph × List COp}
    (g : GInv spec v0 nc m threads steps lin phs) {x : Nat} (hx : x ∉ m.history.toList.map (·.id)) :
    x ∉ lin.map (·.id) := by
  intro hc
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hc
  obtain ⟨h, hh, hid, _⟩ := g.linRec e he
  exact hx (List.mem_map.mpr ⟨h, hh, hid⟩)

theorem calls_record (ws : List (Nat × WatchFn)) (hw : ∀ w ∈ ws, w.2 = .record) (o n : Nat) :
    ws.map (fun (k, f) => Instr.callWatch k f o n) = (ws.map (·.1)).map (fun k => Instr.callWatch k .record o n) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    obtain ⟨k, f⟩ := w
    have : f = .record := hw (k, f) List.mem_cons_self
    subst this
    simp [ih (fun w hw' => hw w (List.mem_cons_of_mem _ hw'))]

theorem watches_add_record (ws : List (Nat × WatchFn)) (hw : ∀ w ∈ ws, w.2 = .record) (k : Nat) :
    ∀ w ∈ ws.filter (·.1 != k) ++ [(k, WatchFn.record)], w.2 = .record := by
  intro w hw'
  rcases List.mem_append.mp hw' with h | h
  · exact hw w (List.mem_filter.mp h).1
  · simp at h; subst h; rfl

theorem watches_remove_record (ws : List (Nat × WatchFn)) (hw : ∀ w ∈ ws, w.2 = .record) (k : Nat) :
    ∀ w ∈ ws.filter (·.1 != k), w.2 = .record := by
  intro w hw'
  exact hw w (List.mem_filter.mp hw').1

theorem invoke_threadOK {spec : Spec Nat Op Res} {v0 : Nat} {nc : Bool} {m : Mem}
    {threads : Array (Option Loc)} {steps : Nat} {lin : List LE} {phs : Nat → Ph × List COp}
    (g : GInv spec v0 nc m threads steps lin phs) {t : Nat} {c : COp} {cs : List COp}
    (hph : phs t = (.idle, c :: cs)) {x : Nat} (hx : c.ids = [x]) {o : Op}
    (ho : c.first.pending = some (x, o)) (hpo : c.first.post = none) {l' : Loc} (hloc : LocOK c.first l')
    (hins : l'.instrs = c.first.instrs ++ restInstrs cs)
    (hnc : nc = true → c.first.noCas = true ∧ ∀ c' ∈ cs, c'.noCas = true) (nd : Nat) :
    ThreadOK nc (m.history.toList ++ [{ id := x, node := nd, op := o, invoke := steps }]) lin (c.first, cs) (some l') := by
  have hfresh : x ∉ m.history.toList.map (·.id) := g.restFresh t x (by rw [hph]; simp [hx])
  refine ⟨hins, hloc, ?_, ?_, hnc⟩
  · intro x' o' h
    rw [ho] at h; injection h with h; injection h with h1 h2; subst h1; subst h2
    exact ⟨⟨_, List.mem_append_right _ List.mem_cons_self, rfl, rfl, rfl⟩, notin_lin_of_fresh g hfresh⟩
  · intro x' r' h; rw [hpo] at h; cases h

set_option hygiene false in
/-- The locks' invariant after a step that leaves the watches lock alone. -/
macro "mtac" : tactic => `(tactic| exact hM.same (by first | rfl | (simp [(lockShared_eq hlk).1]))
  (by first | rfl | (simp [(lockShared_eq hlk).1])) (by first | rfl | simp) (by first | rfl | simp [hcl])
  (by rw [hph]; simp [Ph.isW]) (by rw [hph]; simp [Ph.isL]) (by rw [hph]; simp [Ph.isR]))

syntax "astep" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| astep [$hs,*]) => `(tactic| simp [prog, stepLogged, step, $hs,*, bind, EStateM.bind, mem, get, getThe,
      MonadStateOf.get, EStateM.get, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet,
      EStateM.modifyGet, setMem, Jank.Atom.invoke, answer, stamp])

theorem stepKeeps {spec : Spec Nat Op Res} {v0 : Nat} {nc llsc clj : Bool} (hs : SpecOK spec)
    (hspur : llsc = true → clj = false → nc = false → ∀ v o n, spec v (.cas o n) v (.bool false)) :
    StepKeeps prog (InvF spec v0 nc llsc clj) := by
  intro p t l ⟨hfl, hfc, lin, phs, g, hM⟩ hl
  have ht : t < p.threads.size := getD_some_lt _ _ _ hl
  have hT := g.threadOK t
  rw [hl] at hT
  obtain ⟨hins, hloc, hpend, hpost, hnc⟩ := hT
  rcases hph : phs t with ⟨ph, rest⟩
  rw [hph] at hins hloc hpend hpost hnc
  simp only at hins hloc hpend hpost hnc
  cases ph with
  | drD x =>
    simp only [Ph.instrs, List.cons_append, List.nil_append] at hins
    simp [prog, stepLogged, step, hins, bind, EStateM.bind, mem, get, getThe, MonadStateOf.get, EStateM.get, pure,
      EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, setMem, Jank.Atom.invoke, answer, stamp]
    refine ⟨hfl, hfc, lin ++ [⟨x, .deref, .val p.memory.val, p.steps⟩],
      fun i => if i = t then (.nfC x (.val p.memory.val) 0 0 [] false, rest) else phs i, ?_, by mtac⟩
    refine g.lp ht hl (o := .deref) (by rw [hph]; rfl) rfl g.watchesRecord (hs.deref _) ?_ trivial rfl rfl
      (fun _ => rfl) (by rw [hph]; rfl) (by rw [hph])
    simp [Ph.instrs]
  | swL x =>
    simp only [Ph.instrs, List.cons_append, List.nil_append] at hins
    astep [hins]
    refine ⟨hfl, hfc, lin, fun i => if i = t then (.swV x, rest) else phs i, ?_, by mtac⟩
    refine g.neutral (s' := (.swV x, rest)) ht ?_ ?_ ?_ ?_ (by rw [hph]; rfl) (by rw [hph])
    · rfl
    · rfl
    · exact g.watchesRecord
    refine ⟨by simp [Ph.instrs], rfl, ?_, ?_, ?_⟩
    · intro x' o' h; exact hpend x' o' h
    · intro x' r' h; cases h
    · intro hc; exact hnc hc
  | swV x =>
    simp only [Ph.instrs, List.cons_append, List.nil_append] at hins
    cases hlk : p.memory.validatorMutex.lockShared t with
    | some vm =>
      astep [hins, hlk]
      refine ⟨hfl, hfc, lin, fun i => if i = t then (.swU x, rest) else phs i, ?_, by mtac⟩
      refine g.neutral (s' := (.swU x, rest)) ht ?_ ?_ ?_ ?_ (by rw [hph]; rfl) (by rw [hph])
      · rfl
      · rfl
      · exact g.watchesRecord
      refine ⟨by simp [Ph.instrs], hloc, ?_, ?_, ?_⟩
      · intro x' o' h; exact hpend x' o' h
      · intro x' r' h; cases h
      · intro hc; exact hnc hc
    | none =>
      astep [hins, hlk]
      exact ⟨hfl, hfc, lin, phs, g, hM⟩
  | swC x =>
    simp only [Ph.instrs, List.cons_append, List.nil_append] at hins
    have hx1000 : x ≠ 1000 := fun h => g.not1000 t (by rw [hph, ← h]; simp [tids, Ph.ids])
    rcases spurious_eq p with ⟨b, d, hsp, hb⟩ | ⟨e, hsp⟩
    · by_cases hc : p.memory.val = l.v ∧ b = false
      · astep [hins, hsp, hc, hx1000]
        have hn : l.next = l.v + 1 := hloc
        refine ⟨hfl, hfc, lin ++ [⟨x, .swapInc, .val l.next, p.steps⟩],
          fun i => if i = t then (.nfL x (.val l.next) l.v l.next, rest) else phs i, ?_, by mtac⟩
        refine g.lp ht hl (o := .swapInc) (by rw [hph]; rfl) ?_ ?_ ?_ ?_ trivial rfl rfl
          (fun _ => rfl) (by rw [hph]; rfl) (by rw [hph])
        · rfl
        · exact g.watchesRecord
        · show spec p.memory.val .swapInc l.next (.val l.next)
          rw [hn, ← hc.1]; exact hs.swap _
        · simp [Ph.instrs]
      · astep [hins, hsp, hc, hx1000]
        refine ⟨hfl, hfc, lin, fun i => if i = t then (.swL x, rest) else phs i, ?_, by mtac⟩
        refine g.neutral (s' := (.swL x, rest)) ht ?_ ?_ ?_ ?_ (by rw [hph]; rfl) (by rw [hph])
        · rfl
        · rfl
        · exact g.watchesRecord
        refine ⟨by simp [Ph.instrs], trivial, ?_, ?_, ?_⟩
        · intro x' o' h; exact hpend x' o' h
        · intro x' r' h; cases h
        · intro hc; exact hnc hc
    · astep [hins, hsp]
      exact ⟨hfl, hfc, lin, phs, g, hM⟩
  | idle =>
    cases rest with
    | nil =>
      simp only [Ph.instrs, restInstrs_nil, List.append_nil] at hins
      astep [hins]
      exact ⟨hfl, hfc, lin, phs, g.done ht hl hins, hM⟩
    | cons c cs =>
      rw [restInstrs_cons] at hins
      simp only [Ph.instrs, List.nil_append] at hins
      have hncc : nc = true → c.noCas = true ∧ ∀ c' ∈ cs, c'.noCas = true := fun h =>
        ⟨(hnc h).2 c List.mem_cons_self, fun c' hc' => (hnc h).2 c' (List.mem_cons_of_mem _ hc')⟩
      cases c with
      | swap x =>
        simp only [COp.instrs, List.cons_append, swapInc] at hins
        astep [hins]
        refine ⟨hfl, hfc, lin, fun i => if i = t then ((COp.swap x).first, cs) else phs i, ?_, by mtac⟩
        refine g.invoke ht hph rfl .swapInc t ?_ ?_ ?_ ?_ rfl
        · rfl
        · rfl
        · rfl
        · exact invoke_threadOK g hph rfl rfl rfl trivial (by simp [COp.first, Ph.instrs])
            (fun h => ⟨rfl, (hncc h).2⟩) t
      | deref x =>
        simp only [COp.instrs, List.cons_append, derefOp] at hins
        astep [hins]
        refine ⟨hfl, hfc, lin, fun i => if i = t then ((COp.deref x).first, cs) else phs i, ?_, by mtac⟩
        refine g.invoke ht hph rfl .deref t ?_ ?_ ?_ ?_ rfl
        · rfl
        · rfl
        · rfl
        · exact invoke_threadOK g hph rfl rfl rfl trivial (by simp [COp.first, Ph.instrs])
            (fun h => ⟨rfl, (hncc h).2⟩) t
      | cas x o n =>
        simp only [COp.instrs, List.cons_append, casOp] at hins
        astep [hins]
        refine ⟨hfl, hfc, lin, fun i => if i = t then ((COp.cas x o n).first, cs) else phs i, ?_, by mtac⟩
        refine g.invoke ht hph rfl (.cas o n) t ?_ ?_ ?_ ?_ rfl
        · rfl
        · rfl
        · rfl
        · exact invoke_threadOK g hph rfl rfl rfl trivial (by simp [COp.first, Ph.instrs])
            (fun h => absurd (hncc h).1 (by simp [COp.noCas])) t
      | reset x v =>
        simp only [COp.instrs, List.cons_append, resetTo] at hins
        astep [hins]
        refine ⟨hfl, hfc, lin, fun i => if i = t then ((COp.reset x v).first, cs) else phs i, ?_, by mtac⟩
        refine g.invoke ht hph rfl (.reset v) t ?_ ?_ ?_ ?_ rfl
        · rfl
        · rfl
        · rfl
        · exact invoke_threadOK g hph rfl rfl rfl trivial (by simp [COp.first, Ph.instrs])
            (fun h => ⟨rfl, (hncc h).2⟩) t
      | watch k =>
        simp only [COp.instrs, List.cons_append, addWatch] at hins
        cases hcl : p.memory.clojure with
        | true =>
          astep [hins, hcl]
          refine ⟨hfl, hfc, lin, fun i => if i = t then (.wL k, cs) else phs i, ?_, by exact hM.cljMode hcl (by rfl) (by rfl) (by rfl) (by rfl) _⟩
          refine g.neutral (s' := (.wL k, cs)) ht ?_ ?_ ?_ ?_ (by rw [hph]; rfl) (by rw [hph]; simp [COp.ids])
          · rfl
          · rfl
          · exact g.watchesRecord
          refine ⟨by simp [Ph.instrs], trivial, ?_, ?_, fun h => ⟨rfl, (hncc h).2⟩⟩
          · intro x' o' h; cases h
          · intro x' r' h; cases h
        | false =>
          astep [hins, hcl]
          refine ⟨hfl, by simpa [hcl] using hfc, lin, fun i => if i = t then (.wL k, cs) else phs i, ?_, by exact hM.announce (by rfl) (by rfl) (by simp [hcl]) hcl (by rw [hph]; simp [Ph.isR, Ph.isW, Ph.isL]) (by simp [Ph.isL])⟩
          refine g.neutral (s' := (.wL k, cs)) ht ?_ ?_ ?_ ?_ (by rw [hph]; rfl) (by rw [hph]; simp [COp.ids])
          · rfl
          · rfl
          · exact g.watchesRecord
          refine ⟨by simp [Ph.instrs], trivial, ?_, ?_, fun h => ⟨rfl, (hncc h).2⟩⟩
          · intro x' o' h; cases h
          · intro x' r' h; cases h
  | swU x =>
    simp only [Ph.instrs, List.cons_append, List.nil_append] at hins
    astep [hins]
    refine ⟨hfl, hfc, lin, fun i => if i = t then (.swC x, rest) else phs i, ?_, by mtac⟩
    refine g.neutral (s' := (.swC x, rest)) ht ?_ ?_ ?_ ?_ (by rw [hph]; rfl) (by rw [hph])
    · rfl
    · rfl
    · exact g.watchesRecord
    refine ⟨by simp [Ph.instrs], hloc, ?_, ?_, ?_⟩
    · intro x' o' h; exact hpend x' o' h
    · intro x' r' h; cases h
    · intro hc; exact hnc hc
  | casV x o n =>
    simp only [Ph.instrs, List.cons_append, List.nil_append] at hins
    cases hlk : p.memory.validatorMutex.lockShared t with
    | some vm =>
      astep [hins, hlk]
      refine ⟨hfl, hfc, lin, fun i => if i = t then (.casU x o n, rest) else phs i, ?_, by mtac⟩
      refine g.neutral (s' := (.casU x o n, rest)) ht ?_ ?_ ?_ ?_ (by rw [hph]; rfl) (by rw [hph])
      · rfl
      · rfl
      · exact g.watchesRecord
      refine ⟨by simp [Ph.instrs], trivial, ?_, ?_, ?_⟩
      · intro x' o' h; exact hpend x' o' h
      · intro x' r' h; cases h
      · intro hc; exact hnc hc
    | none =>
      astep [hins, hlk]
      exact ⟨hfl, hfc, lin, phs, g, hM⟩
  | casU x o n =>
    simp only [Ph.instrs, List.cons_append, List.nil_append] at hins
    astep [hins]
    refine ⟨hfl, hfc, lin, fun i => if i = t then (.casC x o n, rest) else phs i, ?_, by mtac⟩
    refine g.neutral (s' := (.casC x o n, rest)) ht ?_ ?_ ?_ ?_ (by rw [hph]; rfl) (by rw [hph])
    · rfl
    · rfl
    · exact g.watchesRecord
    refine ⟨by simp [Ph.instrs], trivial, ?_, ?_, ?_⟩
    · intro x' o' h; exact hpend x' o' h
    · intro x' r' h; cases h
    · intro hc; exact hnc hc
  | rsV x v =>
    simp only [Ph.instrs, List.cons_append, List.nil_append] at hins
    cases hlk : p.memory.validatorMutex.lockShared t with
    | some vm =>
      astep [hins, hlk]
      refine ⟨hfl, hfc, lin, fun i => if i = t then (.rsU x v, rest) else phs i, ?_, by mtac⟩
      refine g.neutral (s' := (.rsU x v, rest)) ht ?_ ?_ ?_ ?_ (by rw [hph]; rfl) (by rw [hph])
      · rfl
      · rfl
      · exact g.watchesRecord
      refine ⟨by simp [Ph.instrs], trivial, ?_, ?_, ?_⟩
      · intro x' o' h; exact hpend x' o' h
      · intro x' r' h; cases h
      · intro hc; exact hnc hc
    | none =>
      astep [hins, hlk]
      exact ⟨hfl, hfc, lin, phs, g, hM⟩
  | rsU x v =>
    simp only [Ph.instrs, List.cons_append, List.nil_append] at hins
    astep [hins]
    refine ⟨hfl, hfc, lin, fun i => if i = t then (.rsL x v, rest) else phs i, ?_, by mtac⟩
    refine g.neutral (s' := (.rsL x v, rest)) ht ?_ ?_ ?_ ?_ (by rw [hph]; rfl) (by rw [hph])
    · rfl
    · rfl
    · exact g.watchesRecord
    refine ⟨by simp [Ph.instrs], trivial, ?_, ?_, ?_⟩
    · intro x' o' h; exact hpend x' o' h
    · intro x' r' h; cases h
    · intro hc; exact hnc hc
  | rsL x v =>
    simp only [Ph.instrs, List.cons_append, List.nil_append] at hins
    astep [hins]
    refine ⟨hfl, hfc, lin, fun i => if i = t then (.rsS x v, rest) else phs i, ?_, by mtac⟩
    refine g.neutral (s' := (.rsS x v, rest)) ht ?_ ?_ ?_ ?_ (by rw [hph]; rfl) (by rw [hph])
    · rfl
    · rfl
    · exact g.watchesRecord
    refine ⟨by simp [Ph.instrs], trivial, ?_, ?_, ?_⟩
    · intro x' o' h; exact hpend x' o' h
    · intro x' r' h; cases h
    · intro hc; exact hnc hc
  | rsS x v =>
    simp only [Ph.instrs, List.cons_append, List.nil_append] at hins
    astep [hins]
    refine ⟨hfl, hfc, lin ++ [⟨x, .reset v, .val v, p.steps⟩],
      fun i => if i = t then (.nfL x (.val v) l.v v, rest) else phs i, ?_, by mtac⟩
    refine g.lp ht hl (o := .reset v) (by rw [hph]; rfl) ?_ ?_ ?_ ?_ trivial rfl rfl
      (fun _ => rfl) (by rw [hph]; rfl) (by rw [hph])
    · rfl
    · exact g.watchesRecord
    · exact hs.reset _ _
    · simp [Ph.instrs]
  | casC x o n =>
    simp only [Ph.instrs, List.cons_append, List.nil_append] at hins
    rcases spurious_eq p with ⟨b, d, hsp, hb⟩ | ⟨e, hsp⟩
    · by_cases hc : p.memory.val = o ∧ b = false
      · astep [hins, hsp, hc]
        refine ⟨hfl, hfc, lin ++ [⟨x, .cas o n, .bool true, p.steps⟩],
          fun i => if i = t then (.nfL x (.bool true) o n, rest) else phs i, ?_, by mtac⟩
        refine g.lp ht hl (o := .cas o n) (by rw [hph]; rfl) ?_ ?_ ?_ ?_ trivial rfl rfl
          (fun _ => rfl) (by rw [hph]; rfl) (by rw [hph])
        · rfl
        · exact g.watchesRecord
        · show spec p.memory.val (.cas o n) n (.bool true)
          rw [hc.1]; exact hs.casT _ _
        · simp [Ph.instrs]
      · astep [hins, hsp, hc]
        refine ⟨hfl, hfc, lin ++ [⟨x, .cas o n, .bool false, p.steps⟩],
          fun i => if i = t then (.nfC x (.bool false) o n [] false, rest) else phs i, ?_, by mtac⟩
        refine g.lp ht hl (o := .cas o n) (by rw [hph]; rfl) ?_ ?_ ?_ ?_ trivial rfl rfl
          (fun _ => rfl) (by rw [hph]; rfl) (by rw [hph])
        · rfl
        · exact g.watchesRecord
        · show spec p.memory.val (.cas o n) p.memory.val (.bool false)
          by_cases hvo : p.memory.val = o
          · have hbt : b = true := by
              cases b with
              | true => rfl
              | false => exact absurd ⟨hvo, rfl⟩ hc
            obtain ⟨h1, h2⟩ := hb hbt
            have hncf : nc = false := by
              cases hn : nc with
              | false => rfl
              | true => exact absurd (hnc hn).1 (by simp [Ph.noCas])
            exact hspur (hfl ▸ h1) (hfc ▸ h2) hncf _ _ _
          · exact hs.casF _ _ _ hvo
        · simp [Ph.instrs]
    · astep [hins, hsp]
      exact ⟨hfl, hfc, lin, phs, g, hM⟩
  | nfL x r o n =>
    simp only [Ph.instrs, List.cons_append, List.nil_append] at hins
    cases hcl : p.memory.clojure with
    | true =>
      astep [hins, hcl]
      refine ⟨hfl, hfc, lin, fun i => if i = t then (.nfC x r o n (p.memory.watches.map (·.1)) false, rest) else phs i, ?_, by exact hM.cljMode hcl (by rfl) (by rfl) (by rfl) (by rfl) _⟩
      refine g.neutral (s' := (.nfC x r o n (p.memory.watches.map (·.1)) false, rest)) ht ?_ ?_ ?_ ?_
        (by rw [hph]; rfl) (by rw [hph])
      · rfl
      · rfl
      · exact g.watchesRecord
      refine ⟨?_, trivial, ?_, ?_, ?_⟩
      · simp only [Ph.instrs, calls_record _ g.watchesRecord]; simp
      · intro x' o' h; cases h
      · intro x' r' h; exact hpost x' r' h
      · intro hc; exact hnc hc
    | false =>
      cases hlk : p.memory.watchesMutex.lockShared t with
      | some wm =>
        astep [hins, hcl, hlk]
        refine ⟨hfl, by simpa [hcl] using hfc, lin,
          fun i => if i = t then (.nfC x r o n (p.memory.watches.map (·.1)) true, rest) else phs i, ?_, by exact hM.lockShared hlk (by rfl) (by rfl) (by simp [hcl]) hcl (by rw [hph]; simp [Ph.isR, Ph.isW, Ph.isL]) (by simp [Ph.isR])⟩
        refine g.neutral (s' := (.nfC x r o n (p.memory.watches.map (·.1)) true, rest)) ht ?_ ?_ ?_ ?_
          (by rw [hph]; rfl) (by rw [hph])
        · rfl
        · rfl
        · exact g.watchesRecord
        refine ⟨?_, trivial, ?_, ?_, ?_⟩
        · simp only [Ph.instrs, calls_record _ g.watchesRecord]; simp
        · intro x' o' h; cases h
        · intro x' r' h; exact hpost x' r' h
        · intro hc; exact hnc hc
      | none =>
        astep [hins, hcl, hlk]
        exact ⟨hfl, hfc, lin, phs, g, hM⟩
  | nfC x r o n ks u =>
    cases ks with
    | cons k ks =>
      simp only [Ph.instrs, List.map_cons, List.cons_append, List.append_assoc] at hins
      astep [hins, watchBody]
      have hMn : MInv { p.memory with calls := p.memory.calls ++ [(k, o, n)] }
          (fun i => if i = t then (.nfC x r o n ks u, rest) else phs i) := by
        exact hM.same (by rfl) (by rfl) (by rfl) (by rfl) (by rw [hph]; simp [Ph.isW]) (by rw [hph]; simp [Ph.isL])
          (by rw [hph]; cases u <;> simp [Ph.isR])
      refine ⟨hfl, hfc, lin, fun i => if i = t then (.nfC x r o n ks u, rest) else phs i, ?_, hMn⟩
      refine g.neutral (s' := (.nfC x r o n ks u, rest)) ht ?_ ?_ ?_ ?_ (by rw [hph]; rfl) (by rw [hph])
      · rfl
      · rfl
      · exact g.watchesRecord
      refine ⟨by simp [Ph.instrs], trivial, ?_, ?_, ?_⟩
      · intro x' o' h; cases h
      · intro x' r' h; exact hpost x' r' h
      · intro hc; exact hnc hc
    | nil =>
      cases u with
      | true =>
        simp only [Ph.instrs, List.map_nil, List.nil_append, ↓reduceIte, List.cons_append] at hins
        astep [hins]
        refine ⟨hfl, hfc, lin, fun i => if i = t then (.nfC x r o n [] false, rest) else phs i, ?_, by exact hM.unlockShared (by rfl) (by rfl) (by rfl) (by rw [hph]; simp [Ph.isW, Ph.isL])⟩
        refine g.neutral (s' := (.nfC x r o n [] false, rest)) ht ?_ ?_ ?_ ?_ (by rw [hph]; rfl) (by rw [hph])
        · rfl
        · rfl
        · exact g.watchesRecord
        refine ⟨by simp [Ph.instrs], trivial, ?_, ?_, ?_⟩
        · intro x' o' h; cases h
        · intro x' r' h; exact hpost x' r' h
        · intro hc; exact hnc hc
      | false =>
        simp only [Ph.instrs, List.map_nil, List.nil_append, Bool.false_eq_true, ↓reduceIte, List.cons_append]
          at hins
        astep [hins]
        refine ⟨hfl, hfc, lin, fun i => if i = t then (.idle, rest) else phs i, ?_, by mtac⟩
        refine g.ret ht hl hph ?_ ?_ ?_ ?_
        · simp [ansF]
        · rfl
        · rfl
        · rfl
  | wL k =>
    simp only [Ph.instrs, List.cons_append, List.nil_append] at hins
    cases hcl : p.memory.clojure with
    | true =>
      astep [hins, hcl]
      refine ⟨hfl, hfc, lin, fun i => if i = t then (.wD k, rest) else phs i, ?_, by exact hM.cljMode hcl (by rfl) (by rfl) (by rfl) (by rfl) _⟩
      refine g.neutral (s' := (.wD k, rest)) ht ?_ ?_ ?_ ?_ (by rw [hph]; rfl) (by rw [hph])
      · rfl
      · rfl
      · exact g.watchesRecord
      refine ⟨by simp [Ph.instrs], trivial, ?_, ?_, ?_⟩
      · intro x' o' h; cases h
      · intro x' r' h; cases h
      · intro hc; exact hnc hc
    | false =>
      cases hlk : p.memory.watchesMutex.lock t with
      | some wm =>
        astep [hins, hcl, hlk]
        refine ⟨hfl, by simpa [hcl] using hfc, lin, fun i => if i = t then (.wD k, rest) else phs i, ?_, by exact hM.lock hlk (by rfl) (by rfl) (by simp [hcl]) hcl (by simp [Ph.isW])⟩
        refine g.neutral (s' := (.wD k, rest)) ht ?_ ?_ ?_ ?_ (by rw [hph]; rfl) (by rw [hph])
        · rfl
        · rfl
        · exact g.watchesRecord
        refine ⟨by simp [Ph.instrs], trivial, ?_, ?_, ?_⟩
        · intro x' o' h; cases h
        · intro x' r' h; cases h
        · intro hc; exact hnc hc
      | none =>
        astep [hins, hcl, hlk]
        exact ⟨hfl, hfc, lin, phs, g, hM⟩
  | wD k =>
    simp only [Ph.instrs, List.cons_append, List.nil_append] at hins
    astep [hins]
    refine ⟨hfl, hfc, lin, fun i => if i = t then (.wU, rest) else phs i, ?_, by mtac⟩
    refine g.neutral (s' := (.wU, rest)) ht ?_ ?_ ?_ ?_ (by rw [hph]; rfl) (by rw [hph])
    · rfl
    · rfl
    · exact watches_add_record _ g.watchesRecord k
    refine ⟨by simp [Ph.instrs], trivial, ?_, ?_, ?_⟩
    · intro x' o' h; cases h
    · intro x' r' h; cases h
    · intro hc; exact hnc hc
  | wU =>
    simp only [Ph.instrs, List.cons_append, List.nil_append] at hins
    cases hcl : p.memory.clojure with
    | true =>
      astep [hins, hcl]
      refine ⟨hfl, hfc, lin, fun i => if i = t then (.idle, rest) else phs i, ?_, by exact hM.cljMode hcl (by rfl) (by rfl) (by rfl) (by rfl) _⟩
      refine g.neutral (s' := (.idle, rest)) ht ?_ ?_ ?_ ?_ (by rw [hph]; rfl) (by rw [hph])
      · rfl
      · rfl
      · exact g.watchesRecord
      refine ⟨by simp [Ph.instrs], trivial, ?_, ?_, ?_⟩
      · intro x' o' h; cases h
      · intro x' r' h; cases h
      · intro hc; exact hnc hc
    | false =>
      astep [hins, hcl]
      refine ⟨hfl, by simpa [hcl] using hfc, lin, fun i => if i = t then (.idle, rest) else phs i, ?_, by exact hM.unlock (by rfl) (by rfl) (by simp [hcl]) (by rw [hph]; simp [Ph.isR, Ph.isL])⟩
      refine g.neutral (s' := (.idle, rest)) ht ?_ ?_ ?_ ?_ (by rw [hph]; rfl) (by rw [hph])
      · rfl
      · rfl
      · exact g.watchesRecord
      refine ⟨by simp [Ph.instrs], trivial, ?_, ?_, ?_⟩
      · intro x' o' h; cases h
      · intro x' r' h; cases h
      · intro hc; exact hnc hc

end Jank.R3.Proofs.AtomLin
