import Jank.R6.Nrepl.Sim

/-!
# Round 6, nREPL: theorems

★ `eintr_draw_unused`: round 3's `tConnStep` draws `net.read.eintr` whenever a read finds its
socket's inbox empty and open, even with EINTR off (Lean lifts the `(← decideRare …)` out of
`m.cfg.eintr && …`, Threads.lean 251). For EVERY connection and process state in that situation
with EINTR off, whatever value the draw takes, the step blocks and leaves the memory and the threads
as they were (or the timeline ends at its decision limit). This is round 5's nREPLA5-4 as a theorem:
holding the draw at 0 (round 5's `whole0` walk, the `n0` counts here) loses no state.
-/

namespace Jank.R6.Nrepl

open Determinismo Jank.R3.Nrepl Jank.NreplServer

/-- A decision either gives a value or stops the timeline at its limit (Decide.lean `next`). -/
theorem next_error_limit (d : Decisions) (name : String) (w : List Nat) (e : Stop)
    (h : d.next name w = .error e) : e = .limit := by
  unfold Decisions.next at h
  by_cases h1 : w.length ≤ 1
  · simp [h1] at h
  · by_cases h2 : d.taken.size ≥ d.limit
    · simp [h1, h2] at h; exact h.symm
    · simp [h1, h2] at h

theorem eintr_draw_unused (t : Nat) (cid : Nat) (connected : Bool) (remainder : Option Bytes)
    (rest : List TCI) (ev : TEval) (tb : Jank.R3.Nrepl.TB) (p : Process TMem TTh)
    (hp : parse {} remainder = .none)
    (he : (p.memory.socks.getD cid {}).inbox = [])
    (hc : (p.memory.socks.getD cid {}).closed = false)
    (hx : p.memory.cfg.eintr = false) :
    match (tConnStep t { cid, connected, remainder, instrs := .readMsg :: rest, ev, tb }).run p with
    | .ok r p' => (match r with | .blocked => True | _ => False) ∧ p'.memory = p.memory ∧ p'.threads = p.threads
    | .error e _ => e = .limit := by
  simp only [tConnStep, tmem, EStateM.run, bind, EStateM.bind, get, getThe, MonadStateOf.get,
    EStateM.get, pure, EStateM.pure, hp, he, hc, hx, List.isEmpty_nil, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte, Bool.false_and, decideRare, decideWeighted, set,
    MonadStateOf.set]
  rcases h : (Chaotic.decisions p).next "net.read.eintr" [7, 1] with e | ⟨v, d⟩
  · have := next_error_limit _ _ _ _ h
    simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw, this]
  · simp [EStateM.set, Chaotic.setDecisions, EStateM.bind, EStateM.pure]

/-! ## The log ordering (Graph.lean `byCid`, `canonMem`)

★ `byCid_bucket`: for every log, every client and either order, a client's part of the ordered log
is its part of the log as it was (same entries, same order). Every World T reader of the six logs
reads one client's part (Graph.lean's note), so it reads the same thing from either order.
★ `byCid_append`: ordering, then appending, then ordering is ordering the appended log: the
per-client logs that steps append to stay canonical whatever interleaving appended them. -/

theorem bucket_unique {α : Type} (n : Nat) (key : α → Nat) (c c' : Nat) (x : α) (hc : c ≤ n) (hc' : c' ≤ n)
    (h1 : bucket n key c x = true) (h2 : bucket n key c' x = true) : c = c' := by
  unfold bucket at h1 h2
  by_cases e1 : c = n <;> by_cases e2 : c' = n <;> simp_all <;> omega

theorem filter_flatMap_bucket {α : Type} (n : Nat) (key : α → Nat) (xs : List α) (c : Nat) (hc : c ≤ n) :
    ∀ (cs : List Nat), (∀ c' ∈ cs, c' ≤ n) → cs.Nodup →
      ((cs.flatMap fun c' => xs.filter (bucket n key c')).filter (bucket n key c)) =
        (if c ∈ cs then xs.filter (bucket n key c) else []) := by
  intro cs
  induction cs with
  | nil => intro _ _; simp
  | cons c0 cs ih =>
    intro hle hnd
    simp only [List.flatMap_cons, List.filter_append]
    have hnd' := (List.nodup_cons.mp hnd)
    rw [ih (fun c' h => hle c' (List.mem_cons_of_mem _ h)) hnd'.2]
    by_cases e : c0 = c
    · subst e
      have : c0 ∉ cs := hnd'.1
      simp [this, List.filter_filter]
    · have hfil : (xs.filter (bucket n key c0)).filter (bucket n key c) = [] := by
        rw [List.filter_filter]
        apply List.filter_eq_nil_iff.mpr
        intro x _ hx
        simp only [Bool.and_eq_true] at hx
        exact e (bucket_unique n key c0 c x (hle c0 (by simp)) hc hx.2 hx.1)
      rw [hfil]
      simp [Ne.symm e]

theorem cidsOf_spec (n : Nat) (d : Bool) : (∀ c' ∈ cidsOf n d, c' ≤ n) ∧ (cidsOf n d).Nodup ∧
    ∀ c ≤ n, c ∈ cidsOf n d := by
  unfold cidsOf
  cases d <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · refine ⟨fun c h => ?_, List.nodup_range, fun c h => ?_⟩
    · simp [List.mem_range] at h; omega
    · simp [List.mem_range]; omega
  · have hnd : (List.range (n + 1)).reverse.Nodup := by
      unfold List.Nodup
      rw [List.pairwise_reverse]
      exact (List.nodup_range).imp fun h => fun e => h e.symm
    refine ⟨fun c h => ?_, hnd, fun c h => ?_⟩
    · simp [List.mem_range] at h; omega
    · simp [List.mem_range]; omega

theorem flatMap_congr' {α β : Type} (l : List α) (f g : α → List β) (h : ∀ a ∈ l, f a = g a) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons]
    rw [h a (by simp), ih (fun a' ha => h a' (by simp [ha]))]

theorem byCid_bucket {α : Type} (n : Nat) (key : α → Nat) (d : Bool) (xs : List α) (c : Nat) (hc : c ≤ n) :
    (byCid n key d xs).filter (bucket n key c) = xs.filter (bucket n key c) := by
  obtain ⟨h1, h2, h3⟩ := cidsOf_spec n d
  unfold byCid
  rw [filter_flatMap_bucket n key xs c hc _ h1 h2]
  simp [h3 c hc]

theorem byCid_append {α : Type} (n : Nat) (key : α → Nat) (d d' : Bool) (xs ys : List α) :
    byCid n key d (byCid n key d' xs ++ ys) = byCid n key d (xs ++ ys) := by
  obtain ⟨h1, _, _⟩ := cidsOf_spec n d
  unfold byCid
  apply flatMap_congr'
  intro c hc
  rw [List.filter_append, List.filter_append]
  have := byCid_bucket n key d' xs c (h1 c hc)
  unfold byCid at this
  rw [this]

/-! ## The World T readers of the logs, for every state

Each reader below is round 3's own expression (Threads.lean): it gives the same answer on a state and
on the same state with its logs ordered by client, either way (`orderMem d`). -/

/-- An entry whose client is `c` is in bucket `min c n`. -/
theorem bucket_of_key {α : Type} (n : Nat) (key : α → Nat) (c : Nat) (x : α) (h : key x = c) :
    bucket n key (min c n) x = true := by
  unfold bucket
  by_cases hc : c ≥ n
  · have : min c n = n := Nat.min_eq_right hc
    simp [this]; omega
  · have : min c n = c := Nat.min_eq_left (by omega)
    simp [this, h]; omega

/-- ★ Any filter that keeps only one client's entries reads the same from either order. -/
theorem byCid_filter_sub {α : Type} (n : Nat) (key : α → Nat) (d : Bool) (xs : List α) (p : α → Bool)
    (c : Nat) (hp : ∀ x, p x = true → key x = c) :
    (byCid n key d xs).filter p = xs.filter p := by
  have hb : ∀ x, p x = true → bucket n key (min c n) x = true := fun x h => bucket_of_key n key c x (hp x h)
  have h1 : ∀ ys : List α, ys.filter p = (ys.filter (bucket n key (min c n))).filter p := by
    intro ys
    rw [List.filter_filter]
    congr 1
    funext x
    cases hpx : p x
    · simp
    · simp [hb x hpx]
  rw [h1, byCid_bucket n key d xs (min c n) (Nat.min_le_right c n), ← h1]

theorem byCid_find?_sub {α : Type} (n : Nat) (key : α → Nat) (d : Bool) (xs : List α) (p : α → Bool)
    (c : Nat) (hp : ∀ x, p x = true → key x = c) :
    (byCid n key d xs).find? p = xs.find? p := by
  rw [← List.head?_filter, ← List.head?_filter, byCid_filter_sub n key d xs p c hp]

theorem byCid_any_sub {α : Type} (n : Nat) (key : α → Nat) (d : Bool) (xs : List α) (p : α → Bool)
    (c : Nat) (hp : ∀ x, p x = true → key x = c) :
    (byCid n key d xs).any p = xs.any p := by
  have h : ∀ ys : List α, ys.any p = (ys.filter p).any (fun _ => true) := by
    intro ys; simp [List.any_filter]
  rw [h, h xs, byCid_filter_sub n key d xs p c hp]

/-- ★ `tRepliesOf` (Threads.lean 547–548: the judge's replies of a request; the `.wait` step's `mine`,
512, is the same filter) is the same with the logs in either order. -/
theorem tRepliesOf_orderMem (d : Bool) (m : TMem) (s : TSent) :
    tRepliesOf (orderMem d m) s = tRepliesOf m s := by
  unfold tRepliesOf orderMem
  simp only
  rw [byCid_filter_sub m.nClients (·.1) d m.replies.toList _ s.cid]
  intro x hx
  obtain ⟨cid, r⟩ := x
  simp only [Bool.and_eq_true, beq_iff_eq] at hx
  exact hx.1

/-- ★ The judge's lookup of an eval's record (Threads.lean 587) is the same in either order. -/
theorem evalsFind_orderMem (d : Bool) (m : TMem) (s : TSent) :
    (orderMem d m).evals.toList.find? (fun e => e.cid == s.cid && e.id == s.id) =
      m.evals.toList.find? (fun e => e.cid == s.cid && e.id == s.id) := by
  unfold orderMem
  simp only
  rw [byCid_find?_sub m.nClients (·.cid) d m.evals.toList _ s.cid]
  intro x hx
  simp only [Bool.and_eq_true, beq_iff_eq] at hx
  exact hx.1

/-- ★ The judge's handler error of a connection (Threads.lean 597) is the same in either order. -/
theorem handlerErrorsFind_orderMem (d : Bool) (m : TMem) (c : Nat) :
    (orderMem d m).handlerErrors.find? (·.1 == c) = m.handlerErrors.find? (·.1 == c) := by
  unfold orderMem
  simp only
  rw [byCid_find?_sub m.nClients (·.1) d m.handlerErrors _ c]
  intro x hx
  simpa using hx

/-- ★ A connection's "already hung" test (Threads.lean 356) is the same in either order. -/
theorem hungAny_orderMem (d : Bool) (m : TMem) (c : Nat) :
    (orderMem d m).hung.any (·.1 == c) = m.hung.any (·.1 == c) := by
  unfold orderMem
  simp only
  rw [byCid_any_sub m.nClients (·.1) d m.hung _ c]
  intro x hx
  simpa using hx

end Jank.R6.Nrepl
