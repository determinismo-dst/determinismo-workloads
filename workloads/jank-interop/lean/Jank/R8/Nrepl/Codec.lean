import Jank.R6.Nrepl.Graph
import Jank.R6.Nrepl.StateHash

/-!
# Round 8, nREPL: a compact codec for World T's states

Round 6 kept each World T state (`PKey`: the memory and the threads) as a Lean object, about 3.8 KB
each once the copies a step makes are counted (an `Array.push` on a shared array copies it). T3's
graph (3,174,744 states by round 6's hashed search) did not fit, so round 6 kept 64+64-bit hashes
and could not decide T3.

The codec splits a state into seven memory components and one per thread, and interns each
component in its own table (hash-consing): a state becomes a short array of small indices (8 bytes
each, unboxed), and each distinct component is stored once. Two states get the same code exactly
when their components are, one by one, the ones a table already holds.

What a table promises (`Tab.holds`): the value stored at an index it returned is the value given
(`=`), or equal to it by round 6's state equality (the derived structural `BEq` of StateEq.lean,
floats by their bits). The table never trusts its hash index: a candidate is returned only after
the `BEq` check, so the hash only finds candidates.

Theorems (for every table, every state):
- ★ `intern_spec`, ★ `internAt_spec`: an interned index holds the value, and every earlier index
  keeps its value (tables only grow);
- ★ `encList_spec`: the same for a list of values (the threads);
- ★ `decode_encode`: decoding a state's code gives a state whose every component is the original
  one or equal to it under round 6's equality, and codes decoded before keep their meaning;
- ★ `same_code`: two states given the same code (at any two times) have, component by component,
  one stored representative to which both are equal or identical.

What is not proved: that round 6's derived `BEq` is Lean's `=` (its assumption nREPLA6-2: plain data,
floats by bits; Lean cannot derive `LawfulBEq` for these nested types, and `Float` has no decidable
equality). The codec merges exactly the states round 6's exact graphs merged.

The fast path (`internAt`): when the caller knows the component is the very object stored at an index
(it decoded the parent state from the tables, and the step left that field alone), it passes that
index with `fast := true`; the theorem's premise is that `fast` implies the stored value is the
value. The driver's `fast` is a pointer comparison (`ptrAddrUnsafe`), which implies identity by the
runtime's object model: that is the one runtime fact the search relies on, and a run with the fast
path off checks it (Run/R8/Nrepl.lean `exact … slow`).
-/

namespace Jank.R8.Nrepl

open Determinismo Jank.R3.Nrepl Jank.R6.Nrepl Jank.NreplServer Jank.Analyzer

/-- Round 6's equality (derived structural `BEq`), or identity. -/
def Same {α : Type} [BEq α] (a b : α) : Prop := a = b ∨ (a == b) = true

/-- An interning table: the values by index, and candidate indices by hash. -/
structure Tab (α : Type) where
  vals : Array α := #[]
  idx : Std.HashMap UInt64 (List Nat) := {}

instance {α : Type} : Inhabited (Tab α) := ⟨{}⟩

/-- Is the value at `i` equal to `x` (round 6's `BEq`)? -/
def Tab.hit {α : Type} [BEq α] (t : Tab α) (x : α) (i : Nat) : Bool :=
  match t.vals[i]? with
  | some y => y == x
  | none => false

def Tab.find? {α : Type} [BEq α] (t : Tab α) (h : UInt64) (x : α) : Option Nat :=
  (t.idx.getD h []).find? (t.hit x)

/-- Appends `x` (the table is taken apart first, so its arrays are updated in place). -/
def Tab.add {α : Type} (t : Tab α) (h : UInt64) (x : α) : Tab α × Nat :=
  let n := t.vals.size
  let prev := t.idx.getD h []
  match t with
  | ⟨vals, idx⟩ => ({ vals := vals.push x, idx := idx.insert h (n :: prev) }, n)

def Tab.internH {α : Type} [BEq α] (t : Tab α) (h : UInt64) (x : α) : Tab α × Nat :=
  match t.find? h x with
  | some i => (t, i)
  | none => t.add h x

def Tab.intern {α : Type} [BEq α] [Hashable α] (t : Tab α) (x : α) : Tab α × Nat :=
  t.internH (hash x) x

/-- `intern` with a fast path: `fast` says `x` is the value stored at `i`. -/
def Tab.internAt {α : Type} [BEq α] [Hashable α] (t : Tab α) (x : α) (i : Nat) (fast : Bool) : Tab α × Nat :=
  if fast && decide (i < t.vals.size) then (t, i) else t.intern x

/-- The table holds `x` at `i`: the stored value is `x` or equal to it (round 6's `BEq`). -/
def Tab.holds {α : Type} [BEq α] (t : Tab α) (i : Nat) (x : α) : Prop :=
  ∃ y, t.vals[i]? = some y ∧ Same y x

/-- `t'` keeps every value of `t` at its index. -/
def Tab.ext {α : Type} (t t' : Tab α) : Prop :=
  t.vals.size ≤ t'.vals.size ∧ ∀ j, j < t.vals.size → t'.vals[j]? = t.vals[j]?

theorem Tab.ext_refl {α : Type} (t : Tab α) : t.ext t := ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem Tab.ext_trans {α : Type} {a b c : Tab α} (h1 : a.ext b) (h2 : b.ext c) : a.ext c :=
  ⟨Nat.le_trans h1.1 h2.1, fun j hj => by rw [h2.2 j (Nat.lt_of_lt_of_le hj h1.1), h1.2 j hj]⟩

theorem Tab.holds_ext {α : Type} [BEq α] {t t' : Tab α} {i : Nat} {x : α} (h : t.holds i x) (he : t.ext t') :
    t'.holds i x := by
  obtain ⟨y, hy, hs⟩ := h
  have hi : i < t.vals.size := by
    rcases Nat.lt_or_ge i t.vals.size with h | h
    · exact h
    · rw [Array.getElem?_eq_none h] at hy; cases hy
  exact ⟨y, by rw [he.2 i hi]; exact hy, hs⟩

theorem Tab.add_spec {α : Type} [BEq α] (t : Tab α) (h : UInt64) (x : α) :
    (t.add h x).1.holds (t.add h x).2 x ∧ t.ext (t.add h x).1 := by
  cases t
  refine ⟨⟨x, ?_, Or.inl rfl⟩, ?_, ?_⟩
  · simp [Tab.add]
  · simp [Tab.add]
  · intro j hj
    simp only [Tab.add]
    rw [Array.getElem?_push_lt hj]
    exact (Array.getElem?_eq_getElem hj).symm

theorem internH_spec {α : Type} [BEq α] (t : Tab α) (h : UInt64) (x : α) :
    (t.internH h x).1.holds (t.internH h x).2 x ∧ t.ext (t.internH h x).1 := by
  unfold Tab.internH
  split
  · next i hf =>
    refine ⟨?_, Tab.ext_refl t⟩
    have hp : t.hit x i = true := List.find?_some hf
    unfold Tab.hit at hp
    cases hv : t.vals[i]? with
    | none => rw [hv] at hp; cases hp
    | some y => rw [hv] at hp; exact ⟨y, hv, Or.inr hp⟩
  · exact Tab.add_spec t h x

/-- ★ An interned index holds the value; earlier indices keep theirs. -/
theorem intern_spec {α : Type} [BEq α] [Hashable α] (t : Tab α) (x : α) :
    (t.intern x).1.holds (t.intern x).2 x ∧ t.ext (t.intern x).1 :=
  internH_spec t (hash x) x

/-- ★ The same with the fast path, whenever `fast` implies the stored value is `x`. -/
theorem internAt_spec {α : Type} [BEq α] [Hashable α] (t : Tab α) (x : α) (i : Nat) (fast : Bool)
    (hfast : fast = true → t.vals[i]? = some x) :
    (t.internAt x i fast).1.holds (t.internAt x i fast).2 x ∧ t.ext (t.internAt x i fast).1 := by
  unfold Tab.internAt
  by_cases hc : (fast && decide (i < t.vals.size)) = true
  · simp only [hc, ↓reduceIte]
    have hf : fast = true := by cases fast <;> simp_all
    exact ⟨⟨x, hfast hf, Or.inl rfl⟩, Tab.ext_refl t⟩
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]; exact intern_spec t x

/-! ## Lists of values (the threads) -/

/-- Interns each value; `hints`: per value, an index and the caller's fast flag. -/
def encList {α : Type} [BEq α] [Hashable α] (t : Tab α) : List α → List (Nat × Bool) → Tab α × List Nat
  | [], _ => (t, [])
  | x :: xs, hs =>
    let (i, f) := hs.headD (0, false)
    let (t1, j) := t.internAt x i f
    let (t2, js) := encList t1 xs hs.tail
    (t2, j :: js)

/-- Decodes a list of indices. -/
def decList {α : Type} (t : Tab α) : List Nat → Option (List α)
  | [] => some []
  | i :: is => do
    let x ← t.vals[i]?
    let xs ← decList t is
    pure (x :: xs)

/-- Every value is held at its index, pointwise. -/
def holdsAll {α : Type} [BEq α] (t : Tab α) : List Nat → List α → Prop
  | [], [] => True
  | i :: is, x :: xs => t.holds i x ∧ holdsAll t is xs
  | _, _ => False

theorem holdsAll_ext {α : Type} [BEq α] {t t' : Tab α} (he : t.ext t') :
    ∀ (is : List Nat) (xs : List α), holdsAll t is xs → holdsAll t' is xs
  | [], [], _ => trivial
  | _ :: is, _ :: xs, ⟨h1, h2⟩ => ⟨Tab.holds_ext h1 he, holdsAll_ext he is xs h2⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- The fast flags are honest: each says its value is stored at its index. -/
def ListHintsOk {α : Type} (t : Tab α) : List α → List (Nat × Bool) → Prop
  | [], _ => True
  | x :: xs, hs =>
    ((hs.headD (0, false)).2 = true → t.vals[(hs.headD (0, false)).1]? = some x) ∧ ListHintsOk t xs hs.tail

theorem hintsOk_ext {α : Type} {t t' : Tab α} (he : t.ext t') :
    ∀ (xs : List α) (hs : List (Nat × Bool)), ListHintsOk t xs hs → ListHintsOk t' xs hs
  | [], _, _ => trivial
  | x :: xs, hs, ⟨h1, h2⟩ => by
    refine ⟨fun hf => ?_, hintsOk_ext he xs hs.tail h2⟩
    have hv := h1 hf
    have hi : (hs.headD (0, false)).1 < t.vals.size := by
      rcases Nat.lt_or_ge (hs.headD (0, false)).1 t.vals.size with h | h
      · exact h
      · rw [Array.getElem?_eq_none h] at hv; cases hv
    rw [he.2 _ hi]; exact hv

theorem trivial_hints {α : Type} (t : Tab α) : ∀ (xs : List α), ListHintsOk t xs []
  | [] => trivial
  | _ :: xs => ⟨fun h => by simp at h, trivial_hints t xs⟩

/-- ★ `encList`: every value held at its index, the table only grown. -/
theorem encList_spec {α : Type} [BEq α] [Hashable α] :
    ∀ (t : Tab α) (xs : List α) (hs : List (Nat × Bool)), ListHintsOk t xs hs →
      holdsAll (encList t xs hs).1 (encList t xs hs).2 xs ∧ t.ext (encList t xs hs).1
  | t, [], _, _ => ⟨trivial, Tab.ext_refl t⟩
  | t, x :: xs, hs, ⟨h1, h2⟩ => by
    simp only [encList]
    have ⟨a1, a2⟩ := internAt_spec t x (hs.headD (0, false)).1 (hs.headD (0, false)).2 h1
    have h2' := hintsOk_ext a2 xs hs.tail h2
    have ⟨b1, b2⟩ := encList_spec (t.internAt x (hs.headD (0, false)).1 (hs.headD (0, false)).2).1 xs hs.tail h2'
    exact ⟨⟨Tab.holds_ext a1 b2, b1⟩, Tab.ext_trans a2 b2⟩

theorem decList_holds {α : Type} [BEq α] (t : Tab α) :
    ∀ (is : List Nat) (xs : List α), holdsAll t is xs →
      ∃ ys, decList t is = some ys ∧ ys.length = xs.length ∧ ∀ k (hk : k < xs.length) (hk' : k < ys.length),
        Same ys[k] xs[k]
  | [], [], _ => ⟨[], rfl, rfl, fun k hk => by simp at hk⟩
  | i :: is, x :: xs, ⟨⟨y, hy, hs⟩, h2⟩ => by
    obtain ⟨ys, hd, hl, hk⟩ := decList_holds t is xs h2
    refine ⟨y :: ys, by simp [decList, hy, hd], by simp [hl], ?_⟩
    intro k hk1 hk2
    cases k with
    | zero => exact hs
    | succ k => exact hk k (by simpa using hk1) (by simpa using hk2)
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem decList_ext {α : Type} {t t' : Tab α} (he : t.ext t') :
    ∀ (is : List Nat) (ys : List α), decList t is = some ys → decList t' is = some ys
  | [], ys, h => h
  | i :: is, ys, h => by
    simp only [decList] at h ⊢
    cases hv : t.vals[i]? with
    | none => rw [hv] at h; cases h
    | some y =>
      rw [hv] at h
      have hi : i < t.vals.size := by
        rcases Nat.lt_or_ge i t.vals.size with h' | h'
        · exact h'
        · rw [Array.getElem?_eq_none h'] at hv; cases hv
      rw [he.2 i hi, hv]
      cases hd : decList t is with
      | none => rw [hd] at h; cases h
      | some zs =>
        rw [hd] at h
        rw [decList_ext he is zs hd]
        exact h

/-! ## World T's states -/

abbrev MiscT := TConfig × Nat × List UInt8 × List UInt8 × List Nat × Nat × Nat × Nat × Option String ×
  Option String × Option Nat
abbrev LogsT := Array TSent × Array EvalRec × List (Nat × String) × List Nat × List (Nat × String)

/-- A state's components: seven of the memory, and the threads. -/
structure Comps where
  jw : JW
  fds : Array (Option Desc)
  temps : List (String × List UInt8 × Bool)
  socks : Array Sock
  misc : MiscT
  replies : Array (Nat × JVal)
  logs : LogsT
  threads : List (Option TTh)

def split (k : PKey) : Comps :=
  let m := k.mem
  { jw := m.jw, fds := m.fds, temps := m.temps, socks := m.socks,
    misc := (m.cfg, m.nextTemp, m.terminal, m.outBuf, m.pending, m.nClients, m.accepted, m.nextUuid,
      m.crashed, m.acceptDied, m.capLock)
    replies := m.replies, logs := (m.sent, m.evals, m.handlerErrors, m.connEnded, m.hung)
    threads := k.threads.toList }

def join (c : Comps) : PKey :=
  let (cfg, nextTemp, terminal, outBuf, pending, nClients, accepted, nextUuid, crashed, acceptDied, capLock) := c.misc
  let (sent, evals, handlerErrors, connEnded, hung) := c.logs
  { mem := { cfg, jw := c.jw, fds := c.fds, temps := c.temps, nextTemp, terminal, outBuf, socks := c.socks,
             pending, nClients, accepted, nextUuid, replies := c.replies, sent, crashed, acceptDied,
             handlerErrors, connEnded, evals, capLock, hung }
    threads := c.threads.toArray }

/-- Splitting loses nothing. -/
theorem join_split (k : PKey) : join (split k) = k := by
  cases k with
  | mk mem threads => cases mem; simp [join, split]

structure Tabs where
  jw : Tab JW := {}
  fds : Tab (Array (Option Desc)) := {}
  temps : Tab (List (String × List UInt8 × Bool)) := {}
  socks : Tab (Array Sock) := {}
  misc : Tab MiscT := {}
  replies : Tab (Array (Nat × JVal)) := {}
  logs : Tab LogsT := {}
  th : Tab (Option TTh) := {}
  deriving Inhabited

/-- Fast-path hints for a state's components: an index and a flag each (`Hints.none`: no fast path). -/
structure Hints where
  jw : Nat × Bool := (0, false)
  fds : Nat × Bool := (0, false)
  temps : Nat × Bool := (0, false)
  socks : Nat × Bool := (0, false)
  misc : Nat × Bool := (0, false)
  replies : Nat × Bool := (0, false)
  logs : Nat × Bool := (0, false)
  th : List (Nat × Bool) := []

/-- A state's code: seven memory indices, then one per thread. -/
def Tabs.encodeC (T : Tabs) (c : Comps) (h : Hints := {}) : Tabs × List Nat :=
  -- taken apart first, so that each table is updated in place
  match T with
  | ⟨tjw, tfds, ttemps, tsocks, tmisc, treplies, tlogs, tth⟩ =>
  let (jw, a) := tjw.internAt c.jw h.jw.1 h.jw.2
  let (fds, b) := tfds.internAt c.fds h.fds.1 h.fds.2
  let (temps, d) := ttemps.internAt c.temps h.temps.1 h.temps.2
  let (socks, e) := tsocks.internAt c.socks h.socks.1 h.socks.2
  let (misc, f) := tmisc.internAt c.misc h.misc.1 h.misc.2
  let (replies, g) := treplies.internAt c.replies h.replies.1 h.replies.2
  let (logs, l) := tlogs.internAt c.logs h.logs.1 h.logs.2
  let (th, ts) := encList tth c.threads h.th
  ({ jw, fds, temps, socks, misc, replies, logs, th }, a :: b :: d :: e :: f :: g :: l :: ts)

def Tabs.encode (T : Tabs) (k : PKey) (h : Hints := {}) : Tabs × List Nat := T.encodeC (split k) h

def Tabs.decodeC (T : Tabs) : List Nat → Option Comps
  | a :: b :: d :: e :: f :: g :: l :: ts => do
    let jw ← T.jw.vals[a]?
    let fds ← T.fds.vals[b]?
    let temps ← T.temps.vals[d]?
    let socks ← T.socks.vals[e]?
    let misc ← T.misc.vals[f]?
    let replies ← T.replies.vals[g]?
    let logs ← T.logs.vals[l]?
    let threads ← decList T.th ts
    pure { jw, fds, temps, socks, misc, replies, logs, threads }
  | _ => none

def Tabs.decode (T : Tabs) (code : List Nat) : Option PKey := (T.decodeC code).map join

/-- Component by component: identical, or equal under round 6's `BEq`. -/
def SameComps (x y : Comps) : Prop :=
  Same x.jw y.jw ∧ Same x.fds y.fds ∧ Same x.temps y.temps ∧ Same x.socks y.socks ∧ Same x.misc y.misc ∧
  Same x.replies y.replies ∧ Same x.logs y.logs ∧ x.threads.length = y.threads.length ∧
  ∀ k (h1 : k < x.threads.length) (h2 : k < y.threads.length), Same x.threads[k] y.threads[k]

def Tabs.ext (T T' : Tabs) : Prop :=
  T.jw.ext T'.jw ∧ T.fds.ext T'.fds ∧ T.temps.ext T'.temps ∧ T.socks.ext T'.socks ∧ T.misc.ext T'.misc ∧
  T.replies.ext T'.replies ∧ T.logs.ext T'.logs ∧ T.th.ext T'.th

/-- The hints are honest: each flag set says its component is the value stored at its index. -/
def Tabs.HintsOk (T : Tabs) (c : Comps) (h : Hints) : Prop :=
  (h.jw.2 = true → T.jw.vals[h.jw.1]? = some c.jw) ∧ (h.fds.2 = true → T.fds.vals[h.fds.1]? = some c.fds) ∧
  (h.temps.2 = true → T.temps.vals[h.temps.1]? = some c.temps) ∧
  (h.socks.2 = true → T.socks.vals[h.socks.1]? = some c.socks) ∧
  (h.misc.2 = true → T.misc.vals[h.misc.1]? = some c.misc) ∧
  (h.replies.2 = true → T.replies.vals[h.replies.1]? = some c.replies) ∧
  (h.logs.2 = true → T.logs.vals[h.logs.1]? = some c.logs) ∧ ListHintsOk T.th c.threads h.th

theorem Tabs.hintsOk_none (T : Tabs) (c : Comps) : T.HintsOk c {} := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial_hints _ _⟩ <;> intro h <;> simp at h

/-- ★ For every table and every state (and honest hints): the code decodes to a state whose every
component is the original one or equal to it under round 6's equality, and the tables only grew. -/
theorem decode_encode (T : Tabs) (c : Comps) (h : Hints) (hh : T.HintsOk c h) :
    T.ext (T.encodeC c h).1 ∧ ∃ c', (T.encodeC c h).1.decodeC (T.encodeC c h).2 = some c' ∧ SameComps c' c := by
  cases T with
  | mk tjw tfds ttemps tsocks tmisc treplies tlogs tth =>
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hh
  have ⟨a1, a2⟩ := internAt_spec tjw c.jw h.jw.1 h.jw.2 h1
  have ⟨b1, b2⟩ := internAt_spec tfds c.fds h.fds.1 h.fds.2 h2
  have ⟨d1, d2⟩ := internAt_spec ttemps c.temps h.temps.1 h.temps.2 h3
  have ⟨e1, e2⟩ := internAt_spec tsocks c.socks h.socks.1 h.socks.2 h4
  have ⟨f1, f2⟩ := internAt_spec tmisc c.misc h.misc.1 h.misc.2 h5
  have ⟨g1, g2⟩ := internAt_spec treplies c.replies h.replies.1 h.replies.2 h6
  have ⟨l1, l2⟩ := internAt_spec tlogs c.logs h.logs.1 h.logs.2 h7
  have ⟨t1, t2⟩ := encList_spec tth c.threads h.th h8
  refine ⟨⟨a2, b2, d2, e2, f2, g2, l2, t2⟩, ?_⟩
  obtain ⟨y1, hy1, s1⟩ := a1
  obtain ⟨y2, hy2, s2⟩ := b1
  obtain ⟨y3, hy3, s3⟩ := d1
  obtain ⟨y4, hy4, s4⟩ := e1
  obtain ⟨y5, hy5, s5⟩ := f1
  obtain ⟨y6, hy6, s6⟩ := g1
  obtain ⟨y7, hy7, s7⟩ := l1
  obtain ⟨ys, hys, hl, hk⟩ := decList_holds _ _ _ t1
  refine ⟨{ jw := y1, fds := y2, temps := y3, socks := y4, misc := y5, replies := y6, logs := y7, threads := ys }, ?_, ?_⟩
  · simp only [Tabs.encodeC, Tabs.decodeC]
    simp only [hy1, hy2, hy3, hy4, hy5, hy6, hy7, hys]
    rfl
  · exact ⟨s1, s2, s3, s4, s5, s6, s7, hl, fun k h1 h2 => hk k h2 h1⟩

/-- Codes decoded by a table decode the same way after the table grew. -/
theorem decodeC_ext {T T' : Tabs} (he : T.ext T') (code : List Nat) (c : Comps)
    (hd : T.decodeC code = some c) : T'.decodeC code = some c := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := he
  match code, hd with
  | a :: b :: d :: e :: f :: g :: l :: ts, hd =>
    simp only [Tabs.decodeC] at hd ⊢
    have get {α : Type} {t t' : Tab α} (he : t.ext t') (i : Nat) (y : α) (hy : t.vals[i]? = some y) :
        t'.vals[i]? = some y := by
      have hi : i < t.vals.size := by
        rcases Nat.lt_or_ge i t.vals.size with h' | h'
        · exact h'
        · rw [Array.getElem?_eq_none h'] at hy; cases hy
      rw [he.2 i hi]; exact hy
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hd
    obtain ⟨y1, h1, y2, h2, y3, h3, y4, h4, y5, h5, y6, h6, y7, h7, ys, h8, rfl⟩ := hd
    simp only [get e1 a y1 h1, get e2 b y2 h2, get e3 d y3 h3, get e4 e y4 h4, get e5 f y5 h5,
      get e6 g y6 h6, get e7 l y7 h7, decList_ext e8 ts ys h8, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def]

/-- ★ Two states given one code, at any two times (the second table grown from the first): both
decode to one stored state, to which each is, component by component, identical or equal under
round 6's equality. So the search merges two states only when round 6's exact graph would. -/
theorem same_code (T : Tabs) (c₁ c₂ : Comps) (h₁ h₂ : Hints) (U : Tabs)
    (hh₁ : T.HintsOk c₁ h₁) (hu : (T.encodeC c₁ h₁).1.ext U) (hh₂ : U.HintsOk c₂ h₂)
    (hc : (T.encodeC c₁ h₁).2 = (U.encodeC c₂ h₂).2) :
    ∃ r, SameComps r c₁ ∧ SameComps r c₂ := by
  obtain ⟨_, r₁, hd₁, hs₁⟩ := decode_encode T c₁ h₁ hh₁
  obtain ⟨_, r₂, hd₂, hs₂⟩ := decode_encode U c₂ h₂ hh₂
  have hd₁' := decodeC_ext (Tabs.ext_trans' hu (decode_encode U c₂ h₂ hh₂).1) _ _ hd₁
  rw [hc, hd₂] at hd₁'
  cases hd₁'
  exact ⟨r₁, hs₁, hs₂⟩
where
  Tabs.ext_trans' {A B C : Tabs} (h1 : A.ext B) (h2 : B.ext C) : A.ext C :=
    ⟨Tab.ext_trans h1.1 h2.1, Tab.ext_trans h1.2.1 h2.2.1, Tab.ext_trans h1.2.2.1 h2.2.2.1,
     Tab.ext_trans h1.2.2.2.1 h2.2.2.2.1, Tab.ext_trans h1.2.2.2.2.1 h2.2.2.2.2.1,
     Tab.ext_trans h1.2.2.2.2.2.1 h2.2.2.2.2.2.1, Tab.ext_trans h1.2.2.2.2.2.2.1 h2.2.2.2.2.2.2.1,
     Tab.ext_trans h1.2.2.2.2.2.2.2 h2.2.2.2.2.2.2.2⟩

end Jank.R8.Nrepl
