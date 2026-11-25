import Jank.R5.Nrepl.Chunk

/-!
# Round 5, nREPL: a kernel-evaluable copy of round 2's bencode parser

Round 2's `parseRecur`/`parseList`/`parseDict` (Jank/Nrepl/Bencode.lean, bencode.jank 21–76) are a
mutual recursion Lean compiles by well-founded recursion, which neither `decide` nor the kernel
evaluates. `recK`/`listK`/`dictK` are the same bodies with one more argument, a fuel `F` that every
call spends, so they are structural (and evaluate); running out throws `fuelOut`, a message no path
of the original throws.

★ `recK_agrees` (and its list/dict parts): for every fuel, input, depth and position, the copy either
runs out of fuel or gives exactly what the original gives. So a concrete run of the copy that does not
run out *is* the original's result (`parseK_sound`), and `t7_prefixes_none_k` turns the T7 check of
`Chunk.lean` into a theorem.
-/

namespace Jank.R5.Nrepl

open Jank.NreplServer

/-- Running out of fuel throws what a stack overflow throws: `parse` maps it to `.crash`, so a copy
that ran out of fuel can never pass for "nil" (`parseK_sound`). -/
def fuelOut : PErr := .stackOverflow

mutual
def recK (p : Platform) (data : Bytes) : Nat → Nat → PM (Option JVal)
  | 0, _ => throw fuelOut
  | _ + 1, 0 => throw .stackOverflow
  | F + 1, depth + 1 => do
    let pos ← get
    match nthByte p data pos with
    | some 105 =>
      let start := pos + 1
      set start
      let n := indexOf p data start 101
      match subsPlus data (some start) n with
      | none => pure none
      | some s =>
        let out := parseLong s
        set ((n.getD 0) + 1)
        pure (out.map JVal.int)
    | some 108 =>
      set (pos + 1)
      listK p data F depth [] (data.length + 1)
    | some 100 =>
      set (pos + 1)
      dictK p data F depth [] (data.length + 1)
    | some b =>
      if 48 ≤ b && b ≤ 57 then
        let start := pos
        let end_ := indexOf p data start 58
        match subsPlus data (some start) end_ with
        | none => pure none
        | some n =>
          let len := parseLong n
          let start' := (end_.getD 0) + 1
          match len with
          | none => throw (.thrown "(+ start bytes): bytes is nil")
          | some l =>
            let stop := jankAdd start' l
            match subsPlus data (some start') (some stop) with
            | none => pure none
            | some out =>
              set stop
              pure (some (.str out))
      else pure none
    | none => pure none
  termination_by structural F _ => F

def listK (p : Platform) (data : Bytes) : Nat → Nat → List JVal → Nat → PM (Option JVal)
  | 0, _, _, _ => throw fuelOut
  | _ + 1, _, _, 0 => throw .hang
  | F + 1, depth, out, fuel + 1 => do
    match nthByte p data (← get) with
    | none => pure none
    | some 101 =>
      modify (· + 1)
      pure (some (.vec out))
    | some _ =>
      match ← recK p data F depth with
      | some v => listK p data F depth (out ++ [v]) fuel
      | none => pure none
  termination_by structural F _ _ _ => F

def dictK (p : Platform) (data : Bytes) : Nat → Nat → List (JVal × JVal) → Nat → PM (Option JVal)
  | 0, _, _, _ => throw fuelOut
  | _ + 1, _, _, 0 => throw .hang
  | F + 1, depth, out, fuel + 1 => do
    match nthByte p data (← get) with
    | none => pure none
    | some 101 =>
      modify (· + 1)
      pure (some (.map out))
    | some _ =>
      let k ← recK p data F depth
      let v ← recK p data F depth
      match k, v with
      | some k, some v => dictK p data F depth (assocMap out k v) fuel
      | _, _ => pure none
  termination_by structural F _ _ _ => F
end

/-- `parse` over the copy (`Bencode.lean` `parse`, with `recK F` for `parseRecur`). -/
def parseK (p : Platform) (F : Nat) (s : Option Bytes) : Parsed :=
  match s with
  | none => .none
  | some data =>
    match (recK p data F p.maxDepth).run 0 with
    | .ok (some v, pos) => .value v (notEmpty (data.drop pos.toNat))
    | .ok (none, _) => .none
    | .error (.thrown _) => .none
    | .error .hang => .none
    | .error .stackOverflow => .crash

def prefixesNoneK (p : Platform) (F : Nat) (m : Bytes) : Bool :=
  (List.range m.length).all fun k => isNoneP (parseK p F (some (m.take k)))

def wholeOkK (p : Platform) (F : Nat) (m : Bytes) : Bool :=
  match parseK p F (some m) with
  | .value _ none => true
  | _ => false

/-- Kernel evaluation of the copy on T7's requests: every proper prefix gives nil, every request
parses whole (fuel 400), on both `char` signednesses. -/
theorem t7_k : (t7Msgs.all fun m => !m.isEmpty && prefixesNoneK {} 400 m && wholeOkK {} 400 m) = true ∧
    (t7Msgs.all fun m => !m.isEmpty && prefixesNoneK { signedChar := false } 400 m &&
      wholeOkK { signedChar := false } 400 m) = true := by
  decide +kernel

/-! ## The copy agrees with the original -/

/-- `x` runs out of fuel (throws `fuelOut`) or gives exactly what `y` gives, from every position. -/
def Agrees {α : Type} (x y : PM α) : Prop :=
  ∀ s : Int, x.run s = .error fuelOut ∨ x.run s = y.run s

theorem agrees_refl {α : Type} (x : PM α) : Agrees x x := fun _ => Or.inr rfl

theorem agrees_bind {α β : Type} {x y : PM α} {f g : α → PM β} (hx : Agrees x y)
    (hf : ∀ a, Agrees (f a) (g a)) : Agrees (x >>= f) (y >>= g) := by
  intro s
  rcases hx s with h | h
  · left
    rw [StateT.run_bind, h]; rfl
  · rw [StateT.run_bind, StateT.run_bind, h]
    cases hy : y.run s with
    | error e => right; rfl
    | ok r =>
      obtain ⟨a, s'⟩ := r
      exact hf a s'

/-- The body of `parseRecur (depth + 1)` over the loops it calls. -/
def bodyR (p : Platform) (data : Bytes) (L : Nat → List JVal → Nat → PM (Option JVal))
    (D : Nat → List (JVal × JVal) → Nat → PM (Option JVal)) (depth : Nat) : PM (Option JVal) := do
  let pos ← get
  match nthByte p data pos with
  | some 105 =>
    let start := pos + 1
    set start
    let n := indexOf p data start 101
    match subsPlus data (some start) n with
    | none => pure none
    | some s =>
      let out := parseLong s
      set ((n.getD 0) + 1)
      pure (out.map JVal.int)
  | some 108 =>
    set (pos + 1)
    L depth [] (data.length + 1)
  | some 100 =>
    set (pos + 1)
    D depth [] (data.length + 1)
  | some b =>
    if 48 ≤ b && b ≤ 57 then
      let start := pos
      let end_ := indexOf p data start 58
      match subsPlus data (some start) end_ with
      | none => pure none
      | some n =>
        let len := parseLong n
        let start' := (end_.getD 0) + 1
        match len with
        | none => throw (.thrown "(+ start bytes): bytes is nil")
        | some l =>
          let stop := jankAdd start' l
          match subsPlus data (some start') (some stop) with
          | none => pure none
          | some out =>
            set stop
            pure (some (.str out))
    else pure none
  | none => pure none

def bodyL (p : Platform) (data : Bytes) (R : Nat → PM (Option JVal))
    (self : List JVal → Nat → PM (Option JVal)) (depth : Nat) (out : List JVal) (fuel : Nat) :
    PM (Option JVal) := do
  match nthByte p data (← get) with
  | none => pure none
  | some 101 =>
    modify (· + 1)
    pure (some (.vec out))
  | some _ =>
    match ← R depth with
    | some v => self (out ++ [v]) fuel
    | none => pure none

def bodyD (p : Platform) (data : Bytes) (R : Nat → PM (Option JVal))
    (self : List (JVal × JVal) → Nat → PM (Option JVal)) (depth : Nat) (out : List (JVal × JVal))
    (fuel : Nat) : PM (Option JVal) := do
  match nthByte p data (← get) with
  | none => pure none
  | some 101 =>
    modify (· + 1)
    pure (some (.map out))
  | some _ =>
    let k ← R depth
    let v ← R depth
    match k, v with
    | some k, some v => self (assocMap out k v) fuel
    | _, _ => pure none

theorem recK_succ (p : Platform) (data : Bytes) (F depth : Nat) :
    recK p data (F + 1) (depth + 1) = bodyR p data (listK p data F) (dictK p data F) depth := rfl

theorem parseRecur_succ (p : Platform) (data : Bytes) (depth : Nat) :
    parseRecur p data (depth + 1) = bodyR p data (parseList p data) (parseDict p data) depth := by
  rw [parseRecur]; rfl

theorem listK_succ (p : Platform) (data : Bytes) (F depth : Nat) (out : List JVal) (fuel : Nat) :
    listK p data (F + 1) depth out (fuel + 1) =
      bodyL p data (recK p data F) (listK p data F depth) depth out fuel := rfl

theorem parseList_succ (p : Platform) (data : Bytes) (depth : Nat) (out : List JVal) (fuel : Nat) :
    parseList p data depth out (fuel + 1) =
      bodyL p data (parseRecur p data) (parseList p data depth) depth out fuel := by
  rw [parseList]; rfl

theorem dictK_succ (p : Platform) (data : Bytes) (F depth : Nat) (out : List (JVal × JVal)) (fuel : Nat) :
    dictK p data (F + 1) depth out (fuel + 1) =
      bodyD p data (recK p data F) (dictK p data F depth) depth out fuel := rfl

theorem parseDict_succ (p : Platform) (data : Bytes) (depth : Nat) (out : List (JVal × JVal)) (fuel : Nat) :
    parseDict p data depth out (fuel + 1) =
      bodyD p data (parseRecur p data) (parseDict p data depth) depth out fuel := by
  rw [parseDict]; rfl

theorem bodyR_mono (p : Platform) (data : Bytes) {L1 L2 : Nat → List JVal → Nat → PM (Option JVal)}
    {D1 D2 : Nat → List (JVal × JVal) → Nat → PM (Option JVal)}
    (hL : ∀ d o f, Agrees (L1 d o f) (L2 d o f)) (hD : ∀ d o f, Agrees (D1 d o f) (D2 d o f))
    (depth : Nat) : Agrees (bodyR p data L1 D1 depth) (bodyR p data L2 D2 depth) := by
  unfold bodyR
  refine agrees_bind (agrees_refl _) (fun pos => ?_)
  generalize nthByte p data pos = o
  split
  · exact agrees_refl _
  · exact agrees_bind (agrees_refl _) (fun _ => hL _ _ _)
  · exact agrees_bind (agrees_refl _) (fun _ => hD _ _ _)
  · exact agrees_refl _
  · exact agrees_refl _

theorem bodyL_mono (p : Platform) (data : Bytes) {R1 R2 : Nat → PM (Option JVal)}
    {S1 S2 : List JVal → Nat → PM (Option JVal)}
    (hR : ∀ d, Agrees (R1 d) (R2 d)) (hS : ∀ o f, Agrees (S1 o f) (S2 o f))
    (depth : Nat) (out : List JVal) (fuel : Nat) :
    Agrees (bodyL p data R1 S1 depth out fuel) (bodyL p data R2 S2 depth out fuel) := by
  unfold bodyL
  refine agrees_bind (agrees_refl _) (fun pos => ?_)
  generalize nthByte p data pos = o
  split
  · exact agrees_refl _
  · exact agrees_refl _
  · refine agrees_bind (hR depth) (fun r => ?_)
    cases r with
    | some v => exact hS _ _
    | none => exact agrees_refl _

theorem bodyD_mono (p : Platform) (data : Bytes) {R1 R2 : Nat → PM (Option JVal)}
    {S1 S2 : List (JVal × JVal) → Nat → PM (Option JVal)}
    (hR : ∀ d, Agrees (R1 d) (R2 d)) (hS : ∀ o f, Agrees (S1 o f) (S2 o f))
    (depth : Nat) (out : List (JVal × JVal)) (fuel : Nat) :
    Agrees (bodyD p data R1 S1 depth out fuel) (bodyD p data R2 S2 depth out fuel) := by
  unfold bodyD
  refine agrees_bind (agrees_refl _) (fun pos => ?_)
  generalize nthByte p data pos = o
  split
  · exact agrees_refl _
  · exact agrees_refl _
  · refine agrees_bind (hR depth) (fun k => agrees_bind (hR depth) (fun v => ?_))
    cases k <;> cases v
    all_goals first | exact hS _ _ | exact agrees_refl _

/-- ★ For every fuel, input, depth, accumulator and position: the copy runs out of fuel or gives
exactly what round 2's `parseRecur`/`parseList`/`parseDict` give. -/
theorem k_agrees (p : Platform) (data : Bytes) : ∀ F,
    (∀ depth, Agrees (recK p data F depth) (parseRecur p data depth)) ∧
    (∀ depth out fuel, Agrees (listK p data F depth out fuel) (parseList p data depth out fuel)) ∧
    (∀ depth out fuel, Agrees (dictK p data F depth out fuel) (parseDict p data depth out fuel)) := by
  intro F
  induction F with
  | zero =>
    refine ⟨fun _ _ => Or.inl rfl, fun _ _ _ _ => Or.inl rfl, fun _ _ _ _ => Or.inl rfl⟩
  | succ F ih =>
    obtain ⟨ihR, ihL, ihD⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · intro depth
      cases depth with
      | zero => intro s; left; rfl
      | succ d =>
        rw [recK_succ, parseRecur_succ]
        exact bodyR_mono p data (fun d o f => ihL d o f) (fun d o f => ihD d o f) d
    · intro depth out fuel
      cases fuel with
      | zero => intro s; right; rw [parseList]; rfl
      | succ f =>
        rw [listK_succ, parseList_succ]
        exact bodyL_mono p data ihR (fun o f' => ihL depth o f') depth out f
    · intro depth out fuel
      cases fuel with
      | zero => intro s; right; rw [parseDict]; rfl
      | succ f =>
        rw [dictK_succ, parseDict_succ]
        exact bodyD_mono p data ihR (fun o f' => ihD depth o f') depth out f

/-- ★ A run of the copy that does not end in `.crash` is the original's result. -/
theorem parseK_sound (p : Platform) (F : Nat) (s : Option Bytes) (h : parseK p F s ≠ .crash) :
    parseK p F s = parse p s := by
  cases s with
  | none => rfl
  | some data =>
    have ha := (k_agrees p data F).1 p.maxDepth 0
    simp only [parseK, parse] at h ⊢
    rcases ha with ha | ha
    · rw [ha] at h; simp [fuelOut] at h
    · rw [ha]
      cases hr : StateT.run (parseRecur p data p.maxDepth) 0 with
      | ok r =>
        obtain ⟨o, pos⟩ := r
        cases o <;> rfl
      | error e => cases e <;> rfl

/-- ★ T7's requests satisfy the hypotheses of `chunking_independent`, as theorems about round 2's
parser (from `t7_k` and `parseK_sound`). -/
theorem t7_hyps (p : Platform) (hp : p = {} ∨ p = { signedChar := false }) :
    hypsHold p t7Msgs = true := by
  have hk : (t7Msgs.all fun m => !m.isEmpty && prefixesNoneK p 400 m && wholeOkK p 400 m) = true := by
    rcases hp with rfl | rfl
    · exact t7_k.1
    · exact t7_k.2
  unfold hypsHold
  rw [List.all_eq_true] at hk ⊢
  intro m hm
  have h := hk m hm
  simp only [Bool.and_eq_true] at h ⊢
  refine ⟨⟨h.1.1, ?_⟩, ?_⟩
  · unfold prefixesNone
    unfold prefixesNoneK at h
    rw [List.all_eq_true] at h ⊢
    intro k hk'
    have e := h.1.2 k hk'
    have hn : parseK p 400 (some (m.take k)) = .none := (isNoneP_iff _).mp e
    rw [← parseK_sound p 400 _ (by rw [hn]; simp)]
    exact e
  · unfold wholeOk
    unfold wholeOkK at h
    have hc : parseK p 400 (some m) ≠ .crash := by
      intro hc; rw [hc] at h; simp at h
    rw [← parseK_sound p 400 _ hc]
    exact h.2

/-- ★ For every chunking of each of T7's requests (both `char` signednesses), `read-message`'s loop
gives the message a whole read gives, once, and an empty buffer. -/
theorem t7_chunking_independent (p : Platform) (hp : p = {} ∨ p = { signedChar := false })
    (m : Bytes) (hm : m ∈ t7Msgs) (chunks : List Bytes) (hcat : chunks.flatten = m) :
    ∃ v, parse p (some m) = .value v none ∧ (readLoop p none chunks).1 = [v] ∧
      EmptyBuf (readLoop p none chunks).2 :=
  chunking_independent_all p t7Msgs (t7_hyps p hp) m hm chunks hcat



end Jank.R5.Nrepl
