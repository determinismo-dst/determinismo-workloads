/-
  Theorems about the replica.  No `sorry`, no axioms beyond propext,
  Classical.choice and Quot.sound (printed by FlecsLean/Axioms.lean).  Round
  1 checked the generation lemmas with `bv_decide`; round 2 re-proves them by
  bit extensionality and `omega`.
-/
import FlecsLean.Ops

namespace Flecs

/-! ### Generations (api_defines.h 333-335)

Round 2: proved by bit extensionality (each bit of a `UInt64` through
`BitVec.getLsbD`, with the index split into the 16-bit ranges the masks
cut) and by `omega` on `toNat` for the 16-bit arithmetic.  No `bv_decide`,
so no native-evaluation axioms. -/

theorem u64_ext {a b : UInt64} (h : ∀ i, i < 64 → a.toBitVec.getLsbD i = b.toBitVec.getLsbD i) : a = b :=
  UInt64.toBitVec_inj.mp (BitVec.eq_of_getLsbD_eq h)

theorem hE : ENTITY_MASK = (OfNat.ofNat (2 ^ 32 - 1) : UInt64) := rfl
theorem hG : GENERATION_MASK = (OfNat.ofNat (2 ^ 16 - 1) : UInt64) <<< 32 := rfl
theorem hF : (0xFFFF : UInt64) = (OfNat.ofNat (2 ^ 16 - 1) : UInt64) := rfl
theorem hS : ((32 : UInt64).toBitVec % 64).toNat = 32 := by decide
theorem hS48 : ((48 : UInt64).toBitVec % 64).toNat = 48 := by decide

/-- Bit extensionality over the generation layout: unfold to `getLsbD`,
    split the bit index at 16, 32 and 48, and let `simp` decide each
    comparison with `omega`. -/
macro "bits" : tactic => `(tactic| (
  apply u64_ext
  intro i hi
  simp only [lo32, generation, hE, hG, hF, UInt64.toBitVec_and, UInt64.toBitVec_or,
    UInt64.toBitVec_not, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight,
    BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', hS, hS48, BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    UInt64.toBitVec_ofNat, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
  rcases (show i < 16 ∨ (16 ≤ i ∧ i < 32) ∨ (32 ≤ i ∧ i < 48) ∨ 48 ≤ i by omega) with h | h | h | h <;>
    simp (disch := omega) [decide_eq_true, decide_eq_false]))

/-- `ECS_GENERATION_INC` keeps the 32-bit id. -/
theorem genInc_lo32 (e : UInt64) : lo32 (genInc e) = lo32 e := by
  unfold genInc; bits

/-- The generation of a handle packed from `a`'s other bits and `y`. -/
theorem gen_of_pack (a y : UInt64) :
    generation ((a &&& ~~~ GENERATION_MASK) ||| ((0xFFFF &&& y) <<< 32)) = y &&& 0xFFFF := by
  bits

theorem gen_of_pack' (a y : UInt64) :
    generation ((a &&& ~~~ GENERATION_MASK) ||| ((y &&& 0xFFFF) <<< 32)) = y &&& 0xFFFF := by
  bits

theorem pack_mask (a y : UInt64) :
    ((a &&& ~~~ GENERATION_MASK) ||| ((y &&& 0xFFFF) <<< 32)) &&& ~~~ GENERATION_MASK =
      a &&& ~~~ GENERATION_MASK := by
  bits

theorem unpack (e : UInt64) :
    (e &&& ~~~ GENERATION_MASK) ||| ((generation e &&& 0xFFFF) <<< 32) = e := by
  bits

/-- `ECS_GENERATION_INC` adds one to the 16-bit generation, modulo 2^16. -/
theorem genInc_generation (e : UInt64) :
    generation (genInc e) = (generation e + 1) &&& 0xFFFF := by
  unfold genInc; exact gen_of_pack _ _

/-- The bits above the generation (flags) are kept. -/
theorem genInc_high (e : UInt64) :
    genInc e &&& ((0xFFFF : UInt64) <<< 48) = e &&& ((0xFFFF : UInt64) <<< 48) := by
  unfold genInc; bits

theorem land16 (x : Nat) : x &&& 65535 = x % 65536 := Nat.and_two_pow_sub_one_eq_mod x 16
theorem land16' (x : Nat) : 65535 &&& x = x % 65536 := by rw [Nat.and_comm]; exact land16 x

theorem arith16 (g k : UInt64) :
    0xFFFF &&& (((g + k) &&& 0xFFFF) + 1) = (g + (k + 1)) &&& 0xFFFF := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_and, UInt64.toNat_add, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  simp only [land16, land16']
  omega

theorem arith16_period (g : UInt64) : (g + 65536) &&& 0xFFFF = (g + 0) &&& 0xFFFF := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_and, UInt64.toNat_add, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  simp only [land16]
  omega

/-- `n`-fold application. -/
def iterN (f : UInt64 → UInt64) : Nat → UInt64 → UInt64
  | 0, x => x
  | n + 1, x => f (iterN f n x)

/-- Normal form of an id after `k` recycles. -/
def genIter (e : UInt64) (k : UInt64) : UInt64 :=
  (e &&& ~~~ GENERATION_MASK) ||| (((generation e + k) &&& 0xFFFF) <<< 32)

theorem genInc_genIter (e k : UInt64) :
    genInc (genIter e k) = genIter e (k + 1) := by
  unfold genInc genIter
  rw [pack_mask, gen_of_pack', arith16]

theorem genIter_zero (e : UInt64) : genIter e 0 = e := by
  unfold genIter
  have : generation e + 0 = generation e := by simp
  rw [this]; exact unpack e

theorem toUInt64_succ (n : Nat) : (n + 1).toUInt64 = n.toUInt64 + 1 := by
  simp [Nat.toUInt64, UInt64.ofNat_add]

theorem iterate_genInc (e : UInt64) (n : Nat) : iterN genInc n e = genIter e n.toUInt64 := by
  induction n with
  | zero => simp [iterN, genIter_zero]
  | succ n ih => rw [iterN, ih, genInc_genIter, toUInt64_succ]

/-- After 2^16 recycles of the same id, the handle of the first incarnation
    is the handle of the current one: `ecs_is_alive` cannot tell them apart. -/
theorem genInc_period (e : UInt64) : iterN genInc 65536 e = e := by
  rw [iterate_genInc]
  have h1 : (65536 : Nat).toUInt64 = 65536 := rfl
  rw [h1]
  unfold genIter
  rw [arith16_period]
  have : generation e + 0 = generation e := by simp
  rw [this]; exact unpack e

/-! ### The delete action for a target (on_delete.c 111-152) -/

theorem deleteAction_delete : ∀ (ps : List Policy), Policy.delete ∈ ps →
    deleteAction ps = some .delete
  | [], h => by simp at h
  | [p], h => by
    have hp : p = .delete := by simpa [eq_comm] using h
    simp [deleteAction, hp]
  | p :: q :: qs, h => by
    by_cases hp : p = .delete
    · simp [deleteAction, hp]
    · have h' : Policy.delete ∈ q :: qs := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm hp
        · exact h
      rw [show deleteAction (p :: q :: qs) = deleteAction (q :: qs) by simp [deleteAction, hp]]
      exact deleteAction_delete (q :: qs) h'

theorem deleteAction_no_delete : ∀ (ps : List Policy) (_ : Policy.delete ∉ ps) (hne : ps ≠ []),
    deleteAction ps = some (ps.getLast hne)
  | [], _, hne => absurd rfl hne
  | [p], h, _ => by
    have hp : p ≠ .delete := fun e => h (by simp [e])
    simp [deleteAction, hp]
  | p :: q :: qs, h, hne => by
    have hp : p ≠ .delete := fun e => h (by simp [e])
    have h' : Policy.delete ∉ q :: qs := fun m => h (List.mem_cons_of_mem _ m)
    rw [show deleteAction (p :: q :: qs) = deleteAction (q :: qs) by simp [deleteAction, hp]]
    rw [deleteAction_no_delete (q :: qs) h' (List.cons_ne_nil _ _)]
    simp

/-- Panic is honoured only when the panicking relationship's pair is the
    last one for the target in the table's type and no pair has Delete. -/
theorem deleteAction_panic_iff (ps : List Policy) :
    deleteAction ps = some .panic ↔
      (Policy.delete ∉ ps ∧ ∃ h : ps ≠ [], ps.getLast h = .panic) := by
  constructor
  · intro hd
    by_cases hdel : Policy.delete ∈ ps
    · rw [deleteAction_delete ps hdel] at hd; cases hd
    · have hne : ps ≠ [] := by intro h; subst h; simp [deleteAction] at hd
      refine ⟨hdel, hne, ?_⟩
      rw [deleteAction_no_delete ps hdel hne] at hd
      exact Option.some.inj hd
  · rintro ⟨hdel, hne, hl⟩
    rw [deleteAction_no_delete ps hdel hne, hl]

/-- The counterexample of `panic_target_order.c`: a Panic pair followed by a
    Remove pair for the same target. -/
example : deleteAction [.panic, .remove] = some .remove := by decide
example : deleteAction [.remove, .panic] = some .panic := by decide

/-! ### Entity index (storage/entity_index.c) -/

namespace EIndex

/-- Dense/sparse agreement: every slot of the dense array points back at
    itself through the record of its id. -/
def DenseInv (ix : EIndex) : Prop :=
  ∀ i, 1 ≤ i → i < ix.dense.size → (ix.recOf (ix.denseAt i)).dense = i

/-- `tryGetAny` returns the id's record. -/
theorem tryGetAny_some {ix : EIndex} {e : UInt64} {r : Rec} (h : ix.tryGetAny e = some r) :
    r = ix.recOf e := by
  unfold tryGetAny at h
  by_cases hp : ix.hasPage e
  · by_cases hd : (ix.recOf e).dense = 0
    · simp [hp, hd] at h
    · simp [hp, hd] at h
      exact h.symm
  · simp [hp] at h

/-- An id in the not-alive part of the dense array is not alive. -/
theorem not_alive_of_dead_slot (ix : EIndex) (hinv : DenseInv ix) (i : Nat)
    (h1 : ix.alive ≤ i) (h0 : 1 ≤ i) (h2 : i < ix.dense.size) :
    ix.isAlive (ix.denseAt i) = false := by
  unfold isAlive tryGet
  have hr := hinv i h0 h2
  cases h : ix.tryGetAny (ix.denseAt i) with
  | none => simp
  | some r =>
    have hrec := tryGetAny_some h
    subst hrec
    simp [hr, h1]

/-- `flecs_entity_index_new_id` recycling branch (entity_index.c 294-297)
    never hands out an id that is alive. -/
theorem newId_recycled_not_alive (ix : EIndex) (hinv : DenseInv ix)
    (hpos : 1 ≤ ix.alive) (hrec : ix.alive ≠ ix.dense.size) (hle : ix.alive ≤ ix.dense.size)
    (ix' : EIndex) (e : UInt64) (hnew : ix.newId = .ok (ix', e)) :
    ix.isAlive e = false := by
  unfold newId at hnew
  simp only [hrec, bne_iff_ne, ne_eq, not_false_eq_true, ↓reduceIte] at hnew
  have he : e = ix.denseAt ix.alive := by
    cases hnew; rfl
  subst he
  exact not_alive_of_dead_slot ix hinv ix.alive (Nat.le_refl _) hpos
    (Nat.lt_of_le_of_ne hle hrec)

end EIndex

end Flecs
