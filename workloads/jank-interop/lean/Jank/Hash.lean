import Std.Tactic.BVDecide

/-!
# Hashing: jank's hash.cpp beside Clojure's Murmur3.java

Every function is over `UInt32` as the C++ `u32` and Java's `int` arithmetic wrap. jank's
definitions cite src/cpp/jank/hash.cpp; Clojure's cite clojure/lang/Murmur3.java (1.12).
-/

namespace Jank.Hash

/-! ## jank (src/cpp/jank/hash.cpp) -/

def seed : UInt32 := 0
def C1 : UInt32 := 0xcc9e2d51
def C2 : UInt32 := 0x1b873593

/-- hash.cpp `rotate_left(u32, i8)`. -/
def rotl (x : UInt32) (r : UInt32) : UInt32 := (x <<< r) ||| (x >>> (32 - r))

/-- hash.cpp `fmix(u32 h1, u32 length)`. -/
def fmix (h1 length : UInt32) : UInt32 :=
  let h1 := h1 ^^^ length
  let h1 := h1 ^^^ (h1 >>> 16)
  let h1 := h1 * 0x85ebca6b
  let h1 := h1 ^^^ (h1 >>> 13)
  let h1 := h1 * 0xc2b2ae35
  h1 ^^^ (h1 >>> 16)

/-- hash.cpp `mix_k1`. -/
def mixK1 (k1 : UInt32) : UInt32 := rotl (k1 * C1) 15 * C2

/-- hash.cpp `mix_h1`. -/
def mixH1 (h1 k1 : UInt32) : UInt32 := rotl (h1 ^^^ k1) 13 * 5 + 0xe6546b64

/-- hash.cpp `mix_collection_hash`. -/
def mixCollectionHash (hash length : UInt32) : UInt32 := fmix (mixH1 seed (mixK1 hash)) length

/-- hash.cpp `combine` (boost's hash_combine on u32). -/
def combine (s t : UInt32) : UInt32 := s ^^^ (t + 0x9e3779b9 + (s <<< (6 : UInt32)) + (s >>> (2 : UInt32)))

/-- hash.cpp `integer(u64)` (what `integer(i64)` calls on a 64-bit platform). -/
def integer (input : UInt64) : UInt32 :=
  if input == 0 then 0
  else
    let low := input.toUInt32
    let high := (input >>> 32).toUInt32
    let h1 := mixH1 seed (mixK1 low)
    let h1 := mixH1 h1 (mixK1 high)
    fmix h1 8

/-- hash.cpp `real(f64)`: the double's bits `v ^ (v >> 32)`, truncated (Java's Double.hashCode). -/
def real (bits : UInt64) : UInt32 := (bits ^^^ (bits >>> 32)).toUInt32

/-- How the platform's `char` widens: signed on x86-64 and Apple arm64, unsigned on Linux
AArch64. -/
inductive CharSign where | signed | unsigned
  deriving Repr, BEq

def widen (cs : CharSign) (b : UInt8) : UInt32 :=
  match cs with
  | .unsigned => b.toUInt32
  | .signed => if b ≥ 128 then b.toUInt32 ||| 0xFFFFFF00 else b.toUInt32

/-- hash.cpp `string(immutable_string_view)`: over the UTF-8 bytes; a pair is
`input[i - 1] | (input[i] << 16)` with `char`s (so the sign of `char` matters past ASCII), the
odd last byte is read as `u8`. -/
def string (cs : CharSign) (input : List UInt8) : UInt32 := Id.run do
  let arr := input.toArray
  let length := arr.size
  let mut h1 := seed
  let mut i := 1
  while i < length do
    let k1 := widen cs arr[i-1]! ||| (widen cs arr[i]! <<< 16)
    h1 := mixH1 h1 (mixK1 k1)
    i := i + 2
  if length % 2 == 1 then
    let k1 := arr[length - 1]!.toUInt32
    h1 := h1 ^^^ mixK1 k1
  return fmix h1 (2 * length.toUInt32)

/-- hash.cpp `integer(u32)` (Murmur3 hashInt). -/
def integer32 (input : UInt32) : UInt32 :=
  if input == 0 then 0 else fmix (mixH1 seed (mixK1 input)) 4

/-- jtl/immutable_string.hpp `to_hash`: Java's String.hashCode over the bytes (`ptr[i] & 0xff`),
then `hash::integer` of that u32 (persistent_string and character hash with this). -/
def immutableString (bytes : List UInt8) : UInt32 :=
  integer32 (bytes.foldl (fun h b => 31 * h + b.toUInt32) 0)

/-- symbol.cpp `symbol::to_hash`: `combine(hash::string(name), hash::string(ns))`. -/
def symbol (cs : CharSign) (ns name : List UInt8) : UInt32 := combine (string cs name) (string cs ns)

/-- keyword.cpp `keyword::to_hash`: `sym->to_hash() + 0x9e3779b9`. -/
def keyword (cs : CharSign) (ns name : List UInt8) : UInt32 := symbol cs ns name + 0x9e3779b9

/-- hash.hpp `ordered(It begin, It end)` (vectors, lists, ...): from 1, `31 * hash + h`. -/
def orderedRange (hs : List UInt32) : UInt32 :=
  mixCollectionHash (hs.foldl (fun acc h => 31 * acc + h) 1) hs.length.toUInt32

/-- hash.hpp `unordered(It begin, It end)` for single elements (sets): from 0, summed. -/
def unorderedRange (hs : List UInt32) : UInt32 :=
  mixCollectionHash (hs.foldl (· + ·) 0) hs.length.toUInt32

/-- hash.hpp `unordered(It begin, It end)` for pairs (maps): `31 * h(k) + h(v)` summed from 0. -/
def unorderedPairs (kvs : List (UInt32 × UInt32)) : UInt32 :=
  mixCollectionHash (kvs.foldl (fun acc (k, v) => acc + (31 * k + v)) 0) kvs.length.toUInt32

/-- hash.cpp `ordered(object_ref)`: on a `sequence_like` object, from 1, `31 * hash + h`; else
the object's own `to_hash()`. -/
def orderedSeq (hs : List UInt32) : UInt32 := orderedRange hs

/-- hash.cpp `unordered(object_ref)`: on a `sequence_like` object, from **1**, summed; else the
object's own `to_hash()`. (The range version starts from 0.) -/
def unorderedSeq (hs : List UInt32) : UInt32 :=
  mixCollectionHash (hs.foldl (· + ·) 1) hs.length.toUInt32

/-- big_integer.cpp `big_integer::to_hash`: boost-style `hash_combine` of the 64-bit limbs
(least significant first) with `std::hash<limb_type>` (the identity on libc++ and libstdc++),
seeded with the sign, over `size_t`, truncated to `u32`. -/
def bigInteger (v : Int) : UInt32 :=
  let sign : UInt64 := if v < 0 then 1 else 0
  let rec limbs (m : Nat) (fuel : Nat) : List UInt64 :=
    match fuel with
    | 0 => []
    | fuel + 1 => if m == 0 then [] else (UInt64.ofNat (m % 2^64)) :: limbs (m / 2^64) fuel
  -- boost cpp_int keeps one limb for 0.
  let ls := match limbs v.natAbs 64 with | [] => [0] | l => l
  let s := ls.foldl (fun (s : UInt64) (l : UInt64) => s ^^^ (l + 0x9e3779b9 + (s <<< (6 : UInt64)) + (s >>> (2 : UInt64)))) sign
  s.toUInt32

/-! ## Clojure (clojure/lang/Murmur3.java, Numbers.hasheq) -/

namespace Clj

def mixK1 (k1 : UInt32) : UInt32 :=
  let k1 := k1 * 0xcc9e2d51
  let k1 := (k1 <<< 15) ||| (k1 >>> 17)
  k1 * 0x1b873593

def mixH1 (h1 k1 : UInt32) : UInt32 :=
  let h1 := h1 ^^^ k1
  let h1 := (h1 <<< 13) ||| (h1 >>> 19)
  h1 * 5 + 0xe6546b64

def fmix (h1 length : UInt32) : UInt32 :=
  let h1 := h1 ^^^ length
  let h1 := h1 ^^^ (h1 >>> 16)
  let h1 := h1 * 0x85ebca6b
  let h1 := h1 ^^^ (h1 >>> 13)
  let h1 := h1 * 0xc2b2ae35
  h1 ^^^ (h1 >>> 16)

def hashLong (input : UInt64) : UInt32 :=
  if input == 0 then 0
  else
    let low := input.toUInt32
    let high := (input >>> 32).toUInt32
    let h1 := mixH1 0 (mixK1 low)
    let h1 := mixH1 h1 (mixK1 high)
    fmix h1 8

def mixCollHash (hash count : UInt32) : UInt32 := fmix (mixH1 0 (mixK1 hash)) count

def hashOrdered (hs : List UInt32) : UInt32 :=
  mixCollHash (hs.foldl (fun acc h => 31 * acc + h) 1) hs.length.toUInt32

def hashUnordered (hs : List UInt32) : UInt32 :=
  mixCollHash (hs.foldl (· + ·) 0) hs.length.toUInt32

/-- Numbers.hasheq for a Double: "if(x.equals(-0.0)) return 0;  // match 0.0", else
Double.hashCode. -/
def hasheqDouble (bits : UInt64) : UInt32 :=
  if bits == 0x8000000000000000 then 0 else (bits ^^^ (bits >>> 32)).toUInt32

/-- BigInt.hasheq: `Murmur3.hashLong(lpart)` when it fits a long (Numbers.hasheqFrom does the
same for BigInteger in range): the same hash as the equal Long. -/
def hasheqBigInt (v : Int) : UInt32 :=
  if -9223372036854775808 ≤ v ∧ v ≤ 9223372036854775807 then hashLong (UInt64.ofInt v)
  else 0x5eed  -- out of long range: BigInteger.hashCode (not modeled)

end Clj

/-! ## Theorems -/

/-- jank's Murmur3 steps are Clojure's. -/
theorem mixK1_eq (k : UInt32) : mixK1 k = Clj.mixK1 k := by
  unfold mixK1 Clj.mixK1 rotl C1 C2; rfl

theorem mixH1_eq (h k : UInt32) : mixH1 h k = Clj.mixH1 h k := by
  unfold mixH1 Clj.mixH1 rotl; rfl

theorem fmix_eq (h n : UInt32) : fmix h n = Clj.fmix h n := rfl

/-- `hash` of a jank integer (small or heap: number.cpp `to_hash` → `hash::integer(i64)`) is
Clojure's `hashLong` for every 64-bit value. -/
theorem integer_eq_hashLong (x : UInt64) : integer x = Clj.hashLong x := by
  unfold integer Clj.hashLong
  simp only [mixK1_eq, mixH1_eq, fmix_eq, seed]

/-! ### The collection mix is injective in the hash

Each step of `mix_collection_hash` (mix_k1: multiply by an odd constant, rotate, multiply;
mix_h1 from seed 0: rotate, multiply by 5, add; fmix: xor-shifts and odd multiplications) has an
inverse. So two different basis values never mix to the same hash. -/

/-- Multiplicative inverses mod 2^32 of the odd constants. -/
def C1inv : UInt32 := 0xdee13bb1
def C2inv : UInt32 := 0x56ed309b
def M1inv : UInt32 := 0xa5cb9243  -- 0x85ebca6b⁻¹
def M2inv : UInt32 := 0x7ed1b41d  -- 0xc2b2ae35⁻¹
def FiveInv : UInt32 := 0xcccccccd

theorem inverses : C1 * C1inv = 1 ∧ C2 * C2inv = 1 ∧ (0x85ebca6b : UInt32) * M1inv = 1 ∧
    (0xc2b2ae35 : UInt32) * M2inv = 1 ∧ (5 : UInt32) * FiveInv = 1 := by decide

def rotr (x : UInt32) (r : UInt32) : UInt32 := (x >>> r) ||| (x <<< (32 - r))

/-- `mix_collection_hash` as its steps. -/
def stepK1a (x : UInt32) : UInt32 := x * C1
def stepRot15 (x : UInt32) : UInt32 := rotl x 15
def stepK1b (x : UInt32) : UInt32 := x * C2
def stepRot13 (x : UInt32) : UInt32 := rotl x 13
def stepH1 (x : UInt32) : UInt32 := x * 5 + 0xe6546b64
def stepLen (n x : UInt32) : UInt32 := x ^^^ n
def stepXs16 (x : UInt32) : UInt32 := x ^^^ (x >>> (16 : UInt32))
def stepM1 (x : UInt32) : UInt32 := x * 0x85ebca6b
def stepXs13 (x : UInt32) : UInt32 := x ^^^ (x >>> (13 : UInt32))
def stepM2 (x : UInt32) : UInt32 := x * 0xc2b2ae35

theorem mixCollectionHash_steps (x n : UInt32) :
    mixCollectionHash x n = stepXs16 (stepM2 (stepXs13 (stepM1 (stepXs16 (stepLen n
      (stepH1 (stepRot13 (stepK1b (stepRot15 (stepK1a x)))))))))) := by
  unfold mixCollectionHash fmix mixH1 mixK1 seed stepXs16 stepM2 stepXs13 stepM1 stepLen stepH1
    stepRot13 stepK1b stepRot15 stepK1a
  simp only [UInt32.zero_xor]

theorem inj_of_left_inv {f g : UInt32 → UInt32} (h : ∀ x, g (f x) = x) : Function.Injective f := by
  intro a b e
  have ha := h a
  rw [e, h b] at ha
  exact ha.symm

theorem mul_cancel (x c ci : UInt32) (h : c * ci = 1) : x * c * ci = x := by
  rw [UInt32.mul_assoc, h, UInt32.mul_one]

theorem stepK1a_inj : Function.Injective stepK1a :=
  inj_of_left_inv (g := (· * C1inv)) fun x => mul_cancel x C1 C1inv inverses.1
theorem stepK1b_inj : Function.Injective stepK1b :=
  inj_of_left_inv (g := (· * C2inv)) fun x => mul_cancel x C2 C2inv inverses.2.1
theorem stepM1_inj : Function.Injective stepM1 :=
  inj_of_left_inv (g := (· * M1inv)) fun x => mul_cancel x _ M1inv inverses.2.2.1
theorem stepM2_inj : Function.Injective stepM2 :=
  inj_of_left_inv (g := (· * M2inv)) fun x => mul_cancel x _ M2inv inverses.2.2.2.1
theorem stepH1_inj : Function.Injective stepH1 :=
  inj_of_left_inv (g := fun y => (y - 0xe6546b64) * FiveInv) fun x => by
    unfold stepH1; rw [UInt32.add_sub_cancel]; exact mul_cancel x 5 FiveInv inverses.2.2.2.2
theorem stepRot15_inj : Function.Injective stepRot15 :=
  inj_of_left_inv (g := fun y => rotr y 15) fun x => by unfold stepRot15 rotr rotl; bv_decide
theorem stepRot13_inj : Function.Injective stepRot13 :=
  inj_of_left_inv (g := fun y => rotr y 13) fun x => by unfold stepRot13 rotr rotl; bv_decide
theorem stepLen_inj (n : UInt32) : Function.Injective (stepLen n) :=
  inj_of_left_inv (g := fun y => y ^^^ n) fun x => by unfold stepLen; bv_decide
theorem stepXs16_inj : Function.Injective stepXs16 :=
  inj_of_left_inv (g := stepXs16) fun x => by unfold stepXs16; bv_decide
theorem stepXs13_inj : Function.Injective stepXs13 :=
  inj_of_left_inv (g := fun y => y ^^^ (y >>> (13 : UInt32)) ^^^ (y >>> (26 : UInt32)))
    fun x => by unfold stepXs13; bv_decide

theorem mix_injective (x y n : UInt32) (h : mixCollectionHash x n = mixCollectionHash y n) : x = y := by
  rw [mixCollectionHash_steps, mixCollectionHash_steps] at h
  exact stepK1a_inj (stepRot15_inj (stepK1b_inj (stepRot13_inj (stepH1_inj (stepLen_inj n
    (stepXs16_inj (stepM1_inj (stepXs13_inj (stepM2_inj (stepXs16_inj h))))))))))

/-- `hash::unordered(object_ref)` (from 1) never agrees with `hash::unordered(begin, end)` (from
0) on the same element hashes: `hash-unordered-coll` of a seq is never the hash of the set of
its elements. -/
theorem unorderedSeq_ne_unorderedRange (hs : List UInt32) : unorderedSeq hs ≠ unorderedRange hs := by
  intro h
  unfold unorderedSeq unorderedRange at h
  have := mix_injective _ _ _ h
  -- foldl (+) 1 = foldl (+) 0 + 1
  have shift : ∀ (l : List UInt32) (a : UInt32), l.foldl (· + ·) (a + 1) = l.foldl (· + ·) a + 1 := by
    intro l; induction l with
    | nil => intro a; rfl
    | cons x xs ih => intro a; simp only [List.foldl_cons]; rw [← ih]; congr 1; ac_rfl
  have h1 := shift hs 0
  simp only [UInt32.zero_add] at h1
  rw [h1] at this
  have ne : ∀ s : UInt32, s + 1 ≠ s := by intro s; bv_decide
  exact ne _ this

/-- A map's seq (base_persistent_map_sequence.cpp `to_hash` → `hash::unordered(this)`) and the
vector of its one entry (`hash::ordered`) never hash alike, whatever the entry. -/
theorem mapseq1_ne_vector1 (e : UInt32) : unorderedSeq [e] ≠ orderedRange [e] := by
  intro h
  unfold unorderedSeq orderedRange at h
  have := mix_injective _ _ _ h
  simp only [List.foldl_cons, List.foldl_nil] at this
  have h31 : (1 : UInt32) + e = 31 * 1 + e := this
  have ne : ∀ e : UInt32, (1 : UInt32) + e ≠ 31 * 1 + e := by intro e; bv_decide
  exact ne e h31

/-- -0.0 and 0.0: jank's `hash::real` tells them apart; Clojure's hasheq does not. -/
theorem negzero_hashes :
    real 0x8000000000000000 ≠ real 0 ∧ Clj.hasheqDouble 0x8000000000000000 = Clj.hasheqDouble 0 := by
  decide

end Jank.Hash
