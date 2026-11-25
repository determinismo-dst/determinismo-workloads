import Jank.Hash
import Std.Tactic.BVDecide

/-!
# Keys with a chosen hash

jank hashes a long with `hash::integer(u64)` (hash.cpp; Murmur3 `hashLong`): for input
`hi * 2^32 + lo ≠ 0` it is `fmix(mix_h1(mix_h1(0, mix_k1(lo)), mix_k1(hi)), 8)`. Every step is a
bijection of `u32`, so for every target hash `h` and every high word `hi` there is exactly one
low word `lo` with that hash: a long literal with any chosen hash, and as many distinct longs
with the same 32-bit hash as there are high words. They drive the CHAMP to a chosen depth (keys
sharing the low `5 d` bits of their hash share `d` levels) and to its collision nodes (equal
32-bit hashes; immer's `size_t` hash has its upper half zero, so 13 levels down).
-/

namespace Jank.R3.Immer.HashInv

open Jank.Hash

def rotr32 (x : UInt32) (r : UInt32) : UInt32 := (x >>> r) ||| (x <<< (32 - r))

/-- The `h1` with `mix_h1(h1, k1) = y`. -/
def invMixH1 (y k1 : UInt32) : UInt32 := rotr32 ((y - 0xe6546b64) * FiveInv) 13 ^^^ k1

/-- The `k` with `mix_k1(k) = w`. -/
def invMixK1 (w : UInt32) : UInt32 := rotr32 (w * C2inv) 15 * C1inv

/-- The `x` with `fmix(x, 8) = h`. -/
def invFmix8 (h : UInt32) : UInt32 :=
  let x := h ^^^ (h >>> 16)
  let x := x * M2inv
  let x := x ^^^ (x >>> 13) ^^^ (x >>> 26)
  let x := x * M1inv
  let x := x ^^^ (x >>> 16)
  x ^^^ 8

/-- The long (as its 64 bits) with high word `hi` whose jank hash is `h`. -/
def longWithHash (h hi : UInt32) : UInt64 :=
  let y := invFmix8 h
  let z := invMixH1 y (mixK1 hi)
  let lo := invMixK1 (invMixH1 z 0)
  (hi.toUInt64 <<< 32) ||| lo.toUInt64

/-- The long as a signed value (`i64`). -/
def longValue (h hi : UInt32) : Int := (longWithHash h hi).toInt64.toInt

theorem xor_xor_cancel (a k : UInt32) : (a ^^^ k) ^^^ k = a := by bv_decide
theorem rotl_rotr13 (x : UInt32) : rotl (rotr32 x 13) 13 = x := by unfold rotl rotr32; bv_decide
theorem rotl_rotr15 (x : UInt32) : rotl (rotr32 x 15) 15 = x := by unfold rotl rotr32; bv_decide
theorem xs16_xs16 (x : UInt32) : (x ^^^ (x >>> 16)) ^^^ ((x ^^^ (x >>> 16)) >>> 16) = x := by bv_decide
theorem xs13_inv (x : UInt32) :
    let y := x ^^^ (x >>> 13) ^^^ (x >>> 26)
    y ^^^ (y >>> 13) = x := by intro y; bv_decide
theorem inv_mul (x c ci : UInt32) (h : ci * c = 1) : x * ci * c = x := by
  rw [UInt32.mul_assoc, h, UInt32.mul_one]

theorem mixK1_of_inv (w : UInt32) : mixK1 (invMixK1 w) = w := by
  unfold mixK1 invMixK1
  rw [inv_mul _ C1 C1inv (by decide), rotl_rotr15, inv_mul _ C2 C2inv (by decide)]

theorem mixH1_of_inv (y k : UInt32) : mixH1 (invMixH1 y k) k = y := by
  unfold mixH1 invMixH1
  rw [xor_xor_cancel, rotl_rotr13, inv_mul _ 5 FiveInv (by decide), UInt32.sub_add_cancel]

theorem mixH1_zero_comm (w : UInt32) : mixH1 0 w = mixH1 w 0 := by
  unfold mixH1; rw [UInt32.zero_xor, UInt32.xor_zero]

theorem fmix_of_inv (h : UInt32) : fmix (invFmix8 h) 8 = h := by
  unfold fmix invFmix8
  simp only [xor_xor_cancel]
  generalize hx : (h ^^^ h >>> 16) * M2inv = x1
  rw [xs16_xs16, inv_mul _ 0x85ebca6b M1inv (by decide), xs13_inv, ← hx,
    inv_mul _ 0xc2b2ae35 M2inv (by decide), xs16_xs16]

/-- The halves of `(hi << 32) | lo`. -/
theorem halves (hi lo : UInt32) :
    ((hi.toUInt64 <<< 32) ||| lo.toUInt64).toUInt32 = lo ∧
    (((hi.toUInt64 <<< 32) ||| lo.toUInt64) >>> 32).toUInt32 = hi := by
  constructor <;> bv_decide

/-- Every long built by `longWithHash h hi` that is not 0 hashes to `h` in jank. -/
theorem integer_longWithHash (h hi : UInt32) (hne : longWithHash h hi ≠ 0) :
    integer (longWithHash h hi) = h := by
  unfold integer
  have hne' : (longWithHash h hi == 0) = false := by simpa using hne
  rw [hne']
  simp only [Bool.false_eq_true, ite_false]
  unfold longWithHash
  rw [(halves _ _).1, (halves _ _).2, mixK1_of_inv, seed, mixH1_zero_comm, mixH1_of_inv,
    mixH1_of_inv, fmix_of_inv]

end Jank.R3.Immer.HashInv
