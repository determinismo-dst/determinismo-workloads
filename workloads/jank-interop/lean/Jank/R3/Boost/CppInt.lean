import Jank.R3.Boost.Ieee

/-!
# Round 3, Boost: `boost::multiprecision::cpp_int` as jank uses it

jank's `native_big_integer` is `number<cpp_int_backend<>>` (include/cpp/jank/type.hpp:33): an
unbounded, signed-magnitude integer of 64-bit limbs (`BOOST_HAS_INT128` holds on the x86-64 and
AArch64 compilers jank supports: cpp_int/cpp_int_config.hpp:104-121, `limb_type` 64 bits,
decimal blocks of 18 digits).

Replicated here from deps/boost-multiprecision (2b3ab082):

- string assignment, `cpp_int_backend::do_assign_string` (non-trivial branch, cpp_int.hpp:1752-1922);
- decimal printing, `do_get_string` (cpp_int.hpp:2039-2137) with the flags jank passes (none);
- conversion to `double`, `eval_convert_to` (cpp_int/misc.hpp:185-278);
- the limbs and sign jank's `big_integer::to_hash` reads (big_integer.cpp:148-170).

The arithmetic jank reaches (`+ - * / %`, comparisons, `gcd`) is cpp_int's exact integer
arithmetic: `/` truncates toward zero and `%` takes the dividend's sign, as for built-in
integers (boost's documentation, "cpp_int"), and `gcd` is non-negative (cpp_int/misc.hpp:559-578
ends with `result.sign(false)`): assumption MPA1. A value is an `Int`.
-/

namespace Jank.R3.Boost.CppInt

/-- A C string's bytes: up to the first NUL (`std::strlen`, `while (*s)`). -/
def cstr (s : List Nat) : List Nat := s.takeWhile (· != 0)

def isDec (c : Nat) : Bool := 48 ≤ c && c ≤ 57

/-- `do_assign_string(s, false_type)` (cpp_int.hpp:1752-1922): the value, or the
`std::runtime_error` it throws. A leading `-`; then `0x`/`0X` selects base 16 (both characters
dropped) and any other leading `0` base 8 (kept: it is an octal digit). Base 16 and 8 skip
leading zeros and place each digit's bits; base 10 reads blocks of 18 digits. The empty string
(after the prefix) is 0. -/
def assignString (s0 : List Nat) : Except String Int := Id.run do
  let mut s := cstr s0
  let mut n := s.length
  let mut radix : Nat := 10
  let mut isneg := false
  if n != 0 && s.head? == some 45 then
    n := n - 1; s := s.drop 1; isneg := true
  if n != 0 && s.head? == some 48 then
    if n > 1 && (s[1]! == 120 || s[1]! == 88) then
      radix := 16; s := s.drop 2; n := n - 2
    else
      radix := 8; n := n - 1
  let mut result : Int := 0
  if n != 0 then
    if radix == 16 then
      s := s.dropWhile (· == 48)
      for c in s do
        let val : Nat :=
          if isDec c then c - 48
          else if 97 ≤ c && c ≤ 102 then 10 + (c - 97)
          else if 65 ≤ c && c ≤ 70 then 10 + (c - 65)
          else 99
        if val == 99 then return .error "Unexpected content found while parsing character string."
        result := result * 16 + val
    else if radix == 8 then
      s := s.dropWhile (· == 48)
      for c in s do
        if 48 ≤ c && c ≤ 55 then result := result * 8 + (c - 48)
        else return .error "Unexpected content found while parsing character string."
    else
      -- Base 10: `block` takes up to 18 digits; `block_mult` is 10^18, or 10^(i+1) for the last.
      let mut rest := s
      let mut fuel := s.length + 1
      while !rest.isEmpty && fuel > 0 do
        fuel := fuel - 1
        let mut block : Nat := 0
        let mut mult : Nat := 1000000000000000000
        let mut i := 0
        let mut stop := false
        while i < 18 && !stop do
          match rest with
          | [] => stop := true
          | c :: tl =>
            if !isDec c then return .error "Unexpected character encountered in input."
            block := block * 10 + (c - 48)
            rest := tl
            if tl.isEmpty then
              mult := 10 ^ (i + 1); stop := true
            i := i + 1
        result := result * mult + block
  return .ok (if isneg then -result else result)

/-- The number of 64-bit limbs of `|v|` (`size()`; 0 has one limb). -/
def size (v : Int) : Nat := Id.run do
  let mut m := v.natAbs
  let mut k := 1
  m := m / 2 ^ 64
  while m != 0 do
    k := k + 1; m := m / 2 ^ 64
  return k

/-- The limbs of `|v|`, least significant first (`limbs()`). -/
def limbs (v : Int) : List Nat :=
  (List.range (size v)).map fun i => (v.natAbs / 2 ^ (64 * i)) % 2 ^ 64

/-- `do_get_string(f = 0, false_type)` (cpp_int.hpp:2039-2137), decimal: one limb through
`std::to_string`, more through blocks of 18 digits (`divide_unsigned_helper` by 10^18), leading
zeros erased, `"0"` for an empty result, `-` for a negative value. -/
def str (v : Int) : String := Id.run do
  let neg := v < 0
  let t := v.natAbs
  let mut result : List Char := []
  if size v == 1 then
    result := (toString t).toList
  else
    let bits := size v * 64
    let len := bits / 3 + 1
    let mut buf : Array Char := Array.replicate len '0'
    let mut pos : Int := len - 1
    let mut tt := t
    let mut fuel := len + 1
    while tt != 0 && fuel > 0 do
      fuel := fuel - 1
      let r := tt % 1000000000000000000
      tt := tt / 1000000000000000000
      let mut vv := r
      let mut i := 0
      let mut brk := false
      while i < 18 && !brk do
        buf := buf.set! pos.toNat (Char.ofNat (48 + vv % 10))
        vv := vv / 10
        if pos == 0 then brk := true else pos := pos - 1
        i := i + 1
    result := buf.toList
  result := result.dropWhile (· == '0')
  if result.isEmpty then result := ['0']
  return String.ofList ((if neg then ['-'] else []) ++ result)

/-- The bit length of `n` (`eval_msb_imp + 1`), 0 for 0. -/
def bitLen (n : Nat) : Nat := if n == 0 then 0 else Nat.log2 n + 1

/-- `eval_convert_to(double*, backend)` (cpp_int/misc.hpp:185-278): more than 53 bits keep the
top 53 (`mask`, `ldexp` per limb), then round up with `nextafter(r, 2r)` when the first dropped
bit is set and either a lower bit or the last kept bit is set (round to nearest, ties to even).
A truncated value at or past 2^1024 is infinite. -/
def toDouble (v : Int) : Float :=
  let m := v.natAbs
  if m == 0 then 0.0 else
  let bits := bitLen m
  let r : Float :=
    if bits > 53 then
      let drop := bits - 53
      let trunc := (m / 2 ^ drop) * 2 ^ drop
      let base : Float :=
        if bits > 1024 then Float.ofBits 0x7FF0000000000000
        else Float.ofBits (Jank.Codegen.Float.ofRat false trunc 1)
      let roundBit := drop - 1
      let bitSet := fun (k : Nat) => (m / 2 ^ k) % 2 == 1
      if bitSet roundBit && ((m % 2 ^ roundBit != 0) || bitSet (roundBit + 1)) then
        -- nextafter(r, 2r) for a positive finite r; infinity stays infinite.
        if base.isInf then base else Float.ofBits (base.toBits + 1)
      else base
    else Float.ofBits (Jank.Codegen.Float.ofRat false m 1)
  if v < 0 then -r else r

/-- jank's own `hash_combine` (big_integer.cpp:148-153) on `std::size_t`: `std::hash` of a
64-bit limb is the identity (assumption A4). -/
def hashCombine (seed : UInt64) (h : UInt64) : UInt64 :=
  seed ^^^ (h + (0x9e3779b9 : UInt64) + (seed <<< 6) + (seed >>> 2))

/-- `big_integer::to_hash(native_big_integer const &)` (big_integer.cpp:155-170): the seed starts
at the sign (1 for negative), each limb is combined; `uhash` keeps the low 32 bits. -/
def bigHash (v : Int) : UInt32 :=
  let seed0 : UInt64 := if v < 0 then 1 else 0
  ((limbs v).foldl (fun s l => hashCombine s (UInt64.ofNat l)) seed0).toUInt32

/-- C++ truncating division and remainder (cpp_int's `/` and `%`). -/
def tdiv (a b : Int) : Int := Int.tdiv a b
def tmod (a b : Int) : Int := Int.tmod a b

/-- `i64` range. -/
def i64min : Int := -9223372036854775808
def i64max : Int := 9223372036854775807
def fitsI64 (v : Int) : Bool := i64min ≤ v && v ≤ i64max

end Jank.R3.Boost.CppInt
