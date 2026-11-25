/-!
# Round 4: `clojure.data.json`

**jank** (src/jank/clojure/data/json.jank, src/cpp/clojure/data/json_native.cpp) over nlohmann
json 02dfbea3 (deps/json):
- `read-str` (json.jank 9–59 → json_native.cpp `read_str` 198–202): `nlohmann::json::parse(s)`
  (throws `parse_error`, a native exception, on any malformed or empty input), then `read`
  (126–196). Integers: the lexer (include/nlohmann/detail/input/lexer.hpp 1249–1299) keeps a
  non-negative integer as `number_unsigned` when `strtoull` fits 64 bits, a negative one as
  `number_integer` when `strtoll` fits, anything else as `number_float`; `read` returns
  `json.get<i64>()` (142), a `static_cast` (from_json.hpp 77–107): an unsigned value past
  2^63 wraps. With `:bigdec true` a decimal becomes `big_decimal(json.get<f64>())` (147),
  the double's binary value (S9's path). `default-read-options` (json.jank 5–7) has no
  `:eof-error?`.
- `write-str` (json.jank 61–110 → `write` 37–120): `big_integer`/`big_decimal`/`uuid` become
  JSON *strings* of their `to_string` (69–72); a non-finite double is dumped as `null`
  (serializer.hpp `dump_float` 799–806); a character is neither listed nor seqable: it throws
  "JSON write error (unsupported type)" (117–118); data.json throws there too.

**data.json** 2.5.2 (its source, clojure/data/json.clj): `read-integer` (184–189) gives a Long
or a BigInt; `read-decimal` (191–194) `(bigdec string)` from the text; `read-str` (550–558)
defaults `:eof-error?` to true and returns `:eof-value` on empty input when it is false;
`write-bignum` writes BigInt/BigInteger/BigDecimal as JSON numbers (772–780); NaN and infinite
doubles throw "JSON error: cannot write Double NaN" (705–720); characters throw too (no
JSONWriter for Character, `default-write-fn` 793–794), as in jank.
-/

namespace Jank.R4.Core.Json

/-- A JSON number token (sign, digits) read back. -/
inductive Num where
  | long (i : Int)
  | big (i : Int)
  | dbl (approx : Int)   -- a double; only that it is a double and its rounded value matter here
  deriving Repr, BEq, Inhabited

def Num.code : Num → String
  | .long i => toString i
  | .big i => s!"{i}N"
  | .dbl i => s!"{i}.0 (double)"

def u64Max : Int := 2 ^ 64 - 1
def i64Min : Int := -(2 ^ 63)
def i64Max : Int := 2 ^ 63 - 1

/-- nlohmann's lexer (1249–1299) then `json.get<i64>()` (json_native.cpp 142). -/
def jankReadInteger (v : Int) : Num :=
  if 0 ≤ v then
    if v ≤ u64Max then
      -- number_unsigned, static_cast<int64_t>: two's complement wrap
      .long (if v ≤ i64Max then v else v - 2 ^ 64)
    else .dbl v
  else
    if i64Min ≤ v then .long v else .dbl v

/-- data.json `read-integer` (184–189): a Long when it fits, else a BigInt. -/
def cljReadInteger (v : Int) : Num :=
  if i64Min ≤ v ∧ v ≤ i64Max then .long v else .big v

/-- `=` on the two results (a BigInt and a long of the same value are `=`; a double never is
here, since every double case is outside the long range and data.json gives a BigInt). -/
def sameNum : Num → Num → Bool
  | .long a, .long b => a == b
  | .long a, .big b => a == b
  | .big a, .long b => a == b
  | .big a, .big b => a == b
  | .dbl _, .dbl _ => true
  | _, _ => false

/-- For every integer in [2^63, 2^64): jank reads a negative long, data.json the exact BigInt. -/
theorem jank_reads_u64_wrapped (v : Int) (h1 : 2 ^ 63 ≤ v) (h2 : v ≤ u64Max) :
    jankReadInteger v = .long (v - 2 ^ 64) ∧ cljReadInteger v = .big v := by
  have h0 : (0 : Int) ≤ v := Int.le_trans (by decide) h1
  have hn : ¬ v ≤ i64Max := by unfold i64Max; omega
  have hn2 : ¬ (i64Min ≤ v ∧ v ≤ i64Max) := fun ⟨_, b⟩ => hn b
  simp [jankReadInteger, cljReadInteger, h0, h2, hn]

/-- Exactly representable in binary64 (normal range): a decimal `m / 10^k` whose reduced
denominator is a power of two and whose odd part fits 53 bits. -/
def dyadic53 (m : Int) (k : Nat) : Bool := Id.run do
  -- reduce m / 10^k = m / (2^k 5^k): divide out 5s from m
  let mut num := m.natAbs
  let mut fives := k
  while fives > 0 && num % 5 == 0 && num > 0 do
    num := num / 5
    fives := fives - 1
  if num == 0 then return true
  if fives > 0 then return false
  -- odd part of the numerator must fit 53 bits
  let mut odd := num
  while odd % 2 == 0 do odd := odd / 2
  return odd < 2 ^ 53

/-- `:bigdec true` on a decimal `m/10^k`: data.json gives the exact decimal; jank gives the
double's binary value, equal to it exactly when the decimal is a binary64 value. -/
def bigdecAgrees (m : Int) (k : Nat) : Bool := dyadic53 m k

/-- What `write-str` does with a value of each kind (json_native.cpp `write` 37–113 against
data.json's JSONWriter). -/
structure WriteCase where
  src : String
  jank : String
  clj : String
  deriving Repr, Inhabited

def writeCases : List WriteCase :=
  [ ⟨"123N", "\"123\" (a JSON string)", "123"⟩,
    ⟨"1.5M", "\"1.5\" (a JSON string)", "1.5"⟩,
    ⟨"##NaN", "null", "throws: cannot write Double NaN"⟩,
    ⟨"##Inf", "null", "throws: cannot write Double Infinity"⟩,
    ⟨"\\a", "throws: JSON write error (unsupported type: character)", "throws: Don't know how to write JSON of class java.lang.Character"⟩,
    ⟨"[1 \"x\" nil true]", "[1,\"x\",null,true]", "[1,\"x\",null,true]"⟩,
    ⟨"{:a 1}", "{\"a\":1}", "{\"a\":1}"⟩ ]

end Jank.R4.Core.Json
