import Jank.StrModel

/-!
# Round 6, strings: what the case functions do with a cut string (corrects round 2's `jUpper`)

util/string.cpp `to_uppercase` 26–36 / `to_lowercase` 14–24 decode with
`std::wstring_convert<std::codecvt_utf8<wchar_t>>::from_bytes`. In libstdc++ 15.3.0
(deps/libstdcxx-15.3.0-codecvt: locale_conv.h `__do_str_codecvt` 55–100 and `from_bytes` 336–347;
codecvt.cc `read_utf8_code_point` 252–330 and `ucs4_in` 468–475):

- a byte 0x80–0xC1 or 0xF5–0xFF in lead position, a bad continuation byte, an overlong 3-byte form or
  an encoded surrogate is `error`: `from_bytes` throws std::range_error("wstring_convert::from_bytes");
- a last character with fewer bytes than its lead announces is `partial`: `__do_str_codecvt` returns
  true with what it converted, so the cut character is dropped without an error.

Round 2's `jUpper`/`jLower` (and so `jCapitalize`) threw for every invalid text; `fromBytes` below is
the corrected decoder. W4 is its first case: `(upper-case (subs "é" 0 1))` is "" in jank.
-/

namespace Jank.R6.Str

open Jank.Str

/-- libstdc++ 15.3.0 `codecvt_utf8<wchar_t>` through `from_bytes` (maxcode 0x10FFFF). -/
def fromBytes : List UInt8 → Except String (List Nat)
  | [] => .ok []
  | b :: rest =>
    let c1 := b.toNat
    let cont (x : UInt8) : Bool := x.toNat &&& 0xC0 == 0x80
    if c1 < 0x80 then (fromBytes rest).map (c1 :: ·)
    else if c1 < 0xC2 then .error "range_error"
    else if c1 < 0xE0 then
      match rest with
      | [] => .ok []
      | c2 :: rest' =>
        if !cont c2 then .error "range_error"
        else (fromBytes rest').map ((((c1 &&& 0x1F) <<< 6) ||| (c2.toNat &&& 0x3F)) :: ·)
    else if c1 < 0xF0 then
      match rest with
      | [] => .ok []
      | c2 :: rest' =>
        if !cont c2 then .error "range_error"
        else if c1 == 0xE0 && c2.toNat < 0xA0 then .error "range_error"
        else if c1 == 0xED && c2.toNat ≥ 0xA0 then .error "range_error"
        else match rest' with
          | [] => .ok []
          | c3 :: rest'' =>
            if !cont c3 then .error "range_error"
            else (fromBytes rest'').map
              ((((c1 &&& 0x0F) <<< 12) ||| ((c2.toNat &&& 0x3F) <<< 6) ||| (c3.toNat &&& 0x3F)) :: ·)
    else if c1 < 0xF5 then
      match rest with
      | [] => .ok []
      | c2 :: rest' =>
        if !cont c2 then .error "range_error"
        else if c1 == 0xF0 && c2.toNat < 0x90 then .error "range_error"
        else if c1 == 0xF4 && c2.toNat ≥ 0x90 then .error "range_error"
        else match rest' with
          | [] => .ok []
          | c3 :: rest'' =>
            if !cont c3 then .error "range_error"
            else match rest'' with
              | [] => .ok []
              | c4 :: rest''' =>
                if !cont c4 then .error "range_error"
                else (fromBytes rest''').map
                  ((((c1 &&& 0x07) <<< 18) ||| ((c2.toNat &&& 0x3F) <<< 12) ||| ((c3.toNat &&& 0x3F) <<< 6) |||
                    (c4.toNat &&& 0x3F)) :: ·)
    else .error "range_error"

/-- `to_uppercase` with the corrected decoder (replaces round 2's `jUpper`). -/
def jUpper6 (loc : Locale) (s : List UInt8) : R :=
  match fromBytes s with
  | .ok cps => .str (cps.flatMap fun c => utf8 (towupper loc c))
  | .error e => .err e

/-- W4: the cut lead byte is dropped (""), a stray continuation byte throws; round 2's model threw
for both. -/
theorem w4_values : jUpper6 .utf8 [0xC3] = .str [] ∧ jUpper6 .utf8 [0xA9] = .err "range_error" ∧
    jUpper6 .utf8 (jstr [0x61, 0xE9]) = .str (jstr [0x41, 0xC9]) := by
  decide

theorem w4_round2_model : jUpper .utf8 [0xC3] = .err "std::range_error (wstring_convert)" := by
  simp [jUpper, decodeUtf8]

end Jank.R6.Str
