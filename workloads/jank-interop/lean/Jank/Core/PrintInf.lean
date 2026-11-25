import Determinismo

/-!
# Printing infinities and NaN with `print`, `println` and inside collections

Fork B covered doubles' digits (B15), strings and characters in `str` of a collection (B16) and
the printer's vars (B21); its `print-str` table had no infinities. This file covers them.

jank 7135b7708 (paths under `upstream-main/compiler+runtime/src/cpp/jank/runtime/`; unchanged since
f3d82d654):
- obj/number.cpp `small_real::to_string` (409): `"Infinity"`, `"-Infinity"`, `"NaN"`, else the
  digits; `small_real::to_code_string` (432): `"##Inf"`, `"##-Inf"`, `"##NaN"`, else
  `to_string` (`real::` 291/314 the same);
- core.cpp `print` (141), `print1` (161), `println` (169): each argument's `to_string`; `pr`
  (192), `prn` (213): `to_code_string`; core.jank `str` (one arg: `.to_string`), `pr-str`
  (`.to_code_string`);
- core/to_string.hpp `to_string(begin, end, …)` (28): a collection's elements by `to_string`;
  base_persistent_map.cpp `to_string_impl` (62) the same for maps.

Clojure 1.12 core_print.clj: `print-method Double` (131) writes `##Inf`, `##-Inf`, `##NaN`
whatever `*print-readably*` is; `print`/`println` go through `print-method`; `str` of a double
is `Double.toString` (`"Infinity"`, `"NaN"`); `str` of a collection is `RT.printString`
(`print-method`).
-/

namespace Jank.Core.PrintInf

/-- The values printed: special doubles, one ordinary double, and collections of them. -/
inductive PV where
  | inf | ninf | nan
  | d15
  | vec (xs : List PV)
  | map (kvs : List (String × PV))
  deriving Inhabited

/-- number.cpp 409 `to_string`. -/
def jankToStringAtom : PV → String
  | .inf => "Infinity"
  | .ninf => "-Infinity"
  | .nan => "NaN"
  | _ => "1.5"

/-- number.cpp 432 `to_code_string`. -/
def jankToCodeAtom : PV → String
  | .inf => "##Inf"
  | .ninf => "##-Inf"
  | .nan => "##NaN"
  | _ => "1.5"

mutual
/-- `to_string`: atoms by number.cpp 409, collections by to_string.hpp 28 / map 62. -/
def jankToString : PV → String
  | .vec xs => "[" ++ joinS xs ++ "]"
  | .map kvs => "{" ++ joinM kvs ++ "}"
  | v => jankToStringAtom v
def joinS : List PV → String
  | [] => ""
  | [x] => jankToString x
  | x :: xs => jankToString x ++ " " ++ joinS xs
def joinM : List (String × PV) → String
  | [] => ""
  | [(k, v)] => ":" ++ k ++ " " ++ jankToString v
  | (k, v) :: kvs => ":" ++ k ++ " " ++ jankToString v ++ ", " ++ joinM kvs
end

mutual
/-- `to_code_string` (and Clojure's `print-method` for these values: the same text). -/
def codeString : PV → String
  | .vec xs => "[" ++ joinC xs ++ "]"
  | .map kvs => "{" ++ joinCM kvs ++ "}"
  | v => jankToCodeAtom v
def joinC : List PV → String
  | [] => ""
  | [x] => codeString x
  | x :: xs => codeString x ++ " " ++ joinC xs
def joinCM : List (String × PV) → String
  | [] => ""
  | [(k, v)] => ":" ++ k ++ " " ++ codeString v
  | (k, v) :: kvs => ":" ++ k ++ " " ++ codeString v ++ ", " ++ joinCM kvs
end

def PV.code : PV → String := codeString

/-- What each printing function writes, in jank. -/
def jank (fn : String) (v : PV) : String :=
  match fn with
  | "str" => jankToString v
  | "print-str" => jankToString v
  | "println-str" => jankToString v ++ "\n"
  | _ => codeString v -- pr-str

/-- In Clojure: `str` of a double is `Double.toString`, of a collection `print-method`;
`print`/`println`/`pr` all go through `print-method`, which writes `##Inf`/`##NaN` for doubles. -/
def clj (fn : String) (v : PV) : String :=
  match fn with
  | "str" => match v with
    | .vec _ | .map _ => codeString v
    | a => jankToStringAtom a
  | "println-str" => codeString v ++ "\n"
  | _ => codeString v

def values : List PV :=
  let atoms := [PV.inf, .ninf, .nan, .d15]
  atoms ++ atoms.map (fun a => .vec [a]) ++ atoms.map (fun a => .map [("k", a)]) ++
    [.vec [.d15, .nan], .vec [.vec [.inf]]]

def fns : List String := ["str", "print-str", "println-str", "pr-str"]

/-- Every function on every value: those that print differently. -/
def table : List (String × String × String) := Id.run do
  let mut out := []
  for f in fns do
    for v in values do
      let j := jank f v
      let c := clj f v
      if j != c then out := out ++ [(s!"({f} {v.code})", c, j)]
  return out

theorem print_inf :
    jank "print-str" .inf = "Infinity" ∧ clj "print-str" .inf = "##Inf" ∧
    jank "str" (.vec [.nan]) = "[NaN]" ∧ clj "str" (.vec [.nan]) = "[##NaN]" := by
  decide

end Jank.Core.PrintInf
