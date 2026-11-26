import Jank.R9.Err.Catch
import Jank.R9.Err.Paths

/-! Round 9, area E (`jank9-err`): errors as objects.

`walk`: every handler list of length ≤ 4 over 9 handler types, against 9 thrown values, under
stock, V7a and A34: the generated code (`fixedTry`, the nested try literally) against the
specification (`specTry`), and how often each differs from the stock code, by kind.
`nth`: every collection kind × index in [-3, 4], stock, X20, X20+X20b against Clojure. -/

open Jank.R5.Errors Jank.R9.Err

def handlerAlphabet : List H :=
  [.object, .errorRef, .std .exception, .std .runtimeError, .std .logicError, .std .invalidArity,
   .int, .default_, .std .badCast]

def thrownAlphabet : List Thrown :=
  [.obj (.kw "k"), .obj (.ex { message := "x", data := .keys ["k"] }),
   .err { kind := .analyzeUnresolvedSymbol, message := "Unable to resolve symbol 'nope'." },
   .err { kind := .runtimeModuleNotFound, message := "Unable to find module." },
   .std .invalidArity "Invalid call to `keyword` with `0` args provided.",
   .std .regexError "Invalid range in bracket expression.",
   .std .logicError "logic", .int 123, .foreign]

/-- Handler lists as jank's analyzer accepts them: `:default` only last, no type twice. -/
def valid (hs : List H) : Bool :=
  (hs.dropLast.all (· != .default_)) && hs.Nodup

def lists : Nat → List (List H)
  | 0 => [[]]
  | n + 1 => [] :: (handlerAlphabet.flatMap fun h => (lists n).map (h :: ·))

def walk : IO Unit := do
  let all := ((lists 4).eraseDups).filter valid
  let mut total := 0
  let mut specFail := 0
  let mut diffA := 0
  let mut diffV := 0
  let mut regress := 0
  for hs in all do
    for t in thrownAlphabet do
      total := total + 1
      for c in [Conv.stock, Conv.v7a, Conv.a34] do
        if fixedTry c hs t != specTry c hs t then specFail := specFail + 1
      let s := stockTry hs t
      let a := fixedTry .a34 hs t
      let v := fixedTry .v7a hs t
      if a != s then diffA := diffA + 1
      if v != s then diffV := diffV + 1
      -- a regression: stock ran a handler and A34 runs a different one or binds differently,
      -- for a value it does not convert
      match s, a with
      | .handled i _, .handled j _ => if i != j && !convertible .a34 t then regress := regress + 1
      | .handled _ _, .escapes _ => regress := regress + 1
      | _, _ => pure ()
  IO.println s!"walk: complete, {all.length} valid handler lists of length ≤ 4 (9 types) × {thrownAlphabet.length} thrown values = {total} cases"
  IO.println s!"  generated code = specification: {total * 3 - specFail} of {total * 3} (stock, V7a, A34); mismatches {specFail}"
  IO.println s!"  A34 differs from stock in {diffA} cases, V7a in {diffV}; regressions on unconverted values: {regress}"

def nthWalk : IO Unit := do
  let colls : List Coll := [.nil, .str 0, .str 3, .vec 0, .vec 2, .seq 0, .seq 2, .kw]
  let mut n := 0
  let mut stockOk := 0
  let mut x20Ok := 0
  let mut fixOk := 0
  for c in colls do
    for i in [(-3 : Int), -2, -1, 0, 1, 2, 3, 4] do
      n := n + 1
      let cl := cNth c i
      if (jNth false false c i).kindEq cl then stockOk := stockOk + 1
      if (jNth true false c i).kindEq cl then x20Ok := x20Ok + 1
      if (jNth true true c i).kindEq cl then fixOk := fixOk + 1
  IO.println s!"nth: complete, {n} cases (8 collections × indices -3..4): agree with Clojure (value / nil / an object throw): stock {stockOk}, X20 {x20Ok}, X20+X20b {fixOk}"

/-- The brief's tests: Clojure's observation, jank's on stock, with round 8's patch, and with
area E's fixes on top (A34 + V9 + V18 + X20b, the merged `err-all` diff). -/
def tests : List (String × String × String × String × String) :=
  [("r34", "ArityException (thrown? passes)", "nil, no throw (fail)", "invalid_arity<0>, std::runtime_error escapes is (error)", "pass (A34 converts it)"),
   ("v07b", ":object", ":error", ":error", "pass (A34/V7a)"),
   ("v07c", ":object", ":error", ":error", "pass (A34/V7a)"),
   ("v08", "nil (ns removed)", "ns kept (fail)", "pass (round 8's load-lib error_ref catch)", "pass (its object catch now sees the error first)"),
   ("v09", "{:vb3 1}", "nil (fail)", "nil (fail)", "pass (V9 + A34/V7a)"),
   ("v09b", "{:vb3b 1}", "nil (fail)", "nil (fail)", "pass (V9 + A34/V7a)"),
   ("v10", "[:object :object]", "[:native :object] (fail)", "pass (round 6's V10 delay)", "pass (A34 converts the rethrown native)"),
   ("v13", "not a string", "a string (fail)", "pass (round 6's V13)", "pass (X20b: nth throws an ex-info)"),
   ("v15", "nil", "std::runtime_error escapes (error)", "same", "error (no fix written)"),
   ("v18", "true, true", "false, false (fail)", "false, false (fail)", "pass (V18)"),
   ("d15", "thrown? passes", "std::runtime_error escapes (error)", "same", "pass (A34)"),
   ("u79", ":caught", "filesystem_error escapes (error)", "same", "pass (A34)"),
   ("u80", "[:a]", "std::runtime_error escapes (error)", "same", "error inside is (reduce-kv still unsupported)"),
   ("u90", "\"1\\n\" ...", "std::runtime_error escapes (error)", "same", "error inside is (sh env still needs strings)"),
   ("v03", "thrown? passes", "no throw (fail)", "std::runtime_error escapes (error)", "pass (A34 with V3)"),
   ("b30 s24 s27 s28 s32 s35", "a match / a pattern", "regex_error escapes (error)", "same", "error inside is (Clojure accepts the pattern)"),
   ("g480 g481 g482", "thrown? passes", "std::runtime_error escapes (error)", "same (X20's miss)", "pass (X20b, or A34)"),
   ("v07 x27 s17 a13 y10", "an object", ":error / escapes", "pass (V7r)", "pass (V7r; A34 alone too)"),
   ("ve1 ve1b (A34)", "thrown / a message", "error", "error", "pass"),
   ("ve2 ve2b ve2c (X20b)", "thrown / nil data", "error", "error", "pass"),
   ("ve3 ve3b ve3c (V7a)", "thrown / :outer", "error", "error", "pass"),
   ("ve4 ve4b (V18)", "compiler data / a cause", "error", "error", "pass (A34 alone: fail)"),
   ("ve5 (V9)", "{:ve5 1}", "error", "error", "pass (A34 alone: fail)"),
   ("ve6 (E9-1)", "a string", "error (ex-message of a string)", "nil (fail)", "nil (fail): no fix"),
   ("ve7 ve7b ve7c (controls)", "pass", "pass", "pass", "pass")]

def main (args : List String) : IO Unit := do
  match args with
  | ["walk"] => walk
  | ["nth"] => nthWalk
  | _ =>
    walk
    nthWalk
    IO.println "tests (Clojure 1.12.3 | stock | round 8's patch | + area E's fixes):"
    for (n, c, s, p, f) in tests do
      IO.println s!"  {n}: Clojure {c} | stock {s} | r8 {p} | E {f}"
