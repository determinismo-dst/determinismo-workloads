/-!
# Round 4: `clojure.pprint` and `clojure.stacktrace` as jank ships them

jank's `src/jank/clojure/pprint.jank` (7 lines) defines `pprint` as `(prn o)` and `write` as
`(pr o)`; `src/jank/clojure/stacktrace.jank` (6 lines) defines only `print-cause-trace`, as
`(print (str tr))`.

Clojure's pretty printer (clojure/pprint/dispatch.clj 92-101 `pprint-vector`): a vector is one
logical block whose separators are `:linear` newlines, so when the vector does not fit in
`*print-right-margin*` (72, pprint_base.clj 45) every separator breaks. That rule is replicated
here for vectors of integers (no nested blocks, no miser mode), enough to compare the two.
-/

namespace Jank.R4.Feedback.Pprint

/-- The flat text of a vector of integers, `[0 1 2]`. -/
def flat (xs : List Nat) : String := "[" ++ " ".intercalate (xs.map toString) ++ "]"

/-- jank's `pprint`: `prn`, the flat text and a newline. -/
def jankPprint (xs : List Nat) : String := flat xs ++ "\n"

/-- Clojure's `pprint` of a vector of integers: flat when it fits in 72 columns, else one
element per line, each after the first indented by the block's 1-column prefix. -/
def cljPprint (xs : List Nat) : String :=
  if (flat xs).length ≤ 72 then flat xs ++ "\n"
  else "[" ++ "\n ".intercalate (xs.map toString) ++ "]\n"

def lines (s : String) : Nat := (s.splitOn "\n").length - 1

/-- Public names of Clojure's namespaces (clojure/pprint/*.clj `defn`/`defmacro` without
`:private`; clojure/stacktrace.clj) against jank's. -/
def cljPprintNames : List String :=
  ["pprint", "pp", "write", "write-out", "print-table", "cl-format", "set-pprint-dispatch",
   "with-pprint-dispatch", "pprint-logical-block", "pprint-newline", "pprint-indent", "pprint-tab",
   "print-length-loop", "get-pretty-writer", "fresh-line", "formatter", "formatter-out"]
def jankPprintNames : List String := ["pprint", "write"]
def cljStacktraceNames : List String :=
  ["root-cause", "print-trace-element", "print-throwable", "print-stack-trace", "print-cause-trace", "e"]
def jankStacktraceNames : List String := ["print-cause-trace"]

def missing (clj jank : List String) : List String := clj.filter (· ∉ jank)

theorem pprint_missing :
    missing cljPprintNames jankPprintNames =
      ["pp", "write-out", "print-table", "cl-format", "set-pprint-dispatch", "with-pprint-dispatch",
       "pprint-logical-block", "pprint-newline", "pprint-indent", "pprint-tab", "print-length-loop",
       "get-pretty-writer", "fresh-line", "formatter", "formatter-out"] := by decide

theorem stacktrace_missing :
    missing cljStacktraceNames jankStacktraceNames =
      ["root-cause", "print-trace-element", "print-throwable", "print-stack-trace", "e"] := by decide

end Jank.R4.Feedback.Pprint
