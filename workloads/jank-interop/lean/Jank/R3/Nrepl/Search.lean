import Jank.R3.Nrepl.World

/-!
# Round 3, nREPL: grammars and searches for World S

Grammars of jank code strings (each a list of one-form fragments; a code string is one fragment
or two joined by a space):

- `gEval`: values, defs, fns, macros defined in one eval and used in the next, output with and
  without a newline, exceptions, `*1`/`*2`/`*e`, a reader error;
- `gNs`: namespace switches (`ns`, `in-ns`, inside a top-level `do`), `ns` fields, lookups and
  completions of what the evals defined, aliases;
- `gKnown`: the triggers of round-2 entries (R126 a value that throws while printed, R132 code with
  no form, R136 whitespace-only output, R127 two sessions);
- `gTopDo`: top-level `do` forms (N1);
- `gResidual*`: the grammars with every found class's trigger removed.
-/

namespace Jank.R3.Nrepl

open Determinismo

/-- Seeds through a SplitMix64 finalizer (consecutive `mkStdGen` seeds draw alike; REPORT-2
"Library gaps"). -/
def mix64 (x : Nat) : Nat :=
  let m : Nat := 2 ^ 64
  let z := (x + 0x9E3779B97F4A7C15) % m
  let z := ((z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9) % m
  let z := ((z ^^^ (z >>> 27)) * 0x94D049BB133111EB) % m
  z ^^^ (z >>> 31)

def exploreMixed (run : Source → Ended) (count : Nat) (first : Nat := 0) : Option Counterexample := Id.run do
  for i in List.range count do
    let o := run (Source.seeded (mix64 (first + i)))
    if let some (property, detail) := o.violation then
      return some { taken := o.taken, property, detail, runs := i + 1 }
  return none

/-! ## Grammars -/

def fEval : List String :=
  ["1", "(def a 1)", "a", "(def a (inc a))", "(defn f [x] (+ x 1))", "(f 1)",
   "(defmacro m [x] (list 'inc x))", "(m 1)", "(println \"x\")", "(print \"y\")",
   "(throw (ex-info \"e\" {}))", "*1", "*2", "(nil? *e)", ")", "(", "(pr-str (map inc [1 2]))"]

def fNs : List String :=
  ["(ns foo)", "(in-ns 'foo)", "(str *ns*)", "(def b 1)", "b", "foo/b", "user/b",
   "(ns bar (:require [clojure.string :as str]))", "(str/join [1 2])", "(defn g [] 2)", "(g)"]

def qNs : List SReq :=
  [.lookup "user" "b", .lookup "foo" "b", .info "foo" "b", .lookup "user" "g", .lookup "foo" "g",
   .lookup "bar" "str/join", .lookup "user" "map", .completions "foo" "b", .completions "user" "g",
   .lookup "clojure.core" "iteration"]

def gEval : Grammar := { name := "gEval", forms := fEval, len := 3 }

def gNs : Grammar := {
  name := "gNs"
  forms := fNs
  nsFields := [some "user", some "foo", none]
  queries := qNs
  len := 3 }

def gTopDo : Grammar := {
  name := "gTopDo"
  forms := ["(do (defmacro m2 [] 2) (m2))", "(m2)", "(do (in-ns 'foo) (def c 1))", "c", "foo/c", "user/c",
            "(do (ns baz) (defn h [] 3))", "(h)", "baz/h", "user/h", "(do (in-ns 'foo) (str *ns*))", "(str *ns*)",
            "(do (require '[clojure.string :as s]) (s/join [1 2]))", "(s/join [3 4])"]
  nsFields := [some "user"]
  len := 2 }

def gKnown : Grammar := {
  name := "gKnown"
  forms := ["(map (fn [_] (throw (ex-info \"p\" {}))) [1])", "(nil? *e)", ";; c", "#_x", "*1",
            "(println)", "(print \" \")", "(println \"x\")", "(def a 1)", "(in-ns 'foo)", "(str *ns*)"]
  nsFields := [some "user", none]
  sessions := 2
  len := 3 }

/-- `load-file` (handler/eval.jank:74): file contents of several forms. -/
def gLoad : Grammar := {
  name := "gLoad"
  forms := ["(def a 1)", "a", "(println \"x\")", "(throw (ex-info \"e\" {}))", "*1"]
  pairs := false
  loadFiles := ["(def a 1) (def b 2) b", "(ns lf) (def c 3)", "(println \"l\") 4", "(def d 4) (throw (ex-info \"e\" {})) (def e 5)",
                "(def f 6) )", ";; only a comment", "c", "(in-ns 'lf2) (def g 7)"]
  nsFields := [some "user", none]
  len := 3 }

/-- The `file` field (R31's `:jank/macro-expansion` meta needs a source with a file). -/
def gFile : Grammar := {
  name := "gFile"
  forms := ["(defmacro mk [& xs] (vec xs))", "(meta (mk 1 2))", "(mk 1 2)", "*ns*"]
  files := [none, some "src/user.clj"]
  nsFields := [some "user"]
  len := 3 }

def gFileNone : Grammar := { gFile with name := "gFileNone", files := [none] }

/-- Values whose printing prints (lazy sequences with side effects): `do-eval` prints `*1` after
`with-capture` ended (handler/eval.jank:31–36, 59). -/
def gLazyOut : Grammar := {
  name := "gLazyOut"
  forms := ["(map println [1 2])", "(map (fn [x] (print x) x) [1 2])", "(println \"a\")", "(doall (map println [3]))", "*1"]
  nsFields := [some "user"]
  len := 2 }

/-- Every fragment of the grammars above except the triggers whose class no aside neutralizes
without the two processes diverging: R126 (a value that throws while printed), R132 (code with no
form), R31 (a `file` field). -/
def fResidual : List String :=
  (fEval ++ fNs ++ gTopDo.forms ++ ["(nil? *e)", "*1", "(println)", "(print \" \")", "(in-ns 'foo)", "*ns*",
     "(defmacro mk [& xs] (vec xs))", "(meta (mk 1 2))"]).eraseDups

def gResidual : Grammar := {
  name := "gResidual"
  forms := fResidual
  pairs := false
  nsFields := [some "user", some "foo", none]
  sessions := 2
  queries := qNs ++ [.info "user" "f", .completions "foo" "c", .lookup "baz" "h"]
  loadFiles := ["(def a 1) (def b 2) b", "(ns lf) (def c 3)", "(println \"l\") 4", "(def d 4) (throw (ex-info \"e\" {})) (def e 5)",
                "(def f 6) )", "c", "(in-ns 'lf2) (def g 7)"]
  len := 2 }

/-- The same with code strings of two fragments (evals only, one request). -/
def gResidualPairs : Grammar := { gResidual with name := "gResidualPairs", pairs := true, queries := [], loadFiles := [], sessions := 1, len := 1 }

/-- The residual grammar, four requests (random exploration). -/
def gResidual4 : Grammar := { gResidual with name := "gResidual4", len := 4 }

def gResEval : Grammar := { gEval with name := "gResEval" }
def gResNs : Grammar := { gNs with name := "gResNs" }

def grammars : List Grammar := [gEval, gNs, gTopDo, gKnown, gResEval, gResNs, gLoad, gFile, gFileNone,
  gResidual, gResidualPairs, gResidual4, gLazyOut]

def grammar? (n : String) : Option Grammar := grammars.find? (·.name == n)

end Jank.R3.Nrepl
