import Jank.R4.Nrepl.SWorld

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

namespace Jank.R4.Nrepl
open Jank.R3.Nrepl

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

/-! ## Round 4: `try`, `binding` and loops in code strings -/

/-- jank's `catch` of a thrown object is `(catch cpp/jank.runtime.object_ref e …)` (book,
cpp-interop/native-exceptions.md); the spec reads it as Clojure's catch of what `throw` threw (NA9). -/
def fTry : List String :=
  ["(try (throw (ex-info \"x\" {})) (catch cpp/jank.runtime.object_ref e (ex-message e)))",
   "(try (println \"a\") 1 (finally (println \"f\")))",
   "(try (throw (ex-info \"x\" {})) (finally (print \"f\")))",
   "(try (throw (ex-info \"x\" {})) (catch cpp/jank.runtime.object_ref e (print \"c\") (throw (ex-info \"y\" {}))) (finally (print \"f\")))",
   "(try (throw (ex-info \"x\" {})) (catch cpp/jank.runtime.object_ref e (throw (ex-info \"y\" {}))) (finally (throw (ex-info \"z\" {}))))",
   "(try (throw (ex-info \"x\" {})) (finally (throw (ex-info \"z\" {}))))",
   "(try 1 (catch cpp/jank.runtime.object_ref e 2) (finally (print \"f\")))",
   "(try (def t1 (throw (ex-info \"d\" {}))) (catch cpp/jank.runtime.object_ref e 5))",
   "t1",
   "(try (in-ns 'tq) (finally (print \"f\")))",
   "(try (throw (ex-info \"x\" {})) (catch :default e (pr-str e)))",
   "(ex-message *e)",
   "(nil? *e)",
   "*1"]

def fBinding : List String :=
  ["(def ^:dynamic *d* 0)", "*d*", "(binding [*d* 1] *d*)",
   "(binding [*d* 1] (println *d*) (throw (ex-info \"b\" {})))",
   "(binding [*d* 2] (in-ns 'tb))", "(def nd 0)", "(binding [nd 1] nd)",
   "(binding [*d* 3] (def bd *d*))", "bd", "(str *ns*)"]

def fLoop : List String :=
  ["(dotimes [i 3] (print i))", "(loop [i 0] (when (< i 3) (print i) (recur (inc i))))",
   "(loop [i 0 acc (vector)] (if (< i 3) (recur (inc i) (conj acc i)) acc))",
   "(dotimes [i 2] (println (try (throw (ex-info \"l\" {})) (catch cpp/jank.runtime.object_ref e i))))",
   "(defn lp [n] (loop [i 0] (if (< i n) (recur (inc i)) i)))", "(lp 3)",
   "(binding [*d* 5] (dotimes [i 2] (print *d*)))"]

/-- The three, single requests and pairs of fragments, two requests per timeline. -/
def gTry : Grammar := { name := "gTry", forms := fTry, nsFields := [some "user"], len := 2 }
def gBinding : Grammar := { name := "gBinding", forms := fBinding, nsFields := [some "user"], len := 3 }
def gLoop : Grammar := { name := "gLoop", forms := fLoop ++ ["(def ^:dynamic *d* 0)"], nsFields := [some "user"], len := 2 }
def gTryAll : Grammar := { name := "gTryAll", forms := (fTry ++ fBinding ++ fLoop).eraseDups, pairs := false,
                           nsFields := [some "user"], len := 3 }

/-- The residual: every fragment above except the two triggers of found classes no variant sets
aside (D24's finally throwing after a handler threw; `(catch :default e …)` binding nil). -/
def fTryRes : List String :=
  ((fTry ++ fBinding ++ fLoop).eraseDups).filter fun f =>
    f != "(try (throw (ex-info \"x\" {})) (catch cpp/jank.runtime.object_ref e (throw (ex-info \"y\" {}))) (finally (throw (ex-info \"z\" {}))))" &&
    f != "(try (throw (ex-info \"x\" {})) (catch :default e (pr-str e)))" &&
    -- E5's trigger, and an unbound root printed (REPORT-3 S70's printing, another area's)
    f != "(ex-message *e)" && f != "t1"
def gTryRes : Grammar := { name := "gTryRes", forms := fTryRes, nsFields := [some "user"], len := 2 }

/-- E5: `*e` after a read or analysis error (safe_eval wraps the error_ref in an ex-info with no
message) against one thrown by `throw`. -/
def gExMsg : Grammar := {
  name := "gExMsg"
  forms := ["(ue5-undefined)", ")", "(throw (ex-info \"m\" {:k 1}))", "(ex-message *e)", "(ex-data *e)", "1"]
  nsFields := [some "user"]
  len := 3 }
def gTryRes3 : Grammar := { gTryRes with name := "gTryRes3", pairs := false, len := 3 }

def grammars : List Grammar := [gEval, gNs, gTopDo, gKnown, gResEval, gResNs, gLoad, gFile, gFileNone,
  gResidual, gResidualPairs, gResidual4, gLazyOut, gTry, gBinding, gLoop, gTryAll, gTryRes, gTryRes3, gExMsg]

def grammar? (n : String) : Option Grammar := grammars.find? (·.name == n)

end Jank.R4.Nrepl
