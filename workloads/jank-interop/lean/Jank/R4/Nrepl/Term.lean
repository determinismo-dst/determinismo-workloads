import Jank.R4.Nrepl.SWorld

/-!
# Round 4: jank's terminal REPL (`jank repl`)

terminal_repl_client.cpp `run` (283–379), jank 7135b7708:

- the nREPL server is started on a background thread (285–287), `*ns*` is `user` with clojure.core
  referred (289–292); `*1 *2 *3 *e` are bound to nil on this thread (323–327);
- the loop (337–376): `read_line` (223–244: `std::getline` when stdin is not a terminal, isocline's
  `ic_readline` otherwise) gives ONE line; it is trimmed; an empty line prints a newline; otherwise
  the line is written to a temp file and `__rt_ctx->eval_file(path_tmp)` runs it
  (context_dynamic.cpp 33–47 → `eval_string`: every form of the line, each analyzed whole);
- a value: `*3 ← *2 ← *1 ← v` and its `to_code_string` is printed; no value (a comment line):
  nothing; an exception (`std::exception`, a jank object, an `error_ref`, anything): printed by
  `print_exception` — `*e` is never set.

The spec: `clojure.main/repl` (main.clj) over the same input as one stream: a form may span lines,
each form is read, evaluated and printed; `*1 *2 *3` shift per form; an exception sets `*e`
(`repl-caught` → `(set! *e e)`), as the `*e` docstring says ("bound in a repl thread to the most
recent exception caught by the repl").
-/

namespace Jank.R4.Nrepl
open Jank.R3.Nrepl

/-- What the REPL shows for one evaluation: a printed value, or an error. -/
inductive Shown where
  | value (txt : String)
  | error
  deriving Repr, BEq, Inhabited

/-- jank's terminal REPL over `lines` (each line one `eval_file`). -/
def jankTerm (lines : List String) : List Shown × Option String := Id.run do
  let c := JConn.start
  let mut s := c.s
  let mut shown : Array Shown := #[]
  for line in lines do
    let input := line.trimAscii.toString
    if input.isEmpty then continue
    let mut r := EvRun.start input.toUTF8.toList
    for _ in [0:400] do
      if r.isDone then break
      let (r', s', _) := r.step s "/tmp/jank-repl-XXXXXX.jank"
      r := r'
      s := s'
    match r.phase with
    | .done (.ok (some v)) =>
      let o1 := (s.tb.deref s.w.slots v1).getD .nil
      let o2 := (s.tb.deref s.w.slots v2).getD .nil
      let tb := (s.tb.set v3 o2).toOption.getD s.tb
      let tb := (tb.set v2 o1).toOption.getD tb
      let tb := (tb.set v1 v).toOption.getD tb
      s := { s with tb }
      shown := shown.push (.value (prObj .jank s.w.heap v))
    | .done (.ok none) => pure ()
    | .done (.error (.unsupported m)) => return (shown.toList, some m)
    | .done (.error .fuel) => return (shown.toList, some "fuel")
    | .done (.error _) => shown := shown.push .error   -- print_exception; *e untouched
    | _ => return (shown.toList, some "step bound")
  return (shown.toList, none)

/-- clojure.main/repl over the same lines as one stream (REPL mode of the spec). -/
def cljTerm (lines : List String) : List Shown × Option String :=
  let code := "\n".intercalate lines
  let (_, _, o) := specEval cljBase {} code none .repl
  (o.items.map fun i => match i with
    | .value pr _ => Shown.value pr
    | .error => Shown.error, o.unsupported)

/-- The terminal REPL fragments: lines, some of them halves of one form. -/
def termLines : List String :=
  ["(def a 1)", "a", "(+ a", " 2)", "(throw (ex-info \"e\" {}))", "(nil? *e)", "*1", "1 2", ";; c", "(println \"p\")"]

end Jank.R4.Nrepl
