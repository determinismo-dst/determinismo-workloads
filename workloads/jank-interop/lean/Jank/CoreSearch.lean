import Determinismo
import Jank.Compare
import Jank.Multi
import Jank.Ns
import Jank.Nrepl

/-! Round 2, core: compare and sort, multimethods, namespaces, the nREPL server. -/

namespace Jank.CoreSearch

open Determinismo

def describe (c : Counterexample) : String :=
  s!"{c.property} after {c.runs} timelines, {c.taken.size} decisions: {c.detail}"

def indent (s : String) : String := (s.splitOn "\n").map ("    " ++ ·) |> "\n".intercalate

def report (name : String) (run : Source → Ended) (seeds : Nat) (maxRuns : Nat) : IO Unit := do
  IO.println s!"== {name}"
  match explore run seeds with
  | some c =>
    IO.println s!"  explore ({seeds} seeds): {describe c}"
    let s := shrink run c
    IO.println s!"  shrunk to {s.taken.size} decisions: {s.detail}"
    IO.println s!"  tape:\n{indent (tape s.taken)}"
  | none => IO.println s!"  explore ({seeds} seeds): nothing"
  match exhaust run maxRuns with
  | .found c =>
    IO.println s!"  exhaust: found after {c.runs} timelines: {c.detail}"
    let s := shrink run c
    IO.println s!"  exhaust's counterexample shrunk to {s.taken.size} decisions: {s.detail}"
    IO.println s!"  tape:\n{indent (tape s.taken)}"
  | .complete n => IO.println s!"  exhaust: complete, {n} timelines, nothing"
  | .stopped n => IO.println s!"  exhaust: stopped at {n} timelines, nothing"

section
open Jank.Compare
def compareSort : IO Unit := do
  report "compare: jank vs Clojure on every pair of the universe" (runBody comparePair) 3000 100000
  let t := pairTable
  IO.println s!"  table: {t.length} of {cvUniverse.length ^ 2} ordered pairs disagree"
  for (a, b, c, j) in t do
    IO.println s!"    (compare {a.code} {b.code}): Clojure {showCmp c}, jank {showCmp j}"
  report "sort: jank vs Clojure, vectors of 0-3 atoms" (runBody sortVec) 3000 100000
  report "sort with a comparator fn (excluding Clojure's int narrowing)" (runBody (sortFn true)) 3000 100000
  report "sort with a comparator fn (including Clojure's int narrowing)" (runBody (sortFn false)) 3000 100000
end

def namespaces : IO Unit := do
  report "namespaces: 1 operation in user" (Jank.Ns.run 1) 500 100000
  report "namespaces: 3 operations in user" (Jank.Ns.run 3) 3000 1000000
  report "namespaces: 3 operations, jank with intern and remove-ns fixed" (fun s => Jank.Ns.run 3 s true) 3000 1000000

def multimethods : IO Unit := do
  report "multimethods: 2 derives, 2 defmethods, 1 prefer-method, a call" (Jank.Multi.run 2 2 1) 3000 200000
  report "multimethods: 3 derives, 3 defmethods, 2 prefer-methods, a call" (Jank.Multi.run 3 3 2) 3000 3000000
  report "multimethods: 3 derives, 3 defmethods, no prefer-method, a call" (Jank.Multi.run 3 3 0) 3000 3000000
  report "multimethods: get-method after 1 derive, 1 defmethod" (fun s => Jank.Multi.run 1 1 0 s true) 300 100000

/-- Every timeline within the bounds (as `exhaust`, not stopping at a violation): how many, and
how many broke each property. -/
def census (run : Source → Ended) (maxRuns : Nat) : Nat × List (String × Nat) := Id.run do
  let mut path : Array Nat := #[]
  let mut counts : List (String × Nat) := []
  for i in List.range maxRuns do
    let o := run (Source.path path)
    if let some (p, _) := o.violation then
      counts := match counts.lookup p with
        | some n => (p, n + 1) :: counts.filter (·.1 != p)
        | none => (p, 1) :: counts
    match nextPath o.taken with
    | none => return (i + 1, counts)
    | some q => path := q
  return (maxRuns, counts)

def story (lines : Array String) : IO Unit := do
  for l in lines do IO.println s!"    {l}"

open Jank.Nrepl in
def nrepl : IO Unit := do
  for (label, roles, lb) in [("two connections, one eval each, stdout fully buffered", [Role.client, .client], false),
                             ("two connections, one eval each, stdout line-buffered (a terminal)", [Role.client, .client], true),
                             ("one eval beside a printer outside any capture (jank repl's terminal, a future), line-buffered", [Role.client, .printer], true),
                             ("one eval beside a printer outside any capture, fully buffered", [Role.client, .printer], false)] do
    let run := fun s => (runCapture roles lb s).1
    report s!"nREPL capture: {label}" run 3000 1000000
    let (n, counts) := census run 1000000
    IO.println s!"  census: {n} interleavings; broken: {counts}"
    match exhaust run 1000000 with
    | .found c =>
      let c := shrink run c
      IO.println s!"  story of the shrunk timeline ({c.taken.size} decisions):"
      story (runCapture roles lb (Source.path c.values)).2
    | _ => pure ()
    report s!"nREPL capture, spec (*out* per session): {label}" (runSpec roles) 100 1000000
  IO.println "== nREPL capture: the fixed race schedule (t0 starts, t1 starts, t0 prints and ends, t1 prints and ends), fully buffered"
  let (e, log) := runCapture [.client, .client] false (Source.path raceSchedule)
  IO.println s!"  {match e.violation with | some (p, d) => s!"{p}: {d}" | none => "nothing"}"
  story log
  -- Each difference on its own: the earlier ones fixed in jank's model, cumulatively.
  let steps : List (String × Fixes) := [
    ("jank as written", {}),
    ("missing ns fixed", { missingNs := true }),
    ("missing ns and printing errors fixed", { missingNs := true, printError := true }),
    ("... and stack overflow fixed", { missingNs := true, printError := true, stack := true }),
    ("... and per-session ns/*1/*e fixed", { missingNs := true, printError := true, stack := true, sessions := true }),
    ("... and interrupt fixed (all five: jank = nREPL expected)", Fixes.all) ]
  for (label, fx) in steps do
    report s!"nREPL sessions, 3 messages with interrupts, {label}" (runSessions fx 3 true) 3000 3000000
  IO.println "== nREPL sessions: hand-picked sequences (jank as written vs nREPL)"
  let seqs : List (List Msg) := [
    [.eval 1 .inNs none, .eval 1 .curNs none],
    [.eval 1 (.lit 1) none, .eval 2 (.lit 2) none, .eval 1 .star1 none],
    [.eval 1 .throws none, .eval 2 .starE none],
    [.eval 1 .lazyThrows none, .eval 1 (.lit 1) none, .eval 2 (.lit 2) none],
    [.eval 1 .forever none, .interrupt 1, .eval 2 (.lit 2) none],
    [.eval 1 (.lit 1) (some "foo")],
    [.eval 1 .recurse none, .eval 2 (.lit 2) none] ]
  for msgs in seqs do
    let (_, jr) := msgs.foldl (fun (acc : JankConn × List Resp) m => let (c, r) := jankStep {} acc.1 m; (c, acc.2 ++ [r])) ({}, [])
    let (_, cr) := msgs.foldl (fun (acc : SpecConn × List Resp) m => let (c, r) := specStepN acc.1 m; (c, acc.2 ++ [r])) ({}, [])
    IO.println s!"  {" ".intercalate (msgs.map Msg.code)}"
    IO.println s!"    nREPL: {", ".intercalate (cr.map Resp.code)}"
    IO.println s!"    jank:  {", ".intercalate (jr.map Resp.code)}"

def searches (args : List String) : IO Unit := do
  let only := args.head?
  if only.isNone || only == some "compare" then compareSort
  if only.isNone || only == some "multi" then multimethods
  if only.isNone || only == some "ns" then namespaces
  if only.isNone || only == some "nrepl" then nrepl

end Jank.CoreSearch
