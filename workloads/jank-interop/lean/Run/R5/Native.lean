import Jank.R5.Native.LdScript
import Jank.R5.Native.LdSpec
import Jank.R5.Native.Libs
import Jank.R5.Native.LibsWorld
import Jank.R5.Native.CApi
import Jank.R5.Native.LdTheorems
import Jank.R3.Search.Common

/-! Round 5 driver: native object loading and the C API (`jank5-native <part> [bound]`). -/

open Determinismo Jank.R3.Search

def censusAll (name : String) (run : Source → Ended) (maxRuns : Nat) : IO Unit := do
  let t0 ← IO.monoMsNow
  let c := censusUnder run #[] maxRuns
  printCensus name c
  let t1 ← IO.monoMsNow
  IO.println s!"  ({(t1 - t0) / 1000} s)"

/-- A census of one partition (the first decision fixed), for segmented runs. -/
def censusPart (name : String) (run : Source → Ended) (pfx : Array Nat) (maxRuns : Nat) : IO Unit := do
  let t0 ← IO.monoMsNow
  let c := censusUnder run pfx maxRuns
  printCensus s!"{name}, partition {pfx}" c
  let t1 ← IO.monoMsNow
  IO.println s!"  ({(t1 - t0) / 1000} s)"

namespace AotWorld
open Jank.R4.Modules.Aot Jank.R5.Native.CApi

structure W where
  decisions : Decisions

instance : Chaotic W where
  decisions w := w.decisions
  setDecisions w d := { w with decisions := d }

/-- Round 4's AOT world, with the dynamic runtime under the corrected run: every program whose
exit status differs from `clojure -M -m`, and every program where round 4's dynamic-runtime
status differs from the corrected one. -/
def body : EStateM Stop W Unit := do
  let b ← decide "b" bPool.length
  let h ← decide "app.head" appHead.length
  let t ← decide "app.tail" appTail.length
  let m ← decide "main" mainPool.length
  let p : Prog := { b := bPool[b]!, app := appHead[h]! ++ appTail[t]!, main := mainPool[m]! }
  let c := clojureRun p
  let r4 := aotRun p false
  let r5 := aotRunR5 p false
  if c.kind == "unresolved" then pure ()
  else if r4.status != r5.status then
    violate "R4->R5: round 4's dynamic-runtime status corrected (-main's throw is caught by jank_call2)"
      s!"program {repr p}; clojure -m status {c.status}; round 4 dynamic {r4.status}; corrected {r5.status} ({r5.phase})"
  else if r5.phase != "compile" && r5.status != c.status then
    violate s!"status differs in phase {r5.phase}" s!"program {repr p}; clojure {c.status}; jank dynamic AOT {r5.status}"

def run (source : Source) : Ended :=
  match body.run { decisions := { source } } with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }
  | .error (.nodeDown _) w => { taken := w.decisions.taken, violation := none }

end AotWorld

def examples : IO Unit := do
  let ex : List String :=
    [ "GROUP ( /lib/x86_64-linux-gnu/libc.so.6 /usr/lib/x86_64-linux-gnu/libc_nonshared.a  AS_NEEDED ( /lib64/ld-linux-x86-64.so.2 ) )",
      "/* GNU ld script */\nOUTPUT_FORMAT(elf64-x86-64)\nGROUP ( /lib/x86_64-linux-gnu/libm.so.6  AS_NEEDED ( /lib/x86_64-linux-gnu/libmvec.so.1 ) )",
      "INPUT ( libfoo_core.so libfoo_extra.so )",
      "INPUT(-lfoo)",
      "GROUP ( AS_NEEDED ( a.so ) )",
      "GROUP ( \"p(.so\" b.so )",
      "GROUP ( a.so",
      "/* GROUP ( a.so )",
      "",
      "GROUP ( \"a\\\\b.so\" )",
      "OUTPUT_FORMAT ( \"x)y\" ) GROUP ( a.so )",
      "INPUT ( a.so ) GROUP ( b.so )" ]
  for t in ex do
    IO.println s!"{repr t}\n  jank parse_ld_script: {repr (Jank.R5.Native.LdScript.parseStr t)}"

def main (args : List String) : IO Unit := do
  match args with
  | ["examples"] => examples
  | ["ld", n] => censusAll s!"ld scripts, ≤{n} tokens (16-token alphabet): jank vs GNU ld" (Jank.R5.Native.LdSpec.run n.toNat!) 100000000
  | ["ld-part", n, k] => censusPart s!"ld scripts, ≤{n} tokens" (Jank.R5.Native.LdSpec.run n.toNat!) #[n.toNat!, k.toNat!] 100000000
  | ["ldctl", n] => censusAll s!"control: glibc-shaped scripts, ≤{n} tokens, ≤1 required file" (Jank.R5.Native.LdSpec.controlRun n.toNat!) 100000000
  | ["libs"] => censusAll "-l world: JIT vs AOT link vs ld" Jank.R5.Native.LibsWorld.run 100000000
  | ["aot"] => censusAll "round 4's AOT world, dynamic runtime, corrected run" AotWorld.run 100000000
  | _ => IO.println "usage: jank5-native examples | ld N | ld-part N K | ldctl N | libs | aot"
