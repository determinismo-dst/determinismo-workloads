import Elle.Props

/-!
# Minimal histories, written by hand from the counterexamples the searches found

Each is a history (invocations and completions, in real-time order), the workload, the models
to run it with, and what the property says. `Main.lean`'s `cases` mode checks each with the
replica and the specification and writes them out for real Elle (`runner/elle.sh`).
-/

namespace Elle.Cases

open Elle Elle.Spec

/-- A transaction: process, outcome, micro-ops (reads with what an `:ok` returned). -/
structure T where
  p : Nat
  status : OpType
  mops : List Mop

inductive Ev where
  | inv (t : Nat)
  | done (t : Nat)

def r (k : Nat) (l : List Int) : Mop := { f := .r, k, v := .list l }
def rnil (k : Nat) : Mop := { f := .r, k, v := .nil }
def a (k : Nat) (e : Int) : Mop := { f := .append, k, v := .int e }
def rv (k : Nat) (v : Int) : Mop := { f := .r, k, v := .int v }
def w (k : Nat) (v : Int) : Mop := { f := .w, k, v := .int v }
def rv0 (k : Nat) : Mop := { f := .r, k, v := .nil }

def build (ts : List T) (evs : List Ev) : History := Id.run do
  let mut ops : Array Op := #[]
  for e in evs do
    match e with
    | .inv i =>
      let t := ts.getD i { p := 0, status := .ok, mops := [] }
      ops := ops.push { index := ops.size, type := .invoke, process := t.p,
                        value := t.mops.map fun m => if m.f == .r then { m with v := .nil } else m }
    | .done i =>
      let t := ts.getD i { p := 0, status := .ok, mops := [] }
      let v := if t.status == .ok then t.mops else t.mops.map fun m => if m.f == .r then { m with v := .nil } else m
      ops := ops.push { index := ops.size, type := t.status, process := t.p, value := v }
  return ops

/-- Each transaction invoked and completed in turn. -/
def serial (ts : List T) : History := build ts ((List.range ts.length).flatMap fun i => [.inv i, .done i])

structure Case where
  name : String
  workload : Gen.Workload
  h : History
  /-- Model sets to run Elle with. -/
  models : List (List String)
  note : String

def cases : List Case := [
  { name := "unobserved-appends-g-single"
    workload := .listAppend
    -- T1 reads x=[] and appends to y; T2 reads y=[] and appends to y and x. Neither append to y
    -- is read: Elle infers T1 -rw-> T2 (x) and T2 -rw-> T1 (y) and calls it G2-item. In both
    -- orders of y's appends the DSG has a cycle with exactly one rw edge (G-single).
    h := build [{ p := 0, status := .ok, mops := [r 0 [], a 1 1] },
                { p := 1, status := .ok, mops := [r 1 [], a 1 2, a 0 1] }]
               [.inv 0, .inv 1, .done 0, .done 1]
    models := [["snapshot-isolation"], ["consistent-view"], ["repeatable-read"]]
    note := "G-single in every interpretation; Elle reports G2-item, SI and consistent-view valid" },
  { name := "process-order-skips-info"
    workload := .listAppend
    -- Process 0 appends 1 to x, then (indeterminate) 2. A read shows [2 1]: the second write
    -- installed first. Session order T0 -> T1, version order T1 -> T0: G0-process.
    h := build [{ p := 0, status := .ok, mops := [a 0 1] },
                { p := 0, status := .info, mops := [a 0 2] },
                { p := 1, status := .ok, mops := [r 0 [2, 1]] }]
               [.inv 0, .done 0, .inv 1, .done 1, .inv 2, .done 2]
    models := [["strong-session-read-uncommitted"], ["strong-session-serializable"], ["strong-read-uncommitted"]]
    note := "G0-process in every interpretation (the info txn committed: its write was read)" },
  { name := "realtime-replaces-process"
    workload := .listAppend
    -- One process appends to x, then reads x = []: it does not see its own write.
    h := serial [{ p := 0, status := .ok, mops := [a 0 1] }, { p := 0, status := .ok, mops := [r 0 []] }]
    models := [["strong-session-snapshot-isolation"],
               ["strong-session-snapshot-isolation", "strong-read-uncommitted"],
               ["strong-session-serializable"], ["strong-session-serializable", "strong-read-uncommitted"]]
    note := "G-single-process; with a realtime model beside it Elle drops process edges" },
  { name := "failed-append-hides-ww"
    workload := .listAppend
    -- x's trace [1 2 3]: W's 1, F's (failed) 2, U's 3, so W's version precedes U's;
    -- y's [1 2]: U before W. G0 in every interpretation; Elle links U's append to F (absent).
    h := serial [{ p := 0, status := .ok, mops := [a 0 1, a 1 2] },
                 { p := 1, status := .fail, mops := [a 0 2] },
                 { p := 2, status := .ok, mops := [a 0 3, a 1 1] },
                 { p := 3, status := .ok, mops := [r 0 [1, 2, 3]] },
                 { p := 4, status := .ok, mops := [r 1 [1, 2]] }]
    models := [["read-uncommitted"]]
    note := "G0 in every interpretation (with G1a and a dirty update); read-uncommitted allows those" },
  { name := "info-write-may-have-aborted"
    workload := .listAppend
    -- T (indeterminate) appends x 1, y 2; U appends x 2, y 1; reads show x [1 2], y [1 2].
    -- If T committed: G0. If T aborted: an aborted read and a dirty update, no G0.
    h := serial [{ p := 0, status := .info, mops := [a 0 1, a 1 2] },
                 { p := 1, status := .ok, mops := [a 0 2, a 1 1] },
                 { p := 2, status := .ok, mops := [r 0 [1, 2]] },
                 { p := 3, status := .ok, mops := [r 1 [1, 2]] }]
    models := [["read-uncommitted"], ["read-committed"]]
    note := "an interpretation (T aborted) has only G1a and a dirty update, which read-uncommitted allows" },
  { name := "register-fuzzy-read"
    workload := .register
    -- T reads x = 1, then x = 2 (a non-repeatable read).
    h := serial [{ p := 0, status := .ok, mops := [w 0 1] },
                 { p := 1, status := .ok, mops := [w 0 2] },
                 { p := 2, status := .ok, mops := [rv 0 1, rv 0 2] }]
    models := [["repeatable-read"], ["consistent-view"], ["snapshot-isolation"]]
    note := "G-single in every interpretation; Elle reports only :internal" },
  { name := "register-second-read-g1c"
    workload := .register
    -- T0 reads x = 2 (T1's write) and writes y = 1; T1 reads y = nil, then y = 1 (T0's
    -- write), and writes x = 2. wr both ways: G1c, whatever the version orders.
    h := build [{ p := 0, status := .ok, mops := [rv 0 2, w 1 1] },
                { p := 1, status := .ok, mops := [rv0 1, rv 1 1, w 0 2] }]
               [.inv 0, .inv 1, .done 0, .done 1]
    models := [["read-committed"], ["serializable"]]
    note := "G1c in every interpretation; Elle infers wr only from each transaction's first read of a key" },
  { name := "register-future-read"
    workload := .register
    -- T reads x = 1, then writes x = 1: it read its own later write.
    h := serial [{ p := 0, status := .ok, mops := [rv 0 1, w 0 1] }]
    models := [["strict-serializable"], ["serializable"]]
    note := "no Adya history: a read of a version its own later write installs" },
  { name := "value-hash-order-a"
    workload := .listAppend
    -- Two committed appends to x, read as [1] and [2] (incompatible); y shows T1 before T0.
    -- Elle takes x's order from the last longest read in Clojure's hash-set order.
    h := serial [{ p := 0, status := .ok, mops := [a 0 1, a 1 4] },
                 { p := 1, status := .ok, mops := [a 0 2, a 1 3] },
                 { p := 2, status := .ok, mops := [r 0 [1]] },
                 { p := 3, status := .ok, mops := [r 0 [2]] },
                 { p := 4, status := .ok, mops := [r 1 [3, 4]] }]
    models := [["read-uncommitted"]]
    note := "the same history with x's elements 1 and 2 swapped is value-hash-order-b" },
  { name := "value-hash-order-b"
    workload := .listAppend
    h := serial [{ p := 0, status := .ok, mops := [a 0 2, a 1 4] },
                 { p := 1, status := .ok, mops := [a 0 1, a 1 3] },
                 { p := 2, status := .ok, mops := [r 0 [2]] },
                 { p := 3, status := .ok, mops := [r 0 [1]] },
                 { p := 4, status := .ok, mops := [r 1 [3, 4]] }]
    models := [["read-uncommitted"]]
    note := "value-hash-order-a with x's elements renamed" },
  { name := "register-initial-state-g-single"
    workload := .register
    -- The register form of unobserved-appends-g-single: nil precedes every value, so every
    -- reader of nil gets an rw edge to every writer, where the DSG has a ww edge.
    h := build [{ p := 0, status := .ok, mops := [rv0 0, w 1 1] },
                { p := 1, status := .ok, mops := [rv0 1, w 1 2, w 0 1] }]
               [.inv 0, .inv 1, .done 0, .done 1]
    models := [["snapshot-isolation"], ["consistent-view"]]
    note := "G-single in every interpretation; Elle reports G2-item" },
  { name := "search-type-recorded-as-other"
    workload := .listAppend
    -- From the differential run: the G1c-realtime search finds a cycle the explainer calls
    -- G-single-item-realtime, records it under that type, and marks G1c-realtime done.
    h := build [{ p := 0, status := .ok, mops := [r 0 [2, 1]] },
                { p := 1, status := .ok, mops := [a 0 2] },
                { p := 0, status := .ok, mops := [r 1 []] },
                { p := 0, status := .ok, mops := [r 0 [2], r 1 []] },
                { p := 0, status := .ok, mops := [a 0 1] }]
               [.inv 0, .done 0, .inv 1, .inv 2, .done 2, .inv 3, .done 3, .inv 4, .done 1, .done 4]
    models := [["strong-read-committed"], ["strict-serializable"]]
    note := "a G1c-realtime cycle exists (T9 -wr-> T1 -rt-> T8 -ww-> T9); Elle names only strong-PL-2-cycle-exists" },
  { name := "info-may-have-aborted-2txn"
    workload := .listAppend
    -- From the exhaustive search: T0 appends 1 and reads [2 1]; T1, invoked later and
    -- indeterminate, appends 2 then 3. Elle: T1 -ww-> T0 (2 before 1) and T0 -ww-> T1 (T1's
    -- unread 3 after 1). T1 cannot have committed (its version [2 3] and T0's [2 1] are not on
    -- one trace); aborted, T0 built on its aborted version: a dirty update, no G0.
    h := serial [{ p := 0, status := .ok, mops := [a 0 1, r 0 [2, 1]] },
                 { p := 0, status := .info, mops := [a 0 2, a 0 3] }]
    models := [["read-uncommitted"]]
    note := "read uncommitted is satisfiable; Elle reports G0" },
  { name := "process-skips-info-2txn"
    workload := .listAppend
    -- T0 reads x = [1], written by T1, which the same process invokes after T0 completes and
    -- which is indeterminate: committed, it is G1c-process; aborted, G1a.
    h := serial [{ p := 0, status := .ok, mops := [r 0 [1]] },
                 { p := 0, status := .info, mops := [a 0 1] }]
    models := [["strong-session-read-committed"], ["strong-read-committed"]]
    note := "strong session read committed violated in every interpretation" },
  { name := "register-info-write-read-early"
    workload := .register
    -- T0 reads x = 1, written only by T1, which its process invokes after T0 completes and
    -- which is indeterminate: committed, G1c-realtime; aborted, G1a.
    h := serial [{ p := 0, status := .ok, mops := [rv 0 1] }, { p := 0, status := .info, mops := [w 0 1] }]
    models := [["strict-serializable"]]
    note := "violated in every interpretation; rw-register indexes only :ok writes (a TODO in its code)" },
  { name := "list-append-garbage-read"
    workload := .listAppend
    h := serial [{ p := 0, status := .ok, mops := [r 0 [7]] }]
    models := [["strict-serializable"]]
    note := "a read of an element nobody appended" }]

end Elle.Cases
